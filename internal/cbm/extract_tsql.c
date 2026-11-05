/*
 * extract_tsql.c -- Microsoft SQL Server (T-SQL) object scripts, read from the text.
 *
 * The vendored SQL grammar parses ANSI SQL. On SQL Server object scripts
 * (`CREATE OR ALTER PROCEDURE [dbo].[x] ... GO`) most files come back
 * parse_partial and no procedure becomes a definition, so a .sql file that looks
 * like T-SQL (cbm_tsql_looks_like) is read here instead:
 *   - CREATE/ALTER PROCEDURE|FUNCTION|TRIGGER|VIEW and CREATE TABLE start an
 *     object: routines and views are Function / Class definitions spanning their
 *     batch (up to the next object, GO or end of file); extra prop `sql_kind`.
 *   - In a routine or view body: EXEC[UTE] <routine> and FROM/JOIN <tvf>(...) are
 *     calls; FROM/JOIN/APPLY <table> is a read; INSERT [INTO], UPDATE, DELETE
 *     [FROM], MERGE [INTO], TRUNCATE TABLE and SELECT ... INTO <table> are writes
 *     (rw records -> READS / WRITES edges). `UPDATE a ... FROM tbl a` and
 *     `DELETE a FROM tbl a` write through the alias to `tbl`.
 * Temp tables (#t), table variables (@t) and CTE names are never objects. A name
 * is the last part of a multipart name without brackets: [dbo].[tblX] -> tblX.
 * Dynamic SQL inside string literals is not read.
 */
#include "arena.h"
#include "cbm.h"
#include "helpers.h"
#include "foundation/constants.h"

#include <ctype.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

enum {
    TSQL_NAME_MAX = 128,    /* longest object or alias name kept */
    TSQL_SNIFF_MAX = 65536, /* bytes cbm_tsql_looks_like inspects */
    TSQL_MAX_CTES = 64,
    TSQL_MAX_PENDING = 128, /* UPDATE/DELETE targets that may still be an alias */
    TSQL_MAX_SEEN = 1024,   /* distinct (name, kind) facts per object */
};

typedef enum { TK_WORD, TK_VAR, TK_TEMP, TK_NUM, TK_PUNCT, TK_GO } tsql_kind;

typedef struct {
    tsql_kind kind;
    const char *text; /* WORD/VAR/TEMP: identifier text without brackets/quotes */
    int len;
    int line;
    char ch;          /* PUNCT: the character */
    bool line_start;  /* first token on its line (GO detection) */
} tsql_tok;

typedef struct {
    tsql_tok *items;
    int count;
    int cap;
} tsql_toks;

static bool toks_push(tsql_toks *t, tsql_tok tok) {
    if (t->count == t->cap) {
        int cap = t->cap ? t->cap * 2 : 1024;
        tsql_tok *grown = realloc(t->items, (size_t)cap * sizeof(tsql_tok));
        if (!grown) {
            return false;
        }
        t->items = grown;
        t->cap = cap;
    }
    t->items[t->count++] = tok;
    return true;
}

static bool is_ident_start(unsigned char c) {
    return isalpha(c) || c == '_' || c >= 0x80;
}

static bool is_ident_char(unsigned char c) {
    return isalnum(c) || c == '_' || c == '$' || c == '#' || c == '@' || c >= 0x80;
}

/* Tokenize: comments and string literals are skipped, [bracketed] and
 * "quoted" identifiers become WORD tokens holding their inner text. */
static bool tsql_lex(const char *s, int n, tsql_toks *out) {
    int i = 0;
    int line = 1;
    bool line_start = true;
    while (i < n) {
        unsigned char c = (unsigned char)s[i];
        if (c == '\n') {
            line++;
            line_start = true;
            i++;
            continue;
        }
        if (isspace(c)) {
            i++;
            continue;
        }
        if (c == '-' && i + 1 < n && s[i + 1] == '-') { /* line comment */
            while (i < n && s[i] != '\n') {
                i++;
            }
            continue;
        }
        if (c == '/' && i + 1 < n && s[i + 1] == '*') { /* block comment, nests in T-SQL */
            int depth = 1;
            i += 2;
            while (i < n && depth > 0) {
                if (s[i] == '\n') {
                    line++;
                } else if (s[i] == '/' && i + 1 < n && s[i + 1] == '*') {
                    depth++;
                    i++;
                } else if (s[i] == '*' && i + 1 < n && s[i + 1] == '/') {
                    depth--;
                    i++;
                }
                i++;
            }
            continue;
        }
        if (c == '\'' || ((c == 'N' || c == 'n') && i + 1 < n && s[i + 1] == '\'')) {
            i += (c == '\'') ? 1 : 2; /* N'...' unicode literal */
            while (i < n) {
                if (s[i] == '\n') {
                    line++;
                }
                if (s[i] == '\'') {
                    if (i + 1 < n && s[i + 1] == '\'') { /* '' escape */
                        i += 2;
                        continue;
                    }
                    i++;
                    break;
                }
                i++;
            }
            line_start = false;
            continue;
        }
        tsql_tok tok = {.line = line, .line_start = line_start};
        line_start = false;
        if (c == '[' || c == '"') {
            char close = c == '[' ? ']' : '"';
            int start = ++i;
            while (i < n && !(s[i] == close && !(i + 1 < n && s[i + 1] == close))) {
                if (s[i] == close) { /* doubled delimiter escape */
                    i++;
                }
                if (s[i] == '\n') {
                    line++;
                }
                i++;
            }
            tok.kind = TK_WORD;
            tok.text = s + start;
            tok.len = i - start;
            if (i < n) {
                i++;
            }
        } else if (c == '@' || c == '#') {
            int start = i++;
            while (i < n && is_ident_char((unsigned char)s[i])) {
                i++;
            }
            tok.kind = c == '@' ? TK_VAR : TK_TEMP;
            tok.text = s + start;
            tok.len = i - start;
        } else if (is_ident_start(c)) {
            int start = i++;
            while (i < n && is_ident_char((unsigned char)s[i])) {
                i++;
            }
            tok.kind = TK_WORD;
            tok.text = s + start;
            tok.len = i - start;
            if (tok.line_start && tok.len == 2 && (s[start] == 'G' || s[start] == 'g') &&
                (s[start + 1] == 'O' || s[start + 1] == 'o')) {
                int k = i;
                while (k < n && (s[k] == ' ' || s[k] == '\t' || s[k] == '\r' ||
                                 isdigit((unsigned char)s[k]))) {
                    k++;
                }
                if (k >= n || s[k] == '\n' || (s[k] == '-' && k + 1 < n && s[k + 1] == '-')) {
                    tok.kind = TK_GO;
                }
            }
        } else if (isdigit(c)) {
            int start = i;
            while (i < n && (isalnum((unsigned char)s[i]) || s[i] == '.')) {
                i++;
            }
            tok.kind = TK_NUM;
            tok.text = s + start;
            tok.len = i - start;
        } else {
            tok.kind = TK_PUNCT;
            tok.ch = (char)c;
            tok.text = s + i;
            tok.len = 1;
            i++;
        }
        if (!toks_push(out, tok)) {
            return false;
        }
    }
    return true;
}

static bool word_is(const tsql_tok *t, const char *kw) {
    if (!t || t->kind != TK_WORD) {
        return false;
    }
    size_t n = strlen(kw);
    if ((size_t)t->len != n) {
        return false;
    }
    for (size_t i = 0; i < n; i++) {
        if (toupper((unsigned char)t->text[i]) != kw[i]) {
            return false;
        }
    }
    return true;
}

/* Words that end a table reference, so they are never read as an alias. */
static bool is_clause_word(const tsql_tok *t) {
    static const char *const kws[] = {
        "WHERE",  "ON",      "JOIN",    "INNER",   "LEFT",     "RIGHT",    "FULL",    "OUTER",
        "CROSS",  "GROUP",   "ORDER",   "HAVING",  "UNION",    "EXCEPT",   "INTERSECT", "SET",
        "WITH",   "OPTION",  "FOR",     "INTO",    "VALUES",   "SELECT",   "FROM",    "AND",
        "OR",     "WHEN",    "THEN",    "ELSE",    "END",      "BEGIN",    "IF",      "WHILE",
        "RETURN", "DECLARE", "EXEC",    "EXECUTE", "INSERT",   "UPDATE",   "DELETE",  "MERGE",
        "USING",  "OUTPUT",  "PIVOT",   "UNPIVOT", "APPLY",    "TABLESAMPLE", "AS",   "NOT",
        "NULL",   "IS",      "IN",      "EXISTS",  "CASE",     "TOP",      "DISTINCT", "ALL",
        "OFFSET", "FETCH",   "PRINT",   "RAISERROR", "THROW",  "COMMIT",   "ROLLBACK", "BREAK",
        "CONTINUE", "GOTO",  "WAITFOR", "CLOSE",   "OPEN",     "DEALLOCATE", "TRUNCATE", "CREATE",
        "ALTER",  "DROP",    "GO",      NULL};
    if (!t || t->kind != TK_WORD) {
        return false;
    }
    for (const char *const *k = kws; *k; k++) {
        if (word_is(t, *k)) {
            return true;
        }
    }
    return false;
}

static void lower_into(char *dst, const char *src, int len) {
    for (int i = 0; i < len; i++) {
        dst[i] = (char)tolower((unsigned char)src[i]);
    }
    dst[len] = '\0';
}

/* Read a multipart object name starting at tokens[*pos]: part ('.' part)*,
 * where `db..tbl` leaves an empty schema. Copies the LAST part into `name` and
 * returns its token kind (TK_WORD for an object, TK_VAR / TK_TEMP for @x / #x),
 * or -1 when tokens[*pos] starts no name. *pos ends on the token after it. */
static int read_object_name(const tsql_toks *tk, int *pos, char *name, int cap) {
    int p = *pos;
    if (p >= tk->count) {
        return -1;
    }
    const tsql_tok *first = &tk->items[p];
    if (first->kind != TK_WORD && first->kind != TK_VAR && first->kind != TK_TEMP) {
        return -1;
    }
    const tsql_tok *last = first;
    p++;
    while (p + 1 < tk->count && tk->items[p].kind == TK_PUNCT && tk->items[p].ch == '.') {
        const tsql_tok *nx = &tk->items[p + 1];
        if (nx->kind == TK_PUNCT && nx->ch == '.') { /* db..tbl */
            p++;
            continue;
        }
        if (nx->kind != TK_WORD && nx->kind != TK_TEMP) {
            break;
        }
        last = nx;
        p += 2;
    }
    if (last->len <= 0 || last->len >= cap) {
        return -1;
    }
    memcpy(name, last->text, (size_t)last->len);
    name[last->len] = '\0';
    *pos = p;
    return (int)last->kind;
}

typedef enum { OBJ_NONE, OBJ_PROC, OBJ_FUNC, OBJ_TRIGGER, OBJ_VIEW, OBJ_TABLE } tsql_obj_kind;

typedef struct {
    char name[TSQL_NAME_MAX];
    int line;
} tsql_pending;

/* ASCII case-insensitive equality (T-SQL names compare case-insensitively under
 * the default collations); portable where strcasecmp is not. */
static bool ci_equal(const char *a, const char *b) {
    for (; *a && *b; a++, b++) {
        if (tolower((unsigned char)*a) != tolower((unsigned char)*b)) {
            return false;
        }
    }
    return *a == *b;
}

typedef struct {
    CBMExtractCtx *ctx;
    tsql_obj_kind kind;
    const char *qn;
    const char *name;
    int start_line;
    int end_line;
    char ctes[TSQL_MAX_CTES][TSQL_NAME_MAX];
    int cte_n;
    tsql_pending pending[TSQL_MAX_PENDING];
    int pending_n;
    char seen[TSQL_MAX_SEEN][TSQL_NAME_MAX + 2];
    int seen_n;
} tsql_obj;

static bool obj_is_body(const tsql_obj *o) {
    return o->kind == OBJ_PROC || o->kind == OBJ_FUNC || o->kind == OBJ_TRIGGER ||
           o->kind == OBJ_VIEW;
}

static bool is_cte(const tsql_obj *o, const char *name) {
    char low[TSQL_NAME_MAX];
    lower_into(low, name, (int)strlen(name));
    for (int i = 0; i < o->cte_n; i++) {
        if (strcmp(o->ctes[i], low) == 0) {
            return true;
        }
    }
    return false;
}

/* Record a fact once per object: kind 'c' call, 'r' read, 'w' write. */
static bool first_time(tsql_obj *o, char kind, const char *name) {
    char key[TSQL_NAME_MAX + 2];
    key[0] = kind;
    lower_into(key + 1, name, (int)strlen(name));
    for (int i = 0; i < o->seen_n; i++) {
        if (strcmp(o->seen[i], key) == 0) {
            return false;
        }
    }
    if (o->seen_n < TSQL_MAX_SEEN) {
        memcpy(o->seen[o->seen_n++], key, strlen(key) + 1);
    }
    return true;
}

static void emit_call(tsql_obj *o, const char *name, int line) {
    if (!o->qn || !first_time(o, 'c', name)) {
        return;
    }
    CBMCall call = {0};
    call.callee_name = cbm_arena_strdup(o->ctx->arena, name);
    call.enclosing_func_qn = o->qn;
    call.start_line = line;
    if (call.callee_name) {
        cbm_calls_push(&o->ctx->result->calls, o->ctx->arena, call);
    }
}

static void emit_rw(tsql_obj *o, const char *name, bool write) {
    if (!o->qn || is_cte(o, name) || !first_time(o, write ? 'w' : 'r', name)) {
        return;
    }
    CBMReadWrite rw = {0};
    rw.var_name = cbm_arena_strdup(o->ctx->arena, name);
    rw.enclosing_func_qn = o->qn;
    rw.is_write = write;
    if (rw.var_name) {
        cbm_rw_push(&o->ctx->result->rw, o->ctx->arena, rw);
    }
}

static const char *obj_kind_name(tsql_obj_kind k) {
    switch (k) {
    case OBJ_PROC:
        return "procedure";
    case OBJ_FUNC:
        return "function";
    case OBJ_TRIGGER:
        return "trigger";
    case OBJ_VIEW:
        return "view";
    case OBJ_TABLE:
        return "table";
    default:
        return NULL;
    }
}

/* Close the current object: flush UPDATE/DELETE targets that never met an
 * alias (they name the table itself) and push the definition. */
static void obj_finish(tsql_obj *o) {
    if (o->kind == OBJ_NONE) {
        return;
    }
    for (int i = 0; i < o->pending_n; i++) {
        emit_rw(o, o->pending[i].name, true);
    }
    CBMArena *a = o->ctx->arena;
    const char **kv = (const char **)cbm_arena_alloc(a, 3 * sizeof(char *));
    if (o->qn && o->name && kv) {
        kv[0] = "sql_kind";
        kv[1] = obj_kind_name(o->kind);
        kv[2] = NULL;
        CBMDefinition def;
        memset(&def, 0, sizeof(def));
        def.name = o->name;
        def.qualified_name = o->qn;
        def.label = (o->kind == OBJ_TABLE || o->kind == OBJ_VIEW) ? "Class" : "Function";
        def.file_path = o->ctx->rel_path;
        def.start_line = (uint32_t)o->start_line;
        def.end_line = (uint32_t)(o->end_line >= o->start_line ? o->end_line : o->start_line);
        def.is_exported = true;
        def.extra_props = kv;
        cbm_defs_push(&o->ctx->result->defs, a, def);
    }
    o->kind = OBJ_NONE;
    o->qn = NULL;
    o->name = NULL;
    o->cte_n = 0;
    o->pending_n = 0;
    o->seen_n = 0;
}

static void obj_start(tsql_obj *o, tsql_obj_kind kind, const char *name, int line) {
    obj_finish(o);
    CBMExtractCtx *ctx = o->ctx;
    o->kind = kind;
    o->name = cbm_arena_strdup(ctx->arena, name);
    o->qn = o->name ? cbm_fqn_compute(ctx->arena, ctx->project, ctx->rel_path, o->name) : NULL;
    o->start_line = line;
    o->end_line = line;
}

/* After a table reference at *pos: an optional [AS] alias. When the alias names
 * a pending UPDATE/DELETE target, that write lands on `table`. */
static void take_alias(tsql_obj *o, const tsql_toks *tk, int *pos, const char *table) {
    int p = *pos;
    if (p < tk->count && word_is(&tk->items[p], "AS")) {
        p++;
    }
    if (p >= tk->count || tk->items[p].kind != TK_WORD || is_clause_word(&tk->items[p]) ||
        tk->items[p].len >= TSQL_NAME_MAX) {
        return;
    }
    char alias[TSQL_NAME_MAX];
    memcpy(alias, tk->items[p].text, (size_t)tk->items[p].len);
    alias[tk->items[p].len] = '\0';
    for (int i = 0; i < o->pending_n; i++) {
        if (ci_equal(o->pending[i].name, alias)) {
            emit_rw(o, table, true);
            o->pending[i] = o->pending[--o->pending_n];
            i--;
        }
    }
    *pos = p + 1;
}

/* FROM / JOIN / APPLY list: table [AS alias] (, table [AS alias])*. A name
 * followed by '(' is a table-valued function call; '(' first is a derived table. */
static void read_sources(tsql_obj *o, const tsql_toks *tk, int pos) {
    for (int guard = 0; guard < 64; guard++) {
        if (pos >= tk->count || (tk->items[pos].kind == TK_PUNCT && tk->items[pos].ch == '(')) {
            return;
        }
        if (is_clause_word(&tk->items[pos])) {
            return;
        }
        char name[TSQL_NAME_MAX];
        int line = tk->items[pos].line;
        int kind = read_object_name(tk, &pos, name, (int)sizeof(name));
        if (kind < 0) {
            return;
        }
        bool call = pos < tk->count && tk->items[pos].kind == TK_PUNCT && tk->items[pos].ch == '(';
        if (kind == TK_WORD) {
            if (call) {
                emit_call(o, name, line);
                return; /* arguments follow; the walk resumes at the next keyword */
            }
            take_alias(o, tk, &pos, name);
            emit_rw(o, name, false);
        }
        if (pos < tk->count && tk->items[pos].kind == TK_PUNCT && tk->items[pos].ch == ',') {
            pos++;
            continue;
        }
        return;
    }
}

/* Body keyword at tokens[t] (a routine or view is open). */
static void body_word(tsql_obj *o, const tsql_toks *tk, int t) {
    const tsql_tok *w = &tk->items[t];
    const tsql_tok *prev = t > 0 ? &tk->items[t - 1] : NULL;
    char name[TSQL_NAME_MAX];
    int p = t + 1;
    if (word_is(w, "EXEC") || word_is(w, "EXECUTE")) {
        if (p + 1 < tk->count && tk->items[p].kind == TK_VAR && tk->items[p + 1].kind == TK_PUNCT &&
            tk->items[p + 1].ch == '=') {
            p += 2; /* EXEC @rc = proc */
        }
        if (read_object_name(tk, &p, name, (int)sizeof(name)) == TK_WORD) {
            emit_call(o, name, w->line);
        }
        return;
    }
    if (word_is(w, "FROM") || word_is(w, "JOIN") || word_is(w, "APPLY")) {
        if (word_is(w, "FROM") && prev && word_is(prev, "DELETE")) {
            return; /* DELETE FROM x: the DELETE rule owns x */
        }
        read_sources(o, tk, p);
        return;
    }
    if (word_is(w, "INSERT") || word_is(w, "MERGE")) {
        if (p < tk->count && word_is(&tk->items[p], "INTO")) {
            p++;
        }
        if (read_object_name(tk, &p, name, (int)sizeof(name)) == TK_WORD) {
            emit_rw(o, name, true);
        }
        return;
    }
    if (word_is(w, "INTO")) {
        if (prev && (word_is(prev, "INSERT") || word_is(prev, "MERGE"))) {
            return;
        }
        if (read_object_name(tk, &p, name, (int)sizeof(name)) == TK_WORD) {
            emit_rw(o, name, true); /* SELECT ... INTO tbl */
        }
        return;
    }
    if (word_is(w, "TRUNCATE")) {
        if (p < tk->count && word_is(&tk->items[p], "TABLE")) {
            p++;
            if (read_object_name(tk, &p, name, (int)sizeof(name)) == TK_WORD) {
                emit_rw(o, name, true);
            }
        }
        return;
    }
    if (word_is(w, "UPDATE") || word_is(w, "DELETE")) {
        if (word_is(w, "UPDATE") && p < tk->count && word_is(&tk->items[p], "STATISTICS")) {
            return;
        }
        if (p < tk->count && word_is(&tk->items[p], "TOP")) { /* TOP (n) */
            p++;
            while (p < tk->count && !(tk->items[p].kind == TK_PUNCT && tk->items[p].ch == ')')) {
                p++;
            }
            p++;
        }
        if (word_is(w, "DELETE") && p < tk->count && word_is(&tk->items[p], "FROM")) {
            p++;
        }
        if (read_object_name(tk, &p, name, (int)sizeof(name)) == TK_WORD &&
            o->pending_n < TSQL_MAX_PENDING) {
            memcpy(o->pending[o->pending_n].name, name, strlen(name) + 1);
            o->pending[o->pending_n].line = w->line;
            o->pending_n++;
        }
        return;
    }
    /* WITH name AS (  /  , name AS (  -- a CTE, never a table. */
    if ((word_is(w, "WITH") || (w->kind == TK_PUNCT && w->ch == ',')) && p + 2 < tk->count &&
        tk->items[p].kind == TK_WORD && word_is(&tk->items[p + 1], "AS") &&
        tk->items[p + 2].kind == TK_PUNCT && tk->items[p + 2].ch == '(' &&
        o->cte_n < TSQL_MAX_CTES && tk->items[p].len < TSQL_NAME_MAX) {
        lower_into(o->ctes[o->cte_n++], tk->items[p].text, tk->items[p].len);
    }
}

/* CREATE [OR ALTER] / ALTER <kind> <name>: start an object. Returns true when
 * tokens[t] began one. */
static bool object_header(tsql_obj *o, const tsql_toks *tk, int t) {
    const tsql_tok *w = &tk->items[t];
    bool create = word_is(w, "CREATE");
    if (!create && !word_is(w, "ALTER")) {
        return false;
    }
    int p = t + 1;
    if (create && p + 1 < tk->count && word_is(&tk->items[p], "OR") &&
        word_is(&tk->items[p + 1], "ALTER")) {
        p += 2;
    }
    if (p >= tk->count) {
        return false;
    }
    const tsql_tok *k = &tk->items[p];
    tsql_obj_kind kind = OBJ_NONE;
    if (word_is(k, "PROC") || word_is(k, "PROCEDURE")) {
        kind = OBJ_PROC;
    } else if (word_is(k, "FUNCTION")) {
        kind = OBJ_FUNC;
    } else if (word_is(k, "TRIGGER")) {
        kind = OBJ_TRIGGER;
    } else if (word_is(k, "VIEW")) {
        kind = OBJ_VIEW;
    } else if (create && word_is(k, "TABLE")) {
        kind = OBJ_TABLE;
    }
    if (kind == OBJ_NONE) {
        return false;
    }
    /* CREATE TABLE inside a routine body is a local work table, not an object. */
    if (kind == OBJ_TABLE && obj_is_body(o)) {
        return false;
    }
    p++;
    char name[TSQL_NAME_MAX];
    if (read_object_name(tk, &p, name, (int)sizeof(name)) != TK_WORD) {
        return false;
    }
    obj_start(o, kind, name, w->line);
    return true;
}

bool cbm_tsql_looks_like(const char *source, int source_len) {
    if (!source || source_len <= 0) {
        return false;
    }
    int n = source_len < TSQL_SNIFF_MAX ? source_len : TSQL_SNIFF_MAX;
    char *low = malloc((size_t)n + 1);
    if (!low) {
        return false;
    }
    lower_into(low, source, n);
    static const char *const objects[] = {"create procedure", "create proc ", "create or alter proc",
                                          "alter procedure",  "alter proc ",  "create function",
                                          "create or alter function", "create view",
                                          "create or alter view",     "create table",
                                          "create trigger",           NULL};
    static const char *const markers[] = {"[dbo]",        "dbo.",          "\ngo\r", "\ngo\n",
                                          "set nocount",  "set ansi_nulls", "set quoted_identifier",
                                          "nvarchar",     "@@",            "begin try",
                                          "getdate()",    "identity(",     NULL};
    bool object = false;
    bool marker = false;
    for (const char *const *k = objects; *k && !object; k++) {
        object = strstr(low, *k) != NULL;
    }
    for (const char *const *k = markers; *k && !marker; k++) {
        marker = strstr(low, *k) != NULL;
    }
    free(low);
    return object && marker;
}

void cbm_tsql_extract(CBMExtractCtx *ctx) {
    tsql_toks tk = {0};
    if (!tsql_lex(ctx->source, ctx->source_len, &tk)) {
        free(tk.items);
        ctx->result->has_error = true;
        return;
    }
    tsql_obj *o = calloc(1, sizeof(tsql_obj));
    if (!o) {
        free(tk.items);
        ctx->result->has_error = true;
        return;
    }
    o->ctx = ctx;
    for (int t = 0; t < tk.count; t++) {
        const tsql_tok *w = &tk.items[t];
        if (w->kind == TK_GO) {
            obj_finish(o);
            continue;
        }
        if (object_header(o, &tk, t)) {
            continue;
        }
        if (o->kind != OBJ_NONE) {
            o->end_line = w->line;
        }
        if (obj_is_body(o) && (w->kind == TK_WORD || w->kind == TK_PUNCT)) {
            body_word(o, &tk, t);
        }
    }
    obj_finish(o);
    free(o);
    free(tk.items);
}
