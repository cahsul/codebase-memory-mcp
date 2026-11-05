/*
 * extract_aspnet.c -- ASP.NET Web Forms markup (.aspx/.ascx/.master) and site
 * maps (.sitemap), read from the text (CBM_LANG_ASPNET has no grammar).
 *
 * A page is compiled by ASP.NET into a class that inherits its code-behind
 * class, so the page itself becomes a Class definition named like that
 * generated class (Orders.aspx -> "Orders_aspx"). It calls:
 *   - its code-behind class, from the directive
 *     `<%@ Page CodeBehind="Orders.aspx.vb" Inherits="Shop.Orders" %>`;
 *   - each event handler wired by a server-control attribute
 *     (`<asp:Button OnClick="btnSave_Click">`, `<input runat="server"
 *     onserverclick="btnGo_ServerClick">`).
 * Both are named by exact QN ("qn:<qn>", registry.c), computed exactly as the
 * VB/C# extractor names the class in the code-behind file, so a handler with
 * the same name on another page is never the target. Without a CodeBehind
 * path the class name alone is used. Client-side attributes (OnClientClick,
 * onclick="return check()") are not server events and are skipped.
 *
 * Handlers wired in code instead (`Handles btnSave.Click`) are linked by the
 * VB extractor: class -> handler (extract_unified.c).
 *
 * A site map node (`<siteMapNode title="Orders" url="Shop/Orders.aspx">`)
 * becomes a Section named by its title path ("Home > Shop > Orders") that
 * calls the page its url names; urls are relative to the site map's folder,
 * the web root. Group nodes (url="#shop"), external links and nodes inside
 * <!-- comments --> give no call.
 */
#include "arena.h"
#include "cbm.h"
#include "helpers.h"
#include "foundation/constants.h"

#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>

enum {
    ASPNET_NAME_MAX = 256,
    ASPNET_PATH_MAX = 1024,
    ASPNET_DEPTH_MAX = 16,
    ASPNET_SLUG_MAX = 48,       /* title characters kept in a site map node's QN */
    ASPNET_DIRECTIVE_OPEN = 3,  /* "<%@" */
    ASPNET_SITEMAP_TAG_LEN = 12 /* "<siteMapNode" */
};

static bool ci_prefix(const char *s, const char *end, const char *prefix) {
    for (; *prefix; s++, prefix++) {
        if (s >= end || tolower((unsigned char)*s) != tolower((unsigned char)*prefix)) {
            return false;
        }
    }
    return true;
}

/* First occurrence of `needle` in [p, end), case-insensitive; NULL if none.
 * The source buffer is not NUL-terminated, so strstr is never used on it. */
static const char *find_ci(const char *p, const char *end, const char *needle) {
    size_t n = strlen(needle);
    for (; p + n <= end; p++) {
        if (ci_prefix(p, end, needle)) {
            return p;
        }
    }
    return NULL;
}

static bool ends_with_ci(const char *s, const char *suffix) {
    size_t n = strlen(s);
    size_t m = strlen(suffix);
    return m <= n && ci_prefix(s + n - m, s + n, suffix);
}

static bool is_identifier(const char *s, size_t n) {
    if (n == 0 || !(isalpha((unsigned char)s[0]) || s[0] == '_')) {
        return false;
    }
    for (size_t i = 1; i < n; i++) {
        if (!(isalnum((unsigned char)s[i]) || s[i] == '_')) {
            return false;
        }
    }
    return true;
}

/* Past the `%>` that closes the `<%` block at p, or `end` when unclosed. */
static const char *skip_code_block(const char *p, const char *end) {
    const char *close = find_ci(p + 2, end, "%>");
    return close ? close + 2 : end;
}

/* The '>' closing the tag that starts at p ('<'), outside quotes and `<% %>`
 * blocks (`Text='<%# Eval("Name") %>'` nests quotes); NULL when unclosed. */
static const char *tag_end(const char *p, const char *end) {
    char quote = 0;
    for (const char *q = p + SKIP_ONE; q < end; q++) {
        if (q + 1 < end && q[0] == '<' && q[1] == '%') {
            q = skip_code_block(q, end) - SKIP_ONE;
        } else if (quote) {
            if (*q == quote) {
                quote = 0;
            }
        } else if (*q == '"' || *q == '\'') {
            quote = *q;
        } else if (*q == '>') {
            return q;
        }
    }
    return NULL;
}

/* Next name="value" (or name='value') pair in [p, end): its spans, and the
 * position after it; NULL when none is left. Bare and unquoted attributes are
 * stepped over. */
static const char *next_attr(const char *p, const char *end, const char **name, size_t *name_len,
                             const char **value, size_t *value_len) {
    while (p < end) {
        if (!(isalpha((unsigned char)*p) || *p == '_')) {
            p++;
            continue;
        }
        const char *n0 = p;
        while (p < end &&
               (isalnum((unsigned char)*p) || *p == '_' || *p == '-' || *p == ':' || *p == '.')) {
            p++;
        }
        const char *n1 = p;
        while (p < end && isspace((unsigned char)*p)) {
            p++;
        }
        if (p >= end || *p != '=') {
            continue;
        }
        p++;
        while (p < end && isspace((unsigned char)*p)) {
            p++;
        }
        if (p >= end || (*p != '"' && *p != '\'')) {
            continue;
        }
        char quote = *p++;
        const char *v0 = p;
        while (p < end && *p != quote) {
            p = (p + 1 < end && p[0] == '<' && p[1] == '%') ? skip_code_block(p, end) : p + 1;
        }
        *name = n0;
        *name_len = (size_t)(n1 - n0);
        *value = v0;
        *value_len = (size_t)(p - v0);
        return p < end ? p + SKIP_ONE : end;
    }
    return NULL;
}

/* Value of attribute `want` (case-insensitive) in [p, end), copied into out. */
static bool attr_value(const char *p, const char *end, const char *want, char *out, size_t cap) {
    const char *name;
    const char *value;
    size_t nl;
    size_t vl;
    size_t wl = strlen(want);
    while ((p = next_attr(p, end, &name, &nl, &value, &vl)) != NULL) {
        if (nl == wl && ci_prefix(name, name + nl, want) && vl < cap) {
            memcpy(out, value, vl);
            out[vl] = '\0';
            return true;
        }
    }
    return false;
}

static void push_call(CBMExtractCtx *ctx, const char *callee, const char *enclosing, int line) {
    CBMCall call = {0};
    call.callee_name = cbm_arena_strdup(ctx->arena, callee);
    call.enclosing_func_qn = enclosing;
    call.start_line = line;
    if (call.callee_name && enclosing) {
        cbm_calls_push(&ctx->result->calls, ctx->arena, call);
    }
}

static int count_lines(const char *from, const char *to, int line) {
    for (const char *q = from; q < to; q++) {
        if (*q == '\n') {
            line++;
        }
    }
    return line;
}

/* The folder part of rel_path, with its trailing '/' ("Shop/" for
 * "Shop/Orders.aspx", "" at the root), written to out. */
static void rel_dir(const char *rel_path, char *out, size_t cap) {
    const char *slash = strrchr(rel_path, '/');
    size_t n = slash ? (size_t)(slash - rel_path) + SKIP_ONE : 0;
    if (n >= cap) {
        n = 0;
    }
    memcpy(out, rel_path, n);
    out[n] = '\0';
}

/* dir + a markup-relative path ("Orders.aspx.vb", "Shop\\Orders.aspx"), with
 * backslashes as '/', a leading "./" dropped. False for a path rooted
 * elsewhere ("~/x", "/x", "http://x") or one that does not fit. */
static bool join_rel(const char *dir, const char *path, char *out, size_t cap) {
    if (path[0] == '~' || path[0] == '/' || path[0] == '\\' || strstr(path, "://")) {
        return false;
    }
    while (path[0] == '.' && (path[1] == '/' || path[1] == '\\')) {
        path += 2;
    }
    int n = snprintf(out, cap, "%s%s", dir, path);
    if (n <= 0 || (size_t)n >= cap) {
        return false;
    }
    for (char *c = out; *c; c++) {
        if (*c == '\\') {
            *c = '/';
        }
    }
    return true;
}

/* Name of the class ASP.NET generates for a markup file: its file name with
 * every non-identifier byte as '_' ("Orders.aspx" -> "Orders_aspx",
 * "Site.Master" -> "Site_Master", "order-list.aspx" -> "order_list_aspx"). */
static bool page_class_name(const char *rel_path, char *out, size_t cap) {
    const char *slash = strrchr(rel_path, '/');
    const char *base = slash ? slash + SKIP_ONE : rel_path;
    size_t n = strlen(base);
    size_t lead = isdigit((unsigned char)base[0]) ? SKIP_ONE : 0;
    if (n == 0 || n + lead >= cap) {
        return false;
    }
    out[0] = '_';
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)base[i];
        out[lead + i] = (char)(isalnum(c) || c == '_' ? c : '_');
    }
    out[lead + n] = '\0';
    return true;
}

/* QN of the page Class defined for the markup file at rel_path. */
static const char *page_def_qn(CBMExtractCtx *ctx, const char *rel_path) {
    char name[ASPNET_NAME_MAX];
    if (!page_class_name(rel_path, name, sizeof(name))) {
        return NULL;
    }
    return cbm_fqn_compute(ctx->arena, ctx->project, rel_path, name);
}

/* ── Pages, user controls, master pages ──────────────────────────── */

typedef struct {
    char cls[ASPNET_NAME_MAX]; /* code-behind class, last segment of Inherits */
    const char *cls_qn;        /* its QN when the CodeBehind path is known */
    const char *kind;          /* "Page", "Control" or "Master" */
} AspnetDirective;

/* Reads the first Page/Control/Master directive. */
static void read_directive(CBMExtractCtx *ctx, AspnetDirective *d) {
    const char *src = ctx->source;
    const char *end = src + ctx->source_len;
    static const char *const kinds[] = {"Page", "Control", "Master"};
    for (const char *p = find_ci(src, end, "<%@"); p; p = find_ci(p + SKIP_ONE, end, "<%@")) {
        const char *close = find_ci(p, end, "%>");
        if (!close) {
            return;
        }
        const char *w = p + ASPNET_DIRECTIVE_OPEN;
        while (w < close && isspace((unsigned char)*w)) {
            w++;
        }
        for (size_t k = 0; k < sizeof(kinds) / sizeof(kinds[0]); k++) {
            size_t kl = strlen(kinds[k]);
            /* "Master" must not match the MasterType directive. */
            if (!ci_prefix(w, close, kinds[k]) ||
                !(w + kl < close && (isspace((unsigned char)w[kl]) || w[kl] == '%'))) {
                continue;
            }
            d->kind = kinds[k];
            char inherits[ASPNET_NAME_MAX];
            if (!attr_value(w + kl, close, "Inherits", inherits, sizeof(inherits))) {
                return;
            }
            const char *dot = strrchr(inherits, '.');
            const char *last = dot ? dot + SKIP_ONE : inherits;
            if (!is_identifier(last, strlen(last))) {
                return;
            }
            snprintf(d->cls, sizeof(d->cls), "%s", last);
            char cb[ASPNET_PATH_MAX];
            char dir[ASPNET_PATH_MAX];
            char cb_rel[ASPNET_PATH_MAX];
            rel_dir(ctx->rel_path, dir, sizeof(dir));
            if ((attr_value(w + kl, close, "CodeBehind", cb, sizeof(cb)) ||
                 attr_value(w + kl, close, "CodeFile", cb, sizeof(cb))) &&
                join_rel(dir, cb, cb_rel, sizeof(cb_rel))) {
                d->cls_qn = cbm_fqn_compute(ctx->arena, ctx->project, cb_rel, d->cls);
            }
            return;
        }
        p = close;
    }
}

/* Server-side event attribute: "on" + event, value a bare handler name.
 * OnClientClick and friends carry JavaScript and are skipped. */
static bool is_server_event(const char *name, size_t nl, const char *value, size_t vl) {
    return nl > 2 && tolower((unsigned char)name[0]) == 'o' &&
           tolower((unsigned char)name[1]) == 'n' && !ci_prefix(name, name + nl, "onclient") &&
           vl < ASPNET_NAME_MAX && is_identifier(value, vl);
}

/* Calls for the event attributes of one server tag [p, te). */
static void tag_handlers(CBMExtractCtx *ctx, const AspnetDirective *d, const char *page_qn,
                         const char *p, const char *te, int line) {
    const char *name;
    const char *value;
    size_t nl;
    size_t vl;
    while ((p = next_attr(p, te, &name, &nl, &value, &vl)) != NULL) {
        if (!is_server_event(name, nl, value, vl)) {
            continue;
        }
        /* Without a known class a bare handler name would bind any page's
         * namesake, so it gives no call. */
        char callee[ASPNET_PATH_MAX + ASPNET_NAME_MAX + 8];
        if (d->cls_qn) {
            snprintf(callee, sizeof(callee), "%s%s.%.*s", CBM_QN_CALLEE_PREFIX, d->cls_qn, (int)vl,
                     value);
        } else if (d->cls[0]) {
            snprintf(callee, sizeof(callee), "%s.%.*s", d->cls, (int)vl, value);
        } else {
            continue;
        }
        push_call(ctx, callee, page_qn, line);
    }
}

static void extract_page(CBMExtractCtx *ctx) {
    const char *src = ctx->source;
    const char *end = src + ctx->source_len;
    CBMArena *a = ctx->arena;
    char name[ASPNET_NAME_MAX];
    const char *page_qn = page_def_qn(ctx, ctx->rel_path);
    if (!page_qn || !page_class_name(ctx->rel_path, name, sizeof(name))) {
        return;
    }
    AspnetDirective d = {0};
    read_directive(ctx, &d);

    const char **kv = (const char **)cbm_arena_alloc(a, 3 * sizeof(char *));
    if (!kv) {
        return;
    }
    kv[0] = "aspnet_kind";
    kv[1] = d.kind ? d.kind : "Page";
    kv[2] = NULL;
    CBMDefinition def;
    memset(&def, 0, sizeof(def));
    def.name = cbm_arena_strdup(a, name);
    def.qualified_name = page_qn;
    def.label = "Class";
    def.file_path = ctx->rel_path;
    def.start_line = 1;
    def.end_line = (uint32_t)count_lines(src, end, 1);
    def.is_exported = true;
    def.extra_props = kv;
    if (!def.name) {
        return;
    }
    cbm_defs_push(&ctx->result->defs, a, def);

    if (d.cls_qn) {
        char callee[ASPNET_PATH_MAX + 8];
        snprintf(callee, sizeof(callee), "%s%s", CBM_QN_CALLEE_PREFIX, d.cls_qn);
        push_call(ctx, callee, page_qn, 1);
    } else if (d.cls[0]) {
        push_call(ctx, d.cls, page_qn, 1);
    }

    int line = 1;
    const char *seen = src;
    for (const char *p = src; p < end; p++) {
        if (*p != '<') {
            continue;
        }
        if (ci_prefix(p, end, "<!--") || ci_prefix(p, end, "<%--")) {
            const char *stop = find_ci(p + 4, end, p[1] == '!' ? "-->" : "--%>");
            if (!stop) {
                break;
            }
            p = stop;
            continue;
        }
        if (p + 1 < end && p[1] == '%') { /* <% code %>, <%= %>, <%# %>, directives */
            p = skip_code_block(p, end) - SKIP_ONE;
            continue;
        }
        if (p + 1 >= end || !isalpha((unsigned char)p[1])) {
            continue;
        }
        const char *te = tag_end(p, end);
        if (!te) {
            break;
        }
        const char *n0 = p + SKIP_ONE;
        const char *n1 = n0;
        while (n1 < te && (isalnum((unsigned char)*n1) || *n1 == ':' || *n1 == '_' || *n1 == '-')) {
            n1++;
        }
        bool prefixed = memchr(n0, ':', (size_t)(n1 - n0)) != NULL;
        char runat[16];
        bool server = prefixed || (attr_value(n1, te, "runat", runat, sizeof(runat)) &&
                                   ci_prefix(runat, runat + strlen(runat), "server"));
        if (server) {
            line = count_lines(seen, p, line);
            seen = p;
            tag_handlers(ctx, &d, page_qn, n1, te, line);
        }
        /* Script and style bodies are not markup: a `<` or an apostrophe in
         * them would otherwise open a phantom tag or quote. */
        size_t tn = (size_t)(n1 - n0);
        const char *close = NULL;
        if (tn == 6 && ci_prefix(n0, n1, "script")) {
            close = find_ci(te, end, "</script");
        } else if (tn == 5 && ci_prefix(n0, n1, "style")) {
            close = find_ci(te, end, "</style");
        }
        p = close ? close : te;
    }
}

/* ── Site maps ───────────────────────────────────────────────────── */

/* The page Class QN a site map url names, or NULL for a group node ("#x"),
 * an external link or a url that names no markup file. "Shop/Orders.aspx?id=1"
 * from "Web.sitemap" -> the page def of "Shop/Orders.aspx". */
static const char *url_page_qn(CBMExtractCtx *ctx, const char *url) {
    char path[ASPNET_PATH_MAX];
    size_t n = strcspn(url, "?#");
    if (n == 0 || n >= sizeof(path)) {
        return NULL;
    }
    memcpy(path, url, n);
    path[n] = '\0';
    const char *p = path;
    if (p[0] == '~') {
        p++;
    }
    while (*p == '/' || *p == '\\') {
        p++;
    }
    char dir[ASPNET_PATH_MAX];
    char rel[ASPNET_PATH_MAX];
    rel_dir(ctx->rel_path, dir, sizeof(dir));
    if (!*p || !join_rel(dir, p, rel, sizeof(rel)) ||
        !(ends_with_ci(rel, ".aspx") || ends_with_ci(rel, ".ascx") ||
          ends_with_ci(rel, ".master"))) {
        return NULL;
    }
    return page_def_qn(ctx, rel);
}

/* QN segment of a site map node: its line, plus nth when several nodes share
 * the line (a one-line site map), plus its title as a slug, so a trace that
 * prints QN tails still reads as the menu ("menu_L5_Orders"). */
static void section_segment(char *seg, size_t cap, int line, int nth, const char *title) {
    int n = nth > 0 ? snprintf(seg, cap, "menu_L%d_%d", line, nth)
                    : snprintf(seg, cap, "menu_L%d", line);
    size_t used = n > 0 && (size_t)n < cap ? (size_t)n : 0;
    size_t start = used;
    for (const char *t = title; *t && used + 2 < cap && used - start < ASPNET_SLUG_MAX; t++) {
        unsigned char c = (unsigned char)*t;
        if (isalnum(c)) {
            if (used == start) {
                seg[used++] = '_';
            }
            seg[used++] = (char)c;
        } else if (used > start && seg[used - 1] != '_') {
            seg[used++] = '_';
        }
    }
    while (used > start && seg[used - 1] == '_') {
        used--;
    }
    seg[used] = '\0';
}

/* nth: index of this node among the nodes on its line, which keeps the QN
 * unique in a site map written on one line. */
static void push_section(CBMExtractCtx *ctx, const char *path, const char *title, const char *url,
                         int line, int nth) {
    CBMArena *a = ctx->arena;
    char seg[ASPNET_SLUG_MAX + 32];
    section_segment(seg, sizeof(seg), line, nth, title[0] ? title : url);
    const char *qn = cbm_fqn_compute(a, ctx->project, ctx->rel_path, seg);
    const char **kv = (const char **)cbm_arena_alloc(a, 5 * sizeof(char *));
    if (!qn || !kv) {
        return;
    }
    kv[0] = "url";
    kv[1] = cbm_arena_strdup(a, url);
    kv[2] = "title";
    kv[3] = cbm_arena_strdup(a, title);
    kv[4] = NULL;
    CBMDefinition def;
    memset(&def, 0, sizeof(def));
    def.name = cbm_arena_strdup(a, path);
    def.qualified_name = qn;
    def.label = "Section";
    def.file_path = ctx->rel_path;
    def.start_line = (uint32_t)line;
    def.end_line = (uint32_t)line;
    def.is_exported = true;
    def.extra_props = kv;
    if (!def.name) {
        return;
    }
    cbm_defs_push(&ctx->result->defs, a, def);
    const char *page = url_page_qn(ctx, url);
    if (page) {
        char callee[ASPNET_PATH_MAX + 8];
        snprintf(callee, sizeof(callee), "%s%s", CBM_QN_CALLEE_PREFIX, page);
        push_call(ctx, callee, qn, line);
    }
}

static void extract_sitemap(CBMExtractCtx *ctx) {
    const char *src = ctx->source;
    const char *end = src + ctx->source_len;
    char titles[ASPNET_DEPTH_MAX][ASPNET_NAME_MAX];
    int depth = 0;
    int line = 1;
    int last_line = 0;
    int nth = 0;
    const char *seen = src;
    for (const char *p = src; p < end; p++) {
        if (*p != '<') {
            continue;
        }
        if (ci_prefix(p, end, "<!--")) {
            const char *stop = find_ci(p + 4, end, "-->");
            if (!stop) {
                break;
            }
            p = stop;
            continue;
        }
        if (ci_prefix(p, end, "</siteMapNode")) {
            depth -= depth > 0;
            continue;
        }
        if (!ci_prefix(p, end, "<siteMapNode")) {
            continue;
        }
        const char *te = tag_end(p, end);
        if (!te) {
            break;
        }
        bool leaf = te[-1] == '/';
        char title[ASPNET_NAME_MAX] = "";
        char url[ASPNET_PATH_MAX] = "";
        (void)attr_value(p + ASPNET_SITEMAP_TAG_LEN, te, "title", title, sizeof(title));
        (void)attr_value(p + ASPNET_SITEMAP_TAG_LEN, te, "url", url, sizeof(url));
        line = count_lines(seen, p, line);
        seen = p;

        /* "Home > Shop > Orders": the titles of the enclosing nodes, then this one. */
        char path[ASPNET_PATH_MAX];
        size_t used = 0;
        path[0] = '\0';
        for (int i = 0; i < depth && i < ASPNET_DEPTH_MAX; i++) {
            if (titles[i][0] && used < sizeof(path)) {
                int w = snprintf(path + used, sizeof(path) - used, "%s > ", titles[i]);
                used = w > 0 ? used + (size_t)w : used;
            }
        }
        if (used < sizeof(path)) {
            snprintf(path + used, sizeof(path) - used, "%s", title[0] ? title : url);
        }
        if (title[0] || url[0]) {
            nth = line == last_line ? nth + 1 : 0;
            last_line = line;
            push_section(ctx, path, title, url, line, nth);
        }
        /* Depth counts past the title buffer so </siteMapNode> stays balanced. */
        if (!leaf) {
            if (depth < ASPNET_DEPTH_MAX) {
                snprintf(titles[depth], sizeof(titles[depth]), "%s", title);
            }
            depth++;
        }
        p = te;
    }
}

void cbm_aspnet_extract(CBMExtractCtx *ctx) {
    if (!ctx || !ctx->source || ctx->source_len <= 0 || !ctx->rel_path) {
        return;
    }
    if (ends_with_ci(ctx->rel_path, ".sitemap")) {
        extract_sitemap(ctx);
    } else {
        extract_page(ctx);
    }
}
