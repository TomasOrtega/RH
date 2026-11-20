"use strict";

const root = document.querySelector("#proof-browser");
const params = new URLSearchParams(location.search);
const startModules = [
  ["Main.lean", "Main theorems"],
  ["Statements.lean", "Statements"],
  ["Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/CancelC.lean", "Worked example"],
];
const proofLabels = {
  authored: "English proof",
  citation: "Proof by reference",
  translation: "English outline",
  "source gap": "Proof source",
};

function element(tag, text, attributes = {}) {
  const node = document.createElement(tag);
  for (const [name, value] of Object.entries(attributes)) node.setAttribute(name, value);
  if (text !== undefined) node.textContent = text;
  return node;
}

function url(fields, fragment = "") {
  return "?" + new URLSearchParams(fields) + fragment;
}

function link(label, href, attributes = {}) {
  return element("a", label, { href, ...attributes });
}

function list(items) {
  const result = element("ul", undefined, { class: "links" });
  for (const item of items) {
    const row = element("li");
    row.append(item);
    result.append(row);
  }
  return result;
}

function codeBlock(source, className = "") {
  const block = element("pre", undefined, { class: className, tabindex: "0" });
  block.append(element("code", source));
  return block;
}

function basename(path) {
  return path.split("/").at(-1);
}

function moduleName(path) {
  return path.replace(/\.lean$/, "").replaceAll("/", ".");
}

async function readPack(filename) {
  const response = await fetch("data/" + filename);
  if (!response.ok) throw new Error("The archive data could not be loaded. Reload to try again.");
  const bytes = new Uint8Array(await response.arrayBuffer());
  if (bytes[0] !== 31 || bytes[1] !== 139) return JSON.parse(new TextDecoder().decode(bytes));
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"));
  return new Response(stream).json();
}

function sidebar(modules, folders, current) {
  const panel = element("aside", undefined, { class: "browser-sidebar", "aria-label": "Archive navigation" });
  const form = element("form", undefined, { action: "./", role: "search" });
  const field = element("div", undefined, { class: "search-field" });
  field.append(
    element("input", undefined, {
      id: "module-search", name: "q", type: "search", placeholder: "e.g. CancelC",
      value: params.get("q") || "", required: "",
    }),
    element("button", "Search"),
  );
  form.append(element("label", "Find a module", { for: "module-search" }), field);
  panel.append(
    form,
    element("h2", "Start here"),
    list(startModules.map(([path, label]) =>
      link(label, url({ module: path }), current === path ? { "aria-current": "page" } : {}))),
    element("h2", "Source folders"),
    list(folders.map(folder => link(folder, url({ folder })))),
    element("p", modules.toLocaleString("en-US") + " Lean modules", { class: "module-count" }),
  );
  return panel;
}

function breadcrumbs(folder) {
  const nav = element("nav", undefined, { class: "breadcrumbs", "aria-label": "Source path" });
  nav.append(link("Lean source", url({ folder: "" })));
  let path = "";
  for (const part of folder.split("/").filter(Boolean)) {
    path = path ? path + "/" + part : part;
    nav.append(" / ", link(part, url({ folder: path })));
  }
  return nav;
}

function renderProse(text, allowCitation) {
  const prose = element("div", undefined, { class: "proof-narrative" });
  for (const block of text.split(/\n\n+/)) {
    const paragraph = element("p");
    const citation = allowCitation && block.match(/^\[Source theorem\]\((\?module=[\w%+.-]+&line=([1-9]\d*)#L\2)\)$/);
    if (citation) {
      paragraph.append(link("Source theorem", citation[1]));
      prose.append(paragraph);
      continue;
    }
    paragraph.textContent = block;
    prose.append(paragraph);
  }
  return prose;
}

function proofCard(path, source, proof, open) {
  const anchor = "L" + proof.line;
  const details = element("details", undefined, { class: "proof", id: anchor });
  const summary = element("summary");
  summary.append(
    element("code", proof.name),
    element("span", proof.kind + " · line " + proof.line),
  );
  details.append(summary);
  const fill = () => {
    const body = element("div", undefined, { class: "proof-body" });
    const raw = element("details", undefined, { class: "claim-source" });
    raw.append(element("summary", "Lean proof"), codeBlock(source.slice(proof.start, proof.end)));
    body.append(
      codeBlock(source.slice(proof.start, proof.statementEnd).trimEnd(), "statement"),
      element("h3", proofLabels[proof.status]),
      renderProse(proof.prose, proof.status === "citation"),
      raw,
      link("Link to line " + proof.line, url({ module: path, line: proof.line }, "#" + anchor), { class: "proof-link" }),
    );
    details.append(body);
  };
  if (open) {
    details.open = true;
    fill();
  } else {
    details.addEventListener("toggle", () => {
      if (details.open && details.childElementCount === 1) fill();
    });
  }
  return details;
}

function moduleView(article, path, record, names) {
  const folder = path.slice(0, path.lastIndexOf("/") + 1);
  const name = basename(path);
  document.title = name + " · RH proof browser";
  const raw = link("Download .lean", "", { download: name });
  raw.addEventListener("click", () => {
    if (raw.getAttribute("href")) return;
    const file = new Blob([record.source], { type: "text/plain;charset=utf-8" });
    raw.href = URL.createObjectURL(file);
  });
  const heading = element("div", undefined, { class: "module-heading" });
  const actions = element("div", undefined, { class: "module-actions" });
  actions.append(link("Full source", url({ module: path, view: "source" }, "#source")), raw);
  heading.append(element("h1", name.replace(/\.lean$/, "")), actions);
  article.append(breadcrumbs(folder), heading);

  const showSource = params.get("view") === "source";
  const selectedLine = params.get("line") || (showSource ? "" : String(record.proofs[0]?.line));
  if (record.proofs.length) {
    article.append(element("h2", "Proofs"));
    for (const proof of record.proofs) {
      article.append(proofCard(path, record.source, proof, String(proof.line) === selectedLine));
    }
  }
  if (record.imports.length) {
    const imports = element("section", undefined, { class: "imports" });
    imports.append(
      element("h2", "Imports"),
      list(record.imports.map(name => names.has(name)
        ? link(name, url({ module: names.get(name) }))
        : element("code", name))),
    );
    article.append(imports);
  }

  const source = element("details", undefined, { class: "full-source", id: "source" });
  source.append(element("summary", "Full Lean source"));
  source.open = showSource || !record.proofs.length;
  if (source.open) {
    source.append(codeBlock(record.source));
  } else {
    source.addEventListener("toggle", () => {
      if (source.open && source.childElementCount === 1) source.append(codeBlock(record.source));
    });
  }
  article.append(source);
  if (location.hash) {
    const target = document.getElementById(location.hash.slice(1));
    target?.scrollIntoView();
  }
}

function folderView(article, folder, modules) {
  const prefix = folder ? folder + "/" : "";
  const folders = new Set();
  const files = [];
  for (const path of modules) {
    if (!path.startsWith(prefix)) continue;
    const child = path.slice(prefix.length);
    if (child.includes("/")) folders.add(child.split("/")[0]);
    else files.push(child);
  }
  article.append(breadcrumbs(folder), element("h1", basename(folder) || "Lean source"));
  if (!folders.size && !files.length) {
    article.append(element("p", "This folder is unavailable."));
    return;
  }
  article.append(list([
    ...Array.from(folders, child => link(child + "/", url({ folder: prefix + child }))),
    ...files.map(child => link(child, url({ module: prefix + child }))),
  ]));
}

function searchView(article, query, modules) {
  const needle = moduleName(query).toLowerCase();
  const exact = [];
  const partial = [];
  for (const path of modules) {
    if (!needle || !moduleName(path).toLowerCase().includes(needle)) continue;
    const match = moduleName(basename(path)).toLowerCase() === needle ? exact : partial;
    match.push(path);
  }
  const paths = exact.concat(partial);
  const limit = 60;
  const count = paths.length.toLocaleString("en-US");
  article.append(
    element("h1", "Module search"),
    element("p", count + (paths.length === 1 ? " module found." : " modules found.") +
      (paths.length > limit ? " Showing the first " + limit + "." : "")),
    list(paths.slice(0, limit).map(path => link(path, url({ module: path })))),
  );
}

async function main() {
  const { modules } = await readPack("catalog.json.gz");
  const packNumbers = new Map(modules);
  const paths = Array.from(packNumbers.keys());
  const folders = [...new Set(paths.filter(path => path.includes("/")).map(path => path.split("/")[0]))];
  const current = params.get("module") || "Main.lean";
  const article = element("article");
  root.replaceChildren(sidebar(paths.length, folders, current), article);
  if (params.has("q")) {
    searchView(article, params.get("q").trim(), paths);
  } else if (params.has("folder")) {
    folderView(article, params.get("folder").replace(/\/$/, ""), paths);
  } else if (packNumbers.has(current)) {
    const loading = element("p", "Loading the module…");
    article.append(loading);
    const pack = await readPack(packNumbers.get(current) + ".json.gz");
    loading.remove();
    const names = new Map(paths.map(path => [moduleName(path), path]));
    moduleView(article, current, pack[current], names);
  } else {
    article.append(element("h1", "Module unavailable"), link("Open Main.lean", url({ module: "Main.lean" })));
  }
}

main().catch(error => root.replaceChildren(element("p", error.message, { role: "alert" })));
