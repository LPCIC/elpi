// Makes the entry points of the web build from their templates, filling in
// what they share and what they inline (see dune):
//
//   node assemble.cjs server server-entry.js > elpi-lsp-web.js
//   node assemble.cjs api api-entry.js web_api.bc.wasm.js web_api.bc.wasm.assets > elpi-api.js
//
// - /*@WASM_FEATURES@*/: a module that uses what the WebAssembly builds need
//   (GC, the legacy exception handling, tail calls), to test the engine with
//   WebAssembly.validate;
// - /*@WASM_FILES@*/ (api): the .wasm files of the WebAssembly build of the
//   API, in base64, by name;
// - /*@WASM_LOADER@*/ (api): the script made by wasm_of_ocaml that starts
//   that build (web_api.bc.wasm.js), as the body of a function.

const fs = require("node:fs");
const path = require("node:path");

const features = `new Uint8Array([
    0, 97, 115, 109, 1, 0, 0, 0, 1, 12, 3, 96, 0, 1, 127, 95, 1, 127, 0, 96, 0,
    0, 3, 3, 2, 0, 0, 13, 3, 1, 0, 2, 7, 5, 1, 1, 102, 0, 0, 10, 26, 2, 4, 0,
    18, 1, 11, 19, 0, 6, 64, 8, 0, 7, 0, 1, 11, 65, 1, 251, 0, 1, 251, 2, 1, 0,
    11,
  ])`;

// replaces the placeholder, which must be there once
function fill(text, placeholder, value) {
  const parts = text.split(`/*@${placeholder}@*/`);
  if (parts.length !== 2) throw new Error(`assemble: ${placeholder} is not in the template once`);
  return parts[0] + value + parts[1];
}

const [kind, template, ...rest] = process.argv.slice(2);
let text = fill(fs.readFileSync(template, "utf8"), "WASM_FEATURES", features);
if (kind === "api") {
  const [loader, assets] = rest;
  const files = {};
  for (const f of fs.readdirSync(assets).filter((f) => f.endsWith(".wasm")).sort())
    files[f] = fs.readFileSync(path.join(assets, f)).toString("base64");
  if (Object.keys(files).length === 0) throw new Error(`assemble: no .wasm file in ${assets}`);
  text = fill(text, "WASM_FILES", JSON.stringify(files));
  text = fill(text, "WASM_LOADER", "\n" + fs.readFileSync(loader, "utf8") + "\n");
} else if (kind !== "server") {
  throw new Error(`assemble: unknown kind ${kind}`);
}
process.stdout.write(text);
