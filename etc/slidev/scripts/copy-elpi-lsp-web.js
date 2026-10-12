// Copies the web language server of Elpi, the npm package elpi-lsp-web (in
// node_modules), to public/elpi-lsp-web/, where the slides load it: the
// worker loads the files next to it at run time, they are served as they are.
// Run before slidev (npm run dev, build, export).

import { cpSync, existsSync, realpathSync, rmSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const src = join(root, "node_modules", "elpi-lsp-web");
const dest = join(root, "public", "elpi-lsp-web");
if (!existsSync(join(src, "elpi-lsp-web.js"))) {
  console.error("node_modules/elpi-lsp-web/elpi-lsp-web.js is missing: npm install (see README.md)");
  process.exit(1);
}
rmSync(dest, { recursive: true, force: true });
// src is a link for a file: dependency, to a directory that can have the
// packages made by make pack-lsp-web
cpSync(realpathSync(src), dest, { recursive: true, dereference: true, filter: (f) => !f.endsWith(".tgz") });
console.log(`public/elpi-lsp-web/: ${realpathSync(src)}`);
