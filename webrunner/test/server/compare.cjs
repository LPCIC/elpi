// Compares the outputs of a run of test_lsp with the expected ones: each
// NAME.output of DIR with the NAME.expected of the first of the EXPECTED
// directories that has one; prints the differences, and fails if there are
// some.
//
//   node compare.cjs DIR EXPECTED...

const fs = require("node:fs");
const path = require("node:path");
const { spawnSync } = require("node:child_process");

const [dir, ...expected] = process.argv.slice(2);
let ok = true;
for (const output of fs.readdirSync(dir).filter((f) => f.endsWith(".output")).sort()) {
  const name = output.slice(0, -".output".length) + ".expected";
  const found = expected.map((d) => path.join(d, name)).find((f) => fs.existsSync(f));
  if (!found) { console.log(`${output}: no ${name}`); ok = false; continue; }
  const r = spawnSync("diff", ["-u", found, path.join(dir, output)], { encoding: "utf8" });
  if (r.status !== 0) { process.stdout.write(r.stdout || r.stderr); ok = false; }
}
process.exit(ok ? 0 : 1);
