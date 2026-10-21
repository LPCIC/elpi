// The tests of the API of Elpi for JavaScript, on the build given on the
// command line (web_api.bc.js or web_api.bc.wasm.js): what they print is
// compared with test.expected.
//
//   node test.cjs path/to/web_api.bc.js

const path = require("node:path");
const server = path.resolve(process.argv[2]);
// the WebAssembly build finds its assets next to the main module
process.mainModule = { filename: server };
const loaded = require(server);

// the WebAssembly build exports elpi asynchronously
async function getElpi() {
  for (let i = 0; i < 1000; i++) {
    const elpi = loaded.elpi || globalThis.elpi;
    if (elpi) return elpi;
    await new Promise((r) => setTimeout(r, 10));
  }
  throw new Error("elpi is not exported");
}

const show = (title, v) => console.log(`${title}: ${JSON.stringify(v)}`);
const texts = (l) => l.map((e) => e.text);

async function main() {
  const { Setup, Parse, Compile, Execute } = await getElpi();
  let output = "";
  Setup.setStdFormatter((s) => (output += s));

  show("default flags", Compile.defaultFlags);
  const elpi = Setup.init({});

  // parse, compile, run
  const program = `
pred p o:int.
p 1. p 2. p 3.
main :- print "hello", p X, X > 1, print X.
`;
  // the goal of Parse.query, which has no error here
  const goal = (e, text) => {
    const r = Parse.query(e, text);
    if (r.error) throw new Error(r.error.text);
    return r.query;
  };
  const ast = Parse.programFrom(elpi, program, { source: "a.elpi" });
  show("parse errors", texts(ast.errors));
  const p = Compile.program(elpi, ast.program);
  show("compile errors", texts(p.errors));
  const run = (text, options) => {
    const q = Compile.query(p.program, goal(elpi, text));
    if (q.error) return { error: q.error.text };
    return Execute.once(Compile.optimize(q.query), options);
  };
  output = "";
  show("main", run("main."));
  show("output", output);
  show("p X", run("p X, X > 1."));
  show("p X, X > 5", run("p X, X > 5."));
  show("constraints", run("declare_constraint (p X) [X]."));
  show("type error in the query", run("p \"x\"."));
  show("noMoreSteps", run("std.iota 1000 L.", { maxSteps: 10 }));

  // errors and warnings: thrown, or returned with maxErrors
  const syntax = Parse.query(elpi, "p (.");
  show("query syntax error", { component: syntax.error.component, loc: syntax.error.loc, message: syntax.error.message.trim() });
  try { Compile.program(elpi, Parse.programFrom(elpi, "p \"x\".\npred p i:int.", { source: "b.elpi" }).program); }
  catch (e) { show("thrown ElpiError", { component: e.component, loc: e.loc, message: e.message.split("\n").pop() }); }
  // errors raised by a run (std.fatal-error, an exception of a builtin):
  // thrown as Errors, also by the WebAssembly build
  for (const q of ['std.fatal-error "boom".', "X is 1 div 0."]) {
    try { run(q); show(q, "not thrown"); }
    catch (e) { show(q, { error: e instanceof Error, message: e.message }); }
  }
  const flags = { maxErrors: 10 };
  const bad = Parse.programFrom(elpi, "p ( .\npred p i:int.\np \"x\".\nq X :- true.\n", { source: "c.elpi", flags });
  show("syntax errors", bad.errors.map((e) => ({ component: e.component, loc: e.loc, message: e.message })));
  const badp = Compile.program(elpi, bad.program, { flags });
  show("type errors", texts(badp.errors));
  show("warnings", badp.warnings.map((w) => w.id));

  // separate compilation
  const scoped = Compile.scopeAst(elpi, ast.program);
  show("scoped programs", scoped.scopedPrograms.length);
  // the empty base has the builtins already
  const base = Compile.emptyBase(elpi);
  const u = Compile.unit(elpi, base, scoped.scopedPrograms[0]);
  show("unit errors", texts(u.errors));
  const prog = Compile.extend(base, u.unit);
  show("extend errors", texts(prog.errors));
  const q = Compile.query(prog.program, goal(elpi, "main."));
  output = "";
  show("separate main", Execute.once(Compile.optimize(q.query)));
  show("separate output", output);

  // conditional compilation: the rules of :if "V" are there if V is defined
  const ifProgram = "pred s o:int.\n:if \"V\" s 1.\ns 2.";
  for (const definedVariables of [[], ["V"]]) {
    const ifp = Compile.program(elpi, Parse.programFrom(elpi, ifProgram, { source: "e.elpi" }).program, { flags: { definedVariables } });
    show(`s X with ${JSON.stringify(definedVariables)}`, Execute.once(Compile.optimize(Compile.query(ifp.program, goal(elpi, "s X.")).query)).assignments);
  }

  // separate compilation of two texts: the second uses a predicate of the
  // first, its unit is compiled against a base that has it
  let base2 = Compile.emptyBase(elpi);
  const unitOf = (base, text, source) => {
    const [sp] = Compile.scopeAst(elpi, Parse.programFrom(elpi, text, { source }).program).scopedPrograms;
    return Compile.unit(elpi, base, sp, { flags: { maxErrors: 10 } });
  };
  const uA = unitOf(base2, "pred r o:int.\nr 1. r 2.", "ua.elpi");
  base2 = Compile.extend(base2, uA.unit).program;
  const uB = unitOf(base2, "pred main2.\nmain2 :- r X, X > 1, print X.", "ub.elpi");
  show("second unit errors", texts(uB.errors));
  base2 = Compile.extend(base2, uB.unit).program;
  output = "";
  show("two units main2", Execute.once(Compile.optimize(Compile.query(base2, goal(elpi, "main2.")).query)));
  show("two units output", output);
  show("against the empty base", texts(unitOf(Compile.emptyBase(elpi), "pred main3.\nmain3 :- r X.", "uc.elpi").errors));

  // accumulate: files of the file system of Node, found by the file resolver
  const fs = require("node:fs");
  const fileResolver = (unit, cwd) => {
    const file = path.join(__dirname, unit.endsWith(".elpi") ? unit : unit + ".elpi");
    if (!fs.existsSync(file)) throw new Error(`cannot find ${unit}`);
    return file;
  };
  const elpiFiles = Setup.init({ fileResolver });
  const acc = Parse.programFrom(elpiFiles, "accumulate test-acc.\nmain :- q X, print X.", { source: path.join(__dirname, "main.elpi") });
  show("accumulate errors", texts(acc.errors));
  const accp = Compile.program(elpiFiles, acc.program);
  output = "";
  show("accumulate main", Execute.once(Compile.optimize(Compile.query(accp.program, goal(elpiFiles, "main.")).query)));
  show("accumulate output", output);
  const missing = Parse.programFrom(elpiFiles, "accumulate nonexistent.", { source: "d.elpi", flags: { maxErrors: 10 } });
  show("accumulate a missing file", missing.errors.map((e) => ({ component: e.component, line: e.loc && e.loc.line, message: e.message })));
  Setup.setErrFormatter(() => {});
}

main().catch((e) => { console.log("FAILED", e); process.exit(1); });
