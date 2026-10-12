// make tests-lsp-web: a use of all the API, typechecked against
// ../../web_api.d.ts (not run: test.cjs runs the API)

import { elpi, Program, ElpiError, ThrownError } from "../../web_api";

const { Setup, Parse, Compile, Execute } = elpi;

let output = "";
Setup.setStdFormatter((s) => (output += s));
Setup.setErrFormatter(() => {});
const e = Setup.init({ fileResolver: (unit, cwd) => unit, flags: { definedVariables: ["V"] } });

const ast = Parse.programFrom(e, "pred p o:int.\np 1. p 2.", { source: "a.elpi", flags: { maxErrors: 3 } });
const errors: ElpiError[] = ast.errors;
const program = Compile.program(e, ast.program, { flags: Compile.defaultFlags });
const parsed = Parse.query(e, "p X, X > 1.", { source: "q" });
if ("error" in parsed) throw new Error(parsed.error.text);
const q = Compile.query(program.program, parsed.query);
if ("query" in q) {
  const o = Execute.once(Compile.optimize(q.query), { maxSteps: 100, delayOutsideFragment: true });
  if (o.outcome === "success") console.log(o.assignments.X, o.constraints, o.state);
} else {
  console.log(q.error.text, q.warnings.map((w) => w.id));
}

const scoped = Compile.scopeAst(e, ast.program);
let base: Program = Compile.emptyBase(e);
for (const sp of scoped.scopedPrograms) base = Compile.extend(base, Compile.unit(e, base, sp).unit).program;

try { Compile.program(e, ast.program); } catch (err) { const t = err as ThrownError; console.log(t.component, t.loc?.line); }

// the opaque types are not interchangeable
// @ts-expect-error
Compile.optimize(base);

const g = globalThis.elpi;
if (g) g.Setup.init();
