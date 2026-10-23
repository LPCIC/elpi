# Elpi in Slidev

Editable and runnable Elpi code in the slides of a [Slidev](https://sli.dev)
deck, powered by the web build of `elpi-lsp` (see `webrunner/README.md` in the
root of the repository), which runs in the browser in a web worker:

- the Elpi code blocks become [Monaco](https://sli.dev/features/monaco-editor)
  editors with Elpi syntax highlighting, errors and warnings underlined as you
  type, and the type of a symbol on hover;
- runnable blocks also run `main` and show below the code what it printed.

    ```elpi {monaco-run}
    main :- print "hello".
    ```

## The reference deck

This folder is a Slidev deck that shows all the features (`slides.md`). In
the root of the elpi repository build the server (it needs js_of_ocaml and
wasm_of_ocaml):

    make webrunner

Then in this directory:

    npm install
    npm run dev

The server is the npm package `elpi-webrunner`, here the one built in
`webrunner/elpi-webrunner/`.

## Setup in your slides

1. Install the npm package `elpi-webrunner` in the slides and copy it to their
   `public/elpi-webrunner/` folder before running Slidev:

   - `npm install elpi-webrunner` (from npm), or
     `npm install path/to/elpi-webrunner-VERSION.tgz`
     (the artifact `elpi-webrunner` of the CI of elpi, or
      `make webrunner pack-webrunner` in the
      root of the elpi repository);
   - copy `scripts/copy-elpi-webrunner.js` to the slides, and run it before
     Slidev, as the `predev`, `prebuild` and `preexport` scripts of
     `package.json` do here; ignore `public/elpi-webrunner` in git.

   The entry point `elpi-lsp-web.js`, which loads
   the server compiled to WebAssembly when the browser can, to JavaScript
   otherwise (about 1MB each). The `.wasm` files must be served as
   `application/wasm` for the WebAssembly server to be used.

2. Copy the files of `setup/` to the `setup/` folder of the slides:

   - `elpi-lsp.ts`: starts the server in a web worker, used by the next two
   - `monaco.ts`: diagnostics and hover in the Monaco editors
   - `code-runners.ts`: runs the code of `{monaco-run}` blocks
   - `shiki.ts`, `elpi-syntax.tmLanguage.json`: Elpi syntax highlighting. If
     the slides already have a `setup/shiki.ts`, add the grammar to its
     `langs` instead. The grammar is the one of the VS Code extension
     ([elpi-lang](https://github.com/LPCIC/elpi-lang), `syntaxes/`) with
     `"name": "elpi"`, which Shiki uses as the language id.

   If `slidev` is running, restart it after adding the files.

3. Optionally, for the output on the right of the code, the CSS of
   `styles/index.css`, see below.

## Usage

An editor with diagnostics and hover:

    ```elpi {monaco}
    pred age -> string, int.
    age "bob" 23.
    ```

The same, plus the output of `main`, run when the slide loads and again on
every edit (or by clicking the play button):

    ```elpi {monaco-run}
    main :- std.map [1,2,3] (x\ y\ y is x * 2) L, print L.
    ```

The code can come from a file:

    <<< @/snippets/example.elpi elpi {monaco-run}

To show only part of the code, put the rest between `% hidden:` and
`% hidden-end` (comments on lines of their own; they can nest): it is folded
when the editor opens, and can be unfolded by clicking. The line of
`% hidden:` stays visible, so the text after the colon (optional) can say
what is folded:

    % hidden: the facts
    pred age o:string, o:int.
    age "bob" 23.
    % hidden-end
    main :- age X Y, print X "is" Y "years old".

The editor, the diagnostics and the run are about the whole code. An export
(`slidev export`, to PDF or PNG) folds nothing: it shows the whole code.

The options of Slidev for runnable blocks apply, e.g.:

```
    ```elpi {monaco-run} {autorun:false}        run only via the play button
    ```elpi {monaco-run} {showOutputAt:'+1'}    reveal the output on a click
    ```elpi {monaco-run} {outputHeight:'10rem'} fixed height for the output
```

### Output on the right

Slidev always renders the output below the editor, in the same
`.slidev-monaco-container`: a CSS grid on that container puts them side by
side. Wrap the block in an element with a class of your choice (keep the
blank lines, or the block is not parsed as markdown):

    <div class="run-side">

    ```elpi {monaco-run}
    main :- print "hello".
    ```

    </div>

and add to a stylesheet of the slides (e.g. `styles/index.css`, as in the
reference deck):

```css
.run-side .slidev-monaco-container {
  display: grid; grid-template-columns: 1fr 1fr; gap: 1rem;
}
/* the output pane: its top border becomes a left one */
.run-side .slidev-monaco-container > div:nth-child(2) {
  border-top: 0; border-left: 1px solid #333;
}
```

The class can also go on the slide (`class: run-side` in its frontmatter) to
affect all its runnable blocks.

## How it works

- One worker runs the server for the whole deck. Every editor is a document of
  its own (`file:///ID.elpi`, created by Slidev); the diagnostics the server
  publishes become Monaco markers.
- Running a block sends the custom request `elpi/run` with the code as `text`
  (and, since the slides have no files, `file:///slides/` as the URI of
  where the text is),
  the query `main` and `maxSteps` 1000000: a program that does not terminate
  stops after about a second with the error `no more steps` (a `Failure.`).
  The result separates the `diagnostics` of the program, which are not shown
  (the editor underlines them), from the `errors` of the query and of the run,
  which are (they include the warning that a program with errors could not be
  fully compiled).
  The defaults are in `run` of `elpi-lsp.ts`.
- `monaco.ts` gives Monaco the folding ranges between `% hidden:` and
  `% hidden-end`, and folds them all when an editor opens: nothing else knows
  about them, the code is the same for the editor, the server and the runner.

## Limitations

- There are no files: `accumulate` gives an error, the program of a block must
  be self-contained, and each block is checked and run on its own.
- The query is always `main`, with no arguments.
- Warnings without a location (e.g. "Undeclared globals") are underlined at
  the beginning of the code.

## Files

- `setup/`: what to copy to the slides, see above
- `slides.md`, `snippets/example.elpi`, `styles/index.css`: the reference deck
- `scripts/copy-elpi-webrunner.js`: copies the server from `node_modules/` to
  `public/elpi-webrunner/` (not in git)
- `package.json`: Slidev and the server, to run the reference deck
- `dune`: keeps dune out of `node_modules/`
