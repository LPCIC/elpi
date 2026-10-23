/*
 * Diagnostics and hover for the Elpi Monaco editors of the slides
 * (```elpi {monaco} and ```elpi {monaco-run} blocks), from the Elpi language
 * server of setup/elpi-lsp.ts.
 *
 * Every editor is a separate document (file:///ID.elpi, created by Slidev):
 * the server checks it on every change and publishes diagnostics, shown as
 * Monaco markers; hovering asks the server for the type of what is under the
 * mouse.
 *
 * The code between the comments % hidden: and % hidden-end (on lines of
 * their own) is folded when the editor opens: the editor, the server and the
 * runner have the whole code, the slide shows the rest. The line of
 * % hidden: stays visible, with what follows the colon, e.g.
 * % hidden: the facts. When exporting (PDF, PNG...) nothing is folded: the
 * export shows the whole code. The diagnostics of the hidden code are not
 * shown (also the ones without a location, e.g. undeclared globals, when all
 * the lines they mention are hidden).
 */

import type { Diagnostic } from './elpi-lsp'
import { defineMonacoSetup } from '@slidev/types'
import { elpiLsp } from './elpi-lsp'

type Monaco = typeof import('monaco-editor')
type Range = Diagnostic['range']

let started = false

// the ranges between % hidden: and % hidden-end (they can nest), 1-based
const begin = /^\s*%\s*hidden:/
const end = /^\s*%\s*hidden-end\b/
function hiddenRanges(model: import('monaco-editor').editor.ITextModel) {
  const ranges: { start: number, end: number }[] = []
  const open: number[] = []
  for (let line = 1; line <= model.getLineCount(); line++) {
    const text = model.getLineContent(line)
    if (begin.test(text))
      open.push(line)
    else if (end.test(text) && open.length > 0)
      ranges.push({ start: open.pop()!, end: line })
  }
  return ranges
}
// the lines that folding hides: the line of % hidden: stays visible
function hiddenLines(model: import('monaco-editor').editor.ITextModel) {
  const lines = new Set<number>()
  for (const { start, end } of hiddenRanges(model))
    for (let l = start + 1; l <= end; l++)
      lines.add(l)
  return lines
}

function setupElpi(monaco: Monaco) {
  const lsp = elpiLsp()

  const severity = [
    monaco.MarkerSeverity.Error, // LSP severities start at 1
    monaco.MarkerSeverity.Error,
    monaco.MarkerSeverity.Warning,
    monaco.MarkerSeverity.Info,
    monaco.MarkerSeverity.Hint,
  ]
  const toRange = (r: Range) => new monaco.Range(
    r.start.line + 1, r.start.character + 1, r.end.line + 1, r.end.character + 1)

  lsp.onDiagnostics = (uri, diagnostics) => {
    const model = monaco.editor.getModel(monaco.Uri.parse(uri))
    if (!model)
      return
    const hidden = hiddenLines(model)
    const shown = (d: Diagnostic) => {
      const r = d.range
      // without a location the server puts it at the beginning: it is hidden
      // if all the lines that its message mentions are
      if (r.start.line === 0 && r.start.character === 0 && r.end.line === 0 && r.end.character === 0) {
        const lines = [...d.message.matchAll(/line (\d+)/g)].map(m => Number(m[1]))
        return lines.length === 0 || !lines.every(l => hidden.has(l))
      }
      return !hidden.has(r.start.line + 1)
    }
    monaco.editor.setModelMarkers(model, 'elpi', diagnostics.filter(shown).map(d => ({
      ...toRange(d.range),
      severity: severity[d.severity ?? 1],
      message: d.message,
      source: d.source,
    })))
  }

  // documents: one per Elpi editor
  const track = (model: import('monaco-editor').editor.ITextModel) => {
    if (model.getLanguageId() !== 'elpi')
      return
    const uri = model.uri.toString()
    lsp.open(uri, model.getValue(), model.getVersionId())
    let timer: ReturnType<typeof setTimeout> | undefined
    const change = model.onDidChangeContent(() => {
      clearTimeout(timer)
      timer = setTimeout(() => lsp.change(uri, model.getValue(), model.getVersionId()), 300)
    })
    model.onWillDispose(() => {
      clearTimeout(timer)
      change.dispose()
      lsp.close(uri)
    })
  }
  monaco.editor.getModels().forEach(track)
  monaco.editor.onDidCreateModel(track)

  monaco.languages.registerFoldingRangeProvider('elpi', {
    provideFoldingRanges(model) {
      return hiddenRanges(model).map(r => ({ ...r, kind: monaco.languages.FoldingRangeKind.Region }))
    },
  })

  // the folds are closed when the editor opens. The folding ranges are
  // computed asynchronously: folding is tried again until some lines are
  // hidden (for at most two seconds), not after, so that what the user opens
  // stays open
  const visibleLines = (editor: import('monaco-editor').editor.ICodeEditor) =>
    editor.getVisibleRanges().reduce((n, r) => n + r.endLineNumber - r.startLineNumber + 1, 0)
  // exporting: `slidev export` loads the slides with ?print=..., the export
  // page of the browser is the route /export (also #/export with hash routing)
  const exporting = () =>
    new URLSearchParams(location.search).has('print')
    || /(^|\/)export\b/.test(location.pathname + location.hash)
  const foldOnOpen = (editor: import('monaco-editor').editor.ICodeEditor) => {
    const model = editor.getModel()
    if (exporting() || !model || model.getLanguageId() !== 'elpi' || !model.getLinesContent().some(l => begin.test(l)))
      return
    let tries = 20
    const fold = () => {
      const before = visibleLines(editor)
      editor.trigger('elpi', 'editor.foldAll', null)
      setTimeout(() => {
        if (visibleLines(editor) === before && --tries > 0)
          fold()
      }, 100)
    }
    fold()
  }
  monaco.editor.onDidCreateEditor((editor) => {
    foldOnOpen(editor) // Slidev gives the model when it creates the editor
    editor.onDidChangeModel(() => foldOnOpen(editor))
  })

  // hover: the type of the symbol under the mouse
  monaco.languages.registerHoverProvider('elpi', {
    async provideHover(model, position) {
      // no hover if the server fails to answer
      const hover = await lsp.request('textDocument/hover', {
        textDocument: { uri: model.uri.toString() },
        position: { line: position.lineNumber - 1, character: position.column - 1 },
      }).catch(() => null)
      if (!hover)
        return null
      const contents = (Array.isArray(hover.contents) ? hover.contents : [hover.contents])
        .map((c: any) => typeof c === 'string' ? c : c.value ?? '')
        .map((value: string) => ({ value: value.replace(/```elpi-hover/g, '```elpi') }))
      return { contents, range: hover.range && toRange(hover.range) }
    },
  })
}

export default defineMonacoSetup((monaco) => {
  if (!started) {
    started = true
    setupElpi(monaco as unknown as Monaco)
  }
})
