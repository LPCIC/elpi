/*
 * The Elpi language server, shared by setup/monaco.ts (diagnostics and
 * hover in the editors) and setup/code-runners.ts (running programs).
 *
 * The server is elpi-lsp for the web, public/elpi-webrunner/elpi-lsp-web.js, run
 * in a web worker; it speaks LSP (JSON-RPC) with postMessage. It is built in
 * the elpi repository by `make webrunner` (compiled to WebAssembly, used when
 * the browser can, and to JavaScript), in webrunner/elpi-webrunner/.
 * Besides the standard LSP requests it answers
 *   elpi/run { textDocument: { uri }, text?, query, maxSteps? }
 *     -> { status: 'success' | 'failure' | 'error', output,
 *          errors: string[], diagnostics: string[],
 *          assignments?: { [name]: string }, constraints?: string[] }
 * where diagnostics are the errors and warnings of the program (the ones
 * underlined in the editor) and errors the ones of the query and of its run
 * (running out of steps is a failure with the error "no more steps"); on
 * success, assignments are the values of the variables of the query and
 * constraints the ones left by the run.
 * A request that the server answers with an error is rejected.
 */

export interface Diagnostic {
  range: { start: { line: number, character: number }, end: { line: number, character: number } }
  severity?: number
  message: string
  source?: string
}
export interface RunResult {
  status: 'success' | 'failure' | 'error'
  output: string
  errors: string[]
  diagnostics: string[]
  assignments?: { [name: string]: string }
  constraints?: string[]
}

class ElpiLsp {
  private worker: Worker
  // the requests waiting for their response
  private pending = new Map<number, { resolve: (result: any) => void, reject: (error: Error) => void }>()
  private nextId = 1
  private ready: Promise<void>
  onDiagnostics: (uri: string, diagnostics: Diagnostic[]) => void = () => {}

  constructor() {
    this.worker = new Worker(`${import.meta.env.BASE_URL}elpi-webrunner/elpi-lsp-web.js`)
    this.worker.onmessage = ({ data }) => {
      if (data.id !== undefined && this.pending.has(data.id)) {
        const { resolve, reject } = this.pending.get(data.id)!
        this.pending.delete(data.id)
        // an error response (e.g. invalid parameters, an exception of the
        // server) rejects the request with its message
        if (data.error)
          reject(new Error(data.error.message ?? 'error of the language server'))
        else
          resolve(data.result)
      }
      else if (data.method === 'textDocument/publishDiagnostics') {
        this.onDiagnostics(data.params.uri, data.params.diagnostics)
      }
    }
    // the server died: the requests waiting for a response fail
    this.worker.onerror = (e) => {
      console.error('[elpi-lsp]', e.message)
      for (const { reject } of this.pending.values())
        reject(new Error(`the language server failed: ${e.message}`))
      this.pending.clear()
    }
    this.ready = this.send('initialize', {
      processId: null,
      rootUri: null,
      capabilities: {},
      initializationOptions: { maxErrors: 100 },
    }).then(() => this.post({ method: 'initialized', params: {} }))
  }

  private post(msg: object) {
    this.worker.postMessage({ jsonrpc: '2.0', ...msg })
  }

  private send(method: string, params: object): Promise<any> {
    return new Promise((resolve, reject) => {
      const id = this.nextId++
      this.pending.set(id, { resolve, reject })
      this.post({ id, method, params })
    })
  }

  async request(method: string, params: object): Promise<any> {
    await this.ready
    return this.send(method, params)
  }

  // a notification has no answer: if the server could not be initialized, it
  // is dropped (the requests report the failure)
  async notify(method: string, params: object) {
    try { await this.ready } catch { return }
    this.post({ method, params })
  }

  open(uri: string, text: string, version: number) {
    return this.notify('textDocument/didOpen', { textDocument: { uri, languageId: 'elpi', version, text } })
  }

  change(uri: string, text: string, version: number) {
    return this.notify('textDocument/didChange', { textDocument: { uri, version }, contentChanges: [{ text }] })
  }

  close(uri: string) {
    return this.notify('textDocument/didClose', { textDocument: { uri } })
  }

  // runs `query` in the program `text`, for at most `maxSteps` steps
  // (a loop stops in about a second with the default); the slides have no
  // files: the text is said to be in a directory, /slides/
  run(text: string, { query = 'main', maxSteps = 1_000_000 } = {}): Promise<RunResult> {
    return this.request('elpi/run', { textDocument: { uri: 'file:///slides/' }, text, query, maxSteps })
  }
}

let instance: ElpiLsp | undefined

export function elpiLsp(): ElpiLsp {
  instance ??= new ElpiLsp()
  return instance
}
