import { defineShikiSetup } from '@slidev/types'
import Elpi from './elpi-syntax.tmLanguage.json'

// Elpi syntax highlighting, in code blocks and in the Monaco editors.
// Merge with your setup/shiki.ts if you already have one.
export default defineShikiSetup(() => {
  return {
    langs: ['ts', 'js', 'vue', 'html', 'yaml', 'md', 'markdown', Elpi],
  }
})
