# Systems verification Fall 2024 course website

[![deploy](https://github.com/tchajed/sys-verif-fa24/actions/workflows/deploy.yml/badge.svg)](https://github.com/tchajed/sys-verif-fa24/actions/workflows/deploy.yml)

[Deployed site](https://tchajed.github.io/sys-verif-fa24/)

Run a dev server: `pnpm docs:dev`

Build static site: `pnpm docs:build`

Tech stack:

- pnpm
- [VuePress 2](https://vuepress.vuejs.org/)
  - Using the [VuePress Hope theme](https://theme-hope.vuejs.press/) (rather than the default)
  - Pretty much the whole setup is in [config.ts](docs/.vuepress/config.ts). YAML frontmatter in individual pages takes care of some aspects.
- Build and deploy via GitHub Pages [workflow](./.github/workflows/deploy.yml)

## Coq syntax highlighting

Highlighting uses shiki, which doesn't have Coq in its default bundle of languages. We use the grammar from VSCoq, which can be updated with this:

```sh
wget -O docs/assets/coq.tmLanguage.json 'https://raw.githubusercontent.com/coq-community/vscoq/main/client/syntax/coq.tmLanguage.json'
```
