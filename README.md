# Systems verification Fall 2024 course website

[![deploy](https://github.com/tchajed/sys-verif-fa24/actions/workflows/deploy.yml/badge.svg)](https://github.com/tchajed/sys-verif-fa24/actions/workflows/deploy.yml) [![website](https://img.shields.io/badge/website-blue?logo=web)](https://tchajed.github.io/sys-verif-fa24/)

## Developing

You'll need Node.js and pnpm. You should probably use [corepack](https://pnpm.io/installation#using-corepack) to get pnpm.

Install the dependencies: `pnpm install`.

Run a dev server to preview changes: `pnpm docs:dev`. The dev server auto-updates and hot-reloads page content, but not structure. Restart it if you make structural changes that affect the sidebar (e.g., add new files), or start it with `pnpm docs:dev --debug` to do a more expensive reload on every change.

Build static site: `pnpm docs:build`.

Auto-format code (with [prettier](https://prettier.io/)): `pnpm fmt`.

## Tech stack

- pnpm for package management
- [VuePress](https://vuepress.vuejs.org/)
  - Using the [VuePress Hope theme](https://theme-hope.vuejs.press/) (rather than the default)
  - Pretty much the whole setup is in [config.ts](docs/.vuepress/config.ts). YAML frontmatter in individual pages takes care of some aspects.
- Build and deploy via [GitHub Pages workflow](./.github/workflows/deploy.yml)
