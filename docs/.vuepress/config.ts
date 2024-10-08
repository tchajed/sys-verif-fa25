import { hopeTheme, navbar, sidebar } from "vuepress-theme-hope";
import { defineUserConfig } from "vuepress";
import { viteBundler } from "@vuepress/bundler-vite";
import { googleAnalyticsPlugin } from "@vuepress/plugin-google-analytics";

// Vue Router picks up configuration for paths in the navbar and sidebar from
// the YAML frontmatter, for example the 'title' (or first h1), 'shortTitle',
// and 'icon'.
//
// README.md is used for the index page of a directory.

const navbarConfig = navbar([
  "/",
  "/assignments/",
  "/notes/",
  {
    text: "Other",
    icon: "circle-question",
    children: [
      {
        text: "Calendar",
        icon: "calendar",
        link: "/#calendar",
      },
      "/syllabus.md",
      "/resources.md",
    ],
  },
]);
const sidebarConfig = sidebar({
  "/": [
    "",
    "syllabus",
    "resources",
    {
      text: "Assignments",
      icon: "list-check",
      prefix: "assignments/",
      link: "/assignments/",
      children: "structure",
    },
    {
      text: "Lecture notes",
      icon: "lightbulb",
      prefix: "notes/",
      link: "/notes/",
      children: ["sep-logic.md", "ipm.md"],
    },
  ],
  "/notes/": "structure",
  "/assignments/": "structure",
});

export default defineUserConfig({
  lang: "en-US",

  // The path to the hosted website from its domain. We deploy to GitHub pages
  // which automatically puts websites at <username>.github.io/<repo-name>,
  // unless using a custom domain.
  base: "/sys-verif-fa24/",

  title: "CS 839",
  description: "Systems Verification Fall 2024",

  // .snippet.md files are usable as '@include' files but don't produce output
  // pages.
  pagePatterns: ["**/*.md", "!**/*.snippet.md", "!.vuepress", "!node_modules"],

  theme: hopeTheme({
    navbar: navbarConfig,
    repo: "https://github.com/tchajed/sys-verif-fa24",
    headerDepth: 2,
    sidebar: sidebarConfig,

    plugins: {
      mdEnhance: {
        tasklist: true,
        include: true,
        // allow {#custom-id} attributes
        attrs: {
          allowed: ["id"],
        },
      },
      git: {
        createdTime: true,
        updatedTime: true,
      },
      markdownMath: {
        type: "katex",
        // copy as text (change to true to copy as LaTeX source)
        copy: false,
        // the rest of the config is passed to KaTeX, see
        // https://katex.org/docs/options.html
      },
      // see https://ecosystem.vuejs.press/plugins/markdown/shiki.html for the below config
      shiki: {
        langs: ["coq", "go", "bash"],
        // customized from one-light and one-dark-pro
        themes: {
          light: "catppuccin-latte",
          dark: "catppuccin-macchiato",
        },
        // add something like {1,7-9} to the ```lang line
        // TODO: disabled for now since text="goal 1" is parsed as highlighting line 1
        highlightLines: false,
        // add // [!code ++] or // [!code --] to the end of a code line (emitted from template compiler for Coq output diffs)
        notationDiff: true,
        // add // [!code highlight] to the end of a line
        notationHighlight: true,
        // add :line-numbers to ```lang line to enable selectively
        lineNumbers: false,
      },
      copyCode: false,
      // https://ecosystem.vuejs.press/plugins/search/search.html
      search: {
        hotKeys: [{ key: "k", ctrl: true }, "/"],
        locales: {
          "/": {
            placeholder: "Search",
          },
        },
      },
    },

    // control page meta information shown
    // see https://theme-hope.vuejs.press/guide/feature/meta.html
    contributors: false,
    editLink: false, // feedback is better than edits/PRs
    // Could add "ReadingTime" (and reduce words/minute, default is 300) or
    // "Word" to give length estimate.
    pageInfo: ["Date", "Category", "Tag"],
    toc: true, // usually desired, but disabled on home page
    print: false, // no need to offer print button

    author: "Tej Chajed",
    license: "CC-BY-NC 4.0",
    logo: "/logo.png",
    favicon: "/favicon.png",
    iconAssets: "fontawesome",
  }),

  plugins: [
    googleAnalyticsPlugin({
      id: "G-RMW4PR7J1M",
    }),
  ],
  bundler: viteBundler(),
  host: "localhost",
});
