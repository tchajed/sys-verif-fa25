import { hopeTheme, navbar, sidebar } from "vuepress-theme-hope";
import { defineUserConfig } from "vuepress";
import { viteBundler } from "@vuepress/bundler-vite";
import { ShikiLang } from "@vuepress/plugin-shiki";
import { googleAnalyticsPlugin } from "@vuepress/plugin-google-analytics";
import * as fs from "fs";

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
      collapsible: true,
      // starts out expanded
      expanded: true,
    },
    {
      text: "Lecture notes",
      icon: "lightbulb",
      prefix: "notes/",
      link: "/notes/",
      children: "structure",
      collapsible: true,
      expanded: true,
    },
  ],
  "/notes/": "structure",
  "/assignments/": "structure",
});

function readShikiLang(path: string, name: string): ShikiLang {
  const grammar = JSON.parse(fs.readFileSync(`docs/assets/${path}`, "utf-8"));
  return {
    ...grammar,
    name: name,
  };
}

const dafnyLang: ShikiLang = readShikiLang("Dafny.tmLanguage.json", "dafny");
const smtLang: ShikiLang = readShikiLang("smt.tmLanguage.json", "smt2");

export default defineUserConfig({
  lang: "en-US",

  // The path to the hosted website from its domain. We deploy to GitHub pages
  // which automatically puts websites at <username>.github.io/<repo-name>,
  // unless using a custom domain.
  base: "/sys-verif-fa25/",

  title: "CS 839",
  description: "Systems Verification Fall 2025",

  // .snippet.md files are usable as '@include' files but don't produce output
  // pages.
  pagePatterns: ["**/*.md", "!**/*.snippet.md", "!.vuepress", "!node_modules"],

  theme: hopeTheme({
    navbar: navbarConfig,
    repo: "https://github.com/tchajed/sys-verif-fa25",
    toc: {
      levels: [2, 3],
    },
    sidebar: sidebarConfig,

    plugins: {
      git: process.env.NODE_ENV === "production",
      // see https://ecosystem.vuejs.press/plugins/markdown/shiki.html for the below config
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
      photoSwipe: false,
      icon: {
        assets: "fontawesome",
      },
    },

    markdown: {
      // NOTE: this doesn't work (non-existent pages go to a 404 page)
      linksCheck: {
        dev: true,
        build: "error",
      },
      tasklist: true,
      include: true,
      // allow {#custom-id} attributes
      attrs: {
        allowed: ["id"],
      },
      mermaid: true,
      math: {
        type: "katex",
        // copy as text (change to true to copy as LaTeX source)
        copy: false,
        // the rest of the config is passed to KaTeX, see
        // https://katex.org/docs/options.html
        macros: {
          "□": "\\square",
          "∗": "\\sep",
          "⊢": "\\entails",
        },
      },
      highlighter: {
        type: "shiki",
        langs: [dafnyLang, smtLang, "coq", "go", "bash", "asm"],
        langAlias: {
          rocq: "coq",
        },
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
        // TODO: doesn't work in rocq (but does work in ts and dafny, for example)
        notationErrorLevel: true,
        // add :line-numbers to ```lang line to enable selectively
        lineNumbers: false,
      },
    },

    // control page meta information shown
    // see https://theme-hope.vuejs.press/guide/feature/meta.html
    contributors: false,
    editLink: false, // feedback is better than edits/PRs
    // Could add "ReadingTime" (and reduce words/minute, default is 300) or
    // "Word" to give length estimate.
    pageInfo: ["Date", "Category", "Tag"],
    print: false, // no need to offer print button

    author: "Tej Chajed",
    license: "CC-BY-NC 4.0",
    logo: "/logo.png",
    favicon: "/favicon.png",
  }),

  plugins: [
    googleAnalyticsPlugin({
      id: "G-RMW4PR7J1M",
    }),
  ],
  bundler: viteBundler(),
  host: "localhost",
});
