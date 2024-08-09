import { hopeTheme, navbar, sidebar } from "vuepress-theme-hope";
import { defineUserConfig } from "vuepress";
import { viteBundler } from "@vuepress/bundler-vite";
import { ShikiLang } from "@vuepress/plugin-shiki";
import * as fs from "fs";

// Vue Router picks up configuration for paths in the navbar and sidebar from
// the YAML frontmatter, for example the 'title' (or first h1), 'shortTitle',
// and 'icon'.
//
// README.md is used for the index page of a directory.

const navbarConfig = navbar(["/", "/assignments/", "/notes/"]);
const sidebarConfig = sidebar({
  "/": [
    "",
    "syllabus",
    {
      text: "Assignments",
      icon: "list-check",
      prefix: "assignments/",
      link: "/assignments/",
      children: "structure",
    },
    "notes/",
  ],
  "/notes/": "structure",
  "/assignments/": "structure",
});

// Load the Coq grammar manually since shiki doesn't have it. The grammar
// definition comes from VS Coq.

const coqGrammar: any = JSON.parse(
  // TODO: is there a way to make this path relative to the vuepress or docs
  // directories?
  fs.readFileSync("docs/assets/coq.tmLanguage.json", "utf-8")
);

const coqLang: ShikiLang = {
  ...coqGrammar,
  // need to override the capitalized name "Coq" in the grammar (even using Coq
  // as the language in a markdown block doesn't work)
  name: "coq",
};

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
    repo: "https://github.com/tchajed/sys-verif-fa24-proofs",
    headerDepth: 2,
    sidebar: sidebarConfig,

    plugins: {
      mdEnhance: {
        katex: true,
        tasklist: true,
        include: true,
      },
      shiki: {
        langs: [coqLang, "go", "bash"],
        themes: {
          light: "one-light",
          dark: "one-dark-pro",
        },
      },
    },

    // control page meta information shown
    // see https://theme-hope.vuejs.press/guide/feature/meta.html
    contributors: false,
    editLink: false, // web repo is private
    pageInfo: ["Date", "Category", "Tag"],
    toc: true, // disabled on home page
    print: false,

    author: "Tej Chajed",
    license: "CC0-1.0",
    logo: "/logo.png",
    favicon: "/favicon.png",
    iconAssets: "fontawesome",
  }),

  bundler: viteBundler(),
  host: "localhost",
});
