import { hopeTheme, navbar, sidebar } from "vuepress-theme-hope";
import { defineUserConfig } from "vuepress";
import { viteBundler } from "@vuepress/bundler-vite";
import { googleAnalyticsPlugin } from "@vuepress/plugin-google-analytics";

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
    "resources",
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
        // TODO: katex seems to not work
        // katex: {
        //   copy: true,
        // },
        mathjax: true,
        tasklist: true,
        include: true,
        // allow {#custom-id} attributes
        attrs: {
          allowed: ["id"],
        },
      },
      shiki: {
        langs: ["coq", "go", "bash"],
        themes: {
          light: "one-light",
          dark: "one-dark-pro",
        },
        highlightLines: true,
        notationDiff: true,
        // notationHighlight: true,
      },
    },

    // control page meta information shown
    // see https://theme-hope.vuejs.press/guide/feature/meta.html
    contributors: false,
    editLink: false, // feedback is better than edits/PRs
    pageInfo: ["Date", "Category", "Tag"],
    toc: true, // usually desired, but disabled on home page
    print: false, // no need to offer print button

    author: "Tej Chajed",
    license: "CC0-1.0",
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
