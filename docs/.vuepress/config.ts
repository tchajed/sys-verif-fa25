import { hopeTheme, navbar, sidebar } from "vuepress-theme-hope";
import { defineUserConfig } from "vuepress";
import { viteBundler } from "@vuepress/bundler-vite";

// Vue Router picks up configuration for paths in the navbar and sidebar from
// the YAML frontmatter, for example the 'title' (or first h1), 'shortTitle',
// and 'icon'.
//
// README.md is used for the index page of a directory.

const navbarConfig = navbar(["/", "/assignments/"]);
const sidebarConfig = sidebar({
  "/": [
    "",
    "syllabus",
    {
      text: "Assignments",
      icon: "file-lines",
      prefix: "assignments/",
      link: "/assignments/",
      children: [
        "setup",
        "assignment1",
        "assignment2",
        "assignment3",
        "project",
      ],
    },
  ],
});

export default defineUserConfig({
  lang: "en-US",

  // The path to the hosted website from its domain. We deploy to GitHub pages
  // which automatically puts websites at <username>.github.io/<repo-name>,
  // unless using a custom domain.
  base: "/sys-verif-fa24/",

  title: "CS 839",
  description: "Systems Verification Fall 2024",

  theme: hopeTheme({
    navbar: navbarConfig,
    repo: "https://github.com/tchajed/sys-verif-fa24-proofs",
    sidebar: sidebarConfig,

    // control page meta information shown
    // see https://theme-hope.vuejs.press/guide/feature/meta.html
    contributors: false,
    editLink: false,
    pageInfo: ["Date"],
    toc: true, // disabled on home page
    print: false,

    plugins: {
      mdEnhance: {
        katex: true,
        tasklist: true,
        include: true,
      },
    },
    logo: "/logo.png",
    favicon: "/favicon.png",
    iconAssets: "fontawesome",
  }),

  bundler: viteBundler(),
  host: "localhost",
});
