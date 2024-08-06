import { hopeTheme } from 'vuepress-theme-hope'
import { defineUserConfig } from 'vuepress/cli'
import { viteBundler } from '@vuepress/bundler-vite'

export default defineUserConfig({
  lang: 'en-US',
  base: "/sys-verif-fa24/",

  title: 'CS 839',
  description: 'Systems Verification Fall 2024',

  theme: hopeTheme({
    navbar: [{
      text: 'Calendar',
      link: '/',
    }, '/assignments'],

    sidebar: [
      {
        link: '/',
        text: 'Home',
      },
      '/syllabus',
      '/assignments',
    ],

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
      }
    },
    logo: '/logo.png',
    favicon: '/favicon.png',
    iconAssets: "fontawesome",
  }),

  bundler: viteBundler(),
})
