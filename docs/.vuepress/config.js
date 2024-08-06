import { hopeTheme } from 'vuepress-theme-hope'
import { defineUserConfig } from 'vuepress/cli'
import { viteBundler } from '@vuepress/bundler-vite'
import { mdEnhancePlugin } from 'vuepress-plugin-md-enhance'

export default defineUserConfig({
  lang: 'en-US',
  base: "/sys-verif-fa24/",

  title: 'CS 839',
  description: 'Systems Verification Fall 2024',

  theme: hopeTheme({
    logo: '/logo.png',
    favicon: '/favicon.png',
    iconAssets: "fontawesome",
    navbar: ['/', '/assignments'],

    sidebar: [
      '/',
      '/syllabus',
      '/assignments',
    ],

    // control page meta information shown
    // see https://theme-hope.vuejs.press/guide/feature/meta.html
    contributors: false,
    editLink: false,
    pageInfo: ["Date"],
  }),

  plugins: [
    mdEnhancePlugin({
      katex: true,
    })
  ]

  bundler: viteBundler(),
})
