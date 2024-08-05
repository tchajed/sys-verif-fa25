import { defaultTheme } from '@vuepress/theme-default'
import { defineUserConfig } from 'vuepress/cli'
import { viteBundler } from '@vuepress/bundler-vite'

export default defineUserConfig({
  lang: 'en-US',
  base: "/sys-verif-fa24/",

  title: 'CS 839',
  description: 'Systems Verification Fall 2024',

  theme: defaultTheme({
    logo: 'https://vuejs.press/images/hero.png',

    navbar: ['/', '/assignments'],

    sidebar: ['/README.md', '/assignments.md', '/syllabus.md'],
  }),

  bundler: viteBundler(),
})
