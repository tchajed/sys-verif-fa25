---
icon: gears
order: 1
---

# Setup

## Assignment repo

The programming assignments will be distributed in [sys-verif-fa25-proofs](https://github.com/tchajed/sys-verif-fa25-proofs). You'll need it as a git repository so you can get updates with `git pull`, since this is how assignments and demos in lecture will be released. (If you have trouble getting updates, please let me know.)

::: danger Clone, don't fork

**Please do not fork the repo**, since this will make your submission public. GitHub does not support private forks of public repositories.

Instead, you can either clone and work locally, or follow the below instructions to work in a private repo that is not a GitHub fork (I do recommend doing that so you have a backup).

:::

::: details Creating a private GitHub repo for your work

Create a new private repo called sys-verif-fa25-proofs (without any content). (As a student, you can get unlimited private repos with the [student pack](https://education.github.com/pack/join).) Follow these instructions to set it up (fill in your username in the first step):

```bash
GH_USER=<username>
git clone https://github.com/tchajed/sys-verif-fa25-proofs
cd sys-verif-fa25-proofs
git remote rename origin upstream
git remote add origin git@github.com:$GH_USER/sys-verif-fa25-proofs.git
git push --set-upstream origin main
git submodule update --init --recursive
```

You now have a copy of the repo, with the `main` branch tracking your private repo, and with a second remote `upstream` pointing to the class repo.

**To get updates**: run `git fetch upstream` to get new commits from the `tchajed/sys-verif-fa25-proofs` repo, then `git merge upstream/main` to pull in new changes into your own repo.

If you accidentally forked the course repo, don't panic; you can just delete the fork and re-create it.

:::

## Installing Rocq

The setup I recommend is to use Docker, VS Code, and a container I created for this class.

::: details Option 1: VS Code + Docker dev container

This setup should work well on macOS and Linux; it should also be workable in Windows with WSL, but I don't have much experience with that.

Install [Docker](https://www.docker.com/get-started/)

Install [VS Code](https://code.visualstudio.com/)

Install the [Dev Containers extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers).

- You can install it directly in VS Code through [this link](vscode:extension/ms-vscode-remote.remote-containers).
- Alternate option 2: at the command line you can run `code --install-extension ms-vscode-remote.remote-containers`.

The most important VS Code feature to learn is the Command Palette, accessed from View > Command Palette. The shortcut is worth learning (ctrl-shift-p, cmd-shift-p on macOS). The command palette gives search access to most editor functionality and shows keyboard shortcuts if you want to learn them.

Once you have the dev container extension, use the "Dev Containers: Reopen in Container" command on the sys-verif-fa25-proofs repo. This will use Rocq from the container while still running VS Code natively. You should now use the built-in VS Code terminal to run `make` to ensure your code compiles.

The setup installs the VSCoq extension by default. You might want to try out [coq-lsp](https://marketplace.visualstudio.com/items?itemName=ejgallego.coq-lsp), which has a different and simpler interaction model. I'm not sure if it will be more or less stable than VSCoq, so if you use it please let me know your experience. **Use only one of VSCoq and coq-lsp**.

:::

If you feel comfortable setting up your own tools, you can instead install Rocq on your own.

::: details Option 2: install Rocq on your own

Install Rocq 9.0.0 for compatibility. You should install Rocq using opam.

You will need an IDE for Rocq:

- I recommend VS Code with the [VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq) extension.

  You might want to try out [coq-lsp](https://marketplace.visualstudio.com/items?itemName=ejgallego.coq-lsp), which has a different and simpler interaction model. I have limited experience with it, so I don't know how stable it will be; if you use it please let me know your experience. **Use only one of VSCoq and coq-lsp**.

- If you use Emacs, then [Proof General](https://proofgeneral.github.io/) is excellent (this is what I personally use, with Doom Emacs and vim keybindings).
- If you use Vim or Neovim, then [Coqtail](https://github.com/whonore/Coqtail) is also good.

Once you have Rocq installed, run `make` to make sure everything is working.

If you don't use VS Code, you'll need to follow the [Iris editor setup instructions](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md?ref_type=heads) to be able to input Unicode characters easily. For VS code that setup is already provided by the assignment repo.

:::

## Submitting assignments

We'll use the course [Canvas page](https://canvas.wisc.edu/courses/477243) for submitting assignments (and not much else).

You'll do all the programming in the sys-verif-fa25-proofs repo. To submit your code, run the script `./etc/prepare-submit` to generate `hw.tar.gz`. Then, go to the assignment's page on Canvas and submit that file. I'm having you submit all the code in the repo (not just for the relevant assignment) to simplify the setup for you.

For all assignments, you're **strongly encouraged** to submit early with partial progress, once a week. There aren't many assignments, but you should still be doing some work every week, and this will give me an idea of how far along you are in between due dates. If you want any specific feedback, please add a comment on Canvas so I take a look quickly and respond.
