---
icon: 'file-lines'
---

# Assignments

## Assignment repo

You'll do the programming assignments using the starter code in <https://github.com/tchajed/sys-verif-fa24-proofs>. **Please do not fork the repo**, since this will make your submission public. GitHub does not support private forks of public repositories. Instead, you can either work locally, or follow the below instructions to work in a private repo that is not a GitHub fork (I do recommend doing that so you have a backup). If you accidentally fork the repo, don't panic, you should be able to delete and re-create it.

Create a new private repo called sys-verif-fa24-proofs (without any content). (As a student, you can get unlimited private repos with the [student pack](https://education.github.com/pack/join).) Follow these instructions to set it up (fill in your username in the first step):

```sh
GH_USER=<username>
git clone https://github.com/tchajed/sys-verif-fa24-proofs
cd sys-verif-fa24-proofs
git remote rename origin upstream
git remote add upstream git@github.com:$GH_USER/sys-verif-fa24-proofs.git
git push --set-upstream origin main
```

You now have a copy of the repo, with the `main` branch tracking your private repo, and with a remote `upstream` pointing to the class repo. You can now do something like `git fetch upstream` and `git merge upstream/main` to pull in new changes.

## Installing Coq

### Docker + VS Code

The setup I recommend is to use Docker, VS Code, and a container I created for this class. This setup should work well on macOS and Linux; it should also be workable in Windows with WSL, but I don't have much experience with that. To use this setup, you'll need to:

Install [Docker](https://www.docker.com/get-started/)

Install [VS Code](https://code.visualstudio.com/)

Install the [Dev Containers extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers).

- You can install it directly in VS Code through [this link](vscode:extension/ms-vscode-remote.remote-containers).
- Alternate option 2: you can also install the extension from the Extensions sidebar item.
- Alternate option 3: at the command line you can run `code --install-extension ms-vscode-remote.remote-containers`.

The most important VS Code feature to learn is the Command Palette, accessed from View > Command Palette. The shortcut is worth learning (ctrl-shift-p, cmd-shift-p on macOS). The command palette gives search access to most editor functionality and shows keyboard shortcuts if you want to learn them.

### Install Coq and an IDE on your own

You can also try to install Coq on your own. Make sure to get Coq 8.19.2 for compatibility (Coq 8.20 is also likely to work when it's released).

You will need an IDE for Coq:

- I'd recommend VS Code with the VSCoq extension.
- If you use Emacs, then [Proof General](https://proofgeneral.github.io/) is excellent (this is what I personally use, with Doom Emacs and vim keybindings).
- If you use Vim or Neovim, then [Coqtail](https://github.com/whonore/Coqtail) is also decent.

## List of assignments

- [Assignment 1 (Coq)](./hw1-coq)
- Assignment 2 (GooseLang verification)
- Assignment 3 (Separation logic theory)

  Note that this is a theory assignment for which you'll submit a written document.

- Final project
