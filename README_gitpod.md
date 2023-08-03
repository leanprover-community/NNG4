### Remote running via GitPod

You don't need to install anything onto your computer using this method.

Just click here: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/kbuzzard/IISc-experiments)

Note to self: I got gitpod working by adding the files `.gitpod.yml` and `.docker/gitpod/Dockerfile`

### Remote running via Codespaces

You don't need to install anything onto your computer using this method.

Go to the project's [home page on GitHub](https://github.com/kbuzzard/IISc-experiments),
click "Code" and then "Codespaces" so it looks like this:

Pic: ![codespaces installation](png/codespaces.png?raw=true "codespaces installation")

Then click "create codespace on main", and then wait for a few minutes. When it looks like everything has downloaded, open up the `IIScExperiments` directory (not the file!) and the code I've been using in the lectures should just work.

Note to self: I got codespaces working by adding the files `.devcontainer/devcontainer.json` and `.devcontainer/Dockerfile`.
