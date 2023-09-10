# NNG4

This is the lean4 version of the classical *Natural Number Game*. It uses the [Lean4 Game Engine](https://github.com/leanprover-community/lean4game) and is running live at [adam.math.hhu.de](https://adam.math.hhu.de/#/game/nng).

The game was initially designed for lean3 and has been adapted for lean4. [See lean3 version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/).

## Getting Started

There are multiple ways to run the game locally:

### Local setup

### VSCode Devcontainer

The full instructions are at [Running games locally](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#running-games-locally).
In particular, the recommended setup is to have `docker` installed on your computer
and then click on the pop-up "Reopen in Container" which is shown when
opening this project in VSCode.

You can then open [localhost:3000](http://localhost:3000) in a browser.

After making changes to the code, you need to run `lake build` in a terminal and
reload the web page inside the "Simple Browser".

### Codespaces

If you open the repository in codespaces, it it should run the game locally in the background. You can open it for for example under "Ports" and clicking on
"Open in Browser".


Note: You have to wait until `npm` started properly.
In particular, this is after a message like
`[client] webpack 5.81.0 compiled successfully in 38119 ms` appears. This might take a good while.

As with devcontainers, you need to run `lake build` after changing any lean files and then reload the browser.

### Gitpod

Not verified to work yet.


## Contributing

If you want to contribute to the Natural Number Game, it is probably best if you ask us for access and push on a non-`main` branch in this repo. That way a github-action will build the game automatically.

See the [documentation](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md) for an explanation of the game commands.

## Codespaces and Gitpod

You can work on this repository using Gitpod : [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/hhu-adam/NNG4)

You can also work on it using Github codespaces (click "Code" and then "Codespaces" and then "create codespace on main").

### Creating a new game

In order to create a new game, click "use this template"  above to create your own game. That way there is a github action that can build a docker image from your `main` branch which can be used to add the game to the server at [adam.math.hhu.de](https://adam.math.hhu.de).

## Development

### Installation

The full instructions are at [Running games locally](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#running-games-locally).
In particular, the recommended setup is to have `docker` installed on your computer
and then click on the pop-up "Reopen in Container" which is shown when
opening this project in VSCode.

The game is then accessible at [localhost:3000/#/g/local/game](http://localhost:3000/#/g/local/game).
