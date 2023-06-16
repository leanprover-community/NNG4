# NNG4

This is the lean4 version of the classical *Natural Number Game*. It uses the [Lean4 Game Engine](https://github.com/leanprover-community/lean4game) and is running live at [adam.math.hhu.de](https://adam.math.hhu.de/#/game/nng).

The game was initially designed for lean3 and has been adapted for lean4. [See lean3 version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/).

## Contributing

If you want to contribute to the Natural Number Game, it is probably best if you ask us for access and push on a non-`main` branch in this repo. That way a github-action will build the game automatically.

See the [documentation](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md) for an explanation of the game commands.

### Creating a new game

In order to create a new game, click "use this template"  above to create your own game. That way there is a github action that can build a docker image from your `main` branch which can be used to add the game to the server at [adam.math.hhu.de](https://adam.math.hhu.de).

## Development

### Installation

Note that the setup is currently still in development and will likely see changes
and improvements in the next few months.

To run a local version of the game on your `localhost`, follow the
instructions "[Running games locally](https://github.com/leanprover-community/lean4game/blob/main/DOCUMENTATION.md#running-games-locally)".
