# NNG4

This is the lean4 version of the classical *Natural Number Game*. It uses
the [Lean4 Game Engine](https://github.com/leanprover-community/lean4game) and is
running live at [adam.math.hhu.de](https://adam.math.hhu.de).

The game was initially designed for lean3 and has been adapted for lean4. [See lean3 version](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/).

## Getting Started

You can develop the game as any lean project and use `lake build` to build it.

Moreover, there are multiple ways to run the game while developing it, which are described in
[Running Games Locally](https://github.com/leanprover-community/lean4game/blob/main/doc/running_locally.md)

## Contributing

PRs/Issues fixing typos, inconsistencies, missing hints, etc. are very welcome!

### Translations
 We happily accept translations of the game into different lanugages! You can use `.i18n/Game.pot` and translate it into `.i18n/Game-{lang}.po` where `{lang}` is the ISO language code like `fr` or `en_UK`, using for example POEdit.

 We would like the following requirements for a translation PR:

 - One independent person from the community, who understands the language, gives a review on the PR. You could for example look at the [Lean Community Map](https://leanprover-community.github.io/meet.html) or ask on Zulip. Such a review an be quite generic and does not have to be super detailed.
 - In the credits (i.e. in the string translating them), ideally you should add yourself as a translator for this language.

## Documentation

See [Creating a Game](https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md) at
the [lean4game repo](https://github.com/leanprover-community/lean4game) for a detailed
explanation.
