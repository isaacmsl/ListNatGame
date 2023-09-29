# ListNatGame
A little game of  Natural's List using Lean4.

## How to play

1. Create a fork
1. Clone the fork at your computer 
1. Create a copy of `ListNatGame.lean` in `players/`  and set your name on it, like: `Isaac.lean`;
1. Fix all errors to complete the game (obsviously, the functions must honor its names);
1. Complete all theorems.

## Lean4 commands

Some commands you might know:

1. **rw** (change goal)
```
rw [theorem/axiom]
```
1. **if** **then** **else**
```
if even 2 then 2 else 3
```

1. **induction** **with**
```
inductin xs with
| nil =>
  sorry
| cons x xs h =>
  sorry
```

1. **cases** **with**
```
cases h : even 1 with
| true =>
  sorry
| false =>
  sorry
```

More tactis [here](https://lean-lang.org/theorem_proving_in_lean4/tactics.html).

## Share results

Please make a pull requests to this repository to add your answers with:

1. Create a fork
1. Create a new branch with your name: `git checkout -b name`
1. Commit your modifications with: `git commit -am "feat: <name> anwers"`
1. Push the new commit to the Github
1. Make a pull request :)

Good game!

## Highscores

- 🥇 Débora Tayná
- 🥈 Gabrielle Borja
- 🥉 ???
