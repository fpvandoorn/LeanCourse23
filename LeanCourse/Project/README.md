## Personal Info

Please fill out the following:
```
First & last name: Ludwig Monnerjahn
Uni-ID: s6lumonn
```

## Your own project

During the second half of the course you will work on a project in any area of mathematics of your choice. You can put your project files in this folder.

Since a project likely consists of more than 1 file, it will be useful to publish this as a repository on Github.


## Git Terminology

* `git` is a version control system. It will store changes you made, and will allow you to revert to previous versions of your files.
* All versions of your files are stored in the `git history`.
* A `commit` is a snapshot of the repository. You have to manually make a commit, and can only refer to the state of the repository at each commit.
* Before you commit you can `stage` the files that you want to include in your next commit.
* You have to `push` commits that you make locally on your computer to save them remotely (on `github.com`).
* You can `pull` to download remote commits and get them locally (added by someone else, or added by you on another computer).
* `fetch` is similar to `pull`, but it only downloads the new changes to your git history, but doesn't actually incorporate the changes
* VSCode uses the word `sync` to mean `pull` + `push`.
* A `fork` is your own remote copy of the repository on `github.com` (something like `github.com/<YourUsername>/LeanCourse23`). You cannot write to the main repository (`github.com/fpvandoorn/LeanCourse23`)
* If two people both make independent commits to a repository, you can `merge` the commits to create a new commit that has both changes.
* If both commits make a change to the same (or adjacent) lines of a file, then you will get a `merge conflict` which means you have to decide how to merge these two changes.
  - *If you get a merge conflict*: this means that you modified a file that I also modified. `git` should tell you which file(s) have a conflict. The easiest way to solve this is to duplicate (copy/paste) the file(s) with a merge conflict (to have a version with your local changes), and then in the VSCode Source Control tab right-click the file(s) and press `Discard changes`.

## Git Instructions

We will be using git via the interface on VSCode. You can also do it from the command line.

### Getting started

* Create an account on `github.com`
* On the command line, run the following two commands, with your name and email substituted in:
```
git config --global user.name "Your Name"
git config --global user.email "youremail@yourdomain.com"
```
* In VSCode, open this file and add your name and your Uni-ID at the top.
* Save all your open files
* Click on the `Source Control` button (left bar, likely the third button from the top).
* Write a small commit message (what you write is not important, but it should not be empty). Press `Commit`.
* Press `Yes` (or `Always`) on the prompt `There are no staged changes to commit. Would you like to stage all changes and commit them directly?`. This will also commit your changes to all other files, which is fine.
* Press `Sync changes`
* Press `OK` (or `OK, don't show again`) when prompted `This action will pull and push commits from and to "origin/master"`
* In the new window, press `Sign in with browser`
* if needed, sign in to Github
* Press `Authorize git-ecosystem`
* You get the message that you don't have permission to push. Press `Create Fork`.
* You should now see your changes at `github.com/<YourUsername>/LeanCourse23`.

### Pushing Later Commits

Pushing another commit after the first one is easy:

* Save all your open files
* Write a small commit message and press `Commit`.
* Press `Sync changes`

### Pulling commits

After you create your fork I believe that VSCode will not `sync` or `pull` new changes correctly by itself anymore.

To get new changes, do the following:
* Press the three dots icon at the top-right of the `source control` panel `... > Pull / Push > Fetch From All Remotes`
* Then do `... > Branch > Merge branch > upstream/master`
* (optionally) press `sync changes`.

Note: After you have created a fork, `git pull` will likely not work anymore from the command line. You can still pull changes from the command line using `git pull upstream master`.


### Command-line

If you would like to use Git from your command-line instead, you can use the commands `git pull`, `git add`, `git commit -am "commit message"`, `git push`, `git status`, `git log`, among others. Google for information how to exactly use these commands.

## Formalization Topics

You can choose a topic in any area of mathematics.

A good topic should be
* not yet in mathlib (although it's also fine to give a different proof of something already in mathlib);
* not too hard (don't overestimate how much you can do in your project);
* not require too many prerequisites that are not yet part of mathlib.

On the mathlib website there are some useful pages:
* [topics in mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [undergraduate topics in mathlib](https://leanprover-community.github.io/undergrad.html)
* [undergraduate topics not yet in mathlib](https://leanprover-community.github.io/undergrad_todo.html
)
* [the full contents of mathlib](https://leanprover-community.github.io/mathlib4_docs/) (use the search in the top right)


Some suggested topics:

<!-- Do not edit the lines below to avoid merge conflicts, since I will add more suggested topics. -->

* In **algebraic topology** define CW-complexes and cellular (co)homology.
  Prove some abstract properties of CW-complexes, or compute the cellular (co)homology of some concrete CW-complexes (e.g. spheres).

* In **algebraic topology** define Eilenberg-Maclane spaces and prove that they have the correct homotopy groups.

* In **analysis**: the Fourier transform and convolution have been defined in mathlib. Show that the Fourier transform of a convolution is the product of Fourier transforms.

* In **complex analysis** define the winding number of a closed curve. You can either use topological path lifting, or its analytic definition (Cauchy's integral formula exists in mathlib).

* In **complex analysis** define the Laurent series and show that it converges on an annulus.

* In **differential geometry** define a Riemannian metric and define basic notions of Riemannian geometry.

* In **differential geometry** define smooth `n`-forms and de Rham cohomology.

* In **Galois theory** define constructible numbers in ℂ and prove that they form the smallest subfield of ℂ closed under square roots. If time permits, prove some famous impossibility results (trisection of an angle / doubling of a cube). Example reference: [David Cox, Galois Theory, Ch 10.1].

* In **game theory**, define games, pure and mixed strategies, and Nash equilibria. Assuming Brouwer's fixed point theorem, prove that there always exists a Nash equilibrium of mixed strategies. (Brouwer's fixed point theorem is [proven in Lean](https://github.com/Shamrock-Frost/BrouwerFixedPoint/blob/master/src/brouwer_fixed_point.lean#L274), though not yet incorporated in mathlib.)

* In **general topology** define some spaces that are typically used for counterexamples, such as the Hawaiian earring, the long line, wild knots or the horned sphere.

* In **group theory**, classify all groups of order 8, or if you want a challenge, of order 16.

* In **hyperbolic geometry** define the Poincaré model of hyperbolic geometry - either the disc model or the half-plane model (or another model altogether), and show that is satisfies most of Euclid's axioms for geometry, but that the parallel postulate fails.

* In **model theory**: complete types of a language are defined in mathlib. Prove for a countable theory that if there are uncountably many types with `n` free variables, then there are continuum many. Or harder: show that in this case that `T` has continuum many non-isomorphic models.

* In **number theory** solve some diophantine equations. Show that there are no nonzero integer solutions to `x^4-y^4=z^2`. Find all solutions to `x^2+y^2=z^3` and to `|2^k-3^l|=1`.

* In **planar geometry** many results are missing. Choose one: the theorem of Ceva's theorem, Desargues's theorem, Feuerbach's theorem, Menelaus's theorem, Morley's trisecor theorem.

* In **set theory** define club sets, stationary sets and prove Fodor's lemma.
