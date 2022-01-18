# Brown CS 1951x: Formal Proof and Verification, 2021

In this repository, you'll find Lean files for [CS1951x](https://cs.brown.edu/courses/cs1951x), copied so that John Hughes can work on the assignments from this repository, commit from either home or office, etc. 

## Using this repository

This repository is a [Lean project](https://leanprover-community.github.io/install/project.html).
There are some basic steps you should take at the beginning to set it up.
These only need to be done once.
If and when you need to create any new `.lean` files,
create them in the `src` directory of this project,
to ensure that all your expected imports are available.

### Setup

We assume that you have installed:
* `git`
* `lean` (via `elan`)
* `leanproject`
* VSCode and the Lean extension

To set up:
```bash
leanproject get get git@github.com:spike7638/fpv2021.git\
cd fpv2021
lean --make src/lovelib.lean
```

When you open VSCode, make sure that you use the **Open Folder** feature
to open the entire `fpv2021` directory,
instead of opening individual files. 
The easiest way to do this is from the command line:
```bash
cd fpv2021
code .
```
But `File -> Open Folder...` works fine too.

### Debugging

The Lean files should be quick to load. 
If you see orange bars in VSCode for a long time (20 seconds is way too much),
something might be wrong.
This can be caused by accidentally making changes to library files,
or by having too many files open in VSCode that import each other.

First, in VSCode, close any editor tabs that you aren't using anymore.
Then open the Command Palette (`ctrl-shift-p` or `cmd-shift-p`)
and run `Lean: Restart`. 
You might find it useful to map this to a hotkey in VSCode. Rob uses `ctrl-r`.

If that doesn't work, let's make sure you have a fresh copy of the library.
In the root `fpv2021` directory, run:
```bash
leanpkg configure
leanproject get-mathlib
lean --make src/lovelib.lean
```
If this last line takes more than a few seconds, things might still be wrong.