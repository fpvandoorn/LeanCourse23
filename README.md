# Bonn Lean Course WiSe 23/24


## Installation

To install Lean on a university computer, run `install_lean`. To install it on your own laptop, follow these [instructions](https://leanprover-community.github.io/get_started.html). In either case, you still have to get the course repository. Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

### Get the course repository

* Open a new terminal (I recommend `git bash` on Windows, which was installed as part of git in the first step).

* Go the the directory where you would like this package to live.

* Run `git clone git@github.com:fpvandoorn/LeanWiSe2324.git`.

* Run `cd LeanWiSe2324`

* Run `lake exe cache get`
  * On Windows, if you get an error that starts with `curl: (35) schannel: next InitializeSecurityContext failed` it is probably your antivirus program that doesn't like that we're downloading many files. The easiest solution is to temporarily disable your antivirus program.

* Launch VS Code, either through your application menu or by typing
  `code .`. (MacOS users need to take a one-off
  [extra step](https://code.visualstudio.com/docs/setup/mac#_launching-from-the-command-line)
   to be able to launch VS Code from the command line.)

* If you launched VS Code from a menu, on the main screen, or in the File menu,
  click "Open folder" (just "Open" on a Mac), and choose the folder
  `LeanWiSe2324` (*not* one of its subfolders).

* Test that everything is working by opening `LeanCourse/Test.lean`.
  It is normal if it takes 10-40 seconds for Lean to start up.

* More files will be added to this repository during the tutorial. The first exercises are in `LeanCourse/Session1_Basics/01Calculating.lean`.

### Get new exercises

If you have already followed the steps above, and want to get the latest exercises, open a terminal in your local copy of this repository (e.g. `cd LeanWiSe2324`) and then run `git pull`. This gives you the new exercises.

## More information

You can find the textbook that we will use online in
[html format](https://leanprover-community.github.io/mathematics_in_lean/)
or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf).
