#!/bin/not_a_shell_script

# Commandes a executer a la main, en regardant la sortie !
# Concu pour Linux Debian/Ubuntu (utilisations de apt),
# A adapter au gestionnaire de paquet de votre linux si besoin

# ---------------------------------------------------------------------------
# CHAPTER 1 : emacs

apt install emacs emacs-common-non-dfsg
# Remarque : emacs-common-non-dfsg est nouveau sur Ubuntu 20.04.1
# par rapport à 18.04.
# Vérifier que les pkg suivants ont bien été installés :
#     emacs-bin-common emacs-common emacs-el emacs-gtk emacsen-common
# Ou si besoin les installer avec :
# apt install emacs-bin-common emacs-common emacs-el emacs-gtk emacsen-common

# emacs initialization file
#cp ltpf_2020.emacs ~/.emacs
cat ltpf_2020.emacs >> ~/.emacs

# install pkgs emacs (a few seconds)
emacs --batch -l ~/.emacs --eval "(package-refresh-contents)"
emacs --batch -l ~/.emacs --eval "(package-install 'tuareg)"         # OCaml mode
emacs --batch -l ~/.emacs --eval "(package-install 'proof-general)"  # Coq mode

emacs --batch -l ~/.emacs --eval "(package-install 'company)"        # optional
emacs --batch -l ~/.emacs --eval "(package-install 'company-coq)"    # optional
emacs --batch -l ~/.emacs --eval "(package-install 'auto-complete)"  # optional
emacs --batch -l ~/.emacs --eval "(package-install 'merlin-eldoc)"   # optional
emacs --batch -l ~/.emacs --eval "(package-install 'magit)"          # git mode (optional)

# ---------------------------------------------------------------------------
# CHAPTER 2 : opam (package manager for OCaml), OCaml and tools

# Pour la suite
# Deux autres packages sont conseillés : curl et m4
apt install curl m4

# 2.1 : opam
# ----------

# Information from http://opam.ocaml.org/doc/Install.html
# On a RECENT Ubuntu (20.4) you get opam-2.05
apt install opam
# BUT with Ubuntu 18.04 you get opam-1.2 which is too old
# Run instead :
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
# And you will get even better, e.g. opam-2.07

# environment setup
opam init --yes
eval `opam env`


# 2.2 : OCaml
# -----------

# install given version of the compiler (3-4 minutes)
opam switch create 4.11.1
eval `opam env`


# 2.3 : tools for OCaml
# ---------------------

# tool for detecting required syst packages
opam install -y depext

# detect required syst packages for user-setup
opam depext user-setup
# should answer "All required OS packages found"
# Otherwise, proceed as suggested, e.g.
# $ sudo apt install m4

# install user-setup
opam install -y user-setup

# completes emacs initialization file
opam user-setup install


# install merlin
opam install -y merlin


# ---------------------------------------------------------------------------
# CHAPTER 3 : coq and coqide

# 3.1  : coq (required)
# ---------------------

# detect required syst packages for coq (just in case)
opam depext coq
# should answer "All required OS packages found"
# or maybe, install m4 first

# install coq (10 minutes)
opam install -y coq

# 3.2  : coqide (optional)
# ------------------------

opam depext coqide
# Be careful !! if answer different from "All required OS packages found"
# Otherwise apt install etc. (on Debian/Ubuntu)
# Or : sudo opam depext -y coqide

# install coqide (2 minutes)
opam install -y coqide
