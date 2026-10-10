OPAM_SWITCH ?= ocaml-5.4.1-rocq-9.2
RUN = opam exec --switch=$(OPAM_SWITCH) --

.PHONY: all check assets clean
all:
	$(RUN) dune build @all
check: all
	$(RUN) dune build @runtest
	$(RUN) rocq check -silent -Q _build/default/theories Fsubomega -Q _build/default/tests FsubomegaTests Fsubomega.Conservativity Fsubomega.TypingConservativity FsubomegaTests.Examples
assets:
	python3 assets/build.py
clean:
	$(RUN) dune clean
