OCAMLBUILD = ocamlbuild

SOURCES   = defs.ml bigstep.ml smallstep.ml
BIGSTEP   = bigstep.byte
SMALLSTEP = smallstep.byte
#PACKS = oUnit

all: $(SOURCES)
	$(OCAMLBUILD) $(BIGSTEP)   -r
	$(OCAMLBUILD) $(SMALLSTEP) -r

clean:
	$(OCAMLBUILD) -clean
