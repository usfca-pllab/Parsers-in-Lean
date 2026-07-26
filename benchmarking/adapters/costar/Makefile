COSTAR_DIR := ../../../related-work/CoStar
ROCQFLAGS := -Q $(COSTAR_DIR)/parser CoStar

.PHONY: all clean check-parser

all: worker

check-parser:
	@test -f $(COSTAR_DIR)/parser/Main.vo || \
	  (echo "CoStar proof objects are missing; build related-work/CoStar/parser first" >&2; exit 1)

extracted/Indexed.ml: Indexed.v | check-parser
	mkdir -p extracted
	rocq c $(ROCQFLAGS) Indexed.v

worker: extracted/Indexed.ml worker.ml dune dune-project
	dune build --profile release worker.exe
	cp -f _build/default/worker.exe worker

clean:
	rm -f Indexed.glob Indexed.vo Indexed.vok Indexed.vos
	rm -rf extracted _build
	rm -f worker
