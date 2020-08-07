all: parser evaluation

parser:
	$(MAKE) -C parser

evaluation:
	$(MAKE) -C evaluation

clean:
	$(MAKE) -C parser clean
	$(MAKE) -C evaluation clean

.PHONY: all parser evaluation clean
