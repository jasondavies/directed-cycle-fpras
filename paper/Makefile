.PHONY: all clean
PAPER := directed-cycle-fpras
all: $(PAPER).pdf

$(PAPER).pdf: $(PAPER).tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(PAPER).tex

clean:
	latexmk -c $(PAPER).tex
