default:

install:
	python3 -m pip install -r tool/requirements.txt; \
	python3 -m pip install -e tool

uninstall:
	python3 -m pip uninstall benchtool
	rm -rf tool/benchtool.egg-info
	rm -rf tool/build
	rm -rf tool/dist
	rm -rf temp

DATA = data
FIGURES = figures
FULL =

collect4.1:
	mkdir -p $(DATA)/4.1
	python3 experiments/haskell-experiments/4.1/Collect.py --data=$(DATA)/4.1 $(FULL)

save4.1:
	cd $(DATA)/4.1 && ls >> completed.txt

analyze4.1:
	mkdir -p $(FIGURES)/fig1
	python3 experiments/haskell-experiments/4.1/Analysis.py --data=$(DATA)/4.1 --figures=$(FIGURES)/fig1

collect4.2:
	mkdir -p $(DATA)/4.2
	python3 experiments/haskell-experiments/4.2/Collect.py --data=$(DATA)/4.2 $(FULL)

save4.2:
	cd $(DATA)/4.2 && ls >> completed.txt

analyze4.2:
	mkdir -p $(FIGURES)
	python3 experiments/haskell-experiments/4.2/Analysis.py --data=$(DATA)/4.2 --figures=$(FIGURES) 
