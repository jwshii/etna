default:

install:
	python3 -m pip install -r tool/requirements.txt; \
	python3 -m pip install -e tool

uninstall:
	python3 -m pip uninstall benchtool

clean:
	rm -rf tool/benchtool.egg-info
	rm -rf tool/build
	rm -rf tool/dist
	rm -rf temp
