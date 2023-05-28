default:

install:
	python3 -m pip install -r bench-tool/requirements.txt; \
	python3 -m pip install -e bench-tool

uninstall:
	python3 -m pip uninstall benchtool

clean:
	rm -rf bench-tool/benchtool.egg-info
	rm -rf bench-tool/build
	rm -rf bench-tool/dist
	rm -rf temp
