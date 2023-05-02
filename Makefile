default:

# 1. Install wheel, setuptools, and twine.
# 2. Build a wheel file from the benchtools directory.
# 3. Install the wheel using pip.
install:
	python3 -m pip install -r bench-tool/requirements.txt; \
	python3 -m pip install -e bench-tool

# TODO: Is this necessary?
install-permanent:
	cd bench-tool; \
	python3 -m pip install -r requirements.txt; \
	python3 setup.py bdist_wheel; \
	python3 -m pip install dist/*.whl; \
	cd -

uninstall:
	python3 -m pip uninstall benchtool

clean:
	rm -rf bench-tool/benchtool.egg-info
	rm -rf bench-tool/build
	rm -rf bench-tool/dist
	rm -rf temp