install:
	sage -pip install -e .
	rm -r build
	rm -r homogeneous.egg-info

test:
	sage -t bundle_collection

coverage:
	sage --coverage bundle_collection

docs: docs/Makefile
	cd docs && make html
	cd docs && make latexpdf

docs-clean:
	cd docs && make clean

lint:
	black bundle_collection
	isort --profile black bundle_collection
	flake8 --extend-ignore=E741 --max-line-length 88 bundle_collection
	ruff check --ignore=E741 bundle_collection

.PHONY: install test coverage docs-clean docs lint
