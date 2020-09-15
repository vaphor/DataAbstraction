SRC=src/*
all:dataabs
build/src/main.native: $(SRC)
	ocamlbuild main.native -I src -build-dir build
dataabs: build/src/main.native
	cp $^ $@
clean:
	rm -rf build/
demo: demo.smt2 dataabs
	./dataabs demo.smt2
test: demo.smt2 dataabs
	@mkdir -p build
	./dataabs demo.smt2 > build/demoabs.smt2
	@if [ $$(which z3) = "" ]; then echo "Failed to find z3 solver"; fi
	@which z3  > /dev/null
	@echo "Using z3 solver : $$(which z3)"
	@echo "Result is : " $$(z3 build/demoabs.smt2)
	@echo "Expected is : sat"
	
.PHONY: demo test clean


