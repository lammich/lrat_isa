.PHONY: code check_thys

htmlbase = https://lammich.github.io/lrat_isa/Unsorted/lrat_isa

all: code test

dist: all README.md

README.md: README.in.md
	sed -re 's|\(THYS:([^)]*)\)|($(htmlbase)/\1)|g' README.in.md > README.md

code:
	make -C code

test: code
	@ echo "Testing checker "
	@ ./code/lrat_isa ex/ex1.cnf ex/ex1.lrat | grep -q "^s VERIFIED UNSAT"
	@ echo "OK"

check_thys:
	isabelle build -D .
