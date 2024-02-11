.PHONY: code check_thys

htmlbase = https://lammich.github.io/lrat_isa/Unsorted/lrat_isa

all: README.md code

README.md: README.in.md
	sed -re 's|\(THYS:([^)]*)\)|($(htmlbase)/\1)|g' README.in.md > README.md

code:
	make -C code

check_thys:
	isabelle build -D .
