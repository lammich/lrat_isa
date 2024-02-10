default: lrat_isa lrat_isa_dbg

libs_dep=lib_isabelle_llvm.cpp lib_isabelle_llvm.c


# libs=/lib/x86_64-linux-gnu/libboost_iostreams.a /lib/x86_64-linux-gnu/libboost_filesystem.a /lib/x86_64-linux-gnu/libboost_system.a lib_isabelle_llvm.cpp
libs=-lboost_iostreams lib_isabelle_llvm.cpp
cflags=-std=c++20 -stdlib=libstdc++ -Wall -Wno-unused-function -ggdb -O3 -flto -I${HOME}/include -fuse-ld=lld -static

# cflags=-std=c++20 -stdlib=libstdc++ -Wall -Wno-unused-function -ggdb -O3 -flto -lboost_iostreams -I${HOME}/include lib_isabelle_llvm.cpp

# cflags=-std=c++11 -stdlib=libstdc++ -march=native -w -Wall -fexceptions -O3 -I${HOME}/include -I$(gcode) -s
# -mllvm -inline-threshold=100000 -flto

compile=clang++ $(cflags) $(libs)


lrat_isa_export.dbg.ll: lrat_isa_export.ll
	./ll_dbg_tag.sh lrat_isa_export.ll

lrat_isa_dbg: main.cpp lrat_isa_export.dbg.ll $(libs_dep) ll_dbg.cpp Makefile
	$(compile) main.cpp lrat_isa_export.dbg.ll ll_dbg.cpp -o lrat_isa_dbg

lrat_isa: main.cpp lrat_isa_export.ll $(libs_dep) Makefile
	$(compile) main.cpp lrat_isa_export.ll -o lrat_isa

clean:
	rm -f lrat_isa_export.dbg.ll lrat_isa_dbg lrat_isa
