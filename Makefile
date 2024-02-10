.PHONY: code check_thys

code:
	make -C code

check_thys:
	../bin/isabelle build -D .
