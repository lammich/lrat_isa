.PHONY: code check_thys

code:
	make -C code

check_thys:
	isabelle build -D .
