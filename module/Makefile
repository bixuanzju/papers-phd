.PHONY : all
all:
	stack build module-impl

.PHONY : repl
repl:
	stack build module-impl && stack exec module-impl-exe

.PHONY : doc
doc:
	make -C doc

.PHONY : proof
proof:
	make -C proof

.PHONY : clean
clean :
	make -C doc clean

.PHONY : distclean
distclean : clean
	make -C doc distclean
	stack clean
