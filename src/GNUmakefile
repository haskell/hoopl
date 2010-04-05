SRC=Graph Label GraphUtil Fuel MkGraph Dataflow
HS=${SRC:%=Compiler/Hoopl/%.hs}
O=${SRC:%=Compiler/Hoopl/%.o}

.PHONY: all

all: $O


%.o: %.hs
	ghc --make -c $*.hs
