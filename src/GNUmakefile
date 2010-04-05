SRC=Graph Label GraphUtil Fuel MkGraph Dataflow
HOOPL=Compiler/Hoopl
HS=${SRC:%=$(HOOPL)/%.hs}
O=${SRC:%=$(HOOPL)/%.o}


.PHONY: all clean

all: $O


%.o: %.hs
	ghc --make -c $*.hs


clean:
	rm -f $(HOOPL)/*.o
	rm -f $(HOOPL)/*.hi
	rm -f *~ $(HOOPL)/*~
