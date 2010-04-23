
all:V: obj

obj:V:
	ghc -i$TOP --make *.hs

clean:V:
	rm -f *.o *.hi *~

test install build check:V:
	(cd $TOP && mk $target)
