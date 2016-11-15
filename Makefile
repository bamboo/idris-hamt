hamt: src/**/*.idr
	idris --build hamt.ipkg

run: hamt
	./hamt
