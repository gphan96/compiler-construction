all:
	bnfc CPP.cf
	happy -gca ParCPP.y
	alex -g LexCPP.x
	stack build
	echo '#!/bin/bash\nstack exec compiler $$1' > compiler
	chmod a+x compiler

clean:
	-rm -f compiler
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocCPP.ps DocCPP.txt compiler
	stack clean

distclean: clean
	-rm -f DocCPP.* LexCPP.* ParCPP.* LayoutCPP.* SkelCPP.* PrintCPP.* TestCPP.* AbsCPP.* TestCPP ErrM.* SharedString.* CPP.dtd XMLCPP.*
	stack clean --full

