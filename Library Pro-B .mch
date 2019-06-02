MACHINE Library
SETS BOOKS
VARIABLES inlib , issued , nonissued , rest , nonrest
INVARIANT
 inlib <: BOOKS&
 rest <: inlib &
 nonrest <: inlib&
 nonissued <: nonrest&
 issued <: nonrest&
 rest /\ nonrest ={}&
 issued /\ nonissued ={}&
 inlib <:rest \/ nonrest&
 nonrest <:issued \/ nonissued 
 
INITIALISATION inlib , issued , nonissued , rest , nonrest:= {} , {} , {} , {} ,{}
OPERATIONS
  RestrictBook(s)=
	PRE s : nonrest & s: nonissued
	THEN rest := rest \/ {s};
	          nonrest := nonrest \{s};
	          nonissued := nonissued \{s}
	END;
   NotrestrictedBook(s)=
	PRE s : rest
	THEN nonrest := nonrest \/ {s};
	          rest := rest \ {s};
                            nonissued := nonissued \/ {s}
 	END;
  issueBook(s)=
	PRE s : nonissued
	THEN issued := issued \/ {s};
	          nonissued := nonissued \{s}
	END;
   returnBook(s)=
	PRE s : issued
	THEN nonissued := nonissued \/ {s};
	          issued := issued \ {s}
 	END;
   AddNewBook(s)=
	PRE s : (BOOKS\inlib)
	THEN inlib := inlib \/ {s};
	          nonrest := nonrest \/ {s};
	          nonissued:= nonissued \/ {s}
	END;
   removeBook(s)=
	PRE s : inlib & s : nonissued
	THEN inlib := inlib \ {s};
	          nonrest := nonrest \ {s};
	          nonissued := nonissued \ {s}
	END
END



