# Magma to GAP converter
MGMCONVER:="version 0.51, Jul/4/19"; # version number
# (C) Alexander Hulpke

LINEWIDTH:=80;
COMMENTWIDTH:=LINEWIDTH-3;


TOKENS:=["if","then","eq","cmpeq","neq","and","or","else","not","assigned",
         "while","ne","repeat","until","error","do","assert",
	 "vprint","print","printf","vprintf",
	 "freeze","import","local","for","elif","intrinsic","to",
	 "end for","end function","end if","end intrinsic","end while",
	 "procedure","end procedure","where","break","func",
         "function","return",":=","+:=","-:=","*:=","/:=","cat:=","=",
	 "\\[","\\]","delete","exists",
	 "[","]","(",")","\\(","\\)","`",";","#","!","<",">","&","$","$$",":->","hom","map",
	 "cat","[*","*]","{@","@}","{*","*}",
         "case<","func<",
	 "continue",
	 "->","@@","forward","join",
	 "+","-","*","/","div","mod","in","notin","^","~","..",".",",","\"",
	 "{","}","|","::",":","@","cmpne","subset","by","try","end try",
	 "catch err","catch e",
	 "declare verbose","declare attributes","error if",
	 "exists","forall","time","rep",
	 "sub","ext","quo",
	 "eval","select","rec","recformat","require","case","when","end case",
	 "^^", "adj", "is", "non", "notadj", "notsubset", "sdiff", "xor",
	 "%%%" # fake keyword for comments
	 ];
# Magma binary operators
BINOPS:=["+","-","*","/","div","mod","in","notin","^","`","!","and","|",
         "or","=","eq","cmpeq","ne","le","ge","gt","lt",".","->","@@","@",
	 "cmpne","xor","^^","is", "non" ];
# Magma binaries that have to become function calls in GAP
FAKEBIN:=["meet","subset","join","diff","cat","adj","notadj",
          "notsubset", "sdiff","notin"];
BINOPS:=Union(BINOPS,FAKEBIN);

PAROP:=["+","-","div","mod","in","notin","^","`","!","and",
         "or","=","eq","cmpeq","ne","."];

# operator precedence from
# https://magma.maths.usyd.edu.au/magma/handbook/text/67
# note that some might have been take care of by parser earlier

OPRECED:=["|","`",".","@","@@","!","!!",
"^", "cat", "*", "/", "div", "mod", "+", "-", "meet", "sdiff",
"diff", "join", "adj", "in", "notadj", "notin", "notsubset", "subset",
"non", "cmpeq", "cmpne", "eq", "ge", "gt", "le", "lt", "ne", "not",
"and", "or", "xor", "^^", "non", "->", "=", ":=", "is"];


TOKENS:=Union(TOKENS,BINOPS);
TOKENS:=Union(TOKENS,PAROP);

# translation list for global function names
TRANSLATE:=[
"Append","Add",
"Alt","AlternatingGroup",
"CompanionMatrix","CompanionMat",
"Determinant","DeterminantMat",
"DiagonalJoin","DirectSumMat",
"DiagonalMatrix","DiagonalMat",
"Dimension","DimensionOfMatrixGroup",
"Divisors","DivisorsInt",
"Exclude","RemoveSet",
"Factorisation","CollectedFactors", # not a proper GAP command but close 
"GCD","Gcd",
"Id","One",
"Include","UniteSet",
"IsConsistent","SolutionMat",
"IsEven","IsEvenInt",
"IsOdd","IsOddInt",
"IsPrime","IsPrimeInt",
"Isqrt","RootInt",
"Matrix","MatrixByEntries",
"Modexp","PowerMod",
"Nrows","Length",
"Nullspace","NullspaceMat",
"NumberOfRows","Length",
"Quotrem","QuotientRemainder",
"Reverse","Reversed",
"Roots","RootsOfUPol",
"ScalarMatrix","ScalarMat",
"Solution","SolutionMat",
"Sp","SP",
"Sym","SymmetricGroup",
"Transpose","TransposedMat",
];

# reserved GAP variables that cannot be used as identifierso
GAP_KEYWORDS:=[
"break", "continue", "do", "elif", "else", "end", "fi", "for",
"function", "if", "in", "local", "mod", "not", "od", "or", "readonly",
"readwrite", "rec", "repeat", "return", "then",  "until", "while",
"quit", "QUIT", "IsBound", "Unbind", "TryNextMethod", "Info", "Assert",
];

# add those which are global functions
GAP_RESERVED:=Union(GAP_KEYWORDS,[ "E","X","Z"]);
GAP_SYSVARS:=Difference(NamesSystemGVars(),GAP_RESERVED);

# parses to the following units:

# co commentary
# B* binary operation *
# C function call
# <> substructure constructor
# L list indexing
# I identifier
# V vector
# & reduction operator
# U* unary operation *
# N number
# F function definition
# if conditional
# return
# : [op: a in l] operation
# R range [from..to]
#perm

UnFlat:=function(m)
local n;
  n:=RootInt(Length(m),2);
  if n^2<>Length(m) then
    return fail;
  fi;
  return List([1..n],x->m{[1+n*(x-1)..n*x]});
end;

UnpackNumberList:=function(l)
local m,i;
  m:=[];
  for i in l do
    if not IsRecord(i) then
      Add(m,i);
    elif i.type="N" then
      Add(m,i.name);
    elif i.type="U-" and i.arg.type="N" then
      Add(m,-i.arg.name);
    else
      return fail;
    fi;
      
  od;
  return m;
end;

FILEPRINTSTR:="";
START:="";

FilePrint:=function(arg)
  local f,i,p,a,new;
  f:=arg[1];
  for i in [2..Length(arg)] do
    if not IsString(arg[i]) then
      new:=String(arg[i]);
      if ValueOption("noblank")=true then
        new:=Filtered(new,x->x<>' ');
      fi;
    else
      new:=arg[i];
    fi;
    FILEPRINTSTR:=Concatenation(FILEPRINTSTR,new);
    p:=Position(FILEPRINTSTR,'\b');
    while p<>fail do
      FILEPRINTSTR:=Concatenation(FILEPRINTSTR{[1..p-2]},FILEPRINTSTR{[p+1..Length(FILEPRINTSTR)]});
      p:=Position(FILEPRINTSTR,'\b');
    od;
    p:=Position(FILEPRINTSTR,'\n');
    while p<>fail do
      if p>LINEWIDTH then
	# try to find better break point
	a:=p;
	p:=LINEWIDTH;
	while p>0 and not FILEPRINTSTR[p] in "]) " do
	  p:=p-1;
	od;
	if p=0 or ForAll([1..p],x->FILEPRINTSTR[x]=' ') then
	  p:=a;
	  p:=LINEWIDTH;
	  while p>0 and not FILEPRINTSTR[p] in "," do
	    p:=p-1;
	  od;
	  if p=0 then
	    p:=a;
	  fi;

	fi;
	AppendTo(f,FILEPRINTSTR{[1..p]},"\n");
	FILEPRINTSTR:=Concatenation(START," ",FILEPRINTSTR{[p+1..Length(FILEPRINTSTR)]});
      else
	AppendTo(f,FILEPRINTSTR{[1..p]});
	FILEPRINTSTR:=FILEPRINTSTR{[p+1..Length(FILEPRINTSTR)]};
      fi;
      p:=Position(FILEPRINTSTR,'\n');
    od;

  od;
end;

CHARSIDS:=Concatenation(CHARS_DIGITS,CHARS_UALPHA,CHARS_LALPHA,"_");
CHARSOPS:="+-*/,;:=~!";

MgmParse:=function(file)
local Comment,eatblank,gimme,ReadID,ReadOP,ReadExpression,ReadBlock,
      ExpectToken,doselect,costack,locals,globvars,globimp,defines,problemarea,
      f,l,lines,linum,w,a,idslist,tok,tnum,i,sel,osel,e,comment,forward,
      thisfctname,cmdstack,ProcessWhere,IsAtToken,ReadOptions,makeprintlistnice;

  locals:=[];
  globvars:=[];
  globimp:=[];
  defines:=[];
  forward:=[];

  # print current area (as being problematic)
  problemarea:=function(arg)
  local a,l,s;
    if Length(arg)=0 then a:=10;else a:=arg[1];fi;
    Print("\c\n\n");
    l:=0;
    for i in [Maximum(1,tnum-200)..tnum-a-1] do
      s:=tok[i][2];
      if not IsString(s) then
	s:=String(s);
      fi;
      l:=l+Length(s);
      if l>78 then
	Print("\n");
	l:=Length(s);
      fi;
      Print(s);
    od;
    Print("\n");
    Print(tok{[Maximum(1,tnum-a)..tnum-1]},"\n------\n",tok{[tnum..tnum+a]},"\n");
    l:=0;
    for i in [tnum+a+1..Minimum(Length(tok),tnum+50)] do
      s:=tok[i][2];
      if not IsString(s) then
	s:=String(s);
      fi;
      l:=l+Length(s);
      if l>78 then
	Print("\n");
	l:=Length(s);
      fi;
      Print(s);
    od;
    Print("\n");
  end;

  eatblank:=function()
    while Length(l)>0 and (l[1]=' ' or l[1]='\t') do
      l:=l{[2..Length(l)]};
    od;
    while Length(l)>0 and l[Length(l)]=' ' do
      l:=l{[1..Length(l)-1]};
    od;
  end;

  # read file

  f:=InputTextFile(file);
  lines:=[];
  while not IsEndOfStream(f) do
    l:=ReadLine(f);
    if l<>fail then
      l:=Chomp(l);
      eatblank();
      Add(lines,l);
    fi;
  od;
  CloseStream(f);

  comment:=[];

  gimme:=function()
  local a,b,p;
    while Length(l)<80 and linum<Length(lines) do
      linum:=linum+1;
      a:=lines[linum];
      # comment?
      if Length(a)>1 and PositionSublist(a,"//")<>fail then
        p:=PositionSublist(a,"//");
	l:=Concatenation(l," ",a{[1..p-1]});
	eatblank();
	a:=a{[p+2..Length(a)]};
        # 1-line comment
	Add(comment,a);
	a:="%%%";
      elif Length(a)>1 and PositionSublist(a,"/*")<>fail then
        p:=PositionSublist(a,"/*");
	l:=Concatenation(l," ",a{[1..p-1]});
	eatblank();
	a:=a{[p+2..Length(a)]};
        # possibly multi-line comment
	p:=PositionSublist(a,"*/");
	while p=fail do
	  linum:=linum+1;
	  b:=lines[linum];
	  a:=Concatenation(a,"\n",b);
	  p:=PositionSublist(a,"*/");
	od;
	Append(l,a{[p+2..Length(a)]});
	a:=a{[1..p-1]};
	Add(comment,a);
	a:="%%%";
      fi;
      l:=Concatenation(l," ",a);
      #if PositionSublist(l,"two_power")<>fail then Error("ZUGU");fi;
    od;
    eatblank();
  end;

  IsAtToken:=function(str)
    if tok[tnum][2]="where" then
      ProcessWhere([str,",",";",":",">"]); # maybe other separators
    fi;
    return tok[tnum][2]=str;
  end;

  ExpectToken:=function(arg)
  local s,o,i,a;
    s:=arg[1];
    if Length(arg)>1 then 
      o:=arg[2];
    else
      o:="";
    fi;
    # deal with infix comments before token
    i:=tnum;
    while tok[i][1]="#" do
      i:=i+1;
    od;
    if s<>"#" and i>tnum then
      a:=tok[i];
      while i>tnum do
	tok[i]:=tok[i-1];
        i:=i-1;
      od;
      tok[tnum]:=a;
    fi;

    # is there still a `where'?
    if s<>"where" and tok[tnum][2]="where" then
      ProcessWhere([s]);
    fi;

    if tok[tnum][2]<>s then
      i:=tnum;
      while tok[i][1]="#" do
	i:=i+1;
      od;
      problemarea();
      if i>tnum then
	Error("infix comment?");
      fi;
      Error("expected token ",s," not ",tok[tnum]," ",o);
    fi;
    tnum:=tnum+1;

#Print("I'm at:"); problemarea(); Print("\n");

  end;

  # tokenize, deal with comments and strings

  tok:=[];
  linum:=0;
  l:="";
  gimme();

  while linum<=Length(lines) and Length(l)>0 do
    gimme(); 
    if l[1] in CHARSIDS then
      i:=1;
      # a word-like identifier
      while l[i] in CHARSIDS do
        i:=i+1;
      od;
      a:=l{[1..i-1]};
      l:=l{[i..Length(l)]};eatblank();
      i:=Position(TOKENS,a);

      if a="end" or a="declare" or a="catch" or (a="error" and l{[1..2]}="if") then
        # special case of `end' token -- blank in name
	i:=1;
	while l[i] in CHARSIDS and i<Length(l) do
	  i:=i+1;
	od;
	if i=Length(l) and l[i] in CHARSIDS then
	  Add(l,' ');
	  i:=i+1;
	fi;
	a:=Concatenation(a," ",l{[1..i-1]});
	l:=l{[i..Length(l)]};eatblank();
	i:=Position(TOKENS,a);
        Add(tok,["K",TOKENS[i]]);
      elif i=fail then
	if ForAll(a,x->x in CHARS_DIGITS) then
	  Add(tok,["N",Int(a)]);
	else
	  Add(tok,["I",a]);
	fi;
      # now in K territory
      elif TOKENS[i]="cat" and l{[1,2]}=":=" then
	# fix cat:=
	a:=Concatenation(a,l{[1,2]});
	l:=l{[3..Length(l)]};
	eatblank();
	i:=Position(TOKENS,a);
        Add(tok,["O",TOKENS[i]]);
      elif (TOKENS[i]="case" or TOKENS[i]="func") and l[1]='<' then
        l:=l{[2..Length(l)]};
        eatblank();
        a:=Concatenation(TOKENS[i],"<");
        i:=Position(TOKENS,a);
        Add(tok,["K",TOKENS[i]]);

      elif a="is" then
        Add(tok,["O",":="]);
      else
	if TOKENS[i]="rec" then
	  if l[1]='<' then
	    Add(tok,["K",TOKENS[i]]);
	  else
	    # replace variable name `rec'
	    Add(tok,["I","reco"]);
	  fi;
	else
	  Add(tok,["K",TOKENS[i]]);
	fi;
      fi;
    else
      sel:=[1..Length(TOKENS)];
      i:=0;
      repeat
	i:=i+1;
	osel:=sel;
	sel:=Filtered(sel,x->Length(TOKENS[x])>=i and TOKENS[x][i]=l[i]);
      until Length(sel)=0;
      osel:=Filtered(osel,x->Length(TOKENS[x])=i-1);
      if Length(osel)>1 then 
	Error("nonunique");
      elif Length(osel)=0 then
        # no token fits -- use as identifier
	i:=Maximum(2,i);
	Add(tok,["I",l{[1..i-1]}]);
      else
	if l{[1..i-1]}<>TOKENS[osel[1]] then Error("token error");fi;
	a:=TOKENS[osel[1]];
	if a="%%%" then # this is where the comment should go
	  Add(tok,["#",comment[1]]);
	  comment:=comment{[2..Length(comment)]};
	elif a="\"" then
	  # string token
	  l:=l{[i..Length(l)]};
	  gimme();
	  i:=1;
	  while l[i]<>'"' or (i>1 and l[i-1]='\\') do
	    i:=i+1;
	  od;
	  Add(tok,["S",l{[1..i-1]}]);
	  i:=i+1;
	else
	  Add(tok,["O",a]);
	fi;
      fi;

      l:=l{[i..Length(l)]};eatblank();
    fi;

  od;

  ReadID:=function()
  local i,a;
    gimme();
    i:=1;
    while l[i] in CHARSIDS do
      i:=i+1;
    od;
    a:=l{[1..i-1]};
    l:=l{[i..Length(l)]};
    Print("ID:",a,"\n");
    return a;
  end;

  ReadOP:=function()
  local i,a;
    gimme();
    i:=1;
    while l[i] in CHARSOPS do
      i:=i+1;
    od;
    a:=l{[1..i-1]};
    l:=l{[i..Length(l)]};
    Print("OP:",a,"\n");
    return a;
  end;

  ProcessWhere:=function(stops)
  local a,b;
  #Print("stops=",stops,"\n");

    ExpectToken("where");
    a:=ReadExpression(["is",":=",","]);
    if IsAtToken(",") then
      a:=[a];
      while IsAtToken(",") do
	tnum:=tnum+1;
	b:=ReadExpression(["is",":=",","]);
	Add(a,b);
      od;
    fi;
    tnum:=tnum+1; # skip is/:=
    b:=ReadExpression(stops);
    b:=rec(type:="A",left:=a,right:=b);
    if IsList(a) then b.type:="Amult";fi;
    Add(cmdstack,b);
  end;

  ReadOptions:=function(stops)
  local opts,a,b;
    ExpectToken(":");
    opts:=[];
    repeat
      a:=ReadExpression(Concatenation([":=",","],stops));
      if IsAtToken(":=") then
	ExpectToken(":=");
	b:=ReadExpression(Concatenation([","],stops));
	a:=rec(type:="A",left:=a,right:=b);
      fi;
      Add(opts,a);
      if IsAtToken(",") then
        ExpectToken(",");
      fi;
    until tok[tnum][2] in stops;
    return opts;
  end;

  # read identifier, call, function 
  ReadExpression:=function(stops)
  local obj,e,a,b,c,d,argus,procidf,doprocidf,op,assg,val,pre,lbinops,
        fcomment,stack,locopt;

    lbinops:=Difference(BINOPS,stops);

    procidf:=function()
    local a,b;
      a:=doprocidf();
      while not "[" in stops and IsAtToken("[") do
	ExpectToken("[");
	# postfacto indexing
	b:=ReadExpression(["]",","]);
	if IsAtToken(",") then
	  # array indexing -- translate to iterated index by opening
          # a parenthesis and keeping position
	  tok[tnum]:=["O","["];
	else
	  ExpectToken("]");
	fi;
	a:=rec(type:="L",var:=a,at:=b);
      od;
      return a;
    end;

    doprocidf:=function()
    local a,l,e,b,c,d,eset,open,close,ltype;

      eset:=function()
	while tok[tnum][1]="#" do
	  Add(costack,tok[tnum]);
	  tnum:=tnum+1;
	od;
	return tok[tnum][2];
      end;

      e:=eset();
      a:=fail;

      if e in stops then
	a:=rec(type:="none");
      elif e="(" or e="\\(" then
	tnum:=tnum+1;
        a:=ReadExpression([")",","]);
	if IsAtToken(",")  then 
	  # pair, permutation
	  ExpectToken(",");
	  b:=ReadExpression([")",","]);
	  if IsAtToken(")") and tok[tnum+1][2]<>"(" then
	    # pair
	    ExpectToken(")");
	    #a:=rec(type:="pair",left:=a,right:=b);
	    a:=rec(type:="commutator",left:=a,right:=b);
	    return a;
	  else
	    # permutation
	    b:=[a.name,b.name];
	    a:=();
	    repeat
	      while IsAtToken(",") do
		ExpectToken(",",1);
		e:=ReadExpression([")",","]);
		Add(b,e.name);
	      od;
	      ExpectToken(")",1);
	      b:=MappingPermListList(b,Concatenation(b{[2..Length(b)]},b{[1]}));
	      a:=a*b;
	      if IsAtToken("(") then
		ExpectToken("(");
		# continue
		b:=ReadExpression([")",","]);
		b:=[b.name];
	      else
		b:=fail;
	      fi;
	    until b=fail;
	    a:=rec(type:="perm",perm:=a);
	    return a;
	  fi;
	fi;
	ExpectToken(")");
        return rec(type:="paren",arg:=a);
      elif e in ["[","{","[*","{@","<","{*"] then
	# list tokens
	open:=e;
	if e="[" then
	  close:="]";
	  ltype:="V";
	elif e="{" then
	  close:="}";
	  ltype:="{";
	elif e="[*" then
	  close:="*]";
	  ltype:="[*";
	elif e="{*" then
	  close:="*}";
	  ltype:="{*";
	elif e="{@" then
	  close:="@}";
	  ltype:="{@";
	elif e="<" then
	  close:=">";
	  ltype:="<";
	else
	  Error("other list type?");
	fi;
	ExpectToken(open);
	l:=[];
	b:=fail;
	if IsAtToken(close) then
	  #empty list
	  tnum:=tnum;
	else
	  repeat 
	    #tnum:=tnum+1;
	    a:=ReadExpression([close,",",":","..","|"]);
	    if IsAtToken("|") then
	      ExpectToken("|");
	      b:=a;
	      a:=fail;
	    elif IsAtToken(":") then
	      ExpectToken(":");
	      l:=a; # part 1
	      if tok[tnum][1]<>"I" then
		problemarea();
		Error("weird colon expression");
	      fi;
	      a:=tok[tnum][2]; # part 2
	      tnum:=tnum+1;
	      if IsAtToken("in") then
		ExpectToken("in");
		e:=ReadExpression([close,"|",","]); #part 2
	      elif IsAtToken(",") then
	        a:=[a];
		while IsAtToken(",") do
		  ExpectToken(",");
		  Add(a,tok[tnum][2]);
		  tnum:=tnum+1;
		od;
		ExpectToken("in");
		e:=ReadExpression([close,"|",","]); #part 2
		e:=ListWithIdenticalEntries(Length(a),e);
	      else
	        Error("misformed");
	      fi;

	      if IsAtToken("|") then
		ExpectToken("|");
		a:=rec(type:=":F",op:=l,var:=a,from:=e);
		a.cond:=ReadExpression([close]);
		ExpectToken(close);
	      elif IsAtToken(",") then
		if not (IsList(a) and IsList(a[1])) then
		  # make list of variables if not yet
		  a:=[a];
		  e:=[e];
		fi;
		while IsAtToken(",") do
		  ExpectToken(",");
		  Add(a,tok[tnum][2]); # next variable
		  tnum:=tnum+1;
		  ExpectToken("in");
		  Add(e,ReadExpression([close,",","|"])); 
		od;
		a:=Reversed(a);e:=Reversed(e); # dependency order
		if IsAtToken("|") then
		  ExpectToken("|");
		  c:=[ReadExpression([close,","])];
		  while IsAtToken(",") do
		    ExpectToken(",");
		    Add(c,ReadExpression([close,","])); # next variable
		  od;
		  ExpectToken(close);
		  a:=rec(type:=":mult",op:=l,var:=a,from:=e,open:=open,
	                 cond:=c);
		else
		  ExpectToken(close);
		  a:=rec(type:=":mult",op:=l,var:=a,from:=e,open:=open);
		fi;
	      else
		ExpectToken(close);
		a:=rec(type:=":",op:=l,var:=a,from:=e,open:=open);
		if IsList(e) then
		  a.type:=":mult";
		fi;
	      fi;
	      return a;
	    elif IsAtToken("..") then
	      ExpectToken("..");
	      e:=ReadExpression([close,"by"]); #part 2
	      if IsAtToken("by") then
		ExpectToken("by");
		a:=rec(type:="R",from:=a,to:=e,step:=ReadExpression([close]));
	      else
		a:=rec(type:="R",from:=a,to:=e);
	      fi;
	      ExpectToken(close);
	      return a;
	    elif IsAtToken(",") then
	      ExpectToken(",");
	    fi;
	    if a<>fail then
	      Add(l,a);
	    fi;
	  until IsAtToken(close);

	fi;
	ExpectToken(close);
        a:=rec(type:=ltype,args:=l);
	if b<>fail then
	  a.force:=b;
	fi;
      elif e="<" then
	l:=[];
	repeat 
	  tnum:=tnum+1;
	  a:=ReadExpression([">",","]);
	  Add(l,a);
	until IsAtToken(">");
	ExpectToken(">",6);
	a:=rec(type:="<",args:=l);
      elif e="\\[" then
	l:=[];
	repeat 
	  tnum:=tnum+1;
	  a:=ReadExpression(["\\]","]",","]);
	  Add(l,a);
	until IsAtToken("\\]") or IsAtToken("]");
	tnum:=tnum+1; # as ExpectToken("\\]","]");
	if not ForAll(l,x->IsBound(x.name)) then
	  a:=rec(type:="notperm",notperm:=l);
	else
	  l:=List(l,x->x.name);
	  a:=PermList(l);
	  if Length(l)<>Maximum(l) or a=fail then
	    a:=rec(type:="notperm",notperm:=l);
	  else
	    a:=rec(type:="perm",perm:=a);
	  fi;
	fi;

#      elif e="[*" then
#	l:=[];
#	if tok[tnum+1][2]="*]" then
#	  #empty list
#	  tnum:=tnum+1;
#	else
#	  repeat 
#	    tnum:=tnum+1;
#	    a:=ReadExpression(["*]",","]);
#	    Add(l,a);
#	  until IsAtToken("*]");
#	fi;
#	ExpectToken("*]");
#	a:=rec(type:="[*",args:=l);
#
#      elif e="{@" then
#	l:=[];
#	if tok[tnum+1][2]="@}" then
#	  #empty list
#	  tnum:=tnum+1;
#	else
#	  repeat 
#	    tnum:=tnum+1;
#	    a:=ReadExpression(["@}",","]);
#	    Add(l,a);
#	  until IsAtToken("@}");
#	fi;
#	ExpectToken("@}");
#	a:=rec(type:="{@",args:=l);
#
#      elif e="{" then
#	ExpectToken("{");
#	l:=[];
#	b:=false;
#	if IsAtToken("}") then
#	  #empty list
#	  tnum:=tnum;
#	else
#	  repeat 
#	    a:=ReadExpression(["}",",",".."]);
#	    if IsAtToken("..") then
#	      ExpectToken("..");
#	      b:=true;
#	      Add(l,a);
#	      a:=ReadExpression(["}"]);
#	    elif IsAtToken(",") then
#	      ExpectToken(",");
#	    fi;
#	    Add(l,a);
#	  until IsAtToken("}");
#	fi;
#	ExpectToken("}");
#	if b=true then
#	  a:=rec(type:="R",from:=l[1],to:=l[2]);
#	else
#  a:=rec(type:="{",args:=l);
#fi;

      elif e="sub" or e="ext" then
	# substructure/extension
	ExpectToken(e);
	ExpectToken("<");
	assg:=ReadExpression(["|"]);
	ExpectToken("|");
	l:=[];
	d:=fail;
	repeat
	  if IsAtToken(",") then
	    ExpectToken(",");
	  fi;
	  a:=ReadExpression([">",",",":"]);
	  Add(l,a);
	  if IsAtToken(":") then
	    d:=ReadOptions([">"]);
	  fi;
	until IsAtToken(">");
	ExpectToken(">",2);
	a:=rec(type:=e,within:=assg,span:=l);
	if d<>fail then
	  a.options:=d;
	fi;
      elif e="quo" then
        # quotient
	ExpectToken("quo");
	ExpectToken("<");
	a:=ReadExpression([":","|"]);
	if IsAtToken(":") then
	  ExpectToken(":");
	  b:=ReadExpression(["|"]);
	  a:=rec(type:="quo",format:=a,nominator:=b);
	else
	  a:=rec(type:="quo",nominator:=a);
	fi;
	ExpectToken("|");
	b:=ReadExpression([",",">",":"]);
        if IsAtToken(",") then
          # list of relators/equations
          d:=[b];
          repeat 
            ExpectToken(",");
            b:=ReadExpression([",",">"]);
            Add(d,b);
          until IsAtToken(">");
          ExpectToken(">");
          a.type:="quofp";
          a.denominator:=d;
        else
          a.denominator:=b;

          if IsAtToken(":") then
            d:=ReadOptions([">"]);
            a.options:=d;
          fi;
          ExpectToken(">",-2);
        fi;

      elif e="recformat" then
	ExpectToken("recformat");
	ExpectToken("<");
	while tok[tnum][2]<>">" do
	  tnum:=tnum+1;
	od;
	ExpectToken(">",3);
	a:=rec(type:="S",name:="unneeded record format");
      elif e="rec" then
	ExpectToken("rec");
	ExpectToken("<");
	e:=ReadExpression(["|"]);
	ExpectToken("|");
	assg:=[];
	if tok[tnum][2]<>">" then
	  repeat
	    if IsAtToken(",") then tnum:=tnum+1;fi;
	    b:=ReadExpression([":="]);
	    Add(assg,b);
	    ExpectToken(":=");
	    b:=ReadExpression([",",">"]);
	    Add(assg,b);
	  until IsAtToken(">");
	fi;
	ExpectToken(">",4);
	a:=rec(type:="rec",format:=e,assg:=assg);

      elif e="forall" or e="exists" then
	ExpectToken(e);
        if IsAtToken("(") then
	  ExpectToken("(");
	  d:=ReadExpression([")"]);
	  ExpectToken(")");
	else
	  d:=false; 
	fi;
	b:=ReadExpression(Concatenation(stops,BINOPS));
	a:=rec(type:=e,var:=rec(type:="I",name:=b.var),from:=b.from,cond:=b.cond,varset:=d,op:=b.op);
        #if IsList(b.from) then
	#  Append(a.type,"mult");
	#fi;

#	#Error("expect");
	#ExpectToken("{");
	#a:=ReadExpression([":",","]);
	#ExpectToken(":");
	#a:=ReadExpression(["in"]);
	#ExpectToken("in");
	#b:=ReadExpression(["|"]);
	#ExpectToken("|");
	#c:=ReadExpression(["}"]);
	#ExpectToken("}");
        #a:=rec(type:=e,var:=a,from:=b,cond:=c,varset:=d);
      elif e="rep" then
        ExpectToken("rep");
	a:=procidf();
	if a.type=":F" then
	  a.type:=":1"; # First
	else
	  # make it rep or repmult
	  a.type:=Concatenation("rep",a.type{[2..Length(a.type)]});
	fi;
      elif e="hom" or e="map" then
        tnum:=tnum+1; #ExpectToken("hom");
        ExpectToken("<","hom");
	a:=ReadExpression(["->"]);
	ExpectToken("->");
	b:=ReadExpression(["|"]);
	ExpectToken("|");
	a:=rec(type:=e,domain:=a,codomain:=b);
	c:=ReadExpression([":->",">",",",":"]);
	if IsAtToken(":") then
	  # option
	  assg:=ReadOptions([":->",">",","]);
	  a.options:=assg;
	fi;

	if IsAtToken(">") then
	  # image defn
	  a.kind:="images";
	  a.images:=c;
	elif IsAtToken(":->") then
	  # fct defn.
	  ExpectToken(":->");
	  d:=ReadExpression([">"]);
	  a.kind:="fct";
	  a.var:=c;
	  a.expr:=d;
	elif IsAtToken(",") then
	  # generator images
	  a.kind:="genimg";
          c:=[c];
          while IsAtToken(",") do
            ExpectToken(",");
            d:=ReadExpression([",",">"]);
            Add(c,d);
          od;
	  a.images:=c;
	else
	  problemarea();
	  Error(tok[tnum][2], " not yet done");
	fi;
	ExpectToken(">","endhom");


      elif e="case<" then
        ExpectToken("case<");
        a:=ReadExpression(["|"]);
        ExpectToken("|");
        d:=[];
        repeat
          b:=ReadExpression([":"]);
          ExpectToken(":");
          c:=ReadExpression([",",">"]);
          Add(d,[b,c]);
          if IsAtToken(",") then
            ExpectToken(",");
          fi;
        until IsAtToken(">");
        ExpectToken(">");
        a:=rec(type:="inlinecase",var:=a,conditions:=d);
      elif not (tok[tnum][1] in ["I","N","S"] or e="$" or e="$$") then
	tnum:=tnum+1;
	if e in ["-","#"] then
	  a:=rec(type:=Concatenation("U",e),arg:=procidf());
	elif e="+" then
	  # (spurious) +
	  a:=procidf();
	elif e="&" then

	  while tok[tnum][1]="#" do
	    Add(costack,tok[tnum]);
	    tnum:=tnum+1;
	  od;
	  e:=eset();

	  tnum:=tnum+1;
	  a:=ReadExpression(Union([",",";"],stops));
	  a:=rec(type:="&",op:=e,arg:=a);
	elif e="~" or e="not" or e="assigned" or e="eval" then
          a:=ReadExpression(Concatenation(stops,["and","or"]));
	  a:=rec(type:=Concatenation("U",e),arg:=a);
	elif e="select" then
	  Error("atselect");
	else
	  problemarea();
	  Error("other unary ",e);
	fi;

      else
	if e="$$" then
	  tok[tnum]:=["I",thisfctname];
	  e:=thisfctname;
	fi; # calling the current function

	# identifier/number
	if e="$" then
	  a:=rec(type:="I",name:="$");
	else
	  a:=rec(type:=tok[tnum][1],name:=tok[tnum][2]);
	fi;
	tnum:=tnum+1;

	e:=eset();

	while not (e in stops or e in lbinops) do
	  if e="select" then
	    a:=doselect(a,stops);
	  elif e="(" then
	    # fct call
	    assg:=[];
	    tnum:=tnum+1;
	    argus:=[];
	    while tok[tnum][2]<>")"  and tok[tnum][2]<>":" do
	      b:=ReadExpression([",",")",":"]);
	      if IsAtToken("select") then
		b:=doselect(b,[",",")",":"]);
	      fi;
	      Add(argus,b);
	      if IsAtToken(",") then
		ExpectToken(",");
	      fi;
	    od;
	    if IsAtToken(":") then
	      ExpectToken(":");
	      while tok[tnum][2]<>")" do
		Add(assg,ReadExpression([":=",")",","]));
		if IsAtToken(":=") then
		  ExpectToken(":=");
		  Add(assg,ReadExpression([")",","]));
		else
		  Add(assg,rec(type:="I",name:="true"));
		fi;
		if IsAtToken(",") then
		  ExpectToken(",");
		fi;

	      od;
	    fi;

	    ExpectToken(")");
	    if a.type="I" and not a.name in locals then
	      AddSet(globvars,a.name);
	    fi;
	    a:=rec(type:="C",fct:=a,args:=argus);
	    if Length(assg)>0 then
	      a.type:="CA";
	      a.assg:=assg;
	    fi;
	  elif e="[" then
	    # index
	    tnum:=tnum+1;
	    b:=ReadExpression(["]",",",".."]);
	    if IsAtToken(",") then
	      # array indexing -- translate to iterated index by opening a parenthesis and keeping
	      # position
	      tok[tnum]:=["O","["];
	      a:=rec(type:="L",var:=a,at:=b);
	    elif IsAtToken("..") then
	      ExpectToken("..");
	      c:=ReadExpression(["]"]);
	      b:=rec(type:="R",from:=b,to:=c);
	      a:=rec(type:="LR",var:=a,at:=b);
	      ExpectToken("]");
	    else
	      ExpectToken("]");
	      a:=rec(type:="L",var:=a,at:=b);
	    fi;
	  elif e="<" then
	    pre:=a;
	    # <> structure
	    tnum:=tnum+1;
	    b:=[];
	    repeat
	      a:=ReadExpression(["|",","]);
	      Add(b,a);
	      if IsAtToken(",") then
	        ExpectToken(",");
	      else
	        a:=fail;
	      fi;
	    until a=fail;

	    ExpectToken("|");
	    c:=[];
	    repeat
	      a:=ReadExpression([",",">"]);
	      Add(c,a);
	      if IsAtToken(",") then
	        ExpectToken(",");
	      else
		a:=fail;
	      fi;
            until a=fail;
	    if IsAtToken(":") then
	      ExpectToken(":");
	      #make rest of assignment a comment
	      e:=tnum;
	      while tok[e][2]<>">" do
		e:=e+1;
	      od;
	      tok:=Concatenation(tok{[1..tnum-1]},tok{[e]},
	          [["#",Concatenation(List(tok{[tnum..e-1]},x->String(x[2])))]],
		  tok{[e+1..Length(tok)]});
	    fi;
	    if IsAtToken("select") then
	      c:=doselect(c,stops);
	    fi;
	    ExpectToken(">",5);
	    a:=rec(type:="<>",op:=pre,left:=b,right:=c);

	  elif e="," and stops=[")"] then
	    # expression '(P,C)'
	    ExpectToken(",");
	    b:=ReadExpression(stops);
	    a:=rec(type:="pair",left:=a,right:=b);
	  elif e="where" then

	    ProcessWhere(stops);
	    if a=fail then
	      a:=ReadExpression(stops);
	    fi;
	  else
	    problemarea();
	    Error("eh!");
	  fi;

	  e:=eset();
	od;
      fi;
      return a;
    end;
    
   # 1-line functions
   if tok[tnum]=["K","func<"] then
      ExpectToken("func<");
      assg:=[];
      d:=[];
      repeat
        if IsAtToken(",") then ExpectToken(",");fi;
        a:=ReadExpression([":","|",","]);
        Add(d,a.name);
      until not IsAtToken(",");

      argus:=[];
      if IsAtToken(":") then
        ExpectToken(":");
        repeat
          b:=ReadExpression([":="]);
          Add(argus,b.name);
          ExpectToken(":=");
          c:=ReadExpression([",","|"]);
          Add(assg,rec(type:="A",left:=b,right:=c));
          if IsAtToken(",") then
            ExpectToken(",");
          fi;
        until IsAtToken("|");
      fi;
      ExpectToken("|");
      c:=ReadExpression([">"]);
      ExpectToken(">");
      Add(assg,rec(type:="return",values:=[c]));

      return rec(type:="F",block:=assg,args:=d,locals:=argus);

    elif tok[tnum]=["K","function"] or tok[tnum]=["K","intrinsic"] 
      or tok[tnum]=["K","procedure"] then
      # function
      fcomment:="";
      thisfctname:=tok[tnum-2][2];
      tnum:=tnum+1;
      ExpectToken("(");
      argus:=[];
      while tok[tnum][2]<>")" and tok[tnum][2]<>":" do
        if tok[tnum][1]="I" or IsAtToken("~") then
	  if IsAtToken("~") then
	    ExpectToken("~");
	    a:=Concatenation("TILDEVAR~",tok[tnum][2]);
	    Add(argus,a);
	  else
	    Add(argus,tok[tnum][2]);
	  fi;
	  tnum:=tnum+1;
	  if IsAtToken("::") then
	    ExpectToken("::");
	    if tok[tnum][1]="I" then
	      tnum:=tnum+1; # type identifier
	      if IsAtToken("[") then
		# list type?
		ExpectToken("[");
		ReadExpression(["]"]);
		ExpectToken("]");
	      fi;
	    elif IsAtToken("[") then
	      # list type?
	      ExpectToken("[");
	      ReadExpression(["]"]);
	      ExpectToken("]");
	    elif IsAtToken("{") then
	      # set type?
	      ExpectToken("{");
	      ReadExpression(["}"]);
	      ExpectToken("}");
	    else
	      problemarea();
	      Error("don't understand ::");
	    fi;
	  fi;
	  if IsAtToken(",") then 
	    tnum:=tnum+1; # multiple
	  fi;
	elif tok[tnum][1]="#" then
	  Add(fcomment,'/');
	  Append(fcomment,tok[tnum][2]);
	  Add(fcomment,'/');
	  tnum:=tnum+1;
	else
	  Error("weird token in declaration?");
	fi;
      od;
      assg:=false;
      locopt:=[];
      if IsAtToken(":") then
	ExpectToken(":");
	assg:=[];
	repeat
	  a:=ReadExpression([":="]);
	  Add(assg,a);
	  Add(locopt,a.name);
	  ExpectToken(":=");
	  Add(assg,ReadExpression([")",","]));
	  if IsAtToken(",") then
	    b:=false;
	    ExpectToken(",");
	  else
	    b:=true;
	  fi;
	until b;
	    
      fi;
      ExpectToken(")");
      while tok[tnum][1]="#" do
	Append(fcomment,"/out:");
	Append(fcomment,tok[tnum][2]);
        tnum:=tnum+1;
      od;
      if tok[tnum]=["O","->"] then
	ExpectToken("->");
	if IsAtToken("[") then
	  # to list type
	  ExpectToken("[");
	  ReadExpression(["]"]);
	  #ExpectToken("]"); # will be token in comment (instead of variable)
	elif IsAtToken(".") then
	  tok[tnum]:=["I","."]; # stupid syntax -- use . like identifier
	elif tok[tnum][1]<>"I" then
	  problemarea();
	  Error("-> unexpected");
	fi;
	a:="-> ";
	repeat
	  a:=Concatenation(a,",",tok[tnum][2]," ");
	  tnum:=tnum+1;
          if IsAtToken(",") then
	    tnum:=tnum+1;
	  fi;
        until IsAtToken("{");
	ExpectToken("{");
	while tok[tnum][2]<>"}" do
	  Add(a,' ');
	  if not IsString(tok[tnum][2]) then
	    Append(a,String(tok[tnum][2]));
	  else
	    Append(a,tok[tnum][2]);
	  fi;
	  tnum:=tnum+1;
	od;
	ExpectToken("}");
	fcomment:=Concatenation(fcomment,a);


      elif tok[tnum]=["O","{"] then
	ExpectToken("{");
        #fcomment:="";
	a:="";
	while tok[tnum][2]<>"}" do
	  if Length(fcomment)>0 then
	    Add(fcomment,' ');
	  fi;
	  if not IsString(tok[tnum][2]) then
	    Append(a,String(tok[tnum][2]));
	  else
	    Append(a,tok[tnum][2]);
	  fi;
	  tnum:=tnum+1;
	od;
	ExpectToken("}");
      fi;
      if IsAtToken(";") then
	#spurious ; after function definition
	tnum:=tnum+1;
      fi;

      a:=ReadBlock(["end function","end intrinsic","end procedure"]:inner);
      if tok[tnum][2]="end intrinsic" 
        and (tnum=Length(tok) or tok[tnum+1][2]<>";") then
	# end intrinsic w/o ;
        tok[tnum]:=[ "O", ";" ];
      else
	tnum:=tnum+1; # do end .... token
      fi;

      a:=rec(type:="F",args:=argus,locals:=Union(a[1],locopt),block:=a[2]);
      if Length(fcomment)>0 then
        a.comment:=fcomment;
      fi;
      if assg<>false then
	a.type:="FA";
	a.assg:=assg;
      fi;

      return a;

    # todo: parentheses
    else 
      stack:=[];
      a:=procidf();
      Add(stack,a);
      while tok[tnum][2] in lbinops do
        op:=tok[tnum][2];
	Add(stack,op);
	tnum:=tnum+1;

	b:=procidf();
	Add(stack,b);
	#a:=rec(type:=Concatenation("B",op),left:=a,right:=b);
      od;

      # sort out operation precedence
      i:=1;
      while Length(stack)>1 do
	#Print(stack,"|",OPRECED[i],"|\n");
        a:=2;
	while a<=Length(stack) do
	  if stack[a]=OPRECED[i] then
	    stack:=Concatenation(stack{[1..a-2]},
	      [rec(type:=Concatenation("B",stack[a]),left:=stack[a-1],right:=stack[a+1])],
	      stack{[a+2..Length(stack)]});
	#Print(stack,"{",OPRECED[i],"}\n");
	  else
	    a:=a+2;
	  fi;
	od;
	i:=i+1;
      od;
      return stack[1];

    fi;
  end;

  doselect:=function(arg)
  local cond,yes,no,stops;
    cond:=arg[1];
    if IsList(cond) and Length(cond)=1 and IsRecord(cond[1]) then
      cond:=cond[1];
    fi;
    if Length(arg)>1 then
      stops:=arg[2];
    else
      stops:=[];
    fi;
    ExpectToken("select");
    yes:=ReadExpression(["else"]);
    ExpectToken("else");
    no:=ReadExpression(Concatenation([";","select",">"],stops));
    if IsAtToken("select") then
      no:=doselect(no,stops);
    fi;
    return rec(type:="select",cond:=cond,yescase:=yes,nocase:=no);
  end;

  makeprintlistnice:=function(b)
  local i;
    # insert blanks between arguments
    i:=2;
    while i<=Length(b) do
      if IsRecord(b[i]) and b[i].type="I" 
          and IsRecord(b[i-1]) and b[i-1].type="I" then
        b:=Concatenation(b{[1..i-1]},[" "],b{[i..Length(b)]});
      fi;
      i:=i+1;
    od;
    Add(b,"\\n"); # newline, just keep in GAP format is fine
    return b;
  end;


  ReadBlock:=function(endkey)
  local l,e,a,aif,b,c,d,f,locals,kind,i,CleanoutWhere;

    CleanoutWhere:=function()
    local e;
      if Length(cmdstack)>0 then
	if Length(l)=0 then Error("where what of?");
	else
         for e in cmdstack do
	   # move item before last listed command
	   Add(l,l[Length(l)]);
	   l[Length(l)-1]:=rec(type:="wh",assg:=e);
	 od;
	 cmdstack:=[];
	fi;
      fi;
    end;

    l:=[];
    locals:=[];

    while tnum<=Length(tok) and
      (endkey=false or ForAll(endkey,x->tok[tnum]<>["K",x])) do
      if Length(costack)>0 then
	for e in costack do
	  Add(l,rec(type:="co",text:=e[2]));
	od;
	costack:=[];
      fi;

      e:=tok[tnum];
      tnum:=tnum+1;
      if e[2]="time" then
	# timing....
	Add(l,rec(type:="co",text:="Next line is timing"));
	e:=tok[tnum];
	tnum:=tnum+1;
      fi;

      if e[1]="#" then
	Add(l,rec(type:="co",text:=e[2]));
        CleanoutWhere();
      elif e[1]="K" then
	# keyword

	if e[2]="if" then
	  a:=ReadExpression(["then",";"]);
	  if IsAtToken("then") then
	    ExpectToken("then");
	  elif IsAtToken(";") then
	    ExpectToken(";"); # apparently ; instead of then is permitted
	  else
	    Error("confused if");
	  fi;
	  b:=ReadBlock(["else","end if","elif"]:inner);
	  locals:=Union(locals,b[1]);
	  a:=rec(type:="if",cond:=a,block:=b[2]);
	  Add(l,a);
	  while IsAtToken("elif") do
	    ExpectToken("elif");
	    c:=ReadExpression(["then"]);
	    ExpectToken("then");
	    b:=ReadBlock(["else","end if","elif"]:inner);
	    locals:=Union(locals,b[1]);
	    a.elseblock:=[rec(type:="if",isElif:=true,cond:=c,block:=b[2])];
	    a:=a.elseblock[1]; # make elif an iterated else if
	  od;
	  if IsAtToken("else") then
	    ExpectToken("else");
	    b:=ReadBlock(["end if"]:inner);
	    locals:=Union(locals,b[1]);
	    a.elseblock:=b[2];
	  fi;
	  ExpectToken("end if");
	  ExpectToken(";",1);
	  CleanoutWhere();

	elif e[2]="try" then
	  b:=ReadBlock(["catch err","catch e","end try"]:inner);
	  locals:=Union(locals,b[1]);
	  a:=rec(type:="try",block:=b[2]);
	  Add(l,a);
	  if IsAtToken("catch err") or IsAtToken("catch e") then
	    ExpectToken(ShallowCopy(tok[tnum][2]));
	    b:=ReadBlock(["end try"]);
	    locals:=Union(locals,b[1]);
	    a.errblock:=b[2];
	  fi;
	  ExpectToken("end try");
	  ExpectToken(";",1);
	  CleanoutWhere();
 
	elif e[2]="error if" then
	  a:=ReadExpression([","]);
	  ExpectToken(",");
	  b:=ReadExpression([";"]);
	  ExpectToken(";");
	  Add(l,rec(type:="if",cond:=a,block:=[rec(type:="Print",values:=[b])]));
	  CleanoutWhere();

	elif e[2]="while" then
	  a:=ReadExpression(["do"]);
	  ExpectToken("do");
	  b:=ReadBlock(["end while"]:inner);
	  locals:=Union(locals,b[1]);
	  a:=rec(type:="while",cond:=a,block:=b[2]);
	  ExpectToken("end while");
	  ExpectToken(";",2);
	  Add(l,a);
	  CleanoutWhere();
	elif e[2]="for" then
	  a:=rec(type:="I",name:=tok[tnum][2]);
	  tnum:=tnum+1;
	  if IsAtToken("in") then
	    ExpectToken("in");
	    c:=ReadExpression(["do"]);
	  else
	    ExpectToken(":=");
	    b:=ReadExpression(["to"]);
	    ExpectToken("to");
	    c:=ReadExpression(["do","by"]);
	    c:=rec(type:="R",from:=b,to:=c);
	    if IsAtToken("by") then
	      ExpectToken("by");
	      b:=ReadExpression(["do"]);
	      c.step:=b;
	    fi;
	  fi;

	  ExpectToken("do");
	  b:=ReadBlock(["end for"]:inner);
	  locals:=Union(locals,b[1]);
      #if a.name="cl" then Error("rof");fi;
	  AddSet(locals,a.name);
	  a:=rec(type:="for",var:=a,from:=c,block:=b[2]);
	  ExpectToken("end for");
	  ExpectToken(";",3);
	  Add(l,a);
	  CleanoutWhere();

	elif e[2]="assert" then
	  a:=ReadExpression([";"]);
	  ExpectToken(";",4);
	  a:=rec(type:="assert",cond:=a);
	  Add(l,a);
	  CleanoutWhere();
        elif e[2]="require" then
	  a:=ReadExpression([":"]);
	  ExpectToken(":");
          c:=ReadExpression([";",","]);
          if IsAtToken(",") then
            d:=[c];
            while IsAtToken(",") do
              ExpectToken(",");
              c:=ReadExpression([";",","]);
              Add(d,c);
            od;
            c:=rec(type:="<",args:=d);
          fi;

	  ExpectToken(";","4b");
	  a:=rec(type:="require",cond:=a,mess:=c);
	  Add(l,a);
	  CleanoutWhere();
	elif e[2]="repeat" then
	  b:=ReadBlock(["until"]);
	  ExpectToken("until");
	  locals:=Union(locals,b[1]);
	  a:=ReadExpression([";"]);
	  a:=rec(type:="repeat",cond:=a,block:=b[2]);
	  Add(l,a);
	  ExpectToken(";",5);
	  CleanoutWhere();

	elif e[2]="return" then
	  a:=[];
	  while tok[tnum][2]<>";" do
	    b:=ReadExpression([",",";","select"]);
	    if IsAtToken("select") then
	      b:=doselect(b);
	    fi;
	    Add(a,b);
	    if IsAtToken(",") then
	      tnum:=tnum+1;
	    fi;
	  od;
	  ExpectToken(";",6);
	  Add(l,rec(type:="return",values:=a));
	  CleanoutWhere();
	elif e[2]="vprint" or e[2]="error" or e[2]="print" or e[2]="printf"
	  or e[2]="vprintf" then
	  if e[2]="vprint" or e[2]="vprintf" then
	    kind:="Info";
	    a:=ReadExpression([":",","]);
	    if IsAtToken(",") then
	      ExpectToken(",");
	      d:=ReadExpression([":"]);
	    else
	      d:=1;
	    fi;
	    ExpectToken(":");
	  elif e[2]="print" or e[2]="printf" then
	    kind:="Print";
	    a:=false;
	  else 
	    a:=false;
	    kind:="error";
	  fi;
	  c:=[];
          repeat
	    b:=ReadExpression([",",";"]);
	    Add(c,b);
	    if IsAtToken(",") then
	      ExpectToken(",");
	    fi;
	  until IsAtToken(";");

	  #if tok[tnum][1]="S" then
	  #  c[1]:=tok[tnum][2];
	  #fi;
	  #if tok[tnum+1][2]="," then
	  #  # there are more arguments
	  #  tnum:=tnum+1;
	  #  repeat
	  #    tnum:=tnum+1;
	  #    b:=ReadExpression([",",";"]);
	  #    Add(c,b);
	  #    e:=tok[tnum][2];
	  #  until e=";";
	  #else
	  #  tnum:=tnum+1;
	  #fi;
	  ExpectToken(";",7);

	  a:=rec(type:=kind,class:=a,values:=c);
	  if kind="Info" then a.level:=d;fi;
	  Add(l,a);
	  CleanoutWhere();

        elif e[2]="continue" then
	  ExpectToken(";",-8);
	  Add(l,rec(type:="continue"));
	  CleanoutWhere();
	elif e[2]="freeze" then
	  ExpectToken(";",8);
	elif e[2]="import" then
	  b:=tok[tnum][2];
	  tnum:=tnum+1;
	  ExpectToken(":");
	  c:=[];
	  repeat
	    a:=ReadExpression([",",";"]);
	    Add(c,a);
	    if IsAtToken(",") then
	      ExpectToken(",");
	    else
	      a:=fail;
	    fi;
	  until a=fail;
	  d:=b;
	  b:=Concatenation("import from ",b,":\n");
	  for i in [1..Length(c)] do
	    Add(globimp,rec(file:=d,func:=c[i].name));
	    if i>1 then
	      Append(b,", ");
	    fi;
	    Append(b,c[i].name);
	  od;

	  #Add(l,rec(type:="co",text:=b));

	  ExpectToken(";",9);
	  CleanoutWhere();
	elif e[2]="forward" or e[2]="declare verbose"
	  or e[2]="declare attributes" then
	  if e[2]="forward" then b:="Forward";
	  elif e[2]="declare verbose" then b:="Verbose";
	  elif e[2]="declare attributes" then b:="Attribute";
	  fi;
	  repeat
	    a:=ReadExpression([";",",",":"]);
	    if IsAtToken(":") then
	      # skip type
	      ExpectToken(":");
	      ReadExpression([";",","]);
	    fi;
	    Add(l,rec(type:="co",
	      text:=Concatenation(b," declaration of ",String(a.name))));
            Add(forward,a.name);

            if IsAtToken(",") then
	      ExpectToken(",",10);
	    fi;
	  until IsAtToken(";");
	  ExpectToken(";",10);
	  CleanoutWhere();
	elif e[2]="function" or e[2]="intrinsic" or e[2]="procedure" then
	  tnum:=tnum-1;
	  # rewrite: function Bla 
	  # to Bla:=function
	  tok:=Concatenation(tok{[1..tnum-1]},tok{[tnum+1]},[["O",":="]],
	    tok{[tnum]},tok{[tnum+2..Length(tok)]});
	elif e[2]="local" then
	  c:=[];
	  repeat
	    a:=ReadExpression([",",";"]);
	    Add(c,a);
	    if IsAtToken(",") then
	      ExpectToken(",");
	    else
	      a:=fail;
	    fi;
	  until a=fail;
	  ExpectToken(";",11);
	  for a in c do
	    AddSet(locals,a.name);
	  od;

        elif e[2]="delete" then
	  a:=ReadExpression([";",","]);
	  b:=[a];
	  while tok[tnum][2]<>";" do
	    ExpectToken(",",-11/2);
	    a:=ReadExpression([";",","]);
	    Add(b,a);
	  od;
	  Add(l,rec(type:="delete",del:=b));
	  ExpectToken(";",11/2);
	  CleanoutWhere();
	elif e[2]="break" then
	  a:=ReadExpression([";"]);
	  Add(l,rec(type:="break",var:=a));
	  ExpectToken(";",11/3);
	  CleanoutWhere();

	elif e[2]="case" then
	  e:=ReadExpression([":"]); # variable
	  ExpectToken(":");
	  c:=[];
	  while IsAtToken("when") do
	    ExpectToken("when");
	    a:=ReadExpression([":",","]);
	    if IsAtToken(",") then
	      a:=[a];
	      while IsAtToken(",") do
		ExpectToken(",");
		b:=ReadExpression([":",","]);
		Add(a,b);
	      od;
	    fi;
	    ExpectToken(":");
	    b:=ReadBlock(["when","end case","else"]);
	    locals:=Union(locals,b[1]);
	    Add(c,[a,b[2]]);
	  od;
	  a:=rec(type:="case",test:=e,cases:=c);
	  if IsAtToken("else") then
	    ExpectToken("else");
	    b:=ReadBlock(["end case"]);
	    locals:=Union(locals,b[1]);
            a.elsecase:=b[2];
	  fi;
	  ExpectToken("end case");
	  Add(l,a);
	  CleanoutWhere();
	else
	  problemarea();
	  Error("other keyword ",e);
	fi;
      elif e[1]="I" or e[2]="$$" then
	e:=[e[1],e[2]];
	tnum:=tnum-1;
	if e[2]="$$" then tok[tnum]:=["I",thisfctname]; fi;
	a:=ReadExpression([",",":=","-:=","+:=","*:=","/:=","cat:=",";","<"]);
	if a.type="I" then
	  AddSet(locals,a.name);
	fi;
	e:=tok[tnum];
	tnum:=tnum+1;
	if e[1]<>"O" then 
	  problemarea();
	  Error("missing separator");
	fi;
	if e[2]="<" then
	  # implicit generator assignment
	  c:=[];
	  repeat
	    e:=ReadExpression([",",">"]);
	    Add(c,e);
	    if IsBound(e.name) then
	      AddSet(locals,e.name);
	    fi;
	    if IsAtToken(",") then
	      ExpectToken(",","impgen");
	    fi;
	  until IsAtToken(">");
	  ExpectToken(">","impgen");
	  e:=tok[tnum];
	  tnum:=tnum+1;
	else
	  c:=fail;
	fi;

	if e[2]="," then 
	  b:=[a];
	  while e[2]="," do
	    a:=ReadExpression([",",":=",";"]);
	    Add(b,a);
	    e:=tok[tnum];
	    tnum:=tnum+1;
	  od;
          if e[2]=";" then

            Add(l,rec(type:="Print",values:=makeprintlistnice(b)));
          else
            for a in [1..Length(b)] do
              if b[a].name="_" then
                b[a].name:=Concatenation("forgetvar",String(a));
              fi;
            od;
            a:=ReadExpression([";"]);
            Add(l,rec(type:="Amult",left:=b,right:=a));
            for a in b do
              if a.type="I" then
                AddSet(locals,a.name);
              fi;
            od;
            ExpectToken(";",13);
          fi;
	elif e[2]=":=" then
	  # assignment
	  b:=ReadExpression([",",":=",";","select"]);

	  if IsAtToken("select") then
	    b:=doselect(b);
	  fi;
	  a:=rec(type:="A",left:=a,right:=b);
	  if c<>fail then
	    a.implicitassg:=c;
	  fi;
	  Add(l,a);
	  ExpectToken(";",14);
	  CleanoutWhere();
	  if endkey=false and IsBound(a.left.name) then
	    # top-level assignment -- global variable
	    #Print("> ",a.left.name," <\n");
	    AddSet(defines,a.left.name);
	  fi;
	elif e[2]="-:=" then
	  b:=ReadExpression([";"]);
	  ExpectToken(";",15);
	  Add(l,rec(type:="A-",left:=a,right:=b));
	  CleanoutWhere();
	elif e[2]="+:=" then
	  b:=ReadExpression([";"]);
	  ExpectToken(";",16);
	  Add(l,rec(type:="A+",left:=a,right:=b));
	  CleanoutWhere();
	elif e[2]="*:=" then
	  b:=ReadExpression([";"]);
	  ExpectToken(";");
	  Add(l,rec(type:="A*",left:=a,right:=b));
	  CleanoutWhere();
	elif e[2]="/:=" then
	  b:=ReadExpression([";"]);
	  ExpectToken(";");
	  Add(l,rec(type:="A/",left:=a,right:=b));
	  CleanoutWhere();
	elif e[2]="cat:=" then
	  b:=ReadExpression([";"]);
	  ExpectToken(";");
	  Add(l,rec(type:="Acat",left:=a,right:=b));
	  CleanoutWhere();
	elif e[2]=";" then
	  a.line:=true; # only command in line
	  Add(l,a);
	  CleanoutWhere();
	else
	  problemarea();
	  Error("anders");
	fi;
      elif e[1]="S" then
        # print statement without print (but starting with string) 
        b:=[e[2]];
        while IsAtToken(",") do
          ExpectToken(",");
          a:=ReadExpression([",",";"]);
          Add(b,a);
        od;
        Add(l,rec(type:="Print",values:=makeprintlistnice(b)));
        ExpectToken(";",20);
      elif e[2]=";" then
	# empty command?
      else 
	problemarea();
	Error("cannot deal with token ",e);
      fi;
    od;

    return [locals,l];
  end;

  costack:=[];
  cmdstack:=[];
  tnum:=1; # indicate in token list

  # actual work
  a:=ReadBlock(false);

  globvars:=Difference(globvars,List(globimp,x->x.func));

  return rec(used:=globvars,import:=globimp,defines:=defines,
             forward:=forward,code:=a[2]);

end;

RecursiveFindRec:=function(r,cond)
local i,nodes,n,j;
  if cond(r) then return r;fi;
  nodes:=[r];
  for n in nodes do
    # breadth-first test before recursing
    for i in RecNames(n) do
      if cond(n.(i)) then
	return n.(i);
      elif IsRecord(n.(i)) then
	# add to next layer
	Add(nodes,n.(i));
	# don't split a command block....
      elif i<>"block" and IsList(n.(i)) and ForAny(n.(i),IsRecord) then
	for j in n.(i) do
	  if cond(j) then
	    return j;
	  elif IsRecord(j) then
	    Add(nodes,j);
	  fi;
	od;
      fi;
    od;
  od;
  return fail;
end;

RebuildRecTree:=function(r,replace,by)
local new,i;
  if r=replace then
    return r.(by);
  fi;
  new:=rec();
  for i in RecNames(r) do
    if r.(i)=replace then # use identical?
      new.(i):=RebuildRecTree(r.(i).(by),fail,by);
      replace:=fail; # cannot happen again -- speedup
    elif IsRecord(r.(i)) then
      new.(i):=RebuildRecTree(r.(i),replace,by);
    elif IsList(r.(i)) and ForAny(r.(i),IsRecord) then
      new.(i):=List(r.(i),z->RebuildRecTree(z,replace,by));
    else
      new.(i):=r.(i);
    fi;
  od;
  return new;
end;

VariablesInExpression:=function(r)
local l,i;
  l:=[];
  if IsList(r) then
    l:=Concatenation(List(r,VariablesInExpression));
  elif IsRecord(r) then
    if IsBound(r.type) and r.type="I" then
      return [r.name];
    fi;
    for i in RecNames(r) do
      l:=Union(l,VariablesInExpression(r.(i)));
    od;
  fi;
  return l;
end;

GAPOutput:=function(l,f)
local sz,i,doit,printlist,doitpar,indent,t,mulicomm,traid,declared,tralala,
  unravel,CloseParenthesisOptions,localsstack;

   sz:=SizeScreen();
   SizeScreen([LINEWIDTH+2,sz[2]]);

   # process translation list
   tralala:=[[],[]];
   for i in [1,3..Length(TRANSLATE)-1] do
     Add(tralala[1],Immutable(TRANSLATE[i]));
     Add(tralala[2],Immutable(TRANSLATE[i+1]));
   od;
   SortParallel(tralala[1],tralala[2]);

   START:="";
   indent:=function(n)
     n:=n*2;
     if n<0 then START:=START{[1..Length(START)+n]};
     else Append(START,ListWithIdenticalEntries(n,' '));fi;
   end;

   # translate identifier
   traid:=function(s)
     # TODO: use name space
     if s in l.namespace then
       s:=Concatenation(s,"@");
     elif s in GAP_RESERVED then
       s:=Concatenation("var",s);
     elif s in GAP_SYSVARS and ForAny(localsstack,x->s in x) then
       # local variable overriding GAP global system function
       s:=Concatenation("lvar",s);
     fi;
     return s;
   end;

   printlist:=function(arg)
   local l,i,first;
    l:=arg[1];
    first:=true;
    for i in l do
      if not first then
	FilePrint(f,",");
      else
	first:=false;
      fi;
      if IsRecord(i) then
	doit(i);
      else
	if Length(arg)>1 then
	  FilePrint(f,"\"",i,"\"");
	else
	  FilePrint(f,traid(i));
	fi;
      fi;
    od;
  end;

  # unravel recursive cals from translation of infix to function calls
  unravel:=function(l,type)
  local i,j;
    i:=1;
    while i<=Length(l) do
      if l[i].type=type then
	for j in [Length(l),Length(l)-1..i+1] do
	  l[j+1]:=l[j];
	od;
	l[i+1]:=l[i].right;
	l[i]:=l[i].left;
      else
	i:=i+1;
      fi;
    od;
  end;

  mulicomm:=function(f,str)
  local i,s,p;
    s:=Length(START);
    p:=Position(str,'\n');
    while Length(str)+s>COMMENTWIDTH or p<>fail do
      if p=fail then
	i:=COMMENTWIDTH-s;
      else
	i:=Minimum(COMMENTWIDTH-s,p);
      fi;
      while i>0 and str[i]<>' ' and str[i]<>'\n' do
        i:=i-1;
      od;
      if i=0 then
	i:=Minimum(COMMENTWIDTH,Length(str));
      fi;
      FilePrint(f,"#  ",str{[1..i-1]},"\n",START);
      str:=str{[i+1..Length(str)]};
      if p<>fail then
	p:=Position(str,'\n');
      fi;
    od;
    if Length(str)>0 then
      FilePrint(f,"#  ",str,"\n",START);
    else
      FilePrint(f,"\n",START);
    fi;
  end;

  CloseParenthesisOptions:=function(node)
  local i;
    if IsBound(node.options) then
      FilePrint(f,":");
      for i in [1..Length(node.options)] do
        if i>1 then
	  FilePrint(f,",");
	fi;
	if node.options[i].type="I" then
	  doit(node.options[i]);
	elif node.options[i].type="A" then
	  doit(node.options[i].left);
	  FilePrint(f,":=");
	  doit(node.options[i].right);
        else
	  Error("strange option type");
	fi;
      od;
    fi;
    FilePrint(f,")");
  end;

  localsstack:=[]; # stack holding current local variables

  # doit -- main node processor
  doit:=function(node)
  local t,i,a,b,cachef,cachest,str1,str2;
    t:=node.type;
    if t="A" then
      # special case of declaration assignment
      if IsBound(node.left.type) and node.left.type="I" 
        and node.left.name in declared then
	FilePrint(f,"InstallGlobalFunction(");
	doit(node.left);
	FilePrint(f,",\n",START);
	doit(node.right:ininstall);
	FilePrint(f,")");
	FilePrint(f,";\n\n",START);
      else
	# is there a SELECT involved?
	a:=RecursiveFindRec(node.right,
             x->IsRecord(x) and IsBound(x.type) and x.type="select");
        if a<>fail then
	  # rebuild node.right twice, once with condition and once without
	  FilePrint(f,"# rewritten select statement\n",START,"if ");
	  doit(a.cond);
	  indent(1);
	  FilePrint(f," then\n",START);
	  doit(rec(type:="A",left:=node.left,
	    right:=RebuildRecTree(node.right,a,"yescase")));
	  #indent(-1);
	  FilePrint(f,"\b\belse");
	  #indent(1);
	  FilePrint(f,"\n",START);
	  doit(rec(type:="A",left:=node.left,
	    right:=RebuildRecTree(node.right,a,"nocase")));
	  indent(-1);
	  FilePrint(f,"\b\bfi;\n",START);
	else
	  doit(node.left);
	  FilePrint(f,":=");
	  doit(node.right);
          if IsBound(node.right.type) and 
            (node.right.type="F" or node.right.type="FA") then
            # extra blank line after function assignment
            FilePrint(f,";\n\n",START);
          else
            FilePrint(f,";\n",START);
          fi;
	fi;
      fi;

      if IsBound(node.implicitassg) then
	FilePrint(f,"# Implicit generator Assg from previous line.\n",START);
	for i in [1..Length(node.implicitassg)] do
	  doit(node.implicitassg[i]);
	  FilePrint(f,":=");
	  doit(node.left);
	  FilePrint(f,".",i,";\n",START);
	od;
      fi;
    elif t[1]='A' and Length(t)=2 and t[2] in "+-*/" then
      doit(node.left);
      FilePrint(f,":=");
      doit(node.left);
      FilePrint(f,t{[2]});
      doit(node.right);
      FilePrint(f,";\n",START);
    elif t="Acat" then
      doit(node.left);
      FilePrint(f,":=Concatenation(");
      doit(node.left);
      FilePrint(f,",");
      doit(node.right);
      FilePrint(f,");\n",START);

    elif t="Amult" then
      FilePrint(f,"# =v= MULTIASSIGN =v=\n",START);
      a:=node.left[Length(node.left)];
      doit(a);
      FilePrint(f,":=");
      doit(node.right);
      FilePrint(f,";\n",START);
      for i in [1..Length(node.left)] do
        doit(node.left[i]);
	FilePrint(f,":=");
	doit(a);
	FilePrint(f,".val",String(i),";\n",START);
      od;
      FilePrint(f,"# =^= MULTIASSIGN =^=\n",START);

    elif t="N" then
      FilePrint(f,node.name);
    elif t="I" then
      FilePrint(f,traid(node.name));
    elif t="co" then
      # commentary
      mulicomm(f,node.text);
#      a:=node.text;
#      i:=Position(a,'\n');
#      while i<>fail do
#	FilePrint(f,"\n",START);
#	FilePrint(f,"# ",a{[1..i]},START);
#	a:=a{[i+1..Length(a)]};
#	i:=Position(a,'\n');
#      od;
#
#      FilePrint(f,"#  ",a,"\n",START);
    elif t="W" then
      # warning
      FilePrint(f,"Info(InfoWarning,1,");
      if Length(node.text)>40 then
	FilePrint(f,"\n",START,"  ");
      fi;
      FilePrint(f,"\"",node.text,"\");\n",START);
    elif t="Info" then
      # info
      FilePrint(f,"Info(Info");
      doit(node.class);
      FilePrint(f,",");
      if IsInt(node.level) then
      FilePrint(f,node.level);
      else
	doit(node.level);
      fi;
      FilePrint(f,",");
      a:=node.values;
      if a[1].type="S" and '%' in a[1].name then
	str1:=SplitString(a[1].name,"%");
	for i in [2..Length(str1)] do
	  str1[i]:=str1[i]{[2..Length(str1[i])]}; # letter after % must go
	od;
	b:=[rec(type:="S",name:=str1[1])];
	i:=2;
	while i<=Length(str1) do
	  Add(b,a[i]);
	  Add(b,rec(type:="S",name:=str1[i]));
	  i:=i+1;
	od;
	Append(b,a{[i..Length(a)]});
	a:=b;
      fi;
      if a[Length(a)].type="S" then
        b:=a[Length(a)].name;
	if Length(b)>1 and b{[Length(b)-1..Length(b)]}="\\n" then
	  Unbind(b[Length(b)]); # trailing \n will be supplied by Info
	  Unbind(b[Length(b)]); # trailing \n will be supplied by Info
	  if Length(b)=0 then Unbind(a[Length(a)]);fi;
	fi;
      fi;
      printlist(a,"\"");
      FilePrint(f,");\n",START);
    elif t="Print" then
      # info
      FilePrint(f,"Print(");
      printlist(node.values,"\"");
      FilePrint(f,");\n",START);

    elif t="return" then
      if Length(node.values)=1 then
        FilePrint(f,"return ");
	doit(node.values[1]);
	FilePrint(f,";\n",START);
      else
	FilePrint(f,"return rec(");
	for i in [1..Length(node.values)] do
	  if i>1 then FilePrint(f,",\n",START,"  ");fi;
	  FilePrint(f,"val",String(i),":=");
	  doit(node.values[i]);
	od;
	FilePrint(f,");\n",START);
      fi;
    elif t[1]='F' then
      # function
      FilePrint(f,"function(");
      printlist(node.args);
      FilePrint(f,")\n",START);

      if IsBound(node.comment) then
	mulicomm(f,node.comment);
      fi;

      indent(1);
      if Length(node.locals)>0 then
        FilePrint(f,"local ");
	printlist(node.locals);
	i:=node.locals;
	FilePrint(f,";\n",START);
      else
	i:=[];
      fi;
      localsstack:=Concatenation([i],localsstack);
      if t="FA" then
	for i in [1,3..Length(node.assg)-1] do
	  doit(node.assg[i]);
	  FilePrint(f,":=ValueOption(\"");
	  doit(node.assg[i]);
	  FilePrint(f,"\");\n",START,"if ");
	  doit(node.assg[i]);
	  FilePrint(f,"=fail then\n",START,"  ");
	  doit(node.assg[i]);
	  FilePrint(f,":=");
	  doit(node.assg[i+1]);
	  FilePrint(f,";\n",START,"fi;\n",START);
	od;

      fi;
      for i in node.block do
	doit(i);
      od;
      #FilePrint(f,"\n");
      indent(-1);
      FilePrint(f,"\b\b");
      FilePrint(f,"end");
      localsstack:=localsstack{[2..Length(localsstack)]};
#      if ValueOption("ininstall")=fail then
#	FilePrint(f,";\n",START);
#      fi;
    elif t="S" then
      FilePrint(f,"\"");
      FilePrint(f,node.name);
      FilePrint(f,"\"");
    elif t="C" or t="CA" then
      # fct. call

      # # is there a SELECT involved?
      # a:=RecursiveFindRec(node.right,
#	    x->IsRecord(x) and IsBound(x.type) and x.type="select");
#      if a<>fail then
#        Error("function call with select");
#      fi;
      

      a:=false; # surrounding parenthesis?
      # do we supress the call based on the argument?
      if IsBound(node.fct.name) and node.fct.name="Matrix" and Length(node.args)=1
        and node.args[1].type="C" and node.args[1].fct.name="SparseMatrix" then
        doit(node.args[1]);
      else
        if IsBound(node.fct.name) and node.fct.name="Integers"
          and Length(node.args)>0 then
          FilePrint(f,"(Integers mod ");
          a:=true;
	elif IsBound(node.fct.name) then
	  i:=PositionSorted(tralala[1],node.fct.name);
	  if i<>fail and IsBound(tralala[1][i]) and tralala[1][i]=node.fct.name then
	    FilePrint(f,tralala[2][i]);
	  else
	    doit(node.fct);
	  fi;
	else
	  doit(node.fct);
	fi;

	FilePrint(f,"(");
        if IsBound(node.fct.name) and node.fct.name="Append" then 
          printlist(node.args:NOTILDE);
        else
          printlist(node.args);
        fi;
	if t="CA" then
	  FilePrint(f,":");
	  for i in [1,3..Length(node.assg)-1] do
	    if i>1 then
	      FilePrint(f,",");
	    fi;
	    doit(node.assg[i]);
	    FilePrint(f,":=");
	    doit(node.assg[i+1]);
	  od;
	fi;
	if IsBound(node.line) then
	  FilePrint(f,");\n",START);
	else
	  FilePrint(f,")");
	fi;
      fi;
      if a then 
        FilePrint(f,")");
      fi;

    elif t="L" then
      # list access
      doit(node.var);
      FilePrint(f,"[");
      doit(node.at);
      FilePrint(f,"]");
    elif t="LR" then
      # list access
      doit(node.var);
      FilePrint(f,"{");
      doit(node.at);
      FilePrint(f,"}");

    elif t="V" then
      FilePrint(f,"[");
      printlist(node.args);
      FilePrint(f,"]");
    elif t="{" then
      # Set
      FilePrint(f,"Set([");
      printlist(node.args);
      FilePrint(f,"])");
    elif t="perm" then
      # permutation
      FilePrint(f,node.perm);
    elif t="notperm" then
      t:=UnpackNumberList(node.notperm);
      if t=fail then
	t:=node.notperm;
      fi;
      i:=UnFlat(t);
      if i<>fail then
	t:=i;
      fi;
      if ValueOption("carefree")<>true then
	FilePrint(f,"NOTPERM");
      fi;
      FilePrint(f,t,"\n":noblank);
    elif t="[*" then
      FilePrint(f,"# [*-list:\n",START,"[");
      printlist(node.args);
      FilePrint(f,"]");
    elif t="{@" then
      FilePrint(f,"# {@-list:\n",START,"[");
      printlist(node.args);
      FilePrint(f,"]");
    elif t="R" then
      FilePrint(f,"[");
      doit(node.from);
      if IsBound(node.step) then
	FilePrint(f,",");
	doit(node.from);
	if node.step.type<>"U-" then
	  FilePrint(f,"+");
	fi;
	doit(node.step);
      fi;
      FilePrint(f,"..");
      doit(node.to);
      FilePrint(f,"]");
    elif t="commutator" then
      FilePrint(f,"Comm(");
      doit(node.left);
      FilePrint(f,",");
      doit(node.right);
      FilePrint(f,")");
    elif t="pair" then
      FilePrint(f,"Tuple([");
      doit(node.left);
      FilePrint(f,",");
      doit(node.right);
      FilePrint(f,"])");
    elif t="paren" then
      FilePrint(f,"(");
      doit(node.arg);
      FilePrint(f,")");
    elif t="B!" then
      if IsBound(node.left.fct) and IsBound(node.left.fct.name) and
        node.left.fct.name="Integers" and Length(node.left.args)=0 then
        FilePrint(f,"Int(");
        doit(node.right);
        FilePrint(f,")");
      else
        doit(node.right);
        if ValueOption("carefree")<>true then
          FilePrint(f,"*FORCEOne(");
          doit(node.left);
          FilePrint(f,")");
        else
          FilePrint(f," #CAST ");
          doit(node.left);
          FilePrint(f,"\n",START,"  ");
        fi;
      fi;
    elif t="B`" then
      doit(node.left);
      FilePrint(f,".");
      doit(node.right);
    elif t="Bdiv" then
      FilePrint(f,"QuoInt(");
      doit(node.left);
      FilePrint(f,",");
      doit(node.right);
      FilePrint(f,")");
    elif t="Bcat" or t="Bmeet" or t="Bjoin" then
      if t="Bcat" then
	FilePrint(f,"Concatenation(");
      elif t="Bmeet" then
	FilePrint(f,"Intersection(");
      elif t="Bjoin" then
	FilePrint(f,"Union(");
      fi;
      i:=[node.left,node.right];
      unravel(i,t);
      printlist(i);
      FilePrint(f,")");
    elif t[1]='B' then
      # binary op
      i:=t{[2..Length(t)]};
      a:=i;
      if a in FAKEBIN then
        if a="notin" then
          FilePrint(f,"not (");
          doit(node.left);
          FilePrint(f," in ");

          # avoid `Set`-ing given list
          if node.right.type="{" then
            # hange from `Set`.
            node.right.type:="V";
          fi;

          doit(node.right);
        else
          b:=false;
          #if a="meet" then
          #  a:="Intersection";
          #elif a="join" then
          #  a:="Union";
          #elif a="cat" then
          #  a:="Concatenation";
          if a="diff" then
            a:="Difference";
          elif a="subset" then
            a:="IsSubset";
            b:=true;
          else
            Error("Can't do ",a," yet\n");
          fi;

          FilePrint(f,a,"(");
          if b then
            doit(node.right);
            FilePrint(f,",");
            doit(node.left);
          else
            doit(node.left);
            FilePrint(f,",");
            doit(node.right);
          fi;
        fi;

	FilePrint(f,")");
      else
	# store the strings for both parameters to allow potential later
	# introduction of parentheses
	cachef:=f;
	cachest:=FILEPRINTSTR;
	FILEPRINTSTR:="";
	str1:="";
	f:=OutputTextString(str1,true);
	doit(node.left);
	CloseStream(f);
	str1:=Concatenation(str1,FILEPRINTSTR);
	FILEPRINTSTR:="";


	if i="ne" or i="cmpne" then
	  i:="<>";
	elif i="eq" or i="cmpeq" or i="=" then
	  i:="=";
	elif i="and" then
	  i:=" and ";
	elif i="or" then
	  i:=" or ";
	elif i="mod" then
	  i:=" mod ";
	elif i="in" then
	  i:=" in ";
          # avoid `Set`-ing given list
          if node.right.type="{" then
            # hange from `Set`.
            node.right.type:="V";
          fi;
	elif i="gt" then
	  i:=" > ";
	elif i="ge" then
	  i:=" >= ";
	elif i="lt" then
	  i:=" < ";
	elif i="le" then
	  i:=" <= ";
	fi;

	str2:="";
	f:=OutputTextString(str2,true);
	doit(node.right);
	CloseStream(f);
	str2:=Concatenation(str2,FILEPRINTSTR);
	f:=cachef;

	FILEPRINTSTR:=cachest;
	FilePrint(f,str1);
	FilePrint(f,i);
	FilePrint(f,str2);
      fi;

    elif t="U#" then
      FilePrint(f,"Size(");
      doit(node.arg);
      FilePrint(f,")");
    elif t="U-" then
      FilePrint(f,"-");
      doit(node.arg);
    elif t="U~" then
      if ValueOption("carefree")<>true and ValueOption("NOTILDE")<>true then
	FilePrint(f,"TILDE");
      fi;
      doit(node.arg);
    elif t="Unot" then
      FilePrint(f,"not ");
      doit(node.arg);
    elif t="Uassigned" then
      FilePrint(f,"IsBound(");
      doit(node.arg);
      FilePrint(f,")");
    elif t="Ueval" then
      FilePrint(f,"#EVAL\n",START,"    ");
      doit(node.arg);

    elif t="<>" then
      if node.op.type="I" and node.op.name="func" then
	FilePrint(f,"function(");
	printlist(node.left);
	indent(1);
	FilePrint(f,")\n");
	FilePrint(f,START,"return ");
	if Length(node.right)>1 then
	  Error("multiargument?");
	fi;
	doit(node.right[1]);
	indent(-1);
	FilePrint(f,";\n",START,"end");
      else
	FilePrint(f,"Sub");
	doit(node.op);
	FilePrint(f,"(");
	if Length(node.left)=1 then
	  doit(node.left[1]);
	else
	  printlist(node.left);
	fi;
	FilePrint(f,",[");
	printlist(node.right);
	FilePrint(f,"])");
      fi;
    elif t="<" or t="{*" then
      # seems to be not span, but just another variant of list
      FilePrint(f,"[");
      printlist(node.args);
      FilePrint(f,"]");
      #FilePrint(f,"Span(");
      #printlist(node.args);
      #FilePrint(f,")");
    elif t=":" then
      # ordinary List construct
      FilePrint(f,"List(");
      if node.open<>"[" then
	FilePrint(f," # ",node.open,"-list:\n",START,"  ");
      fi;

      doit(node.from);
      FilePrint(f,",",node.var,"->");
      doit(node.op);
      FilePrint(f,")");

    elif t=":mult" then
      if IsBound(node.cond) then
	str1:=List(node.cond,
	  x->Difference(List(VariablesInExpression(x),
	    y->Position(node.var,y)),[fail]));
	# which conditions to apply when
	str2:=List([1..Length(node.var)],
	  x->Filtered([1..Length(str1)],y->Maximum(str1[y])=x));
	if ForAny(str2,x->Length(x)>1) then
	  Error("multiple conditions on one variable -- still to do");
	fi;
      else
	str2:=List(node.var,x->[]);
      fi;
      # list over multiple entities
      if node.open<>"[" then
	FilePrint(f," # ",node.open,"-multilist:\n",START,"  ");
      fi;
      for i in [1..Length(node.var)-1] do
	indent(1);
	FilePrint(f,"Concatenation(List(");
	if Length(str2[i])>0 then
	  FilePrint(f,"\n",START,"Filtered(");
	  doit(node.from[i]);
	  FilePrint(f,",",node.var[i],"->");
	  doit(node.cond[str2[i][1]]);
	  FilePrint(f,")\n",START);
	else
	  doit(node.from[i]);
	fi;

	FilePrint(f,",\n",START,node.var[i],"->");
      od;
      i:=Length(node.var);
      FilePrint(f,"List(");

      if Length(str2[i])>0 then
	FilePrint(f,"\n",START,"Filtered(");
	doit(node.from[i]);
	FilePrint(f,",",node.var[i],"->");
	doit(node.cond[str2[i][1]]);
	FilePrint(f,")");
      else
	doit(node.from[i]);
      fi;

      FilePrint(f,",\n",START,"  ",node.var[i],"->");
      doit(node.op);
      FilePrint(f,")");
      for i in [1..Length(node.var)-1] do
	indent(-1);
	if i<Length(node.var)-1 then
	  FilePrint(f,")\n",START,"\b\b");
	else
	  FilePrint(f,")");
	fi;
      od;

    elif t="repmult" then
      if IsBound(node.cond) then
	str1:=List(node.cond,
	  x->Difference(List(VariablesInExpression(x),
	    y->Position(node.var,y)),[fail]));
	# which conditions to apply when
	str2:=List([1..Length(node.var)],
	  x->Filtered([1..Length(str1)],y->Maximum(str1[y])=x));
	if ForAny(str2,x->Length(x)>1) then
	  Error("multiple conditions on one variable -- still to do");
	fi;
      else
	Error("repmult without condition");
	str2:=List(node.var,x->[]);
      fi;

      # list over multiple entities
      for i in [1..Length(node.var)-1] do
	indent(1);
	FilePrint(f,"FRes(");
	if Length(str2[i])>0 then
	  FilePrint(f,"\n",START,"Filtered(");
	  doit(node.from[i]);
	  FilePrint(f,",",node.var[i],"->");
	  doit(node.cond[str2[i][1]]);
	  FilePrint(f,")\n",START);
	else
	  doit(node.from[i]);
	fi;

	FilePrint(f,",\n",START,node.var[i],"->");
      od;
      i:=Length(node.var);
      FilePrint(f,"List(");

      if Length(str2[i])>0 then
	FilePrint(f,"\n",START,"FilFirst(");
	doit(node.from[i]);
	FilePrint(f,",",node.var[i],"->");
	doit(node.cond[str2[i][1]]);
	FilePrint(f,")");
      else
	Error("missing condition in last variable");
	doit(node.from[i]);
      fi;

      FilePrint(f,",\n",START,"  ",node.var[i],"->");
      doit(node.op);
      FilePrint(f,")");
      for i in [1..Length(node.var)-1] do
	indent(-1);
	if i<Length(node.var)-1 then
	  FilePrint(f,")\n",START,"\b\b");
	else
	  FilePrint(f,")[1]");
	fi;
      od;

#    elif t="forallmult" or t="existsmult" then
#      if node.varset<>false then
#        doit(node.varset);
#	FilePrint(f,":=");
#      fi;
#      if t="forall" then
#	FilePrint(f,"ForAll(");
#      else
#	FilePrint(f,"ForAny(");
#      fi;
#      doit(node.from);
#      FilePrint(f,",");
#      doit(node.var);
#      FilePrint(f,"->");
#      doit(node.cond);
#      FilePrint(f,")");

    elif t="forall" or t="exists" then
      if node.varset<>false then
        doit(node.varset);
	FilePrint(f,":=");
      fi;
      if t="forall" then
	str1:="ForAll";
      else
	str1:="ForAny";
      fi;
      if IsList(node.from) then
        for i in [1..Length(node.from)] do
	  FilePrint(f,str1,"(");
	  doit(node.from[i]);
	  indent(1);
	  FilePrint(f,",\n",START);
	  FilePrint(f,node.var.name[i]); # the way its constructed a silly wrapper
	  FilePrint(f,"->");
	od;
	if IsList(node.cond) then
	  if Length(node.cond)>1 then Error("multicond");fi;
	  doit(node.cond[1]);
	else
	  doit(node.cond);
	fi;
        for i in [1..Length(node.from)] do
	  indent(-1);
	  FilePrint(f,")");
	od;

      else
	FilePrint(f,str1,"(");
	doit(node.from);
	FilePrint(f,",");
	doit(node.var);
	FilePrint(f,"->");
	doit(node.cond);
	FilePrint(f,")");
      fi;

    elif t="inlinecase" then
      FilePrint(f,"# translated case< statement\n",START);
      FilePrint(f,"function(xxx)\n",START);
      for i in [1..Length(node.conditions)] do
        FilePrint(f,"  ");
        if i>1 then FilePrint(f,"el");fi;
        FilePrint(f,"if xxx=");
        doit(node.conditions[i][1]);
        FilePrint(f," then return ");
        doit(node.conditions[i][2]);
        FilePrint(f,";\n",START);
      od;
      FilePrint(f,"else Error();fi;end(");
      doit(node.var);
      FilePrint(f,")");
    elif t=":F" then
      # is it a List/Filtered construct ?
      str1:=node.op.type<>"I" or node.op.name<>node.var;
      if str1 then
	FilePrint(f,"List(");
      fi;
      # ordinary Filtered construct 
      FilePrint(f,"Filtered(");
      doit(node.from);
      FilePrint(f,",",node.var,"->");
      doit(node.cond);
      FilePrint(f,")");
      if str1 then
	FilePrint(f,",",node.var,"->");
	doit(node.op);
	FilePrint(f,")");
      fi;

    elif t=":1" then
      FilePrint(f,"First(");
      doit(node.from);
      FilePrint(f,",",node.var,"->");
      doit(node.cond);
      FilePrint(f,")");

    elif t="&" then
      if node.op="+" then
        FilePrint(f,"Sum(");
      elif node.op="*" then
        FilePrint(f,"Product(");
      elif node.op="cat" then
        FilePrint(f,"Concatenation(");
      elif node.op="join" then
        FilePrint(f,"Union(");
      elif node.op="meet" then
        FilePrint(f,"Intersection(");
      else
        Error("operation ",node.op," not yet done");
      fi;
      doit(node.arg);
      FilePrint(f,")");
    elif t="rec" then
      FilePrint(f,"rec(");
      indent(1);
      for i in [1,3..Length(node.assg)-1] do
	if i>1 then
	  FilePrint(f,",\n",START);
	fi;
	FilePrint(f,node.assg[i].name,":=");
	doit(node.assg[i+1]);
      od;
      indent(-1);
      FilePrint(f,")");
    elif t="if" then
      if node.cond.type="exists" and IsBound(node.cond.varset) and
	node.cond.varset<>false then 
	if IsBound(node.isElif) then
	  indent(1);
	  FilePrint(f,"else\n",START);
	  Unbind(node.isElif); # no special elif treatment --must be included if.
	fi;
	# implicit assignment in `if' condition

	doit(node.cond.varset);
	FilePrint(f,":=");
	if IsList(node.cond.from) then
	  # this exists with assignment is really the assignment being a
	  # repmult.
	  i:=ShallowCopy(node.cond);
	  i.type:="repmult";
	  i.var:=i.var.name;
	  doit(i);
	  FilePrint(f,";\n",START);
	else
	  FilePrint(f,"First(");
	  doit(node.cond.from);
	  FilePrint(f,",");
	  doit(node.cond.var);
	  FilePrint(f,"->");
	  doit(node.cond.cond);
	  FilePrint(f,");\n",START);
	fi;

	FilePrint(f,"if ");
	doit(node.cond.varset);
	FilePrint(f,"<>fail");
      else
	if IsBound(node.isElif) then
	  FilePrint(f,"elif ");
	else
	  FilePrint(f,"if ");
	fi;

	doit(node.cond);
      fi;

      indent(1);
      FilePrint(f," then\n",START);

      for i in node.block do
	doit(i);
      od;
      indent(-1);

      str1:=true;
      if IsBound(node.elseblock) then
	# is it an ``else if'' case -- translate to elif
	if node.elseblock[1].type="if" and IsBound(node.elseblock[1].isElif) then
	  FilePrint(f,"\b\b");
	  for i in node.elseblock do
	    doit(i);
	  od;
	  if not (node.elseblock[1].cond.type="exists" and
	    IsBound(node.elseblock[1].cond.varset)) then 
	    str1:=false;
	  else
	    indent(-1);
	  fi;
	else
	  FilePrint(f,"\b\belse\n");
	  indent(1);
	  FilePrint(f,START);
	  for i in node.elseblock do
	    doit(i);
	  od;
	  indent(-1);
	fi;

      fi;
      if str1 then
	FilePrint(f,"\b\bfi;\n",START);
      fi;

    elif t="try" then
      FilePrint(f,"# TODO: try \n");
    elif t="while" then
      FilePrint(f,"while ");
      doit(node.cond);
      indent(1);
      FilePrint(f," do\n",START);
      for i in node.block do
	doit(i);
      od;
      indent(-1);
      #FilePrint(f,"\n");
      FilePrint(f,"\b\bod;\n",START);
    elif t="for" then
      FilePrint(f,"for ");
      doit(node.var);
      FilePrint(f," in ");
      doit(node.from);
      indent(1);
      FilePrint(f," do\n",START);
      for i in node.block do
	doit(i);
      od;
      indent(-1);
      FilePrint(f,"\b\bod;\n",START);

    elif t="repeat" then
      indent(1);
      FilePrint(f,"repeat\n",START);
      for i in node.block do
	doit(i);
      od;
      indent(-1);
      FilePrint(f,"\n",START);
      FilePrint(f,"until ");
      doit(node.cond);
      FilePrint(f,";\n",START);
    elif t="case" then
      for i in [1..Length(node.cases)] do
	if i>1 then
	  FilePrint(f,"\b\bel");
	fi;
	FilePrint(f,"if ");
	if IsRecord(node.cases[i][1]) then
	  doit(node.test);
	  FilePrint(f,"=");
	  doit(node.cases[i][1]);
	else
	  for a in [1..Length(node.cases[i][1])] do
	    if a>1 then
	      FilePrint(f," or ");
	    fi;
	    doit(node.test);
	    FilePrint(f,"=");
	    doit(node.cases[i][1][a]);
	  od;
	fi;
	indent(1);
	FilePrint(f," then\n",START);
	for b in node.cases[i][2] do
	  doit(b);
	od;
	indent(-1);
      od;
      if IsBound(node.elsecase) then
	FilePrint(f,"\b\belse\n");
	indent(1);
	FilePrint(f,START);
	for i in node.elsecase do
	  doit(i);
	od;
	indent(-1);
      fi;
      FilePrint(f,"\b\bfi;\n",START);
    elif t="sub" or t="ext" then
      if t="sub" then
	FilePrint(f,"SubStructure(");
      else
	FilePrint(f,"ExtStructure(");
      fi;
      doit(node.within);
      FilePrint(f,",");
      for i in [1..Length(node.span)] do
	if i=2 then
	  FilePrint(f,",#TODO CLOSURE\n",START,"  ");
	elif i>2 then
	  FilePrint(f,",");
	fi;

	doit(node.span[i]);
      od;
      CloseParenthesisOptions(node);
      #FilePrint(f,")");
    elif t="quo" then
      FilePrint(f,"\n",START,"# QUOTIENT\n",START);
      if IsBound(node.format) then
	FilePrint(f,"# FORMAT ");
	doit(node.format);
	FilePrint(f,"\n",START);
      fi;
      doit(node.nominator);
      FilePrint(f,"/");
      doit(node.denominator);
      if IsBound(node.options) then
	FilePrint(f," # OPTIONS ");
        CloseParenthesisOptions(node);
	FilePrint(f,"\n",START);
      fi;
    elif t="quofp" then
      # finitely presented group
      doit(node.nominator);
      FilePrint(f,"/[");
      indent(1);
      str1:=false;
      for i in node.denominator do
        if str1 then FilePrint(f,",\n",START);fi;
        str1:=true;
        if i.type="B=" then
          # relation
          doit(i.left);
          FilePrint(f,"/");
          if i.right.type[1]='B' then
            # binary operation, neds parentheses
            FilePrint(f,"(");
            doit(i.right);
            FilePrint(f,")");
          else
            doit(i.right);
          fi;
        else
          # relator
          doit(i);
        fi;
      od;
      indent(-1);
      FilePrint(f,"]");
    elif t="assert" then
      FilePrint(f,"Assert(1,");
      doit(node.cond);
      FilePrint(f,");\n",START);

    elif t="require" then
      FilePrint(f,START,"\b\bif not ");
      doit(node.cond);
      indent(1);
      FilePrint(f," then\n",START,"Error(");
      doit(node.mess);
      indent(-1);
      FilePrint(f,");\n",START);
      FilePrint(f,"fi;\n",START);

    elif t="select" then
      FilePrint(f,"# rewritten select statement\n",START);
      FilePrint(f,"function(xxx)if xxx then return ");
      doit(node.yescase);
      FilePrint(f,";else return ");
      doit(node.nocase);
      FilePrint(f,";fi;end(");
      doit(node.cond);
      FilePrint(f,")");

      #FilePrint(f,"SELECT(");
      #doit(node.cond);
      #FilePrint(f," then ");
      #doit(node.yescase);
      #FilePrint(f," else ");
      #doit(node.nocase);
      #FilePrint(f,")");
    elif t="hom" or t="map" then
      if t="hom" then
	t:="Homomorphism";
      else
	t:="GeneralMapping";
      fi;
      if node.kind="images" then
        FilePrint(f,"Group",t,"ByImages(");
	doit(node.domain);
	FilePrint(f,",");
	doit(node.codomain);
	indent(1);
	FilePrint(f,",\n",START,"GeneratorsOfGroup(");
	doit(node.domain);
	FilePrint(f,"),");
	doit(node.images);
      elif node.kind="genimg" then
        FilePrint(f,"Group",t,"ByImages(");
	doit(node.domain);
	FilePrint(f,",");
	doit(node.codomain);
	indent(1);
	FilePrint(f,",\n",START);
        FilePrint(f,"GeneratorsOfGroup(");
	doit(node.domain);
	FilePrint(f,"),\n",START,"[");
	printlist(node.images);
        FilePrint(f,"]");

      elif node.kind="fct" then
        FilePrint(f,"Group",t,"ByFunction(");
	doit(node.domain);
	FilePrint(f,",");
	doit(node.codomain);
	indent(1);
	FilePrint(f,",\n",START);
	doit(node.var);
	FilePrint(f,"->");
	doit(node.expr);
      else
        Error("unknown kind ",node.kind);
      fi;
      CloseParenthesisOptions(node);
      indent(-1);

    elif t="error" then
      FilePrint(f,"Error(");
      printlist(node.values,"\"");
      FilePrint(f,");\n",START);
    elif t="break" then
      FilePrint(f,"break");
      if node.var.type<>"none" then
	FilePrint(f," ");
	doit(node.var);
      fi;
      FilePrint(f,";\n",START);
    elif t="continue" then
      FilePrint(f,"continue;\n",START);
    elif t="delete" then
      for i in node.del do
        FilePrint(f,"Unbind(");
	doit(i);
        FilePrint(f,");\n",START);
      od;
    elif t="none" then
      #Error("UUU");
      FilePrint(f,"#NOP\n",START);
    elif t="wh" then
      FilePrint(f,"# FOLLOWING COMMAND IS `WHERE` \n",START);
      i:=node.assg.left;
      if not IsList(i) then i:=[i];fi;
      i:=Filtered(i,x->ForAny(localsstack,y->x in y));
      if Length(i)>0 then
	Error("where is overwriting locals -- TODO");
      fi;
      doit(node.assg);
    else
      Error("NEED TO DO  type ",t," ");
      #Error("type ",t," not yet done");
    fi;
  end;

  PrintTo(f,
    "#  File converted from Magma code -- requires editing and checking\n",
    "#  Magma -> GAP converter, ",MGMCONVER, " by AH\n\n");

  t:="Global Variables used: ";
  for i in [1..Length(l.used)] do
    if i>1 then Append(t,", ");fi;
    Append(t,l.used[i]);
  od;
  mulicomm(f,t);
  FilePrint(f,"\n");

  t:="Defines: ";
  for i in [1..Length(l.defines)] do
    if i>1 then Append(t,", ");fi;
    Append(t,l.defines[i]);
  od;
  mulicomm(f,t);
  FilePrint(f,"\n");

  declared:=Concatenation(l.mustdeclare,l.forward);

  for i in declared do
    FilePrint(f,"DeclareGlobalFunction(\"",traid(i),"\");\n\n");
  od;

  for i in l.code do
    doit(i);
  od;
  FilePrint(f,"\n");
  SizeScreen(sz);

end;

MagmaConvert:=function(arg)
local infile, f,l;

  infile:=arg[1];
  l:=MgmParse(infile);
  l.clashes:=[];
  l.depends:=[];
  l.mustdeclare:=[];
  l.namespace:=[];

  if Length(arg)>1 and IsString(arg[2]) then
    f:=OutputTextFile(arg[2],false);
  else
    f:=fail;
  fi;

  if f=fail then
    f:=OutputTextUser();
  fi;

  GAPOutput(l,f);
  CloseStream(f);
end;


Project:=function(dir,pkgname)
local a,b,c,d,f,l,i,j,r,uses,defs,import,depend,order,subf;
  # TODO: Move into common namespace
  a:=DirectoryContents(Concatenation(dir,"/magma"));
  subf:=Filtered(a,x->x[1]<>'.' 
    and DirectoryContents(Concatenation(dir,"/magma/",x))<>fail);
  a:=Filtered(a,x->Length(x)>2 and x{[Length(x)-1..Length(x)]}=".m");
  for i in subf do
    Exec(Concatenation("mkdir ",dir,"/translate/",i));
    r:=DirectoryContents(Concatenation(dir,"/magma/",i));
    r:=Filtered(r,x->Length(x)>2 and x{[Length(x)-1..Length(x)]}=".m");
    Append(a,List(r,x->Concatenation(i,"/",x)));
  od;
  l:=[];

  for i in a do
    c:=i{[1..Length(i)-2]};
    Print("Reading ",c,"\n");
    r:=MgmParse(Concatenation(dir,"/magma/",c,".m"));
    r.filename:=c;
    Add(l,r);
    #MagmaConvert(Concatenation(dir,"/magma/",c,".m"),Concatenation(dir,"/translate/",c,".g"));
  od;
  uses:=Union(List(l,x->x.used)); # globals used
  defs:=Union(List(l,x->x.defines)); # globals defined
  import:=[];
  for i in l do
    for j in i.import do
      if not j.file in a then
        AddSet(import,j);
      fi;
    od;
  od;

  for i in [1..Length(l)] do
    c:=[];
    d:=[];
    for j in [1..Length(l)] do
      if j<>i then
        c:=Union(c,Intersection(l[i].defines,l[j].defines));
      fi;
      d:=Union(d,List(Filtered(l[j].import,x->x.file=a[i]),x->x.func));
    od;
    l[i].clashes:=c;
    l[i].depends:=Set(List(l[i].import,x->x.file));
    l[i].dependnum:=List(l[i].depends,x->PositionProperty(l,y->Concatenation(y.filename,".m")=x));
    l[i].dependall:=ShallowCopy(l[i].dependnum);
    l[i].mustdeclare:=d;
    l[i].namespace:=defs;
  od;

  # full dependencies
  repeat
    f:=true;
    for i in [1..Length(l)] do
      for j in l[i].dependall do
	if j<>fail and not IsSubset(l[i].dependall,l[j].dependnum) then
	  f:=false;
	  l[i].dependall:=Union(l[i].dependall,l[j].dependnum);
	fi;
      od;
    od;
  until f;

  order:=[1..Length(l)];
  # bubblesort as this is not a proper total order
  for i in [1..Length(l)] do
    for j in [i+1..Length(l)] do
      if (a[order[j]] in l[order[i]].depends or
	Length(l[order[j]].depends)<Length(l[order[i]].depends))
	and not a[order[i]] in l[order[j]].depends  then
	c:=order[i];order[i]:=order[j];order[j]:=c;
      fi;
    od;
  od;

  f:=Filtered(order,x->Length(l[x].mustdeclare)=0);
  order:=Concatenation(Filtered(order,x->not x in f),f);
  Print("No dependencies from ",
    List(l{f},x->x.filename),"\n");

  f:=OutputTextFile(Concatenation(dir,"/translate/read.g"),false);
  AppendTo(f,"ENTER_NAMESPACE(",pkgname,")\n");
  for i in order do
    AppendTo(f,"Read(\"",l[i].filename,".g\");\n");
  od;
  AppendTo(f,"LEAVE_NAMESPACE(",pkgname,")\n");
  CloseStream(f);

  for i in order do
    Print("Processing ",l[i].filename,"\n");
    f:=OutputTextFile(Concatenation(dir,"/translate/",l[i].filename,".g"),false);
    GAPOutput(l[i],f);
    CloseStream(f);
  od;

  return List(l,x->[x.filename,List(l{Filtered(x.dependall,IsInt)},y->y.filename)]);
  #return a;
end;

PathnamesMagmaFiles:=function(path)
local d;
  d:=DirectoryContents(path);
  d:=Filtered(d,x->Length(x)>2 and x{[Length(x)-1,Length(x)]}=".m");
  return List(d,x->Concatenation(path,"/",x));
end;

