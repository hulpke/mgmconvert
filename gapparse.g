# GAP parser
GAPPARSE:="version 0.1, 7/1/19"; # version number
# (C) Alexander Hulpke

LINEWIDTH:=80;
COMMENTWIDTH:=LINEWIDTH-3;


TOKENS:=[ "and", "do", "elif", "else", "end", "fi", "for", "function",
"if", "in", "locval", "mod", "not", "od", "or", "repeat","local","rec",
"return", "then", "until", "while", "break", "rec", "continue",
":=",",","\"","(",")","[","]","{","}",";","<>","<",">","=","<=",">=",
"->","!.","![",".","..","%%%"];

# binary operators
BINOPS:=["+","-","*","/","^","div","mod","in",".","!.","->","=","<>",
"<=",">=","<",">","and","or"];

PAROP:=["+","-","div","mod","in"];

OPRECED:=[".","@","@@","![","!.",
"^", "*", "/", "div", "mod", "+", "-",
"not", "and", "or", "=", "<>","<=",">=","<",">",":=", "->","in"];

DOTPREF:=["FindHomMethodsProjective","SLCR","RECOG"]; # make records a.b identifier names

TOKENS:=Union(TOKENS,BINOPS);
TOKENS:=Union(TOKENS,PAROP);

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

GapParse:=function(file)
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
      if Length(a)>=1 and PositionSublist(a,"#")<>fail then
        p:=PositionSublist(a,"#");
	l:=Concatenation(l," ",a{[1..p-1]});
	eatblank();
	a:=a{[p+2..Length(a)]};
        # 1-line comment
	Add(comment,a);
	a:="%%%";
      fi;
      l:=Concatenation(l," ",a);
      #if PositionSublist(l,"two_power")<>fail then Error("ZUGU");fi;
    od;
    eatblank();
  end;

  IsAtToken:=function(str)
    return tok[tnum][2]=str and tok[tnum][1]<>"S";
  end;

  ExpectToken:=function(arg)
  local s,o,i,a;
    s:=arg[1];
    if Length(arg)>1 then 
      o:=arg[2];
    else
      o:="";
    fi;
    if tok[tnum][2]<>s then Error("expect ",s," but got ",tok[tnum]);fi;
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
    if l[1] in CHARSIDS  then
      i:=1;
      # a word-like identifier
      while l[i] in CHARSIDS or (l[i]='.' and l{[1..i-1]} in DOTPREF) do
        i:=i+1;
      od;
      a:=l{[1..i-1]};
      l:=l{[i..Length(l)]};eatblank();
      i:=Position(TOKENS,a);

      if i=fail then
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
      elif a="is" then
        Add(tok,["O",":="]);
      else
        Add(tok,["K",TOKENS[i]]);
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
	  Add(tok,["\043",comment[1]]);
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


  ReadBlock:=function(endkey)
  local l,e,a,aif,b,c,d,f,locals,kind,i;


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

      if e[1]="#" then
	Add(l,rec(type:="co",text:=e[2]));
      elif e[1]="K" then
	# keyword

	if e[2]="if" then
	  a:=ReadExpression(["then",";"]);
	  if IsAtToken("then") then
	    ExpectToken("then");
	  else
	    Error("confused if");
	  fi;
	  b:=ReadBlock(["else","fi","elif"]:inner);
	  locals:=Union(locals,b[1]);
	  a:=rec(type:="if",cond:=a,block:=b[2]);
	  Add(l,a);
	  while IsAtToken("elif") do
	    ExpectToken("elif");
	    c:=ReadExpression(["then"]);
	    ExpectToken("then");
	    b:=ReadBlock(["else","fi","elif"]:inner);
	    locals:=Union(locals,b[1]);
	    a.elseblock:=[rec(type:="if",isElif:=true,cond:=c,block:=b[2])];
	    a:=a.elseblock[1]; # make elif an iterated else if
	  od;
	  if IsAtToken("else") then
	    ExpectToken("else");
	    b:=ReadBlock(["fi"]:inner);
	    locals:=Union(locals,b[1]);
	    a.elseblock:=b[2];
	  fi;
	  ExpectToken("fi");
	  ExpectToken(";",1);

	elif e[2]="while" then
	  a:=ReadExpression(["do"]);
	  ExpectToken("do");
	  b:=ReadBlock(["od"]:inner);
	  locals:=Union(locals,b[1]);
	  a:=rec(type:="while",cond:=a,block:=b[2]);
	  ExpectToken("od");
	  ExpectToken(";",2);
	  Add(l,a);
	elif e[2]="for" then
	  a:=rec(type:="I",name:=tok[tnum][2]);
	  tnum:=tnum+1;
	  if IsAtToken("in") then
	    ExpectToken("in");
	    c:=ReadExpression(["do"]);
	  else
            Error("wrong for loop");
	  fi;

	  ExpectToken("do");
	  b:=ReadBlock(["od"]:inner);
	  locals:=Union(locals,b[1]);
	  AddSet(locals,a.name);
	  a:=rec(type:="for",var:=a,from:=c,block:=b[2]);
	  ExpectToken("od");
	  ExpectToken(";",3);
	  Add(l,a);

	elif e[2]="repeat" then
	  b:=ReadBlock(["until"]);
	  ExpectToken("until");
	  locals:=Union(locals,b[1]);
	  a:=ReadExpression([";"]);
	  a:=rec(type:="repeat",cond:=a,block:=b[2]);
	  Add(l,a);
	  ExpectToken(";",5);

	elif e[2]="return" then
	  a:=[];
          b:=ReadExpression([";"]);
          Add(a,b);
	  ExpectToken(";",6);
	  Add(l,rec(type:="return",values:=a));

        elif e[2]="continue" then
	  ExpectToken(";",-8);
	  Add(l,rec(type:="continue"));
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

	elif e[2]="break" then
	  a:=ReadExpression([";"]);
	  Add(l,rec(type:="break",var:=a));
	  ExpectToken(";",11/3);

	else
	  problemarea();
	  Error("other keyword ",e);
	fi;
      elif e[1]="I" or e[2]="$$" then
	e:=[e[1],e[2]];
	tnum:=tnum-1;
	if e[2]="$$" then tok[tnum]:=["I",thisfctname]; fi;
	a:=ReadExpression([":=",";"]);
	if a.type="I" then
	  AddSet(locals,a.name);
	fi;

	e:=tok[tnum];
	tnum:=tnum+1;
	if e[1]<>"O" then 
	  problemarea();
	  Error("missing separator");
	fi;
        c:=fail;

	if e[2]=":=" then
	  # assignment
	  b:=ReadExpression([";"]);

	  a:=rec(type:="A",left:=a,right:=b);
	  Add(l,a);
	  ExpectToken(";",14);
	  if endkey=false and IsBound(a.left.name) then
	    # top-level assignment -- global variable
	    #Print("> ",a.left.name," <\n");
	    AddSet(defines,a.left.name);
	  fi;
	elif e[2]=";" then
	  a.line:=true; # only command in line
	  Add(l,a);
	else
	  problemarea();
	  Error("anders");
	fi;
      elif e[2]=";" then
	# empty command?
      else 
	problemarea();
	Error("cannot deal with token ",e);
      fi;
    od;

    return [locals,l];
  end;


  # read identifier, call, function 
  ReadExpression:=function(stops)
  local obj,e,a,b,c,argus,procidf,doprocidf,op,assg,val,pre,lbinops,
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
	  # array indexing -- translate to iterated index by opening a parenthesis and keeping
	  # position
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

      if tok[tnum][1]="S" then
        tnum:=tnum+1;
        return rec(type:="S",value:=e);
      elif e in stops then
	a:=rec(type:="none");
      elif e="(" or e="\\(" then
        #problemarea();Error("huh");
	tnum:=tnum+1;
        a:=ReadExpression([")",","]);
	if IsAtToken(",")  then 
	  # pair, permutation
	  ExpectToken(",");
	  b:=ReadExpression([")",","]);
	  if IsAtToken(")") and tok[tnum+1][2]<>"(" then
	    # pair
	    ExpectToken(")");
	    a:=rec(type:="pair",left:=a,right:=b);
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
      elif e="{" then
        Error("sublist");
      elif e="[" then
	open:=e;
        close:="]";
        ltype:="V";
	ExpectToken(open);
	l:=[];
	b:=fail;
	if IsAtToken(close) then
	  #empty list
	  tnum:=tnum;
	else

          while not IsAtToken(close) or IsAtToken(".,") do
            a:=ReadExpression([close,",",".."]);
            if IsAtToken("..") then
              ExpectToken("..");
              e:=ReadExpression([close]); #part 2
              if Length(l)=0 then
                a:=rec(type:="R",from:=a,to:=e);
              else
                a:=rec(type:="R",from:=l[1],to:=e,second:=a);
              fi;
              ExpectToken(close);
              return a;
            elif IsAtToken(",") then
              Add(l,a);
              ExpectToken(",");
            elif IsAtToken("close") then
              Add(l,a);
            fi;
          od;

	fi;
	ExpectToken(close);
        a:=rec(type:=ltype,args:=l);
	if b<>fail then
	  a.force:=b;
	fi;

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
        elif e="rec" then
          ExpectToken("(");
          argus:=[];
          while not IsAtToken(")") do
            a:=ReadExpression([":=",")"]);
            if IsAtToken(":=") then
              ExpectToken(":=");
              b:=ReadExpression([",",")"]);
              Add(argus,[a,b]);

              if IsAtToken(",") then ExpectToken(",");fi;
            fi;
          od;
          ExpectToken(")");
          a:=rec(type:="rec",components:=argus);
          
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
	  if e="(" then
	    # function call
	    assg:=[];
	    tnum:=tnum+1;
	    argus:=[];
	    while (tok[tnum][1]="S" or tok[tnum][2]<>")")  and tok[tnum][2]<>":" do
	      b:=ReadExpression([",",")",":"]);
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
          elif e="{" then
            tnum:=tnum+1;
	    b:=ReadExpression(["}"]);
            ExpectToken("}");
            a:=rec(type:="SL",var:=a,at:=b);
	  elif e="[" or e="![" then
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
	    ExpectToken(">",5);
	    a:=rec(type:="<>",op:=pre,left:=b,right:=c);

	  elif e="," and stops=[")"] then
	    # expression '(P,C)'
	    ExpectToken(",");
	    b:=ReadExpression(stops);
	    a:=rec(type:="pair",left:=a,right:=b);
	  else
	    problemarea();
	    Error("eh!");
	  fi;

	  e:=eset();
	od;
      fi;
      return a;
    end;

    if tok[tnum]=["K","function"] then
      # function
      fcomment:="";
      thisfctname:=tok[tnum-2][2];
      tnum:=tnum+1;
      ExpectToken("(");
      argus:=[];
      locopt:=[];
      while not IsAtToken(")") do
        a:=ReadExpression([")",","]);
        Add(locopt,a.name);
        if IsAtToken(",") then ExpectToken(",");fi;
      od;

      ExpectToken(")");

      if IsAtToken("local") then 
        ExpectToken("local");
        while not IsAtToken(";") do
          a:=ReadExpression([";",","]);
          Add(locopt,a.name);
          if IsAtToken(",") then ExpectToken(",");fi;
        od;
        ExpectToken(";");
      fi;

      a:=ReadBlock(["end"]:inner);
      tnum:=tnum+1; # do end .... token

      a:=rec(type:="F",args:=argus,locals:=Union(a[1],locopt),block:=a[2]);
      if Length(fcomment)>0 then
        a.comment:=fcomment;
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


  costack:=[];
  cmdstack:=[];
  tnum:=1; # indicate in token list

  # actual work
  a:=ReadBlock(false);
  return a[2];


end;

GlobalIdsIn:=function(node)
local list,recurse,b;

  recurse:=function(n,ignore)
  local l,lign,use,i;
    l:=[];
    if n.type="I" then
      if not (n.name in ignore or n.name in NAMES_SYSTEM_GVARS) then
       Add(l,n.name);
      fi;
    elif n.type="F" then
      lign:=Union(ignore,n.args,n.locals);
      for i in n.block do
        use:=recurse(i,lign);
        l:=Union(l,use);
      od;
    elif n.type="B->" then
      lign:=Union(ignore,[n.left.name]);
      use:=recurse(n.right,lign);
      l:=Union(l,use);
    elif n.type="B." or n.type="B!." then
      l:=recurse(n.left,ignore);
    elif n.type[1]='B' then
      # binary op
      use:=Union(recurse(n.left,ignore),recurse(n.right,ignore));
      l:=use;
    elif n.type="A" then
      # asignment
      use:=Union(recurse(n.left,ignore),recurse(n.right,ignore));
      l:=use;
    elif n.type="L" or n.type="SL" then
      # list access
      l:=Union(l,recurse(n.var,ignore));
      use:=recurse(n.at,ignore);
      l:=Union(l,use);
    elif n.type="C" then
      l:=Union(l,recurse(n.fct,ignore));
      for i in n.args do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;
    elif n.type="return" then
      for i in n.values do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;

    elif n.type="if" then
      l:=Union(l,recurse(n.cond,ignore));
      b:=n.block;
      if IsBound(n.elseblock) then
        b:=Concatenation(b,n.elseblock);
      fi;
      for i in b do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;

    elif n.type="for" then
      l:=Union(l,recurse(n.var,ignore));
      l:=Union(l,recurse(n.from,ignore));
      for i in n.block do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;

    elif n.type="while" or n.type="repeat" then
      l:=Union(l,recurse(n.cond,ignore));
      for i in n.block do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;

    elif n.type="V" then
      for i in n.args do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;
    elif n.type="paren" or n.type[1]='U' then
      l:=recurse(n.arg,ignore);
    elif n.type="C" or n.type="CA" then
      l:=Union(l,recurse(n.fct,ignore));
      for i in n.args do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;

    elif n.type="return" then
      for i in n.values do
        use:=recurse(i,ignore);
        l:=Union(l,use);
      od;

    elif n.type="rec" then
      for i in n.components do
        use:=recurse(i[2],ignore);
        l:=Union(l,use);
      od;

    elif n.type="R" then
      use:=recurse(n.from,ignore);
      l:=Union(l,use);
      use:=recurse(n.to,ignore);
      l:=Union(l,use);
      if IsBound(n.second) then
        use:=recurse(n.second,ignore);
        l:=Union(l,use);
      fi;

    elif n.type in ["N","S","perm","co","none","continue","break"] then
      # ignore
    else
      Error("type: ",n.type);
    fi;
    return l;
  end;
  return recurse(node,[]);
end;

FindDependencies:=function(l)
local provides,i,r;
  provides:=[];
  for i in l do
    if i.type="A" and i.left.type="I" then
      r:=rec(name:=i.left.name,uses:=GlobalIdsIn(i.right));
      if Length(r.name)>2 then Add(provides,r);fi;
    elif i.type="C" and IsBound(i.fct.name) and Length(i.fct.name) >7 
      and i.fct.name{[1..7]}="Install" then
      if IsString(i.args[1]) then
        r:=rec(name:=i.args[1],uses:=GlobalIdsIn(i.args[Length(i.args)]));
        if Length(r.name)>2 then Add(provides,r);fi;
      fi;
    fi;
  od;
  return provides;
end;

PrintDependencies:=function(infiles,textfile,graph)
local alle,i,j,l,dep,allfct,new,out,nam,orphan,ids,solo;
  alle:=[];
  for i in infiles do
    Print("file ",i,"\n");
    l:=GapParse(i);
    Append(alle,l);
  od;
  dep:=FindDependencies(alle);
  dep:=Unique(dep);
  SortBy(dep,x->x.name);
  PrintTo(textfile,"#created automatically from code\n");
  for i in dep do
    AppendTo(textfile,i.name," uses:\n");
    for j in i.uses do 
      AppendTo(textfile,"    ",j,"\n");
    od;
    AppendTo(textfile,"\n");
  od;
  PrintTo(graph,"digraph lattice {\n","size = \"6,6\";\n");

  new:=List(dep,x->x.name);
  allfct:=Union(List(dep,x->x.uses));
  out:=Difference(allfct,new); # external used
  orphan:=Difference(new,allfct); # defined, not used
  new:=Difference(new,orphan); # defined, used
  allfct:=Union(out,orphan,new);
  allfct:=List(allfct,Immutable);
  solo:=Filtered(orphan,x->First(dep,y->y.name=x).uses=[]);
  Sort(allfct);
  ids:=[];
  for i in [1..Length(allfct)] do
    ids[i]:=Concatenation("n",String(i));
    if not allfct[i] in solo then
      AppendTo(graph,"\"",ids[i],"\" [label=\"",allfct[i],"\"");
      if allfct[i] in new then AppendTo(graph,", shape=plaintext");fi;
      if allfct[i] in orphan then AppendTo(graph,", shape=oval");fi;
      AppendTo(graph,"];\n");
    fi;
  od;
  for i in dep do
    for j in i.uses do
      AppendTo(graph,"\"",ids[Position(allfct,i.name)],"\" -> \"",
        ids[Position(allfct,j)],"\";\n");
    od;
  od;
  AppendTo(graph,"}\n");
end;

