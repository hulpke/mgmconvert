# Library of utility functions to aid in Magma code translation

# two list-type functions tha are used in the translation of rep{

# list of first elt satisfying condition or empty list
BindGlobal("FilFirst",function(l,cond)
local x;
  for x in l do
    if cond(x) then
      return [x];
    fi;
  od;
  return [];
end);

# first for which func does not return empty list
BindGlobal("FRes",function(l,func)
local x,a;
  for x in l do
    a:=func(x);
    if Length(a)>0 then
      return a;
    fi;
  od;
  return fail;
end);


# generic subgroup generator, use in place of `SubStructure' if it is
# groups. Should be improved to use more `closure'.
SubgroupContaining:=function(arg)
local P,gens,i;
  P:=arg[1];
  gens:=[];
  for i in [2..Length(arg)] do
    if IsGroup(arg[i]) then
      Append(gens,GeneratorsOfGroup(arg[i]));
    elif IsIdenticalObj(FamilyObj(arg[i]),FamilyObj(One(P))) then
      Add(gens,arg[i]);
    elif IsList(arg[i]) then
      Append(gens,arg[i]);
    else
      Error("don't know what to do with object");
    fi;
  od;
  return SubgroupNC(P,gens);
end;

DeclareGlobalFunction("Submatrix");
InstallGlobalFunction(Submatrix,function(m,a,b,c,d)
  return m{[a..c]}{[b..d]};
end);

# hom is homomorphism defined on fp group
# l is words given by numbers 
DeclareGlobalFunction("WordlistSubgroup");
InstallGlobalFunction(WordlistSubgroup,function(G,l,hom,arg)
local fp,fam;
  fp:=Source(hom);
  fam:=FamilyObj(One(FreeGroupOfFpGroup(fp)));
  l:=List(l,x->AssocWordByLetterRep(fam,x));
  fam:=FamilyObj(One(fp));
  l:=List(l,x->ElementOfFpGroup(fam,x));
  l:=List(l,x->ImagesRepresentative(hom,x));
  l:=SubgroupNC(G,l);
  if Length(arg)>0 then
    SetSize(l,arg[1]);
  fi;
  return l;
end);

DeclareGlobalFunction("MatrixByEntries");

InstallGlobalFunction(MatrixByEntries,function(f,nr,nc,entries)
local i,m,o;
  if ForAll(entries,x->IsList(x) and Length(x)=3) then
    m:=NullMat(nr,nc,f);
    o:=One(f);
    for i in entries do
      m[i[1]][i[2]]:=i[3]*o;
    od;
  else
    if nr*nc<>Length(entries) then
      Error("format?");
    fi;
    m:=List([1..nr],x->entries{[1+nc*(x-1)..nc*x]}*o);
  fi;

  if IsFFECollection(f) then
    m:=ImmutableMatrix(f,m);
  fi;
  return m;
end);

DeclareGlobalFunction("SparseMatrix");

InstallGlobalFunction(SparseMatrix,function(arg)
local R,m,n,l,one,i,a;
  if Length(arg)=3 then
    R:=Cyclotomics;
    m:=arg[1];
    n:=arg[2];
    l:=arg[3];
  else
    R:=arg[1];
    m:=arg[2];
    n:=arg[3];
    l:=arg[4];
  fi;
  a:=NullMat(m,n,R);
  one:=One(R);
  if not IsList(l[1]) then
    m:=1;
    n:=1;
    while n<>Length(l) do
      n:=n+1;
      for i in [1..l[n-1]] do
        a[m][l[n]]:=one*l[n+1];
	n:=n+2;
      od;
      m:=m+1;
    od;
  else
    Error("similar format as by entries");
  fi;

  if IsFFECollection(R) then
    a:=ImmutableMatrix(R,a);
  fi;
  return a;
end);

DeclareGlobalFunction("ScalarMat");

InstallGlobalFunction(ScalarMat,function(dim,s)
  return s*IdentityMat(dim,s);
end);

# GO, SO etc in magma are defined with different generators than in GAP and
# it is not clear that the forms are the same -- in the end a
# base-change might be required to get the same group, which is the reason for not simply
# replacing the code

GOPlus:=function(d,q)
  return GO(1,d,q);
end;

SOPlus:=function(d,q)
  return SO(1,d,q);
end;

GOMinus:=function(d,q)
  return GO(-1,d,q);
end;

SOMinus:=function(d,q)
  return SO(-1,d,q);
end;

