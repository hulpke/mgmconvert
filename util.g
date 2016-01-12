# Library of utility functions to aid in Magma code translation

# hom is homomorphism defined on fp group
# l is words given by numbers 
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

