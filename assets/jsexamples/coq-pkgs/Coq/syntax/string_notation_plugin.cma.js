function(aa){"use strict";var
g=aa.jsoo_runtime,d=g.caml_new_string,j=g.caml_register_global,$=g.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):g.caml_call_gen(a,[b])}function
e(a,b,c){return a.length==2?a(b,c):g.caml_call_gen(a,[b,c])}function
w(a,b,c,d){return a.length==3?a(b,c,d):g.caml_call_gen(a,[b,c,d])}function
r(a,b,c,d,e){return a.length==4?a(b,c,d,e):g.caml_call_gen(a,[b,c,d,e])}var
b=g.caml_get_global_data(),o=d("string_notation_plugin"),l=b.Constrexpr_ops,u=b.Smartlocate,z=b.Nametab,c=b.Pp,m=b.Libnames,A=b.CErrors,k=b.Names,x=b.Global,y=b.Util,q=b.Vernacextend,p=b.Attributes,h=b.Stdarg,i=b.Genarg,al=b.CAst,ap=b.Notation,B=b.Constrintern,v=b.Pretype_errors,s=b.Coqlib,F=b.Pfedit,L=b.Evd,K=b.Locality,C=b.Mltop;j(22,[0,0,0],"String_notation_plugin");var
ak=[0,0],am=[0,0,1],at=[0,0,0],au=[0,1,1],av=[0,1,0],an=[0,0,1],aq=[0,0,0],ar=[0,1,1],as=[0,1,0],X=d(" to Byte.byte or (option Byte.byte) or (list Byte.byte) or (option (list Byte.byte))."),_=d(" should go from "),J=d(")."),M=d(" or (option "),P=d(" should go from Byte.byte or (list Byte.byte) to "),I=d("core.byte.type"),H=d("core.list.type"),G=d("core.option.type"),O=d(":"),T=d("Notation"),U=d("String"),Z=d("StringNotation");function
t(b){var
c=a(s[2],b);return w(z[48],0,k[1][10][1],c)}function
f(e,d,c,b){var
f=[0,a(l[10],c),[0,b]],g=a(l[11],f);try{r(B[10],e,d,0,g);var
h=1;return h}catch(a){a=$(a);if(a[1]===v[1])return 0;throw a}}function
n(d,b,af,k,j,i,ae){function
B(c,b){return a(l[15],[0,c,[0,b,0]])}function
q(b){return a(l[10],b)}var
n=q(t(I)),ag=q(t(H)),ah=q(t(G));function
r(a){return B(ah,a)}var
s=B(ag,n),v=a(u[4],k),ai=e(u[3],0,j),aj=e(u[3],0,i),g=q(k);function
h(c,b){var
d=[0,[0,e(al[1],0,0),0],ak,c,b];return a(l[14],d)}var
C=a(x[31],v)[2][4];function
D(a,b){return[3,[0,v,a+1|0]]}var
E=e(y[19][16],D,C),F=a(y[19][11],E);if(f(d,b,j,h(s,g)))var
o=am;else
if(f(d,b,j,h(s,r(g))))var
o=at;else
if(f(d,b,j,h(n,g)))var
o=au;else
if(f(d,b,j,h(n,r(g))))var
o=av;else
var
K=a(c[3],J),L=a(m[27],k),N=a(c[3],M),O=a(m[27],k),Q=a(c[3],P),R=a(m[27],j),S=e(c[12],R,Q),T=e(c[12],S,O),U=e(c[12],T,N),V=e(c[12],U,L),W=e(c[12],V,K),o=w(A[6],0,0,W);if(f(d,b,i,h(g,s)))var
p=an;else
if(f(d,b,i,h(g,r(s))))var
p=aq;else
if(f(d,b,i,h(g,n)))var
p=ar;else
if(f(d,b,i,h(g,r(n))))var
p=as;else
var
Y=a(c[3],X),Z=a(m[27],k),$=a(c[3],_),aa=a(m[27],i),ab=e(c[12],aa,$),ac=e(c[12],ab,Z),ad=e(c[12],ac,Y),p=w(A[6],0,0,ad);var
ao=[0,af,ae,[2,[0,o,ai,p,aj,k,0]],[0,a(z[41],[2,v]),0],F,1];return a(ap[23],ao)}j(37,[0,n],"String_notation_plugin__String_notation");a(C[9],o);var
D=0,E=0;function
N(q,o,m,l,j,b){var
r=e(p[1],p[8],j),c=b[3];if(c)var
d=a(F[4],c[1]),g=d[1],f=d[2];else
var
h=a(x[2],0),g=a(L[17],h),f=h;var
i=a(k[1][8],l);n(f,g,a(K[7],r),q,o,m,i);return[0,b[1],b[2],c,b[4]]}var
Q=[0,O,[1,[5,a(i[16],h[7])],0]],R=[1,[5,a(i[16],h[17])],Q],S=[1,[5,a(i[16],h[17])],R],V=[0,[0,0,[0,U,[0,T,[1,[5,a(i[16],h[17])],S]]],N,E],D],W=0,Y=[0,function(a){return q[6]}];r(q[2],Z,Y,W,V);j(46,[0,o],"String_notation_plugin__G_string");return}
