function(dO){"use strict";var
H=148,aJ="Firstorder",bt="already done",bB=",",am=141,bs="gintuition",bu=121,t=120,bA="with",br="Depth",an="firstorder",bz="ground_plugin",by="Solver",aI="using",bx="-----",Y=144,bq=114,bw=248,bv="reversible in 1st order mode",x=100,o=dO.jsoo_runtime,B=o.caml_check_bound,bp=o.caml_fresh_oo_id,f=o.caml_new_string,F=o.caml_register_global,p=o.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):o.caml_call_gen(a,[b])}function
b(a,b,c){return a.length==2?a(b,c):o.caml_call_gen(a,[b,c])}function
j(a,b,c,d){return a.length==3?a(b,c,d):o.caml_call_gen(a,[b,c,d])}function
q(a,b,c,d,e){return a.length==4?a(b,c,d,e):o.caml_call_gen(a,[b,c,d,e])}function
al(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):o.caml_call_gen(a,[b,c,d,e,f])}function
dM(a,b,c,d,e,f,g){return a.length==6?a(b,c,d,e,f,g):o.caml_call_gen(a,[b,c,d,e,f,g])}function
dN(a,b,c,d,e,f,g,h,i){return a.length==8?a(b,c,d,e,f,g,h,i):o.caml_call_gen(a,[b,c,d,e,f,g,h,i])}var
e=o.caml_get_global_data(),aj=f(bz),bf=[0,f(bz),f("auto_with")],_=e.Constr,h=e.Util,v=e.Context,d=e.EConstr,ad=e.Hipattern,aa=e.Global,ab=e.Inductiveops,N=e.Reductionops,u=e.Termops,ao=e.CClosure,y=e.Names,O=e.Int,z=e.Not_found,s=e.Stdlib__queue,ay=e.Evd,l=e.Pp,aY=e.Ppconstr,ag=e.Printer,az=e.Hints,I=e.Stdlib,S=e.CErrors,af=e.Typing,P=e.Option,at=e.Heap,m=e.Tacmach,g=e.Tactics,c=e.Tacticals,i=e.Proofview,T=e.Ltac_plugin__Tacinterp,bd=e.Feedback,bb=e.Stdlib__list,aF=e.Ltac_plugin__Pptactic,ak=e.Vernacextend,aE=e.Attributes,be=e.Goptions,V=e.Ltac_plugin__Tacarg,w=e.Genarg,J=e.Stdarg,K=e.Pcoq,X=e.CLexer,aG=e.Ltac_plugin__Tacentries,bS=e.Constrextern,bX=e.Control,b8=e.Evarutil,cb=e.Classops,cc=e.TransparentState,cP=e.Pputils,cx=e.Ltac_plugin__Tacintern,cy=e.Locality,co=e.Auto,cf=e.Mltop,cr=e.Ltac_plugin__Tacenv,cs=e.CAst,cu=e.Ltac_plugin__Tactic_option,cU=e.CWarnings,c2=e.Geninterp;F(57,[0,0,0,0,0,0,0,0],"Ground_plugin");var
r=[0,1],Z=[0,ao[9]],bC=f("Ground_plugin.Formula.Is_atom"),bD=[0,0,[0,0,0]],bE=f("_"),bF=f("Ground_plugin.Unify.UFAIL"),bT=f(" : "),bU=f("| "),bV=f(bx),bW=f(bx),bP=f(" : No such Hint database"),bQ=f("Firstorder: "),bM=[0,0],bL=[0,0],bK=[0,0],b1=f(bv),b0=f("No link"),bZ=f("No axiom link"),bY=f("Not the expected number of hyps."),ca=f("not implemented ... yet"),b_=f("Untypable instance, maybe higher-order non-prenex quantification"),b9=f(bt),b$=f(bt),b5=f("can't happen."),b6=f("x"),cd=[0,0],ce=f(bv),cR=f('Deprecated syntax; use "," as separator'),cJ=f("Firstorder solver tactic is "),ch=[0,f(aJ),[0,f(br),0]],ci=f("Firstorder Depth"),cl=[0,f("Congruence"),[0,f(br),0]],cm=f("Congruence Depth"),ct=f("Firstorder default solver"),cA=f(by),cB=f(aJ),cC=f("Set"),cG=f("Firstorder_Set_Solver"),cK=[0,f("Print"),[0,f(aJ),[0,f(by),0]]],cO=f("Firstorder_Print_Solver"),cS=f("deprecated"),cT=f("firstorder-deprecated-syntax"),c7=f(aI),c_=f(bB),db=f(bB),de=f(aI),dk=f(aI),dn=f("firstorder_using"),ds=f(bA),dv=f(an),dy=f(bA),dA=f(an),dE=f(an),dG=f(an),dJ=f(bs),dL=f(bs);function
ap(h,g,f,e,d,c){var
a=b(h,f,e);return 0===a?b(g,d,c):a}function
aK(j,i,h,g,f,e,d,c){var
a=q(j,h,g,f,e);return 0===a?b(i,d,c):a}var
L=[bw,bC,bp(0)];function
aL(g,f){var
b=g,c=f;for(;;){var
d=a(_[29],c);if(6===d[0]){var
e=d[3];if(0<b){var
b=b-1|0,c=e;continue}return 1+aL(0,e)|0}return 0}}function
$(d,c){var
e=a(aa[31],c[1])[1][6],f=b(ab[4],d,c);function
g(a){return aL(e,a)}return b(h[19][15],g,f)}function
M(i,c,g,e,f){var
k=b(ab[4],i,e);function
l(h){var
i=a(d[9],h),k=a(aa[31],e[1])[1][8],l=a(v[10][4],k),m=q(u[59],c,l,i,f),n=j(d[x],c,g,m)[2];return b(d[99],c,n)[1]}return b(h[19][15],l,k)}function
aq(c,b,a){return q(N[16],Z[1],c,b,a)}function
ac(m,c,A){var
e=q(N[17],Z[1],m,c,A),n=b(ad[23],c,e);if(n){var
o=n[1],B=o[1];return[0,B,b(d[t][1],-1,o[2])]}var
p=b(ad[21],c,e);if(p){var
r=p[1];return[5,r[2],r[3]]}var
s=b(ad[27],c,e);if(s){var
g=s[1],i=g[2],C=g[3],u=b(d[84],c,g[1]),f=u[1],j=b(d[2][2],c,u[2]),v=a(aa[31],f),k=v[2],w=k[4].length-1,D=v[1];if(0===w)return[1,[0,f,j],i];var
E=0<C?1:0,F=function(a){return 0===a?1:0},l=b(h[19][22],F,k[10]);if(!a(ab[21],[0,f,D,k])){var
I=E?l?1:0:1;if(I)return 1===w?[2,[0,f,j],i,l]:[3,[0,f,j],i,l]}return[6,e]}var
x=b(ad[29],c,e);if(x){var
y=x[1],G=y[2],z=b(d[84],c,y[1]),H=z[1];return[4,[0,H,b(d[2][2],c,z[2])],G]}return[6,aq(m,c,e)]}var
C=[0,a(y[1][6],bE)];function
aM(m,g,p,f,c){var
n=[0,0],k=[0,0],l=[0,0];function
i(D,e,C){var
f=D,o=C;for(;;){var
c=ac(m,g,o);switch(c[0]){case
0:var
E=c[2];i(f,1-e,c[1]);var
o=E;continue;case
1:var
s=1-e,F=s?(n[1]=1,0):s;return F;case
4:var
x=c[2],L=c[1],N=a(p,1),O=a(d[12],N),P=B(M(m,g,1,L,x),0)[1],Q=function(g,j,c){var
h=a(v[10][1][4],c);return i([0,O,f],e,b(d[t][1],g,h))},R=2-a(h[17][1],x)|0;return q(h[17][85],Q,R,0,P);case
5:var
S=c[2],T=a(p,1),f=[0,a(d[12],T),f],o=S;continue;case
6:var
r=j(d[t][3],f,0,c[1]),y=1-b(d[55],g,r);if(y){if(e){k[1]=[0,r,k[1]];return 0}l[1]=[0,r,l[1]];var
z=0}else
var
z=y;return z;default:var
G=c[2],H=c[1];if(c[3]){var
A=aq(m,g,j(d[t][3],f,0,o));if(e)k[1]=[0,A,k[1]];else
l[1]=[0,A,l[1]]}var
u=M(m,g,0,H,G),I=function(g,j,c){var
h=a(v[10][1][4],c);return i(f,e,b(d[t][1],g,h))},J=function(b){var
c=1-a(h[17][1],b)|0;return q(h[17][85],I,c,0,b)};if(e)var
K=function(a){return a?0:1},w=b(h[19][22],K,u);else
var
w=e;if(w)n[1]=1;return b(h[19][13],J,u)}}}switch(f){case
0:i(0,0,c);break;case
1:i(0,1,c);break;default:var
e=b(d[98],g,c),o=e[2],r=e[1],s=function(c){var
b=a(p,1);return a(d[12],b)};i(b(h[17][14],s,r),0,o);n[1]=0}return[0,n[1],[0,k[1],l[1]]]}function
aN(g,f,o,w,e,n){function
k(a){return aq(g,f,a)}try{var
q=a(n,0)+1|0,s=r[1]?aM(g,f,n,o,e):bD,t=s[1],x=s[2];if(1===o){var
l=ac(g,f,e);switch(l[0]){case
0:var
i=0;break;case
1:var
i=3;break;case
2:var
i=1;break;case
3:var
i=2;break;case
4:var
z=B(M(g,f,0,l[1],l[2]),0)[1],A=a(h[17][105],z),i=[0,q,a(v[10][1][4],A),t];break;case
5:var
i=4;break;default:throw[0,L,l[1]]}var
u=[1,i]}else{var
c=ac(g,f,e);switch(c[0]){case
0:var
m=c[1],C=c[2],D=k(m),b=ac(g,f,m);switch(b[0]){case
0:var
d=[5,b[1],b[2],C];break;case
1:var
d=[0,b[1],b[2]];break;case
2:var
d=[1,b[1],b[2]];break;case
3:var
d=[2,b[1],b[2]];break;case
4:var
d=[4,b[1],b[2]];break;case
5:var
d=[3,m];break;default:var
d=0}var
j=[4,D,d];break;case
1:var
j=0;break;case
2:var
E=c[1];if(c[3])throw[0,L,k(e)];var
j=[0,E];break;case
3:var
F=c[1];if(c[3])throw[0,L,k(e)];var
j=[1,F];break;case
4:var
j=[3,c[1]];break;case
5:var
j=[2,q,c[1],t];break;default:throw[0,L,c[1]]}var
u=[0,j]}var
y=[0,[0,w,k(e),u,x]];return y}catch(a){a=p(a);if(a[1]===L)return[1,a[2]];throw a}}F(69,[0,r,Z,ap,aK,$,M,C,aM,aN],"Ground_plugin__Formula");var
D=[bw,bF,bp(0)];function
aO(a){return b(d[t][1],-1,a)}function
ar(e,c){function
f(b){var
c=b[1];return[0,c,a(d[am][1],b[2])]}var
g=b(h[17][68],f,e),i=a(d[am][1],c),j=b(u[45],g,i);return a(d[9],j)}function
as(f,W,V){var
i=a(s[2],0),q=[0,0];function
v(c,a){var
d=q[1];function
e(b){var
d=b[1];return[0,d,ar([0,[0,c,a],0],b[2])]}q[1]=[0,[0,c,a],b(h[17][68],e,d)];return 0}function
w(c){var
a=b(d[3],f,c);if(2===a[0]){var
e=a[1];try{var
g=w(b(O[4][2],e,q[1]));return g}catch(a){a=p(a);if(a===z)return c;throw a}}return c}b(s[3],[0,W,V],i);try{for(;;){var
E=a(s[5],i),X=E[2],k=w(b(N[28],f,E[1])),l=w(b(N[28],f,X)),g=b(d[3],f,k),c=b(d[3],f,l);switch(g[0]){case
2:var
r=g[1];if(2===c[0]){var
A=c[1];if(1-(r===A?1:0))if(r<A)v(A,k);else
v(r,l)}else{var
y=ar(q[1],l),$=b(u[37],f,y),at=a(O[2][2],$)?j(u[32],f,r,y)?0:(v(r,y),1):0;if(!at)throw[0,D,k,l]}var
e=3;break;case
6:var
aa=g[3],ab=g[2];switch(c[0]){case
2:var
e=0;break;case
5:var
e=1;break;case
6:var
J=c[3],I=c[2],H=aa,G=ab,e=4;break;default:var
e=2}break;case
7:var
ae=g[3],af=g[2];switch(c[0]){case
2:var
e=0;break;case
5:var
e=1;break;case
7:var
J=c[3],I=c[2],H=ae,G=af,e=4;break;default:var
e=2}break;case
9:var
K=g[2],ag=g[1];switch(c[0]){case
2:var
e=0;break;case
5:var
e=1;break;case
9:var
L=c[2];b(s[3],[0,ag,c[1]],i);var
M=K.length-1;if(M!==L.length-1)throw[0,D,k,l];var
P=M-1|0,ah=0;if(!(P<0)){var
m=ah;for(;;){var
ai=B(L,m)[m+1],aj=[0,B(K,m)[m+1],ai];b(s[3],aj,i);var
ak=m+1|0;if(P!==m){var
m=ak;continue}break}}var
e=3;break;default:var
e=2}break;case
13:var
Q=g[4],al=g[3],am=g[2];switch(c[0]){case
2:var
e=0;break;case
5:var
e=1;break;case
13:var
R=c[4],an=c[3];b(s[3],[0,am,c[2]],i);b(s[3],[0,al,an],i);var
S=Q.length-1;if(S!==R.length-1)throw[0,D,k,l];var
T=S-1|0,ao=0;if(!(T<0)){var
n=ao;for(;;){var
ap=B(R,n)[n+1],aq=[0,B(Q,n)[n+1],ap];b(s[3],aq,i);var
as=n+1|0;if(T!==n){var
n=as;continue}break}}var
e=3;break;default:var
e=2}break;default:var
e=0}switch(e){case
0:if(2===c[0]){var
F=c[1],x=ar(q[1],k),_=b(u[37],f,x);if(a(O[2][2],_))if(j(u[32],f,F,x))var
C=1;else{v(F,x);var
o=2,C=0}else
var
C=1;if(C)throw[0,D,k,l]}else
if(5===g[0]){var
Z=[0,b(u[60],f,k),l];b(s[3],Z,i);var
o=2}else
var
o=0;break;case
1:var
o=0;break;case
2:var
o=1;break;case
3:var
o=2;break;default:b(s[3],[0,G,I],i);var
ac=aO(J),ad=[0,aO(H),ac];b(s[3],ad,i);var
o=3}switch(o){case
0:if(5===c[0]){var
Y=[0,k,b(u[60],f,l)];b(s[3],Y,i);var
t=1}else
var
t=0;break;case
1:var
t=0;break;case
2:var
t=1;break;default:var
t=2}switch(t){case
0:if(1-j(d[104],f,k,l))throw[0,D,k,l];var
U=0;break;case
1:var
U=0;break;default:var
U=1}continue}}catch(a){a=p(a);if(a===s[1])return q[1];throw a}}function
bG(a,g,c){function
e(c){if(b(d[55],a,c))if(b(d[74],a,c)===g)return 0;function
h(a,c){var
b=e(c);return 0<=a?0<=b?a+b|0:a:b}var
f=q(d[118],a,h,-1,c);return 0<=f?f+1|0:-1}return e(c)}function
bH(g,f){var
c=[0,1],e=[0,0];function
h(f,i){var
j=b(d[3],g,i);if(2===j[0]){var
k=j[1];try{var
n=f+b(O[4][2],k,e[1])|0,o=a(d[10],n);return o}catch(b){b=p(b);if(b===z){var
l=c[1];c[1]++;e[1]=[0,[0,k,l],e[1]];return a(d[10],l+f|0)}throw b}}function
m(a){return a+1|0}return al(d[111],g,m,h,f,i)}var
i=h(0,f);return[0,c[1]-1|0,i]}function
aP(a,f,e,c,i){try{var
j=as(a,c,i),g=b(O[4][2],f,j);if(b(d[55],a,g))var
h=[0,[1,e]];else
var
k=bG(a,f,c),h=[0,[0,bH(a,g),k]];return h}catch(a){a=p(a);if(a[1]===D)return 0;if(a===z)return[0,[1,e]];throw a}}function
aQ(f,e,c){function
g(b){return a(d[12],f+b|0)}var
i=b(h[17][56],e,g);return b(d[t][4],i,c)}function
aR(f,e,c){var
a=e[1],g=c[2],i=c[1],j=aQ(0,a,e[2]),k=aQ(a,i,g);try{var
l=as(f,j,k),m=function(c){var
e=c[1]<a?1:0,g=c[2];return e?e:b(d[55],f,g)},n=b(h[17][21],m,l);return n}catch(a){a=p(a);if(a[1]===D)return 0;throw a}}F(74,[0,D,as,aP,aR],"Ground_plugin__Unify");function
aS(a){if(0===a[0]){var
b=a[1];if(typeof
b==="number")return 999;else
switch(b[0]){case
0:return 90;case
1:return 40;case
2:return-30;case
3:return 60;default:var
c=b[2];if(typeof
c==="number")return 0;else
switch(c[0]){case
0:return x;case
1:return 80;case
2:return 70;case
3:return-20;case
4:return 50;default:return-10}}}var
d=a[1];if(typeof
d==="number")switch(d){case
0:return x;case
1:return 40;case
2:return-15;case
3:return-50;default:return x}return-29}var
bI=[0,function(b,a){var
c=aS(a[3]);return aS(b[3])-c|0}],bJ=[0,function(c,a){var
e=a[2],f=c[2],d=b(y[63][2][1],c[1],a[1]);if(0===d){var
g=function(c,a){var
d=o.caml_int_compare(c[1],a[1]),e=a[2],f=c[2];return 0===d?b(_[86],f,e):d};return j(P[5],g,f,e)}return d}],k=a(h[21][1],[0,_[86]]),Q=a(h[20][1],bJ);function
ae(g,a,f,c){var
e=j(d[5],bK,g,a);try{var
h=[0,f,b(k[23],e,c)],i=j(k[4],e,h,c);return i}catch(a){a=p(a);if(a===z)return j(k[4],e,[0,f,0],c);throw a}}function
aT(i,g,f,a){var
c=j(d[5],bL,i,g);try{var
l=b(k[23],c,a),m=function(a){return 1-b(y[63][1],a,f)},e=b(h[17][61],m,l),n=e?j(k[4],c,e,a):b(k[6],c,a);return n}catch(b){b=p(b);if(b===z)return a;throw b}}var
E=a(at[2],bI);function
G(a){return[0,a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8]-1|0]}function
au(c,a){var
d=a[8],e=b(Q[4],c,a[7]);return[0,a[1],a[2],a[3],a[4],a[5],a[6],e,d]}function
av(l,c,e){var
f=b(Q[3],c,e[7]);if(f)var
g=f;else{var
h=c[2],m=c[1];if(h){var
i=h[1],j=i[1],n=i[2],k=function(c){var
e=c[2],o=c[1];if(e){var
f=e[1],g=f[1],p=f[2],h=b(y[63][1],m,o);if(h){var
i=j<g?1:0;if(i){var
q=[0,j,a(d[9],n)];return aR(l,[0,g,a(d[9],p)],q)}var
k=i}else
var
k=h;return k}return 0};return b(Q[17],k,e[7])}var
g=0}return g}function
R(j,g,f,e,i,a){var
h=aN(j,g,f,e,i,a[6]);if(0===h[0]){var
c=h[1];if(1===f){var
k=a[8],l=a[7],m=a[6],n=c[2],o=a[3],p=a[2];return[0,b(E[2],c,a[1]),p,o,n,0,m,l,k]}var
q=a[8],r=a[7],s=a[6],t=a[5],u=a[4],v=a[3],w=ae(g,c[2],e,a[2]);return[0,b(E[2],c,a[1]),w,v,u,t,s,r,q]}var
d=h[1];if(1===f)return[0,a[1],a[2],a[3],d,[0,d],a[6],a[7],a[8]];var
x=a[8],y=a[7],z=a[6],A=a[5],B=a[4],C=[0,d,a[3]],D=ae(g,d,e,a[2]);return[0,a[1],D,C,B,A,z,y,x]}function
aU(c,b,a){function
d(a,b){return a[1]===C?b:ae(c,a[2],a[1],b)}var
e=a[8],f=a[7],g=a[6],i=a[5],k=a[4],l=a[3],m=j(h[17][16],d,b,a[2]);return[0,j(h[17][16],E[2],b,a[1]),m,l,k,i,g,f,e]}function
aw(f,e,c){var
g=c[2],i=j(d[5],bM,f,e),l=b(k[23],i,g);return a(h[17][5],l)}function
ax(g,f){var
b=f;for(;;){var
c=a(E[3],b[1]),d=a(E[4],b[1]);if(c[1]===C){var
e=[0,d,b[2],b[3],b[4],b[5],b[6],b[7],b[8]];if(b[4]===c[2])return[0,c,e];var
b=e;continue}var
h=b[8],i=b[7],j=b[6],k=b[5],l=b[4],m=b[3];return[0,c,[0,d,aT(g,c[2],c[1],b[2]),m,l,k,j,i,h]]}}function
aV(e){var
b=[0,-1],f=Q[1];function
c(a){if(a)b[1]++;return b[1]}var
g=a(d[12],1);return[0,E[1],k[1],0,g,0,c,f,e]}function
bN(c){if(2===c[0]){var
d=c[1],e=function(a){return[3,[0,d,a+1|0]]},f=a(ab[23],d);return b(h[17][56],f,e)}return[0,c,0]}var
bO=a(h[17][76],bN);function
aW(b,e,d,c){var
f=a(bO,d);function
g(c,a){var
g=a[1],d=dM(ay[171],0,0,0,b,a[2],c),e=q(af[2],0,b,d[1],d[2]),f=e[1];return[0,R(b,f,0,c,e[2],g),f]}return j(h[17][16],g,f,[0,c,e])}function
aX(e,c,g,f){var
d=[0,f];function
i(h){var
f=a(az[30],h[7]);switch(f[0]){case
0:case
2:case
3:var
g=f[1][1][1];try{var
i=b(u[103],c,g)[1],k=j(af[1],e,c,g);d[1]=R(e,c,2,i,k,d[1]);var
l=0;return l}catch(a){a=p(a);if(a===z)return 0;throw a}default:return 0}}function
k(d,c,a){return b(h[17][11],i,a)}function
m(d){try{var
c=a(az[15],d),e=c}catch(c){c=p(c);if(c!==z)throw c;var
f=b(I[17],d,bP),g=b(I[17],bQ,f),h=a(l[3],g),e=j(S[6],0,0,h)}return b(az[14][12],k,e)}b(h[17][11],m,g);return[0,d[1],c]}function
bR(c){function
e(h,g,f){var
c=a(aa[2],0),e=a(ay[17],c),i=a(d[9],h),k=al(bS[6],0,0,c,e,i),m=a(l[14],0),n=j(aY[16],c,e,k),o=a(l[3],bT),p=b(l[37],ag[39],g),q=a(l[3],bU),r=b(l[12],q,p),s=b(l[12],r,o),t=b(l[12],s,n),u=b(l[12],t,m);return b(l[12],u,f)}var
f=a(l[3],bV),g=a(l[7],0),h=j(k[12],e,c,g),i=a(l[14],0),m=a(l[3],bW),n=b(l[12],m,i),o=b(l[12],n,h),p=b(l[12],o,f);return b(l[24],0,p)}F(86,[0,[0,k[1],k[2],k[3],k[4],k[5],k[6],k[7],k[8],k[9],k[10],k[11],k[12],k[13],k[14],k[15],k[16],k[17],k[18],k[19],k[20],k[21],k[22],k[23],k[24],k[25],k[26]],Q,ae,aT,E,G,au,av,R,aU,aw,ax,aV,aW,aX,bR],"Ground_plugin__Sequent");function
n(n,k,g,r){function
c(c){a(bX[3],0);var
p=a(i[68][3],c),d=a(m[35][5],c),e=a(m[35][4],c);function
o(w,t,s){var
i=w,g=t,f=s;for(;;){if(0<i){if(g){var
p=g[2],k=g[1],n=a(v[11][1][2],k),x=a(m[35][6],c);if(!q(u[34],d,e,n,x)){var
y=j(u[35],d,e,n);if(!b(h[17][22],y,f)){var
z=o(i-1|0,p,[0,k,f]);return R(d,e,0,[0,n],a(v[11][1][4],k),z)}}var
i=i-1|0,g=p,f=[0,k,f];continue}var
A=a(l[3],bY);return j(S[3],0,0,A)}return r}}var
f=o(n,p,0),s=k?R(d,e,1,C,a(m[35][6],c),f):f;return a(g,s)}return a(i[68][8],c)}function
A(b){return 0===b[0]?a(g[76],[0,b[1],0]):c[65][2]}function
aZ(e,d){function
f(f){try{var
j=function(b){return a(g[43],b)},k=aw(a(m[35][4],f),e,d),n=a(c[65][61],k),o=b(i[73][1],n,j);return o}catch(d){d=p(d);if(d===z){var
h=a(l[3],bZ);return b(c[65][4],0,h)}throw d}}return a(i[68][8],f)}function
a0(m,k,f,h,e){var
o=n(1,0,h,e),q=[0,g[16],0],r=[0,A(f),q];function
s(j){try{var
o=aw(j,m,e),q=a(i[16],o),h=q}catch(d){d=p(d);if(d!==z)throw d;var
k=a(l[3],b0),h=b(c[65][4],0,k)}function
n(e){function
h(e){function
h(b){var
c=[0,a(d[23],[0,b,[0,e]]),0];return a(g[H],c)}var
j=a(c[65][61],f);return b(i[73][1],j,h)}var
j=a(c[65][61],e);return b(i[73][1],j,h)}return b(i[73][1],h,n)}var
t=[0,b(i[73][1],i[54],s),r],u=a(c[65][22],t);return j(c[65][27],u,o,k)}function
a1(d,b,a){var
e=n(0,1,b,a);return j(c[65][27],g[t],e,d)}function
a2(f,e,d){var
h=n(0,1,e,d),i=[0,a(c[65][34],h)],j=b(g[110],0,i);return b(c[65][12],j,f)}function
a3(f,e,d){var
h=n(1,1,e,d),i=a(c[65][34],h),k=b(c[65][3],g[17],i),l=b(c[65][12],k,f),m=n(1,1,e,d);return j(c[65][27],g[16],m,l)}function
a4(l,k,d,h,f){function
e(o){var
e=B($(a(m[35][5],o),l),0)[1],p=n(e,0,h,f),q=[0,b(c[65][31],e,g[16]),0],r=[0,A(d),q],s=g[x],t=a(c[65][61],d),u=[0,b(i[73][1],t,s),r],v=a(c[65][22],u);return j(c[65][27],v,p,k)}return a(i[68][8],e)}function
a5(l,e,d,k,f){function
o(o){var
p=$(a(m[35][5],o),l);function
q(e){var
h=[0,n(e,0,k,f),0],i=[0,b(c[65][31],e,g[16]),h],j=[0,A(d),i];return a(c[65][22],j)}var
r=b(h[19][15],q,p),s=g[x],t=a(c[65][61],d),u=b(i[73][1],t,s);return j(c[65][28],u,r,e)}return a(i[68][8],o)}function
a6(d){var
e=g[x],f=a(c[65][61],d);return b(i[73][1],f,e)}function
aA(e,l,s,k,r,q){var
u=e[2],v=e[1];function
f(o){var
w=a(m[35][4],o),p=M(a(m[35][5],o),w,0,e,l),f=p.length-1,x=a(h[19][12],l),y=n(f,0,r,q),z=[0,b(c[65][31],f,g[16]),0],C=[0,A(k),z];function
D(r){function
c(e){var
f=B(p,e)[e+1],c=a(h[17][1],f),g=[0,[0,v,e+1|0],a(d[2][1],u)],i=[0,a(d[30],g),x],j=a(d[23],i);function
k(b){return a(d[10],c-b|0)}var
l=b(h[19][2],c,k),m=[0,b(d[t][1],c,j),l],n=[0,a(d[23],m)],o=[0,b(d[t][1],c,r),n],q=a(d[23],o);return b(d[45],q,f)}var
e=b(h[17][56],f,c);return a(g[H],e)}var
E=a(c[65][61],k),F=[0,b(i[73][1],E,D),C],G=a(c[65][22],F);return j(c[65][27],G,y,s)}return a(i[68][8],f)}function
a7(k,j,m,l,e,h,f){var
o=b(d[t][1],1,j),p=[0,b(v[4],0,0),k,o],q=a(d[20],p),u=n(2,1,h,f),w=[0,a(c[65][34],u),0],x=[0,g[17],[0,g[17],w]],r=0,s=0,y=[0,A(e),x];function
z(m){var
c=a(d[10],2),e=b(d[t][1],1,k),f=[0,b(v[4],0,0),e,c],h=[0,m,[0,a(d[21],f)]],i=a(d[23],h),l=[0,b(v[4],0,0),j,i],n=[0,a(d[21],l),0];return a(g[H],n)}var
B=a(c[65][61],e),C=[0,b(i[73][1],B,z),y],D=[0,a(c[65][22],C),s];function
E(b){return a(g[43],b)}var
F=a(c[65][61],e),G=[0,b(i[73][1],F,E),D],I=a(g[Y],q),J=[0,b(c[65][21],I,G),r],K=[0,n(1,0,h,f),0],L=[0,A(e),K],M=[0,a(c[65][22],[0,g[17],L]),J],N=a(g[Y],m),O=b(c[65][21],N,M);return b(c[65][12],O,l)}function
a8(f,e,d){if(r[1])var
i=a(l[3],b1),h=b(c[65][4],0,i);else
var
h=f;var
k=n(0,1,e,d),m=a(c[65][34],k),o=b(c[65][3],g[17],m),p=b(c[65][12],o,f),q=n(0,1,e,d),s=j(c[65][27],g[16],q,p);return b(c[65][12],s,h)}function
a9(l,k,d,h,f){function
e(o){var
e=B($(a(m[35][5],o),l),0)[1],p=[0,n(e-1|0,0,h,f),0],q=[0,b(c[65][31],e,g[16]),p],r=[0,A(d),q],s=a(c[65][22],r),t=g[x],u=a(c[65][61],d),v=b(i[73][1],u,t);return j(c[65][27],v,s,k)}return a(i[68][8],e)}function
a_(l,k,j,f,e){var
o=n(0,1,f,G(e)),p=[0,a(c[65][34],o),0],q=n(1,0,f,G(e)),r=[0,a(c[65][34],q),0],s=[0,g[16],r],t=[0,A(j),s];function
u(f){function
e(i){var
j=a(m[35][12],i),e=b(h[17][7],j,0),k=[0,f,[0,a(d[11],e)]],l=a(d[23],k),n=a(g[76],[0,e,0]),o=a(g[H],[0,l,0]);return b(c[65][3],o,n)}return a(i[68][8],e)}var
v=a(c[65][61],j),w=[0,b(i[73][1],v,u),t],x=[0,a(c[65][22],[0,g[16],w]),p],y=a(g[Y],l),z=b(c[65][21],y,x);return b(c[65][12],z,k)}F(92,[0,n,A,aZ,a0,a1,a2,a3,a4,a5,a6,aA,a7,a8,a9,a_],"Ground_plugin__Rules");function
b2(e,c){function
f(e,c){var
f=a(d[am][1],c),g=a(d[am][1],e);return b(_[86],g,f)}if(0===e[0]){var
g=e[1],h=g[1],j=e[2],k=g[2];if(0===c[0]){var
i=c[1],l=c[2],m=i[2],n=i[1],o=function(b,a){return b-a|0},p=function(b,a){return b-a|0};return aK(function(a,b,c,d){return ap(p,o,a,b,c,d)},f,n,h,j,l,k,m)}return 0===h?1:-1}var
q=e[1];return 0===c[0]?0===c[1][1]?-1:1:f(q,c[1])}function
b3(c,a){return c===a?0:c===C?1:a===C?-1:b(y[63][2][1],c,a)}var
b4=[0,function(b,a){return ap(b2,b3,a[1],b[1],a[2],b[2])}],ah=a(h[20][1],b4);function
a$(D,c,m){var
d=[0,ah[1]];function
e(f){var
i=f[3];if(0===i[0]){var
c=i[1];if(typeof
c==="number")var
n=1;else
if(2===c[0])var
v=c[3],k=c[2],u=c[1],g=1,n=0;else
var
n=1;if(n)var
g=0}else{var
e=i[1];if(typeof
e==="number")var
g=0;else
var
v=e[3],k=e[2],u=e[1],g=1}if(g){var
w=f[4],p=[0,1],q=[0,v],B=f[1],r=function(c,a){function
e(f,e){var
a=aP(D,u,k,f,e);if(a){var
c=a[1];return 0===c[0]?(p[1]=0,d[1]=b(ah[4],[0,c,B],d[1]),0):(q[1]=1,0)}return 0}var
f=c[1];function
g(c){var
d=a[2];function
f(a){return e(c,a)}return b(h[17][11],f,d)}b(h[17][11],g,f);var
i=c[2];function
j(c){var
d=a[1];function
f(a){return e(c,a)}return b(h[17][11],f,d)}return b(h[17][11],j,i)},y=m[1],z=function(a){return r(w,a[4])};b(E[5],z,y);var
o=m[5],x=o?[0,o[1],0]:0;r(w,[0,x,m[3]]);var
s=p[1],t=s?q[1]:s,C=t?(d[1]=b(ah[4],[0,[1,k],f[1]],d[1]),0):t;return C}var
A=a(l[3],b5);return j(S[3],0,0,A)}b(h[17][11],e,c);return a(ah[21],d[1])}function
ai(e,b){try{var
f=ax(e,b),g=f[1],a=g[3],k=f[2];if(0===a[0]){var
h=a[1];if(typeof
h==="number")var
d=1;else
if(2===h[0])var
c=1,d=0;else
var
d=1;if(d)var
c=0}else
var
c=typeof
a[1]==="number"?0:1;if(c)var
j=ai(e,k),i=[0,[0,g,j[1]],j[2]];else
var
i=[0,0,b];return i}catch(a){a=p(a);if(a===at[1])return[0,0,b];throw a}}var
ba=a(y[1][6],b6);function
b7(i,c,x,w,f,u){if(x===C)var
o=ba;else
var
G=j(af[1],i,c,w),H=j(N[29],i,c,G),s=b(d[78],c,H)[1][1],I=s?s[1]:ba,o=I;function
z(b){return a(d[10],f-b|0)}var
A=b(h[17][56],f,z),B=b(d[t][4],A,u),n=f,m=y[1][10][1],e=i,l=c,k=0;for(;;){if(0===n)return[0,l,k,B];var
p=j(g[13],m,o,e),q=dN(b8[7],0,0,0,0,0,e,l,ay[125]),D=q[2][1],E=q[1],r=[0,b(v[4],[0,p],0),D],F=b(d[bu],r,e),n=n-1|0,m=b(y[1][10][4],p,m),e=F,l=E,k=[0,r,k];continue}}function
aB(f,e,r,k){function
o(o){var
s=a$(a(m[35][4],o),f,k);function
t(f){if(f[2]===C)var
e=f[1],o=function(j,k){function
f(B){if(0===e[0]){var
f=e[1];if(0===f[1]){var
o=f[2],p=[0,n(0,1,j,G(k)),0],q=a(c[65][35],p),r=a(g[bq],[0,[0,o,0]]);return b(c[65][3],r,q)}var
s=a(l[3],ca);return b(c[65][4],0,s)}var
t=e[1],u=[0,a(c[65][24],g[42]),0],v=[0,n(0,1,j,G(k)),0],w=[0,a(c[65][35],v),0];function
x(c){var
e=a(m[35][12],c),f=b(h[17][7],e,0),i=[0,[0,a(d[11],f),0]];return a(g[bq],i)}var
y=[0,a(i[68][8],x),w],z=[0,a(c[65][22],[0,g[17],y]),u],A=a(g[Y],t);return b(c[65][21],A,z)}return a(i[68][8],f)};else
var
o=function(w,k){var
e=f[2],o=f[1];function
r(x){var
f=a(m[35][4],x);if(0===o[0]){var
t=o[1],r=t[2],s=t[1],u=[0,s,j(d[5],0,f,r)];if(av(f,[0,e,[0,u]],k)){var
y=a(l[3],b9);return b(c[65][4],0,y)}if(0<s)var
z=function(h){function
c(c){var
o=a(m[35][4],c),f=b7(a(m[35][5],c),o,e,h,s,r),t=f[2],u=f[1],v=a(d[23],[0,h,[0,f[3]]]),k=b(d[45],v,t);try{var
A=a(m[35][5],c),B=q(af[2],0,A,u,k),n=B}catch(b){b=p(b);if(!a(S[18],b))throw b;var
w=a(l[3],b_),n=j(S[6],0,0,w)}var
x=n[1],y=a(g[H],[0,k,0]),z=a(i[66][1],x);return b(i[18],z,y)}return a(i[68][8],c)},A=a(c[65][61],e),v=b(i[73][1],A,z);else
var
D=function(b){var
c=[0,a(d[23],[0,b,[0,r]]),0];return a(g[H],c)},E=a(c[65][61],e),v=b(i[73][1],E,D);var
B=[0,n(1,0,w,G(au([0,e,[0,u]],k))),0],C=[0,a(c[65][35],B),0];return a(c[65][22],[0,v,[0,g[17],C]])}var
F=o[1];if(av(f,[0,e,0],k)){var
I=a(l[3],b$);return b(c[65][4],0,I)}var
J=[0,a(c[65][24],g[42]),0],K=[0,n(1,0,w,G(au([0,e,0],k))),0],L=[0,a(c[65][35],K),0],M=[0,g[17],L];function
N(c){function
e(e){var
f=a(m[35][12],e),i=b(h[17][7],f,0),j=[0,c,[0,a(d[11],i)]],k=[0,a(d[23],j),0];return a(g[H],k)}return a(i[68][8],e)}var
O=a(c[65][61],e),P=[0,b(i[73][1],O,N),M],Q=[0,a(c[65][22],[0,g[17],P]),J],R=a(g[Y],F);return b(c[65][21],R,Q)}return a(i[68][8],r)};return o(r,k)}var
u=b(h[17][68],t,s),v=a(c[65][26],u);return b(c[65][12],v,e)}return a(i[68][8],o)}F(94,[0,ai,a$,aB],"Ground_plugin__Instances");function
bc(U,g){function
d(h){function
d(a,d){var
c=d[1];if(1===c[0]){var
e=b(y[18][8],c[1],a[2]);return[0,a[1],e]}return a}var
e=a(cb[25],0),f=j(bb[20],d,cc[2],e);Z[1]=b(ao[3][13],ao[9],f);function
v(x,k){function
d(s){if(o.caml_equal(a(T[8],0),cd)){var
V=a(m[35][4],s),W=[0,a(i[68][12],s),V],X=j(ag[65],0,0,W);b(bd[9],0,X)}try{var
D=ax(a(m[35][4],s),k),g=D[2],h=D[1],e=function(b){return aU(a(m[35][4],s),x,b)},Z=0,f=function(a){return v(Z,a)},d=v([0,h,x],g),y=h[3];if(0===y[0]){var
q=y[1];if(typeof
q==="number")var
t=a6(h[1]);else
switch(q[0]){case
0:var
_=q[1],$=e(g),t=a4(_,d,h[1],f,$);break;case
1:var
aa=q[1],ab=e(g),t=a5(aa,d,h[1],f,ab);break;case
2:var
F=ai(a(m[35][4],s),k),G=F[1],ac=F[2],H=v(b(I[26],G,x),ac);if(r[1])if(0<k[8])var
J=aB(G,H,f,e(k)),z=1;else
var
z=0;else
var
z=0;if(!z)var
J=H;var
t=J;break;case
3:var
ad=q[1];if(r[1])var
ae=e(g),K=a9(ad,d,h[1],f,ae);else
var
K=d;var
t=K;break;default:var
n=q[2],af=q[1];if(typeof
n==="number")var
w=d;else
switch(n[0]){case
3:var
am=n[1];if(0<k[8])if(r[1])var
an=e(g),L=a_(am,d,h[1],f,an),A=1;else
var
A=0;else
var
A=0;if(!A)var
L=d;var
w=L;break;case
4:var
ao=n[2],ap=n[1];if(r[1])var
aq=e(g),M=aA(ap,ao,d,h[1],f,aq);else
var
M=d;var
w=M;break;case
5:var
ar=n[3],as=n[2],au=n[1],av=e(g),w=a7(au,as,ar,d,h[1],f,av);break;default:var
aj=n[2],ak=n[1],al=e(g),w=aA(ak,aj,d,h[1],f,al)}var
ah=e(g),t=a0(af,w,h[1],f,ah)}var
E=t}else{var
N=y[1];if(typeof
N==="number")switch(N){case
0:var
u=a3(d,f,e(g));break;case
1:var
u=a1(d,f,e(g));break;case
2:var
u=a2(d,f,e(g));break;case
3:var
u=d;break;default:if(r[1])var
aw=a(l[3],ce),O=b(c[65][4],0,aw);else
var
O=d;var
u=a8(O,f,e(g))}else{var
P=ai(a(m[35][4],s),k),Q=P[1],ay=P[2],R=v(b(I[26],Q,x),ay);if(r[1])if(0<k[8])var
S=aB(Q,R,f,e(k)),B=1;else
var
B=0;else
var
B=0;if(!B)var
S=R;var
u=S}var
E=u}var
C=E}catch(a){a=p(a);if(a!==at[1])throw a;var
C=U}var
Y=aZ(k[4],k);return b(c[65][12],Y,C)}return a(i[68][8],d)}var
k=a(i[68][3],h),q=a(bb[1],k);return a(g,function(a){var
b=0;return n(q,1,function(a){return v(b,a)},a)})}return a(i[68][8],d)}F(x,[0,bc],"Ground_plugin__Ground");a(cf[9],aj);var
U=[0,3];function
cg(a){return a?(U[1]=b(I[6],a[1],0),0):(U[1]=3,0)}var
cj=[0,0,ci,ch,function(a){return[0,U[1]]},cg];b(be[3],0,cj);var
aC=[0,x];function
ck(a){return a?(aC[1]=b(I[6],a[1],0),0):(aC[1]=0,0)}var
cn=[0,1,cm,cl,function(a){return[0,aC[1]]},ck];b(be[3],0,cn);var
cp=[0,bf,0],cq=[0,function(b,a){return q(co[14],0,0,0,0)}];j(cr[16],0,bf,cq);var
bg=[31,b(cs[1],0,[0,cp,0])],aD=b(cu[1],[0,bg],ct),bh=aD[3],bi=aD[2],bj=aD[1],cv=0,cw=0;function
cz(f,e,d){var
g=b(aE[1],aE[8],e),c=a(cx[2],f);b(bj,a(cy[5],g),c);return d}var
cD=[0,[0,0,[0,cC,[0,cB,[0,cA,[1,[5,a(w[16],V[8])],0]]]],cz,cw],cv],cE=0,cF=[0,function(a){return ak[6]}];q(ak[2],cG,cF,cE,cD);var
cH=0,cI=0,cL=[0,[0,0,cK,function(g,f){a(aE[2],g);var
c=a(bh,0),d=a(l[3],cJ),e=b(l[12],d,c);b(bd[6],0,e);return f},cI],cH],cM=0,cN=[0,function(a){return ak[5]}];q(ak[2],cO,cN,cM,cL);function
W(h,d,g,f){var
e=r[1];function
j(a){var
c=a[2],d=a[1];r[1]=e;return b(i[21],[0,c],d)}function
k(l){r[1]=h;var
j=d?d[1]:a(bi,0)[2],k=bc(j,function(h){function
d(d){var
j=aV(U[1]),k=a(m[35][4],d),l=aW(a(m[35][5],d),k,g,j)[1],n=a(m[35][4],d),e=aX(a(m[35][5],d),n,f,l),o=e[2],p=a(h,e[1]),q=a(i[66][1],o);return b(c[65][3],q,p)}return a(i[68][8],d)});r[1]=e;return k}var
l=a(i[68][8],k);return b(i[22],l,j)}function
bk(d,c,b){return a(aF[27],aY[7])}function
bl(f,e,d){function
b(b){return a(ag[39],b[2])}var
c=a(cP[5],b);return a(aF[27],c)}function
bm(d,c,b){return a(aF[27],ag[39])}function
cQ(b){return a(l[22],cR)}var
bn=q(cU[1],cT,cS,0,cQ);function
cV(b,a){return bm}function
cW(b,a){return bl}var
cX=[0,function(b,a){return bk},cW,cV],cY=[1,[1,J[17]]],cZ=[1,[1,J[17]]],c0=[1,[1,J[17]]],c1=a(w[6],J[17]),c3=[0,[1,a(c2[3],c1)]],c4=0;function
c5(a,c,b){return[0,a,0]}var
c6=[6,K[15][15]],c8=[0,[0,[0,[0,0,[0,a(X[10],c7)]],c6],c5],c4];function
c9(b,e,a,d,c){return[0,a,b]}var
c$=[0,a(X[10],c_)],da=[2,[6,K[15][15]],c$],dc=[0,a(X[10],db)],dd=[6,K[15][15]],df=[0,[0,[0,[0,[0,[0,0,[0,a(X[10],de)]],dd],dc],da],c9],c8];function
dg(d,c,a,f,e){b(bn,0,0);return[0,a,[0,c,d]]}var
dh=[3,[6,K[15][15]]],di=[6,K[15][15]],dj=[6,K[15][15]],dl=[0,[0,[0,[0,[0,[0,0,[0,a(X[10],dk)]],dj],di],dh],dg],df],dm=[0,[1,[0,[0,0,function(a){return 0}],dl]],c3,c0,cZ,cY,cX],bo=b(aG[9],dn,dm),aH=bo[1],dp=bo[2],dq=0;function
dr(f,e,d,c){var
g=a(T[24],c);return W(1,b(P[16],g,f),e,d)}var
dt=[0,ds,[1,[0,[5,a(w[16],J[16])]],0]],du=[1,[5,a(w[16],aH)],dt],dw=[0,[0,[0,dv,[1,[4,[5,a(w[16],V[8])]],du]],dr],dq];function
dx(e,d,c){var
f=a(T[24],c);return W(1,b(P[16],f,e),0,d)}var
dz=[0,dy,[1,[0,[5,a(w[16],J[16])]],0]],dB=[0,[0,[0,dA,[1,[4,[5,a(w[16],V[8])]],dz]],dx],dw];function
dC(e,d,c){var
f=a(T[24],c);return W(1,b(P[16],f,e),d,0)}var
dD=[1,[5,a(w[16],aH)],0],dF=[0,[0,[0,dE,[1,[4,[5,a(w[16],V[8])]],dD]],dC],dB];al(aG[8],aj,dG,0,0,dF);var
dH=0;function
dI(d,c){var
e=a(T[24],c);return W(0,b(P[16],e,d),0,0)}var
dK=[0,[0,[0,dJ,[1,[4,[5,a(w[16],V[8])]],0]],dI],dH];al(aG[8],aj,dL,0,0,dK);F(bu,[0,aj,U,bg,bj,bi,bh,W,bk,bl,bm,bn,aH,dp],"Ground_plugin__G_ground");return}
