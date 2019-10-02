function(ed){"use strict";var
_="*",bd="term computed",bc="+",bb="@[%s@]",l=246,aB="(",bf="+ ",ba="...",bl="h",aA=" ",aa="1",a_="nsatz_compute",a$="print_pol dans dansideal",bk=")*",bi="_vendor+v8.10+64bit/coq/plugins/nsatz/polynom.ml",be="c",C="",bh=113,ai="^",G="0",bg="u",P="\n",bj=248,o=250,$="_vendor+v8.10+64bit/coq/plugins/nsatz/nsatz.ml",p=ed.jsoo_runtime,f=p.caml_check_bound,az=p.caml_equal,a7=p.caml_fresh_oo_id,ay=p.caml_int_compare,a9=p.caml_int_of_string,eb=p.caml_list_of_js_array,w=p.caml_make_vect,b=p.caml_new_string,n=p.caml_obj_tag,O=p.caml_register_global,Z=p.caml_string_notequal,a6=p.caml_trampoline,ax=p.caml_trampoline_return,z=p.caml_wrap_exception;function
c(a,b){return a.length==1?a(b):p.caml_call_gen(a,[b])}function
a(a,b,c){return a.length==2?a(b,c):p.caml_call_gen(a,[b,c])}function
j(a,b,c,d){return a.length==3?a(b,c,d):p.caml_call_gen(a,[b,c,d])}function
a8(a,b,c,d,e){return a.length==4?a(b,c,d,e):p.caml_call_gen(a,[b,c,d,e])}function
ec(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):p.caml_call_gen(a,[b,c,d,e,f])}var
i=p.caml_get_global_data(),aq=[0,0,0],B=[0,0],K=[0,1],Q=[0,2],aw=b("nsatz_plugin"),aj=i.Flags,ab=i.Pp,aE=i.Feedback,aD=i.Stdlib__format,d=i.Stdlib,e=i.Util,H=i.Assert_failure,ak=i.Failure,aF=i.Stdlib__char,D=i.Stdlib__hashtbl,h=i.Stdlib__list,ap=i.CList,I=i.Stdlib__printf,aK=i.Heap,ae=i.Not_found,ao=i.Stdlib__string,k=i.Num,m=i.CamlinternalLazy,u=i.Constr,a3=i.CErrors,aT=i.Coqlib,aU=i.UnivGen,a4=i.EConstr,a1=i.Unix,v=i.Big_int,ar=i.Ratio,cC=i.Stdlib__array,d2=i.Tactics,d4=i.Mltop,d7=i.Stdarg,d8=i.Genarg,ea=i.Ltac_plugin__Tacentries;O(154,[0,0,0,0,0,0],"Nsatz_plugin");var
bm=[0,[18,[1,[0,0,b(C)]],[2,0,[17,0,0]]],b(bb)],br=[0,b(bi),365,43],bQ=b(ba),bt=b(")"),bu=b(aB),bv=b(C),bw=b(C),bx=b(G),bO=b(ba),bP=b(bc),bz=b(C),bA=b(G),bB=b(aa),bD=b(bk),bE=b(aB),bF=b(_),bG=b(G),bH=b(aa),bI=b(ai),bJ=b(ai),bK=b(bk),bL=b(aB),bM=b(ai),bN=b(_),bC=b(bc),by=b(G),bV=b("div_pol1"),bW=[0,b(bi),477,9],bX=b(P),bY=b("x:"),bZ=b(P),b0=b("r:"),b1=b(P),b2=b("q:"),b3=b(P),b4=b("p:"),b5=b("div_pol:\n"),bT=b(P),bS=b("\n{ "),bU=b("}"),bR=[0,[18,[1,[0,0,b(C)]],[2,0,[17,0,0]]],b(bb)],bs=b(bg),bq=b("non"),bo=[0,0],bp=[0,1],cU=b(P),cT=b(C),cV=b("lp:\n"),cS=b("p: "),cR=b("homogeneous polynomials"),cW=b("computed"),cO=b("new polynomial: "),cN=b(be),cQ=b(bl),cP=b(G),cM=b("computation of the Groebner basis"),cL=b("coefficient: "),cK=b("verif sum: "),cJ=b("r: "),cG=b("remainder: "),cH=b("polynomial reduced to 0"),cI=b("r ok"),cE=[0,[12,91,[4,3,0,0,[12,44,[4,3,0,0,[12,93,0]]]]],b("[%i,%i]")],cD=[0,0,0],cA=b(" terms"),cB=b(" + "),cz=b(a$),cy=b(a$),cj=b(G),ck=b(aa),cl=b(ai),ce=b(_),cf=b(_),cg=b(_),ch=b(aa),ci=b(C),cm=b("-1"),cn=b(G),co=b(aa),cr=b(bf),cs=b(C),ct=b(aA),cu=b("-"),cp=b("- "),cq=b(bf),cv=b(G),cw=b(C),cx=b(aA),cd=b(aA),cb=b(" i="),cc=b("lv= "),b$=b("]"),ca=b("["),b9=[0,0],b_=[0,1],cF=b("Nsatz_plugin.Ideal.Make(P).NotInIdealUpdate"),b6=b("Nsatz_plugin.Ideal.NotInIdeal"),dx=[0,b($),243,9],d3=b("nsatz cannot solve this problem"),d1=b("core.eq.refl"),dZ=b(bd),dM=[0,[11,b("number of parameters: "),[4,3,0,0,0]],b("number of parameters: %i")],dJ=[0,[12,120,[4,3,0,0,0]],b("x%i")],dI=b("nsatz: bad parameter"),dQ=b("computation without sugar"),dR=b("computation with sugar"),dS=b("ordre lexico computation without sugar"),dT=b("ordre lexico computation with sugar"),dU=b("computation without sugar, division by pairs"),dV=b("computation with sugar, division by pairs"),dW=b("ordre lexico computation without sugar, division by pairs"),dX=b("ordre lexico computation with sugar, division by pairs"),dK=eb([b("a"),b("b"),b(be),b("d"),b("e"),b("f"),b("g"),b(bl),b("i"),b("j"),b("k"),b("l"),b("m"),b("n"),b("o"),b("p"),b("q"),b("r"),b("s"),b("t"),b(bg),b("v"),b("w"),b("x"),b("y"),b("z")]),dL=b("cert ok"),dN=b(bd),dO=[0,b($),484,11],dP=[0,b($),472,14],dH=[0,b($),501,8],dG=[0,b($),439,11],dF=[0,0,0],dE=[0,[11,b("time: "),[18,[1,[0,0,b(C)]],[8,0,[0,1,10],[0,3],[17,0,[12,115,0]]]]],b("time: @[%10.3f@]s")],dD=[0,[11,b("useful spolynomials: "),[4,3,0,0,[12,32,0]]],b("useful spolynomials: %i ")],dC=[0,[11,b("useless spolynomials: "),[4,3,0,0,0]],b("useless spolynomials: %i")],dz=[0,0,0],dA=[0,0,0],dB=b(G),dw=[0,0],c_=b("plugins.setoid_ring.pexpr"),c$=b("plugins.setoid_ring.const"),da=b("plugins.setoid_ring.var"),db=b("plugins.setoid_ring.add"),dc=b("plugins.setoid_ring.sub"),dd=b("plugins.setoid_ring.mul"),de=b("plugins.setoid_ring.opp"),df=b("plugins.setoid_ring.pow"),dg=b("core.list.type"),dh=b("core.list.nil"),di=b("core.list.cons"),dj=b("num.Z.type"),dk=b("num.Z.Z0"),dl=b("num.Z.Zpos"),dm=b("num.Z.Zneg"),dp=b("num.pos.xI"),dr=b("num.pos.xO"),ds=b("num.pos.xH"),dt=b("num.N.N0"),du=b("num.N.Npos"),d9=b(a_),d$=b(a_);function
aC(b){return aj[4][1]?(a(aD[bh],bm,b),c(d[52],d[28])):0}function
bn(a){return 0}function
s(d){var
b=aj[4][1];if(b){var
e=c(ab[3],d);return a(aE[9],0,e)}return b}function
x(d){var
b=aj[4][1];if(b){var
e=c(d,0),f=c(ab[3],e);return a(aE[9],0,f)}return b}O(160,[0,aC,bn,x,s],"Nsatz_plugin__Utile");function
aG(g){function
G(a){return c(g[14],[0,a])}var
b=G(0),T=G(1);function
I(a){return[0,c(g[14],a)]}var
k=I(bo),U=I(bp);function
V(a){return[1,a,[0,k,U]]}function
J(d,a){if(0===a)return[0,T];var
c=w(a+1|0,[0,b]);f(c,a)[a+1]=[0,T];return[1,d,c]}function
ag(a){return 0===a[0]?1:0}function
ah(a){return 0===a[0]?a[1]:c(d[3],bq)}function
ai(c){return 0===c[0]?a(g[1],c[1],b)?1:0:0}function
r(a){return 0===a[0]?0:a[1]}function
K(b){if(0===b[0])return 0;var
c=b[2],f=b[1];function
g(c,b){var
e=K(c);return a(d[6],e,b)}return j(e[19][18],g,c,f)}function
aj(b){var
c=0;function
f(c,b){var
e=K(c);return a(d[6],e,b)}return j(e[19][18],f,b,c)}function
m(c,b){if(0===c[0]){var
f=c[1];if(0===b[0])return a(g[1],f,b[1])}else{var
h=c[2],i=c[1];if(0!==b[0]){var
d=i===b[1]?1:0,k=b[2];return d?j(e[19][37],m,h,k):d}}return 0}function
W(d){if(0===d[0])return d;var
e=d[2],g=e.length-1-1|0,a=[0,g],k=d[1];for(;;){if(0<a[1]){var
h=a[1];if(m(f(e,h)[h+1],[0,b])){a[1]=a[1]-1|0;continue}}if(0<=a[1]){if(0===a[1])return f(e,0)[1];if(a[1]===g)return d;var
i=w(a[1]+1|0,[0,b]),j=a[1],l=0;if(!(j<0)){var
c=l;for(;;){var
n=f(e,c)[c+1];f(i,c)[c+1]=n;var
o=c+1|0;if(j!==c){var
c=o;continue}break}}return[1,k,i]}return[0,b]}}function
h(b,a){if(1===a[0]){var
c=a[2];if(a[1]===b)return c.length-1-1|0}return 0}function
X(c){if(0===c[0])return 0;var
b=[0,0],f=c[2];function
g(e,c){var
f=e+X(c)|0;b[1]=a(d[6],b[1],f);return 0}a(e[19][14],g,f);return b[1]}function
t(b){if(0===b[0])return[0,b[1]];var
c=b[1];return[1,c,a(e[19][15],t,b[2])]}function
v(e,c,a){if(1===a[0]){var
d=a[2];if(a[1]===e)return c<d.length-1?f(d,c)[c+1]:[0,b]}return 0===c?a:[0,b]}function
o(j,c){if(0===j[0]){var
D=j[1];if(0===c[0])var
q=[0,a(g[5],D,c[1])];else{var
s=c[2],E=c[1],u=a(e[19][15],t,s),F=o(j,f(s,0)[1]);f(u,0)[1]=F;var
q=[1,E,u]}var
r=q}else{var
l=j[2],i=j[1];if(0===c[0]){var
x=a(e[19][15],t,l),G=o(f(l,0)[1],c);f(x,0)[1]=G;var
y=[1,i,x]}else{var
z=c[2],m=c[1];if(i<m){var
A=a(e[19][15],t,z),H=o(j,f(z,0)[1]);f(A,0)[1]=H;var
n=[1,m,A]}else
if(m<i){var
B=a(e[19][15],t,l),I=o(f(l,0)[1],c);f(B,0)[1]=I;var
n=[1,i,B]}else{var
J=h(i,c),K=h(i,j),p=a(d[6],K,J),C=w(p+1|0,[0,b]),L=0;if(!(p<0)){var
k=L;for(;;){var
M=v(i,k,c),N=o(v(i,k,j),M);f(C,k)[k+1]=N;var
O=k+1|0;if(p!==k){var
k=O;continue}break}}var
n=[1,i,C]}var
y=n}var
r=y}return W(r)}function
L(d){if(0===d[0])return c(g[4],d[1]);var
f=a(e[19][15],L,d[2]);return j(e[19][17],g[12],b,f)}function
M(b,c){if(0===b[0])return[0,a(g[9],b[1],c)];var
d=b[2],f=b[1];function
h(a){return M(a,c)}return[1,f,a(e[19][15],h,d)]}function
Y(c){var
d=L(c);return a(g[1],d,b)?c:M(c,d)}function
Z(b){if(0===b[0])return 0;var
d=b[1],f=c(e[19][11],b[2]),g=[0,[0,d,0],a(e[17][68],Z,f)];return c(e[17][59],g)}function
_(d,g,c){if(1===c[0]){var
e=c[2],i=c[1];if(i===g){var
j=w(e.length-1+d|0,[0,b]),k=e.length-1-1|0,n=0;if(!(k<0)){var
a=n;for(;;){var
l=a+d|0,o=f(e,a)[a+1];f(j,l)[l+1]=o;var
p=a+1|0;if(k!==a){var
a=p;continue}break}}return[1,i,j]}}if(m(c,[0,b]))return[0,b];var
h=w(d+1|0,[0,b]);f(h,d)[d+1]=c;return[1,g,h]}function
n(d,c){if(0===d[0]){var
k=d[1];if(0===c[0])return[0,a(g[6],k,c[1])];var
l=c[2],m=c[1];if(a(g[1],k,b))return[0,b];var
p=function(a){return n(d,a)};return[1,m,a(e[19][15],p,l)]}var
h=d[2],f=d[1];if(0===c[0]){if(a(g[1],c[1],b))return[0,b];var
q=function(a){return n(a,c)};return[1,f,a(e[19][15],q,h)]}var
i=c[1],r=c[2];if(f<i){var
s=function(a){return n(d,a)};return[1,i,a(e[19][15],s,r)]}if(i<f){var
t=function(a){return n(a,c)};return[1,f,a(e[19][15],t,h)]}function
u(b,a){return _(b,f,n(a,c))}var
v=a(e[19][16],u,h);return j(e[19][17],o,[0,b],v)}function
al(k,c){if(0===c[0])return[0,b];var
d=c[2],g=c[1];if(g===k){var
e=d.length-1-1|0;if(1===e)return f(d,1)[2];var
h=w(e,[0,b]),i=e-1|0,l=0;if(!(i<0)){var
a=l;for(;;){var
j=a+1|0,m=f(d,j)[j+1],o=n([0,G(a+1|0)],m);f(h,a)[a+1]=o;var
p=a+1|0;if(i!==a){var
a=p;continue}break}}return[1,g,h]}return[0,b]}function
s(b){if(0===b[0])return[0,c(g[8],b[1])];var
d=b[1];return[1,d,a(e[19][15],s,b[2])]}function
N(b,a){return o(b,s(a))}function
x(b,a){return 0===a?U:n(b,x(b,a-1|0))}function
l(b,a){return n(b,a)}function
O(b,a){return N(b,a)}function
y(b,a){return x(b,a)}function
p(b,a){return v(b,h(b,a),a)}function
am(b,a){return v(b,0,a)}function
A(b,a){var
c=h(b,a),d=x(V(b),c);return N(a,n(p(b,a),d))}function
P(c){var
a=c;for(;;){var
b=r(a);if(0<b){var
a=p(b,a);continue}if(0===a[0])return a[1];throw[0,H,br]}}function
an(d){var
c=Y(d),e=P(c);return a(g[3],b,e)?c:s(c)}var
$=[0,1];function
ao(b){var
a=b;for(;;){if(0===a[0])return a[1];var
a=f(a[2],0)[1];continue}}function
aa(b){if($[1]){var
f=c(d[22],b);return a(d[17],bs,f)}if(3<b){var
g=c(aF[1],(b-4|0)+97|0);return a(e[15][1],1,g)}var
h=c(aF[1],b+119|0);return a(e[15][1],1,h)}var
i=[0,0];function
Q(n){if(0<i[1]){if(0===n[0]){var
o=n[1];i[1]=i[1]-1|0;if(a(g[3],b,o))return c(g[15],o);var
u=c(g[15],o),v=a(d[17],u,bt);return a(d[17],bu,v)}var
p=n[2],m=aa(n[1]),j=[0,bv],h=[0,bw],r=Q(f(p,0)[1]);if(1-a(e[15][34],r,bx))j[1]=r;var
q=[0,0],s=p.length-1-1|0;if(!(s<1)){var
l=s;for(;;){if(0<=i[1]){var
k=Q(f(p,l)[l+1]);h[1]=bz;if(1===l){if(1-a(e[15][34],k,bA)){i[1]=i[1]-1|0;if(a(e[15][34],k,bB))h[1]=m;else
if(a(e[15][22],k,43)){var
z=a(d[17],bD,m),A=a(d[17],k,z);h[1]=a(d[17],bE,A)}else{var
B=a(d[17],bF,m);h[1]=a(d[17],k,B)}}}else
if(1-a(e[15][34],k,bG)){i[1]=i[1]-1|0;if(a(e[15][34],k,bH)){var
C=c(d[22],l),D=a(d[17],bI,C);h[1]=a(d[17],m,D)}else
if(a(e[15][22],k,43)){var
E=c(d[22],l),F=a(d[17],bJ,E),G=a(d[17],m,F),H=a(d[17],bK,G),I=a(d[17],k,H);h[1]=a(d[17],bL,I)}else{var
J=c(d[22],l),K=a(d[17],bM,J),L=a(d[17],m,K),M=a(d[17],bN,L);h[1]=a(d[17],k,M)}}var
t=1-c(e[15][40],h[1]),w=t?1-q[1]:t;if(w){i[1]=i[1]-1|0;if(c(e[15][40],j[1]))j[1]=h[1];else{var
y=a(d[17],bC,h[1]);j[1]=a(d[17],j[1],y)}}}else{h[1]=bO;if(1-q[1]){var
N=a(d[17],bP,h[1]);j[1]=a(d[17],j[1],N)}q[1]=1}var
x=l-1|0;if(1!==l){var
l=x;continue}break}}if(c(e[15][40],j[1])){i[1]=i[1]-1|0;j[1]=by}return j[1]}return bQ}function
u(a){i[1]=20;return Q(a)}function
ap(b){var
c=u(b);return a(aD[bh],bR,c)}function
ab(c){var
b=[0,bS];function
f(c){var
e=u(c),f=a(d[17],e,bT);b[1]=a(d[17],b[1],f);return 0}a(e[19][13],f,c);a(d[17],b[1],bU);return 0}function
aq(a){return ab(c(e[19][12],a))}function
E(j,i,e){if(0===e){if(0===j[0]){var
r=j[1];if(0===i[0]){var
s=i[1],x=a(g[10],r,s);return a(g[1],x,b)?[0,[0,a(g[9],r,s)],k]:c(d[3],bV)}}throw[0,H,bW]}var
t=h(e,i),y=p(e,i),f=[0,j],n=[0,k],u=[0,1],z=A(e,i);for(;;){if(u[1])if(!m(f[1],k)){var
v=h(e,f[1]);if(v<t)u[1]=0;else{var
B=p(e,f[1]),C=A(e,f[1]),D=q(B,y,e-1|0),w=l(D,J(e,v-t|0));n[1]=o(n[1],w);f[1]=O(C,l(w,z))}continue}return[0,n[1],f[1]]}}function
q(f,e,b){var
g=E(f,e,b),h=g[2],i=g[1];if(m(h,k))return i;var
j=c(d[22],b),l=a(d[17],j,bX),n=a(d[17],bY,l),o=a(d[17],bZ,n),p=u(h),q=a(d[17],p,o),r=a(d[17],b0,q),s=a(d[17],b1,r),t=u(e),v=a(d[17],t,s),w=a(d[17],b2,v),x=a(d[17],b3,w),y=u(f),z=a(d[17],y,x),A=a(d[17],b4,z),B=a(d[17],b5,A);return c(d[3],B)}function
ar(c,b){var
e=r(b),f=r(c);return q(c,b,a(d[6],f,e))}function
as(c,b){var
f=r(b),g=r(c),e=a(d[6],g,f);try{var
i=h(e,b),j=(1+h(e,c)|0)-i|0;q(n(c,x([0,P(b)],j)),b,e);var
k=1;return k}catch(a){a=z(a);if(a[1]===ak)return 0;throw a}}function
at(d,b,a){if(0===b[0])return[0,k,b,1,d];if(a===b[1]){var
e=[0,0],c=[0,d],f=p(a,b),j=A(a,b),g=[0,k],m=h(a,b);for(;;){var
n=h(a,b);if(n<=h(a,c[1])){var
q=h(a,c[1]),r=p(a,c[1]),s=A(a,c[1]),i=l(r,J(a,q-m|0)),t=l(i,j);c[1]=O(l(f,s),t);g[1]=o(l(f,g[1]),i);e[1]=e[1]+1|0;continue}return[0,c[1],f,e[1],g[1]]}}return[0,k,b,1,d]}function
C(f,c,a,b){if(1===a[0]){var
g=a[2];if(b===a[1]){var
h=function(c,a){return B(c,a,b-1|0)};return j(e[19][17],h,c,g)}}var
d=b-1|0;return f<50?S(f+1|0,c,a,d):ax(S,[0,c,a,d])}function
S(i,f,e,b){if(0===f[0]){var
o=f[1];if(0===e[0]){var
p=c(g[4],e[1]),r=c(g[4],o);return[0,a(g[12],r,p)]}}if(m(f,k))return e;if(m(e,k))return f;if(0===h(b,e))return i<50?C(i+1|0,e,f,b):ax(C,[0,e,f,b]);if(0===h(b,f))return i<50?C(i+1|0,f,e,b):ax(C,[0,f,e,b]);var
s=F(f,b),j=B(s,F(e,b),b-1|0);aC(c(d[22],b));var
t=q(f,j,b),n=ad(t,q(e,j,b),b);return l(j,q(n,F(n,b),b))}function
av(a,b,c){return a6(C(0,a,b,c))}function
B(a,b,c){return a6(S(0,a,b,c))}function
ac(c,b,a){return B(c,b,a)}function
au(c,b){var
e=r(b),f=r(c);return ac(c,b,a(d[6],f,e))}function
F(a,b){if(1===a[0]){var
c=a[2];if(a[1]===b){var
d=function(c,a){return B(c,a,b-1|0)};return j(e[19][17],d,k,c)}}return a}function
ae(u,t,r,o,n,b){var
d=u,a=t,c=r,i=o,g=n;for(;;){if(m(a,k))return d;var
j=h(b,a),e=p(b,a),f=g-j|0,v=s(a),w=E(l(y(s(e),f+1|0),d),v,b)[2],x=af(e,c,f,b),d=a,a=q(w,l(i,y(c,f)),b),c=x,i=e,g=j;continue}}function
ad(j,i,b){var
c=j,a=i;for(;;){if(m(a,k))return c;var
f=h(b,c),d=h(b,a);if(f<d){var
q=a,a=c,c=q;continue}var
g=f-d|0,e=p(b,a),n=s(a),o=E(l(y(s(e),g+1|0),c),n,b)[2];return ae(a,o,y(e,g),e,d,b)}}function
af(c,g,f,e){var
a=[0,c],d=f-1|0,h=1;if(!(d<1)){var
b=h;for(;;){a[1]=q(l(a[1],c),g,e);var
i=b+1|0;if(d!==b){var
b=i;continue}break}}return a[1]}function
R(a){if(0===a[0])return c(g[13],a[1]);var
b=a[2],d=0;function
f(b,a){return a+R(b)|0}return j(e[19][18],f,b,d)}return[0,I,V,J,ag,ai,r,K,aj,m,W,h,X,t,v,o,L,M,Y,Z,ah,_,n,al,s,N,x,l,O,y,p,am,A,P,an,ao,$,aa,i,u,ap,ab,aq,E,q,ar,as,at,au,ac,F,av,B,ad,ae,af,R,c(D[25],[0,m,R])]}O(166,[0,aG],"Nsatz_plugin__Polynom");var
al=[bj,b6,a7(0)],A=[0,0];function
b7(a){return a}function
b8(a){return a}function
y(a){return a.length-1-1|0}function
am(a){return f(a,0)[1]}function
aH(c,d){var
h=y(c);if(A[1]){var
e=[0,0],a=[0,1];for(;;){if(0===e[1])if(a[1]<=h){var
i=a[1],n=f(d,i)[i+1],j=a[1];e[1]=ay(f(c,j)[j+1],n);a[1]=a[1]+1|0;continue}return e[1]}}var
o=f(d,0)[1],k=ay(f(c,0)[1],o);if(0===k){var
g=[0,0],b=[0,h];for(;;){if(0===g[1])if(1<=b[1]){var
l=b[1],p=f(d,l)[l+1],m=b[1];g[1]=-ay(f(c,m)[m+1],p)|0;b[1]=b[1]-1|0;continue}return g[1]}}return k}function
ac(c,e){var
b=y(c),d=w(b+1|0,0),g=0;if(!(b<0)){var
a=g;for(;;){var
h=f(e,a)[a+1],i=f(c,a)[a+1]-h|0;f(d,a)[a+1]=i;var
j=a+1|0;if(b!==a){var
a=j;continue}break}}return d}function
aI(c,g){var
b=[0,1],a=[0,0],h=y(c);for(;;){if(b[1])if(a[1]<=h){var
d=a[1],i=f(g,d)[d+1],e=a[1];b[1]=i<=f(c,e)[e+1]?1:0;a[1]=a[1]+1|0;continue}return b[1]}}function
an(a){var
c=y(a);f(a,0)[1]=0;var
d=1;if(!(c<1)){var
b=d;for(;;){var
e=f(a,0)[1];a[1]=f(a,b)[b+1]+e|0;var
g=b+1|0;if(c!==b){var
b=g;continue}break}}return a}function
ad(e,h){var
c=y(e),g=w(c+1|0,0),i=1;if(!(c<1)){var
b=i;for(;;){var
j=f(h,b)[b+1],k=f(e,b)[b+1],l=a(d[6],k,j);f(g,b)[b+1]=l;var
m=b+1|0;if(c!==b){var
b=m;continue}break}}return an(g)}function
aJ(a){return an(w(a+1|0,0))}function
aL(b){var
Q=c(b[1],b9),t=c(b[1],b_);function
R(a){return a}function
S(d,c){var
f=c[2],g=d[2],e=a(b[9],d[1],c[1]),h=e?az(g,f):e;return h}var
B=c(e[17][51],S),T=[0,B,function(d){function
e(a){return a[1]}var
f=a(h[17],e,d);function
g(a){return a[2]}var
i=a(h[17],g,d),k=c(D[27],i);function
l(d,a){return(d*17|0)+c(b[56],a)|0}return j(h[20],l,k,f)}],U=c(D[25],T);function
C(f,e){try{var
b=a(h[7],f,e);return b}catch(b){b=z(b);if(b[1]===ak){var
g=c(d[22],e),i=a(d[17],cb,g),k=function(c,b){var
e=a(d[17],cd,b);return a(d[17],c,e)},l=j(h[20],k,cc,f);return a(d[17],l,i)}throw b}}function
o(h,e){var
k=h[1];function
g(j,i){var
e=[0,0],l=j.length-1-1|0,m=1;if(!(l<1)){var
b=m;for(;;){var
t=f(j,b)[b+1],h=c(d[22],t);if(Z(h,cj))if(Z(h,ck)){var
o=a(d[17],cl,h),p=C(k,b-1|0),q=[0,a(d[17],p,o),0];e[1]=a(d[26],e[1],q)}else{var
s=[0,C(k,b-1|0),0];e[1]=a(d[26],e[1],s)}var
r=b+1|0;if(l!==b){var
b=r;continue}break}}var
g=e[1];if(g){if(i)return a(ao[7],ce,g);var
n=a(ao[7],cf,g);return a(d[17],cg,n)}return i?ch:ci}function
l(i,k){var
z=i?0:1;if(z)return k?cv:cw;var
A=0,B=i?i[2]:c(d[3],cy),C=l(B,A),D=a(d[17],cx,C),m=i?i[1]:c(d[3],cz),h=m[2],n=c(b[39],m[1]),o=a(d[17],n,b$),e=a(d[17],ca,o);if(Z(e,cm))if(Z(e,cn))if(Z(e,co))if(45===p.caml_string_get(e,0))var
q=g(h,0),r=j(ao[4],e,1,p.caml_ml_string_length(e)-1|0),s=a(d[17],r,q),f=a(d[17],cp,s);else
if(0===k)var
t=g(h,0),u=a(d[17],e,t),f=a(d[17],cq,u);else
var
v=g(h,0),f=a(d[17],e,v);else
if(0===k)var
w=g(h,1),f=a(d[17],cr,w);else
var
f=g(h,1);else
var
f=cs;else
var
x=g(h,1),y=a(d[17],ct,x),f=a(d[17],cu,y);return a(d[17],f,D)}return l(e,1)}function
u(e,b){if(10<c(h[1],b))var
g=c(h[1],b),i=c(d[22],g),j=a(d[17],i,cA),k=a(d[17],cB,j),l=o(e,[0,c(h[5],b),0]),f=a(d[17],l,k);else
var
f=o(e,b);return f}var
V=0;function
k(b,a){return[0,[0,a,aJ(b)],0]}function
g(o,n){var
f=o,e=n,d=0;for(;;){if(f){if(e){var
i=e[2],j=e[1],k=f[2],g=f[1],l=aH(g[2],j[2]);if(0<l){var
f=k,d=[0,g,d];continue}if(0<=l){var
m=a(b[15],g[1],j[1]);if(a(b[9],m,Q)){var
f=k,e=i;continue}var
f=k,e=i,d=[0,[0,m,g[2]],d];continue}var
e=i,d=[0,j,d];continue}return a(h[12],d,f)}return e?a(h[12],d,e):c(h[9],d)}}function
l(m,g,c){function
d(h){var
n=h[2],o=h[1],d=y(g),e=w(d+1|0,0),i=0;if(!(d<0)){var
c=i;for(;;){var
j=f(n,c)[c+1],k=f(g,c)[c+1]+j|0;f(e,c)[c+1]=k;var
l=c+1|0;if(d!==c){var
c=l;continue}break}}return[0,a(b[22],m,o),e]}return a(ap[68],d,c)}function
m(a){return c(b[1],[0,a])}function
W(d,b){var
a=w(d+1|0,0);f(a,b)[b+1]=1;var
c=an(a);return[0,[0,m(1),c],0]}function
X(a){function
d(a){if(a){var
e=a[1],f=e[2],g=e[1],h=d(a[2]);return[0,[0,c(b[24],g),f],h]}return 0}return d(a)}function
n(f,c){function
d(c){if(c){var
e=c[1],g=e[2],h=e[1],i=d(c[2]);return[0,[0,a(b[22],f,h),g],i]}return 0}return d(c)}function
v(e,d){var
a=e,b=0;for(;;){if(a){var
c=a[1],f=a[2],a=f,b=g(l(c[1],c[2],d),b);continue}return b}}function
Y(a,b){if(a){if(0===b)return[0,[0,t,aJ(y(c(h[5],a)[2]))],0];var
d=function(b,a){if(1===a)return b;var
c=d(b,a/2|0),e=v(c,c);return 0===(a%2|0)?e:v(b,e)};return d(a,b)}return 0}function
E(d,c){return a(b[48],d,c)}function
i(a){return c(h[5],a[1])[2]}function
F(b,e){b[3]=b[3]+1|0;if(b[4].length-1<=b[3])b[4]=a(cC[5],b[4],w(b[3],aq));var
c=[0,e,b[3]],d=b[3];f(b[4],d)[d+1]=c;return c}function
_(e,d){var
a=d;for(;;){if(a){var
b=a[1],f=a[2];if(0===aI(e,c(h[5],b[1])[2])){var
a=f;continue}return b}return aq}}function
$(d,c){var
b=d[1];if(b)return a(D[6],b[1],c);throw ae}function
aa(d,c,b){var
a=d[1];return a?j(D[5],a[1],c,b):0}function
G(d,c,e){try{var
a=$(d,c);return a}catch(a){a=z(a);if(a===ae){var
b=_(c,e)[1];return b?(aa(d,c,b),b):b}throw a}}function
q(d,c){return a(b[45],d,c)}function
H(v,e,u){function
f(d){if(d){var
h=d[1],i=h[2],j=h[1],w=d[2],e=G(v,i,u);if(e){var
k=e[1],m=k[1],x=e[2],y=k[2],o=E(j,m),p=q(m,o),z=q(j,o),A=c(b[24],z),s=l(A,ac(i,y),x),r=f(g(n(p,w),s)),B=r[2];return[0,a(b[22],p,r[1]),B]}return[0,t,d]}return[0,t,0]}var
d=f(e);return[0,d[1],d[2]]}function
ab(d,c,b){try{var
e=a(D[6],d[2],[0,c[2],b[2]]);return e}catch(a){a=z(a);if(a===ae)return 0;throw a}}function
J(d,c,b,a){return j(D[5],d[2],[0,c[2],b[2]],a)}function
K(o,n,e,i){function
f(a){if(a){var
h=a[1],i=h[2],p=a[2],r=h[1],d=G(o,i,e);if(d){var
j=d[1],s=d[2],t=j[2],u=q(r,j[1]),k=c(b[24],u),m=ac(i,t),n=f(g(p,l(k,m,s)));return[0,[0,[0,k,m,d],n[1]],n[2]]}return[0,0,a]}return cD}var
d=f(n),p=d[2],r=d[1];function
s(b,e){function
c(c,b){var
d=b[2],f=b[1];if(a(B,b[3],e[1])){var
h=m(1);return g(c,l(f,d,k(y(d),h)))}return c}return j(h[20],c,b,r)}return[0,j(h[23],s,i,e),p]}function
af(s,r){var
d=s[1],e=r[1],a=c(h[5],d)[2],i=c(h[5],e)[2],j=c(h[5],d)[1],n=c(h[5],e)[1],t=c(h[6],d),u=c(h[6],e),o=E(j,n),p=ad(a,i),v=ac(p,a),w=ac(p,i);function
f(d,a){var
e=q(j,o),f=l(c(b[24],e),w,a);return g(l(q(n,o),v,d),f)}var
x=f(t,u),z=m(1),A=f(k(y(a),z),0),B=m(1);return[0,x,A,f(0,k(y(a),B))]}function
ag(c,b){return a(d[26],b,[0,c,0])}var
ah=[0,function(b,a){return aH(a[2],b[2])}],r=c(aK[2],ah),L=r[1],ai=r[2],aj=r[3],ar=r[4],as=r[6];function
M(k,d,b){function
e(r,j){var
u=j[1],l=c(h[5],k[1])[2],s=c(h[5],u)[2],d=[0,1],b=[0,1],t=y(l);for(;;){if(d[1])if(b[1]<=t){var
m=b[1],n=0===f(l,m)[m+1]?1:0;if(n)var
o=n;else
var
q=b[1],o=0===f(s,q)[q+1]?1:0;d[1]=o;b[1]=b[1]+1|0;continue}if(d[1])return r;var
v=i(j),w=ad(i(k),v),e=j[2],g=k[2],x=p.caml_lessthan(g,e)?[0,g,e]:[0,e,g];return a(ai,[0,x,w],r)}}return j(h[20],e,b,d)}function
at(e,d){var
a=e,b=d;for(;;){if(a){var
c=a[2],f=a[1];if(c){var
a=c,b=M(f,c,b);continue}}return b}}function
au(j,b,k,m){var
e=b[2],g=b[1],c=g[2],d=g[1];function
l(a){var
h=a[2]!==d?1:0;if(h){var
k=a[2]!==c?1:0;if(k){var
l=aI(e,i(a));if(l){var
m=a[2]<c?1:0;if(m)var
g=m;else
var
p=i(a),g=1-az(e,ad(i(f(j[4],d)[d+1]),p));if(g){var
n=a[2]<d?1:0;if(n)var
b=n;else
var
o=i(a),b=1-az(e,ad(i(f(j[4],c)[c+1]),o))}else
var
b=g}else
var
b=l}else
var
b=k}else
var
b=h;return b}return a(h[28],l,k)}function
av(e,d){return x(function(g){var
a=0,b=j(as,function(b,a){return a+1|0},d,a),f=c(h[1],e);return j(I[4],cE,f,b)})}var
A=[bj,cF,a7(0)];function
N(t,l,f,r,e,D){var
w=H(l,t[1],e),p=w[2],E=w[1];x(function(c){var
b=u(f,p);return a(d[17],cG,b)});var
y=[0,p,a(b[22],t[2],E)];if(p)throw[0,A,y];s(cH);function
F(a){return 0}var
G=a(h[17],F,e),i=y[2],z=K(l,n(i,r),e,G),B=z[1],I=z[2];s(cI);x(function(c){var
b=o(f,I);return a(d[17],cJ,b)});x(function(k){function
b(c,b,a){return g(c,v(b,a[1]))}var
c=n(i,r),j=o(f,a8(h[25],b,c,B,e));return a(d[17],cK,j)});x(function(c){var
b=o(f,k(1,i));return a(d[17],cL,b)});var
q=0,j=c(h[9],e);for(;;){if(j){var
C=j[2],J=j[1],L=function(b){return function(a){return ab(l,b,a)}}(J),q=[0,a(h[17],L,C),q],j=C;continue}var
M=a(ap[109],D,q),N=function(a){return n(m(-1),a)};return[0,i,1,M,a(h[19],N,B)]}}function
O(a){return a?am(a[1][2]):-1}function
P(e,q,k,R,b,w){var
g=b[1],l=b[2];s(cM);var
i=e[1];if(i)c(D[2],i[1]);var
y=c(h[1],g);return function(T,S){var
k=T,g=S;for(;;){var
r=g[2],b=g[1];av(b,r);try{var
P=c(ar,r),Q=[0,[0,c(aj,r),P]],t=Q}catch(a){a=z(a);if(a!==aK[1])throw a;var
t=0}if(t){var
B=t[1],i=B[2],C=B[1],D=C[1],l=D[2],m=D[1];if(au(e,[0,[0,m,l],C[2]],b,i)){s(cN);var
g=[0,b,i];continue}var
U=f(e[4],l)[l+1],v=af(f(e[4],m)[m+1],U),o=v[1],V=v[3],W=v[2];if(R)if(0!==o){var
ab=O(k[1]);if(ab<O(o)){s(cQ);var
g=[0,b,i];continue}}var
E=H(e,o,b),G=E[1];if(E[2]){var
X=function(c,d,e,f,g){return function(a){var
b=a[2]===d?f:a[2]===c?e:0;return n(g,b)}}(l,m,V,W,G),Y=a(h[17],X,b),I=K(e,n(G,o),b,Y),Z=I[1],p=F(e,I[2]),_=function(c){return function(b,a){return J(e,c,a,b)}}(p);j(h[22],_,Z,b);x(function(c){return function(e){var
b=u(q,c[1]);return a(d[17],cO,b)}}(p));var
L=ag(p,b);try{var
aa=N(k,e,q,w,L,y);return aa}catch(a){a=z(a);if(a[1]===A){var
$=a[2],k=$,g=[0,L,M(p,b,i)];continue}throw a}}s(cP);var
g=[0,b,i];continue}return N(k,e,q,w,b,y)}}(k,[0,g,l])}function
aw(b){if(b){var
c=b[2],d=am(b[1][2]),e=function(a){return am(a[2])===d?1:0};return a(h[27],e,c)}return 1}return[0,R,k,V,W,B,g,X,v,Y,function(c,n,g,b){var
e=[0,0,a(D[1],0,51),0,w(1000,aq)],i=a(h[27],aw,[0,b,g]);if(i)s(cR);x(function(f){var
e=u(c,b);return a(d[17],cS,e)});x(function(f){function
b(e,b){var
f=u(c,b),g=a(d[17],f,cU);return a(d[17],e,g)}var
e=j(h[20],b,cT,g);return a(d[17],cV,e)});function
o(a){return F(e,a)}var
f=a(h[17],o,g);function
p(a){return J(e,a,a,k(n,m(1)))}a(h[15],p,f);var
q=[0,b,t];try{var
y=P(e,c,q,i,[0,f,L],b),l=y}catch(a){a=z(a);if(a[1]!==A)throw a;var
r=a[2];try{var
v=P(e,c,r,i,[0,f,at(f,L)],b)}catch(a){a=z(a);if(a[1]===A)throw al;throw a}var
l=v}s(cW);return l},U]}var
J=[0,b7,b8];O(174,[0,J,aL,al,A],"Nsatz_plugin__Ideal");var
cX=c(v[36],0),aM=k[52],aN=v[24],aO=v[27],aP=v[16],cY=k[51],cZ=v[25],c0=v[4],c1=v[5],c2=v[10],c3=v[8],c4=v[3],c5=v[15],c6=v[33];function
c7(a){try{var
b=c(v[38],a);return b}catch(a){a=z(a);if(a[1]===ak)return 1;throw a}}var
c8=v[19];function
c9(e,d){var
c=e,b=d;for(;;){if(a(aN,b,cX))return c;if(a(aO,c,b)){var
g=b,b=c,c=g;continue}var
f=a(aP,c,b),c=b,b=f;continue}}function
aQ(b){return a(k[32],b,B)?0:[0,b]}function
aR(a){var
b=a[2],c=a[1];return 1===b?c:[6,c,b]}function
as(a){var
b=a[1];if(typeof
b==="number")return a[2];var
c=a[2];return typeof
c==="number"?b:[3,b,c]}function
aS(c){var
b=c[1];if(typeof
b==="number")return 0;var
d=c[2];if(typeof
d==="number")return 0;else
if(0===d[0])if(a(k[32],d[1],K))return b;if(typeof
b!=="number"&&0===b[0]){var
e=c[2];if(a(k[32],b[1],K))return e}return[5,b,c[2]]}function
t(a){return[l,function(d){var
b=c(aT[2],a);return c(aU[22],b)}]}var
at=t(c_),L=t(c$),R=t(da),S=t(db),T=t(dc),U=t(dd),V=t(de),W=t(df),aV=t(dg),aW=t(dh),aX=t(di),g=t(dj),af=t(dk),X=t(dl),dn=t(dm),dq=t(dp),Y=t(dr),ag=t(ds),ah=t(dt),dv=t(du);function
q(a,d){var
b=n(a),f=c(e[19][12],d),g=o===b?a[1]:l===b?c(m[2],a):a;return c(u[15],[0,g,f])}function
au(f){var
a=n(g),b=0,d=0,e=o===a?g[1]:l===a?c(m[2],g):g;return q(aV,[0,q(at,[0,e,d]),b])}function
M(b){if(a(k[26],b,K)){var
d=n(ag);return o===d?ag[1]:l===d?c(m[2],ag):ag}var
e=a(k[12],b,Q);return a(k[26],e,B)?q(Y,[0,M(a(k[11],b,Q)),0]):q(dq,[0,M(a(k[11],b,Q)),0])}function
aY(b){if(a(k[26],b,B)){var
d=n(af);return o===d?af[1]:l===d?c(m[2],af):af}return a(k[28],b,B)?q(X,[0,M(b),0]):q(dn,[0,M(a(k[4],dw,b)),0])}function
E(A){var
b=A;for(;;)if(typeof
b==="number"){var
b=[0,B];continue}else
switch(b[0]){case
0:var
x=c(k[54],b[1]),d=c(ar[5],x),y=c(ar[3],d);c(k[51],y);var
z=c(ar[2],d),f=n(g),C=[0,aY(c(k[51],z)),0],D=o===f?g[1]:l===f?c(m[2],g):g;return q(L,[0,D,C]);case
1:var
h=n(g),F=[0,M(c(k[43],b[1])),0],G=o===h?g[1]:l===h?c(m[2],g):g;return q(R,[0,G,F]);case
2:var
i=n(g),H=[0,E(b[1]),0],I=o===i?g[1]:l===i?c(m[2],g):g;return q(V,[0,I,H]);case
3:var
J=b[1],N=[0,E(b[2]),0],j=n(g),O=[0,E(J),N],P=o===j?g[1]:l===j?c(m[2],g):g;return q(S,[0,P,O]);case
4:var
Q=b[1],X=[0,E(b[2]),0],p=n(g),Y=[0,E(Q),X],Z=o===p?g[1]:l===p?c(m[2],g):g;return q(T,[0,Z,Y]);case
5:var
_=b[1],$=[0,E(b[2]),0],r=n(g),aa=[0,E(_),$],ab=o===r?g[1]:l===r?c(m[2],g):g;return q(U,[0,ab,aa]);default:var
s=b[2],ac=b[1];if(0===s){var
t=n(g),ad=[0,aY(K),0],ae=o===t?g[1]:l===t?c(m[2],g):g;return q(L,[0,ae,ad])}var
u=c(k[47],s),af=0;if(a(k[32],u,B))var
e=n(ah),v=o===e?ah[1]:l===e?c(m[2],ah):ah;else
var
v=q(dv,[0,M(u),0]);var
w=n(g),ag=[0,E(ac),[0,v,af]],ai=o===w?g[1]:l===w?c(m[2],g):g;return q(W,[0,ai,ag])}}function
N(g){var
b=c(u[29],g);if(9===b[0]){var
d=b[2];if(1===d.length-1){var
e=d[1],f=n(Y),h=b[1],i=o===f?Y[1]:l===f?c(m[2],Y):Y;if(a(u[80],h,i)){var
j=N(e);return a(k[6],Q,j)}var
p=N(e),q=a(k[6],Q,p);return a(k[1],K,q)}}return K}function
F(M){var
i=c(u[29],M);if(9===i[0]){var
d=i[2],x=d.length-1,b=i[1];if(2===x){var
j=d[2],y=n(R),O=o===y?R[1]:l===y?c(m[2],R):R;if(a(u[80],b,O)){var
P=N(j);return[1,c(k[40],P)]}var
z=n(L),Q=o===z?L[1]:l===z?c(m[2],L):L;if(a(u[80],b,Q)){var
h=c(u[29],j);if(9===h[0]){var
r=h[2];if(1===r.length-1){var
s=r[1],t=n(X),I=h[1],J=o===t?X[1]:l===t?c(m[2],X):X;if(a(u[80],I,J))var
p=N(s),g=1;else
var
K=N(s),p=a(k[4],B,K),g=1}else
var
g=0}else
var
g=0;if(!g)var
p=B;return[0,p]}var
A=n(V),Y=o===A?V[1]:l===A?c(m[2],V):V;return a(u[80],b,Y)?[2,F(j)]:0}if(3===x){var
e=d[2],f=d[3],C=n(S),Z=o===C?S[1]:l===C?c(m[2],S):S;if(a(u[80],b,Z)){var
_=F(f);return[3,F(e),_]}var
D=n(T),$=o===D?T[1]:l===D?c(m[2],T):T;if(a(u[80],b,$)){var
aa=F(f);return[4,F(e),aa]}var
E=n(U),ab=o===E?U[1]:l===E?c(m[2],U):U;if(a(u[80],b,ab)){var
ac=F(f);return[5,F(e),ac]}var
G=n(W),ad=o===G?W[1]:l===G?c(m[2],W):W;if(a(u[80],b,ad)){var
v=c(u[29],f);if(9===v[0]){var
w=v[2];if(1===w.length-1)var
H=N(w[1]),q=1;else
var
q=0}else
var
q=0;if(!q)var
H=B;var
ae=c(k[45],H);return[6,F(e),ae]}return 0}}return 0}function
aZ(e){var
b=c(u[29],e);if(9===b[0]){var
a=b[2],d=a.length-1-1|0;if(!(2<d>>>0))switch(d){case
0:return 0;case
1:break;default:var
f=a[2],g=aZ(a[3]);return[0,F(f),g]}}throw[0,H,dx]}function
dy(c,b){function
e(g,f){var
b=g,c=f;for(;;)if(typeof
b==="number")return c;else
switch(b[0]){case
0:return c;case
1:var
h=a9(b[1]);return a(d[6],c,h);case
2:var
b=b[1];continue;case
3:var
i=b[2],j=e(b[1],c),b=i,c=j;continue;case
4:var
k=b[2],l=e(b[1],c),b=k,c=l;continue;case
5:var
m=b[2],n=e(b[1],c),b=m,c=n;continue;default:var
b=b[1];continue}}return e(b,c)}var
a0=aG([0,aN,aO,cZ,c0,c1,c2,c3,c4,c5,aP,c8,c9,c7,aM,c6]),r=aL(a0);function
av(h,a){var
b=c(r[1],a);function
g(b){if(b){var
m=b[2],n=b[1],r=n[1],o=c(J[1],n[2]).length-1-1|0,s=function(h,l){var
g=h[2],d=h[1],e=c(J[1],l[2]),a=[0,0],m=1;if(!(o<1)){var
b=m;for(;;){if(0<f(e,b)[b+1])a[1]=b;var
q=b+1|0;if(o!==b){var
b=q;continue}break}}if(0===a[1])return[0,d,g];if(d<a[1]){var
i=a[1],n=f(e,i)[i+1];return[0,a[1],n]}if(a[1]===d){var
j=a[1];if(f(e,j)[j+1]<g){var
k=a[1],p=f(e,k)[k+1];return[0,a[1],p]}}return[0,d,g]},p=j(e[17][15],s,dz,b),h=p[2],a=p[1];if(0===a){var
i=function(a){if(0===a[0])return aQ(c(cY,a[1]));var
b=a[2],f=a[1];function
g(e,b,a){var
g=aR([0,[1,c(d[22],f)],e]);return as([0,a,aS([0,i(b),g])])}return j(e[19][47],g,b,0)},l=i(r);return c(e[17][48],m)?l:as([0,l,g(m)])}var
t=function(i,g){var
b=g[2],j=g[1],k=i[2],l=i[1];if(h<=f(c(J[1],b),a)[a+1]){var
m=c(J[1],b),d=c(e[19][8],m);d[a+1]=f(d,a)[a+1]-h|0;return[0,[0,[0,j,c(J[2],d)],l],k]}return[0,l,[0,[0,j,b],k]]},q=j(e[17][15],t,dA,b),u=q[2],v=q[1],w=1===h?[1,c(d[22],a)]:aR([0,[1,c(d[22],a)],h]),x=g(c(e[17][9],u));return as([0,aS([0,w,g(c(e[17][9],v))]),x])}return aQ(c(k[43],dB))}return g(b)}function
a2(b,a){function
d(b,a){if(b){if(0===b[1]){var
c=b[2];if(a){var
e=a[1];return[0,e,d(c,a[2])]}throw[0,H,dG]}var
f=d(b[2],a);return[0,r[3],f]}return a}var
f=d(b,c(e[17][9],a));return c(e[17][9],f)}function
dY(as){var
u=aZ(as),h=j(e[17][15],dy,0,u);if(u){var
v=u[1];if(typeof
v==="number")var
d=0;else
if(0===v[0]){var
N=v[1];if(0===N[0]){var
y=u[2];if(y){var
C=y[1];if(typeof
C==="number")var
G=1;else
if(0===C[0]){var
O=C[1],P=N[1];if(0===O[0]){var
Q=O[1],V=y[2];if(7<P>>>0){var
W=c(ab[3],dI);j(a3[6],0,0,W)}else
switch(P){case
0:s(dQ);A[1]=0;break;case
1:s(dR);A[1]=0;break;case
2:s(dS);A[1]=1;break;case
3:s(dT);A[1]=1;break;case
4:s(dU);A[1]=0;break;case
5:s(dV);A[1]=0;break;case
6:s(dW);A[1]=1;break;default:s(dX);A[1]=1}var
X=function(b){return a(I[4],dJ,b+1|0)},Y=a(e[17][56],h,X),Z=[0,a(e[18],dK,Y)],_=function(b){function
d(b){if(typeof
b==="number")var
e=r[3];else
switch(b[0]){case
0:var
g=b[1];if(a(k[32],g,B))var
i=r[3];else
var
l=[0,c(aM,g)],i=a(r[2],h,l);var
e=i;break;case
1:var
f=a9(b[1]);if(f<=Q)var
m=c(a0[2],f),j=a(r[2],h,m);else
var
j=a(r[4],h,f);var
e=j;break;case
2:var
n=d(b[1]),e=c(r[7],n);break;case
3:var
o=b[1],p=d(b[2]),q=d(o),e=a(r[6],q,p);break;case
4:var
s=b[1],t=d(b[2]),u=c(r[7],t),v=d(s),e=a(r[6],v,u);break;case
5:var
w=b[1],x=d(b[2]),y=d(w),e=a(r[8],y,x);break;default:var
z=b[2],A=d(b[1]),e=a(r[9],A,z)}return e}return d(b)},D=a(e[17][68],_,V);if(D){var
$=D[1],aa=c(e[17][9],D[2]),K=c(r[11][1],12),U=function(b){try{var
c=a(r[11][7],K,b);return c}catch(a){a=z(a);if(a===ae){j(r[11][5],K,b,1);return 0}throw a}},L=function(b){if(b){var
c=b[1],d=L(b[2]),e=d[2],f=d[1];if(!a(r[5],c,r[3]))if(!U(c))return[0,[0,c,f],[0,0,e]];return[0,f,[0,1,e]]}return dF},M=L(aa),R=M[2],ac=M[1],T=c(a1[90],0),t=a8(r[10],Z,h,ac,$);x(function(d){var
b=c(a1[90],0)-T;return a(I[4],dE,b)});s(dL);var
ad=c(e[17][9],t[3]),F=[0,t[4],ad],i=c(e[17][1],F),p=w(i,0),J=function(b){if(!(i<=b))if(!f(p,b)[b+1]){f(p,b)[b+1]=1;var
c=a(e[17][7],F,b),d=function(e,d){var
c=1-a(r[5],d,r[3]);return c?J((e+b|0)+1|0):c};return a(e[17][12],d,c)}return 0};J(0);var
S=function(b,c){function
d(a,d){if(i<=((b+a|0)+1|0))return 1;var
c=(b+a|0)+1|0;return f(p,c)[c+1]}return f(p,b)[b+1]?[0,a(e[17][63],d,c)]:0},b=a(ap[66],S,F);x(function(f){var
d=i-c(e[17][1],b)|0;return a(I[4],dC,d)});x(function(f){var
d=c(e[17][1],b);return a(I[4],dD,d)});if(b){var
af=b[2],ag=a2(R,b[1]),ah=av(h,a(r[2],h,t[1])),ai=[6,0,t[2]],aj=c(e[17][9],af),ak=function(a){return a2(R,a)},al=a(e[17][68],ak,aj),am=function(a){return av(h,a)},an=c(e[17][68],am),ao=a(e[17][68],an,al),aq=function(a){return av(h,a)},ar=a(e[17][68],aq,ag);x(function(b){return a(I[4],dM,Q)});s(dN);var
aw=a(e[18],[0,[0,ah,[0,ai,ar]],0],ao),ax=function(b){return a(e[17][68],E,b)},ay=a(e[17][68],ax,aw),az=q(aW,[0,au(0),0]),aA=function(d,b){var
a=n(g),f=0,h=0,i=o===a?g[1]:l===a?c(m[2],g):g,k=q(aW,[0,q(at,[0,i,h]),f]);function
p(d,b){var
a=n(g),e=[0,d,[0,b,0]],f=0,h=o===a?g[1]:l===a?c(m[2],g):g;return q(aX,[0,q(at,[0,h,f]),e])}var
r=[0,j(e[17][16],p,d,k),[0,b,0]];return q(aX,[0,au(0),r])},aB=j(e[17][16],aA,ay,az);s(dZ);return aB}throw[0,H,dO]}throw[0,H,dP]}var
d=1,G=0}else
var
G=1;if(G)var
d=1}else
var
d=1}else
var
d=1}else
var
d=0}throw[0,H,dH]}function
d0(a){var
b=[0,q(aV,[0,au(0),0]),a],d=c(aT[2],d1),e=[0,c(aU[22],d),b],f=c(u[15],e),g=[0,c(a4[9],f),0];return c(d2[148],g)}function
a5(a){try{var
e=dY(a),b=e}catch(a){a=z(a);if(a!==al)throw a;var
d=c(ab[3],d3),b=j(a3[6],0,0,d)}return d0(b)}O(186,[0,a5],"Nsatz_plugin__Nsatz");c(d4[9],aw);var
d5=0;function
d6(a,b){return a5(c(a4[141][1],a))}var
d_=[0,[0,[0,d9,[1,[5,c(d8[16],d7[11])],0]],d6],d5];ec(ea[8],aw,d$,0,0,d_);O(191,[0,aw],"Nsatz_plugin__G_nsatz");return}
