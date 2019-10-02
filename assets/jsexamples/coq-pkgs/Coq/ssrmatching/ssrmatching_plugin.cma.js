function(gz){"use strict";var
bW="Only identifiers are allowed here",b4="partial term ",U="in",bV="mk_tpattern_matcher with no upats_origin.",ac=246,r=141,b3="(",bU=149,a4=158,ab="In",bY="ssrpattern",b2="pattern",a3=157,a1="As",u=" in ",ar="_vendor+v8.10+64bit/coq/plugins/ssrmatching/ssrmatching.ml",bT="_ssrpat_",V=173,a5=120,b1="The ",aa="in ",b0="do_once never called.",aD=101,a7="ssrmatching_plugin",bS="_",bZ="Qed",bX=" of ",a6=248,a2=" as ",o=gz.jsoo_runtime,I=o.caml_check_bound,a0=o.caml_equal,aY=o.caml_fresh_oo_id,bR=o.caml_ml_string_length,d=o.caml_new_string,aZ=o.caml_notequal,aX=o.caml_register_global,bQ=o.caml_string_get,J=o.caml_string_notequal,s=o.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):o.caml_call_gen(a,[b])}function
b(a,b,c){return a.length==2?a(b,c):o.caml_call_gen(a,[b,c])}function
i(a,b,c,d){return a.length==3?a(b,c,d):o.caml_call_gen(a,[b,c,d])}function
t(a,b,c,d,e){return a.length==4?a(b,c,d,e):o.caml_call_gen(a,[b,c,d,e])}function
$(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):o.caml_call_gen(a,[b,c,d,e,f])}function
aC(a,b,c,d,e,f,g){return a.length==6?a(b,c,d,e,f,g):o.caml_call_gen(a,[b,c,d,e,f,g])}function
gy(a,b,c,d,e,f,g,h){return a.length==7?a(b,c,d,e,f,g,h):o.caml_call_gen(a,[b,c,d,e,f,g,h])}var
g=o.caml_get_global_data(),T=[0,[0,0,0]],bE=[0,d(a7),d(bY)],bI=d(a7),l=g.Tacmach,K=g.Printer,c=g.Pp,f=g.EConstr,n=g.Names,bF=g.Ltac_plugin__Tacenv,B=g.Genarg,an=g.Ltac_plugin__Tacinterp,am=g.Proofview,S=g.Context,h=g.Evd,v=g.DAst,m=g.CErrors,e=g.Constr,bm=g.Typeclasses,ak=g.Assert_failure,aO=g.Evar,bn=g.UState,j=g.Util,L=g.Ppconstr,H=g.Option,ae=g.Not_found,aR=g.Vars,aB=g.Goal,ag=g.Environ,ai=g.Evarutil,bd=g.Ftactic,M=g.Libnames,bh=g.Constrexpr_ops,as=g.Stdlib,bv=g.Termops,bk=g.Pretype_errors,bp=g.Recordops,aw=g.Term,aK=g.Evarconv,aL=g.Unification,N=g.CAst,W=g.Geninterp,be=g.Genintern,at=g.Global,ba=g.Constrintern,a9=g.Feedback,bG=g.Mltop,y=g.CLexer,q=g.Pcoq,ap=g.Ltac_plugin__Tacentries,e1=g.Tacticals,eM=g.Tactics,d_=g.Stdarg,d3=g.Ltac_plugin__Tacsubst,dM=g.Ltac_plugin__Tacintern,c_=g.CArray,c1=g.Failure,cW=g.Invalid_argument,cT=g.Sorts,cS=g.Globnames,cM=g.Reductionops,cx=g.Conv_oracle,cw=g.Reduction,ct=g.Glob_ops,ci=g.Ltac_plugin__Pptactic,b8=g.CamlinternalLazy,ca=g.Goptions;aX(156,[0,0,0],"Ssrmatching_plugin");var
eX=d("matches:"),eY=d("instance:"),e2=d("Not supported"),eV=[0,1],eW=[0,1],eZ=d("BEGIN INSTANCES"),e0=d("END INSTANCES"),eT=d(bY),eN=d(b2),eL=d("selected"),eF=d("matching impacts evars"),eD=d(" does not match any subterm of the goal"),eE=d(b4),eB=[0,1],ex=[0,[0,1,0]],ey=[0,[0,0,[0,1,0]]],ew=d("pattern without redex."),ev=[0,0],er=[0,d(ar),1136,48],en=d("in the pattern?"),eo=d('Does the variable bound by the "in" construct occur '),ep=d(" did not instantiate ?"),eq=d("Matching the pattern "),et=[0,1],eu=[0,1],es=[0,1],el=d("typed as: "),ek=d("decoded as: "),ej=[0,d(ar),1056,58],eg=d(bT),eh=d(a1),ei=d(ab),ef=[0,d(ar),1011,55],ed=d("."),ee=d("bad encoding for pattern "),ec=d("interpreting: "),ea=d("interpreting a term with no ist"),d9=[0,d(ar),943,12],d8=d(bW),dP=d(bW),dO=d(bT),dN=d("globbing pattern: "),dQ=d("( _ as _ )"),dR=d("( _ as _ in _ )"),dS=d("( _ in _ )"),dT=d("( _ in _ in _ )"),dU=d(ab),dW=d(ab),dX=d(ab),dZ=d(ab),dY=d("where are we?."),dV=d(ab),d0=d(a1),d1=d(a1),dC=d(aa),dD=d(u),dE=d(u),dF=d(aa),dG=d(u),dH=d(u),dI=d(u),dJ=d(a2),du=d(aa),dv=d(u),dw=d(u),dx=d(aa),dy=d(u),dz=d(u),dA=d(u),dB=d(a2),dl=d(aa),dm=d(u),dn=d(u),dp=d(aa),dq=d(u),dr=d(u),ds=d(u),dt=d(a2),dj=d("matches but type classes inference fails"),dk=d("does not match any subterm of the goal"),di=d(bV),dg=d("are equal to the "),dh=d("all matches of "),df=d("companion function never called."),c$=d("of "),da=d(" of the "),de=d(" of"),db=d(" occurrence"),dc=d(" < "),dd=d("Only "),c5=d(bX),c6=d(b1),c3=d(bX),c4=d(b1),c8=d("term "),c9=d(b4),c7=d(bV),c2=d(b0),cZ=d(b0),cV=d("incomplete ise in match_upats_FO."),cX=d("IN FO."),cR=[0,d(ar),462,13],cN=d(u),cO=d("indeterminate "),cP=d("indeterminate pattern"),cD=d("RHS"),cC=d("LHS"),cz=[0,0],cy=[0,1],cq=d("combineCG: different ist"),cr=d("have: mixed C-G constr."),cs=d("have: mixed G-C constr."),cn=[0,0],cm=[12,0,0,0],cl=d("not a GLambda"),cj=d("not a CRef."),ce=d("$"),cc=d(")"),cd=d(b3),cb=d("glob_constr: term with no ist"),b7=d("SSR: "),b6=[0,d("ssrmatching")],gx=d("SSRMATCHINGDEBUG"),b9=[0,d("Debug"),[0,d("SsrMatching"),0]],b_=d("ssrmatching debugging"),co=[13,0,0,0],cv=d("Ssrmatching_plugin.Ssrmatching.NoProgress"),cB=d("Ssrmatching_plugin.Ssrmatching.NoMatch"),cG=d(bS),cJ=d(bS),cU=d("Ssrmatching_plugin.Ssrmatching.FoundUnif"),dL=d("rpatternty"),eQ=d(b2),eU=d(a7),fZ=d(b3),f0=d("@"),fg=d(U),fk=d(U),fp=d(U),fs=d(U),fw=d(U),fz=d(U),fE=d(U),fH=d("as"),fJ=d("rpattern"),fV=d(bZ),fX=d("cpattern"),f1=d("ssrtermkind"),gf=d(bZ),gh=d("lcpattern"),gr=d("ssrpatternarg"),gu=d("ssrinstancesoftpat"),gw=d("ssrinstoftpat"),b5=m[6];function
D(a){return b(b5,a,b6)}function
a8(d,b){var
e=a(c[3],b);return i(m[6],d,[0,b],e)}var
aE=a9[6],ad=[0,function(a){return 0}];function
aF(d){var
e=o.caml_obj_tag(d),f=250===e?d[1]:ac===e?a(b8[2],d):d,g=a(c[3],b7),h=b(c[12],g,f);return b(a9[9],0,h)}try{o.caml_sys_getenv(gx);ad[1]=aF}catch(a){a=s(a);if(a!==ae)throw a}function
a_(a){return a?(ad[1]=aF,0):(ad[1]=function(a){return 0},0)}var
b$=[0,0,b_,b9,function(a){return ad[1]===aF?1:0},a_];b(ca[4],0,b$);function
af(b){return a(ad[1],b)}function
a$(c){var
b=a(e[29],c);return 9===b[0]?[0,b[1],b[2]]:[0,c,[0]]}function
bb(e,d,c){var
a=bQ(d,c);if(48<=a)var
b=61===a?1:123===a?1:0;else{if(40===a)return 0;var
b=47<=a?1:0}return b?1:40===e?1:0}function
bc(m,f,e){var
n=a(f,e),o=a(c[49],n),g=b(as[17],o,ce),d=0;for(;;){if(22<(bQ(g,d)-10|0)>>>0){if(b(m,g,d)){var
h=a(c[3],cc),i=a(f,e),j=a(c[3],cd),k=b(c[12],j,i),l=b(c[12],k,h);return b(c[26],1,l)}return a(f,e)}var
d=d+1|0;continue}}var
cf=L[17],cg=L[16];function
aG(c){var
e=c[2],f=c[1],d=a(at[2],0),j=a(h[17],d);function
g(e){var
c=e[2],g=e[1];if(c)return i(cg,d,j,c[1]);var
f=a(at[2],0);return b(K[27],f,g)}return bc(function(a,b){return bb(f,a,b)},g,e)}function
p(c){var
e=c[2],f=c[1],d=a(at[2],0),j=a(h[17],d);function
g(e){var
c=e[2],g=e[1];if(c)return i(cf,d,j,c[1]);var
f=a(at[2],0);return b(K[26],f,g)}return bc(function(a,b){return bb(f,a,b)},g,e)}function
ch(e,g){var
c=a(B[2],e),f=a(W[1][1],e);function
h(b,a){return[0,b,a]}function
i(b,a){return a}function
j(c,b){return a(bd[1],[0,f,b])}function
d(c,a,f,e,d){return b(g,c,a)}b(be[9],c,h);b(be[10],c,i);b(W[7],c,j);b(W[4],c,[0,[0,f]]);t(ci[1],c,d,d,d);return c}function
aH(c){var
b=c[1];return 0===b[0]?a(M[33],b[1]):0}function
ck(c){var
b=a(v[1],c);if(5===b[0])if(b[1])return 1;return 0}function
aI(e){var
b=a(v[1],e);if(5===b[0]){var
d=b[1];if(d)return[0,d[1],b[4]]}var
f=a(c[3],cl);return i(m[3],0,0,f)}function
bf(b){return 13===a(v[1],b)[0]?1:0}function
bg(a){return b(N[1],a,cm)}function
au(d,c,a){return b(N[1],d,[16,c,[0,a]])}var
cp=v[3],O=function(a){return b(cp,0,a)}(co);function
ah(c,a){return b(v[3],0,[14,c,[0,a]])}function
aJ(e,d,o,n){function
f(e,b){if(e){var
d=e[1];if(b){if(d===b[1])return[0,d];var
f=a(c[3],cq);return i(m[3],0,0,f)}return[0,d]}return b?[0,b[1]]:0}var
g=e[2],h=g[2],j=e[1],p=g[1];if(h){var
k=d[2][2];if(k){var
q=k[1],r=h[1],s=f(e[3],d[3]);return[0,j,[0,O,[0,b(o,r,q)]],s]}var
t=a(c[3],cr);return i(m[3],0,0,t)}var
l=d[2];if(l[2]){var
u=a(c[3],cs);return i(m[3],0,0,u)}var
v=l[1],w=f(e[3],d[3]);return[0,j,[0,b(n,p,v),0],w]}function
P(d){var
b=d[2],c=b[2],e=b[1];return c?a(bh[6],c[1]):a(ct[23],e)}function
bi(c,b,a){return[0,c,[0,O,[0,b]],a]}var
cu=32;function
bj(a,b){return bi(cu,a,b)}function
z(d,c){var
e=a(f[9],c),g=b(ai[30],d,e);return a(f[r][1],g)}var
X=[a6,cv,aY(0)];function
aj(e,b,d,c){var
f=a(h[152],b),g=[0,a(h[47],b),f];try{aC(cw[14],0,0,e,[0,g],d,c);var
i=1;return i}catch(a){return 0}}function
Q(d,a,c,b){try{var
e=$(aK[4],0,d,a,c,b);return e}catch(a){a=s(a);if(a[1]===aK[3])throw[0,bk[1],d,a[2],[4,c,b,[0,a[3]]]];throw a}}function
bl(j,i,d,h,g){var
c=i,b=0,k=d.length-1;for(;;){if(b===k)return c;var
e=h+b|0,l=I(g,e)[e+1],m=a(f[9],l),n=I(d,b)[b+1],c=Q(j,c,a(f[9],n),m),b=b+1|0;continue}}function
aM(e,j,i,h){var
k=a(f[9],h),l=a(f[9],i),g=a(ag[4],e),c=a(cx[8],g),b=a(aL[4],c)[1],d=[0,0,b[2],b[3],b[4],c,b[6],b[7],b[8],b[9],b[10],1,1],m=[0,[0,d,d,d,0,a(aL[4],c)[5]]];return aC(aL[8],e,j,0,m,l,k)}function
aN(k,d,l){var
c=[0,k],m=a(f[r][1],l);function
g(l){var
m=a(e[29],l);if(3===m[0]){var
k=m[1];try{var
q=g(b(h[43],d,k));return q}catch(l){var
f=k[1],n=b(j[19][15],g,k[2]);if(1-b(h[26],c[1],f)){var
o=b(h[23],d,f),p=b(ai[38],d,o);c[1]=i(h[22],c[1],f,p)}return a(e[5],[0,f,n])}}return b(e[aD],g,l)}function
n(e,k,o){if(0===a(h[9],k)){var
l=b(h[23],d,e),j=a(h[9],l);if(j){var
m=g(a(f[r][1],j[1])),n=a(f[9],m);c[1]=i(h[31],e,n,c[1]);return 0}return 0}return 0}var
o=g(m);i(h[27],n,k,0);var
p=a(f[9],o),q=a(h[bU],d);return[0,c[1],q,p]}function
av(k,j,i,r,q,p){var
s=k?k[1]:1,c=t(aK[11],j,0,0,r),u=a(h[54],c),d=aN(i,c,q),l=d[3],e=d[2],m=d[1],n=a(h[V],m);function
v(a){return b(h[36],n,a)}var
w=b(aO[7][18],v,u),x=b(h[53],n,w),f=b(h[a4],x,e),o=s?aC(bm[23],0,0,0,cy,j,f):f;if(a(p,c)){if(o===f)return[0,m,e,l];var
g=aN(i,o,l),y=g[3],z=g[1];return[0,z,b(bn[6],e,g[2]),y]}throw X}function
R(d,c,f,a){var
g=Q(d,c,f,a),e=av(cz,d,c,g,a,function(a){return 1});return b(h[a4],e[1],e[2])}function
cA(c,e,d){var
f=a(h[87],c),g=a(l[2],c),i=R(a(l[5],c),g,e,d);return b(l[3],f,i)}function
bo(c,k){var
d=a(e[29],k);switch(d[0]){case
3:return b(j[19][13],c,d[1][2]);case
5:var
l=d[3];a(c,d[1]);return a(c,l);case
8:var
n=d[4],o=d[3];a(c,d[2]);a(c,o);return a(c,n);case
9:var
p=d[2];a(c,d[1]);return b(j[19][13],c,p);case
13:var
q=d[4],r=d[2];a(c,d[3]);a(c,r);return b(j[19][13],c,q);case
16:return a(c,d[2]);case
6:case
7:var
m=d[3];a(c,d[2]);return a(c,m);case
14:case
15:var
g=d[1][2],h=g[2],i=h.length-1-1|0,s=g[3],t=0;if(!(i<0)){var
f=t;for(;;){a(c,I(h,f)[f+1]);a(c,I(s,f)[f+1]);var
u=f+1|0;if(i!==f){var
f=u;continue}break}}return 0;default:return 0}}var
x=[a6,cB,aY(0)];function
Y(b){return 0===b?a(c[3],cC):a(c[3],cD)}function
cE(a){return 0===a?1:0}function
E(b,a){return 1}function
cF(b){try{var
c=1+a(bp[4],[1,b])|0;return c}catch(a){return 0}}function
bq(b){switch(a(e[29],b)[0]){case
4:case
6:case
7:case
13:case
14:case
15:return 1;default:return 0}}var
cH=a(n[1][6],cG),cI=a(e[2],cH);function
F(g,f,d){function
c(d){return a(e[38],d)?cI:b(e[aD],c,d)}var
h=c(d);return i(K[6],g,f,h)}var
cK=a(n[1][6],cJ),cL=a(f[11],cK);function
aP(e,a,d){function
c(d){return b(f[54],a,d)?cL:i(f[109],a,c,d)}var
g=c(d);return i(K[11],e,a,g)}function
br(I,H,G,E,C,X,W,V){var
u=C[1],Z=C[2],_=H?H[1]:0,$=a(f[9],V),J=b(cM[34],u,$),aa=J[2],g=a(f[r][1],J[1]),d=b(j[17][68],f[r][1],aa),p=a(e[29],g);switch(p[0]){case
3:var
L=p[1][1];if(b(h[26],E,L))var
w=[0,[0,L],g,d];else
if(0===d)if(I)var
M=I[1],ac=M[1],ad=F(G,u,M[2]),ae=a(c[3],cN),af=Y(ac),ah=a(c[3],cO),aj=b(c[12],ah,af),ak=b(c[12],aj,ae),al=b(c[12],ak,ad),w=a(D(0),al);else
var
am=a(c[3],cP),w=i(m[6],0,0,am);else
var
w=[0,5,g,d];var
l=w,o=0;break;case
7:var
l=[0,3,g,d],o=0;break;case
8:var
an=p[4],ao=p[2],ap=aZ(an,a(e[1],1))?[0,2,g,d]:[0,5,ao,d],l=ap,o=0;break;case
10:var
N=p[1][1],A=cF(N);if(0===A)var
B=0;else
if(a(j[17][1],d)<A)var
B=0;else
var
P=b(j[17][107],A,d),aq=P[2],O=[0,[1,N],b(aw[13],g,P[1]),aq],B=1;if(!B)var
O=[0,1,g,d];var
l=O,o=0;break;case
16:var
l=[0,[1,a(n[62][6],p[1])],g,d],o=0;break;case
1:case
11:case
12:var
z=0,v=g,y=d,o=1;break;default:var
z=4,v=g,y=d,o=1}if(!o)var
z=l[1],v=l[2],y=l[3];var
K=a(j[19][12],y),x=[0,u],q=[0,u],ab=a(e[15],[0,v,K]),R=_?1:0,Q=a(ag[10],G),T=a(j[17][1],Q)+R|0;function
k(p){var
c=p;for(;;){var
g=a(e[29],c);if(3===g[0]){var
d=g[1],l=d[1],u=d[2];try{var
L=k(b(h[43],q[1],d));return L}catch(g){g=s(g);if(g===h[41]){if(b(h[26],E,l))return b(e[aD],k,c);var
m=b(h[23],q[1],l),v=a(h[6],m),w=b(as[6],0,u.length-1-T|0),y=b(j[17][108],w,v),z=function(c,b){var
d=c[2],f=c[1];if(0===b[0]){var
g=b[1],h=k(b[2]),j=i(aw[5],g,h,d);return[0,[0,a(e[2],g[1]),f],j]}var
l=b[2],m=b[1],n=k(b[3]),o=k(l);return[0,f,t(aw[4],m,o,n,d)]},A=a(f[r][5],y),B=[0,0,k(a(f[r][1],m[1]))],n=i(S[11][9],z,B,A),C=n[2],D=n[1],o=a(ai[1],0),F=x[1],G=a(f[9],C);x[1]=t(h[115],o,G,0,F);var
H=q[1],I=a(e[4],o),J=b(aw[13],I,D),K=a(f[9],J);q[1]=i(h[31],l,K,H);var
c=b(h[43],q[1],d);continue}throw g}}return b(e[aD],k,c)}}var
U=k(ab);return[0,x[1],[0,z,U,v,K,Z,W,X]]}function
bs(g,d,f){var
i=d[1],n=d[3],o=d[2],j=a$(g),k=j[1],p=j[2],l=a(e[29],k);switch(l[0]){case
3:var
m=l[1][1];if(b(h[35],i,m))throw x;var
c=[0,m];break;case
7:var
c=3;break;case
8:var
c=2;break;case
10:var
c=1;break;case
1:case
11:case
12:var
c=0;break;default:var
c=4}return[0,i,o,[0,c,g,k,p,n,f[6],f[7]]]}function
cQ(g,k,i){function
h(b){var
c=a(bp[12],[0,[1,g],b])[2][7];return a(j[17][1],c)}function
l(c){var
b=a(e[29],c);switch(b[0]){case
9:return b[2].length-1;case
16:return 0;default:throw[0,ak,cR]}}try{var
f=a(e[29],k);switch(f[0]){case
4:var
d=h([1,a(cT[12],f[1])]),c=2;break;case
6:var
d=h(0),c=2;break;case
10:if(b(n[17][12],f[1][1],g))var
d=l(i[3]),c=2;else
var
c=1;break;case
16:var
m=a(n[62][6],f[1]);if(b(n[17][12],m,g))var
d=l(i[3]),c=2;else
var
c=0;break;case
1:case
11:case
12:var
c=1;break;default:var
c=0}switch(c){case
0:var
d=-1;break;case
1:var
d=h([0,a(cS[16],k)]);break}return d}catch(a){a=s(a);if(a===ae)return-1;throw a}}function
bt(d,c){var
b=a(e[29],c);return 3===b[0]?a0(d,b[1][1]):0}function
ax(d,c,b){if(0===c)return d;var
f=c===b.length-1?b:i(j[19][7],b,0,c);return a(e[15],[0,d,f])}function
aQ(i){function
g(l,k){var
d=l,c=k;for(;;){var
f=a(e[29],d);switch(f[0]){case
3:var
m=f[1];try{var
n=g(b(h[43],i,m),c);return n}catch(a){return[0,d,c]}case
5:var
d=f[1];continue;case
9:var
o=f[1],d=o,c=b(j[19][5],f[2],c);continue;default:return[0,d,c]}}}return function(b){var
c=a(e[29],b);switch(c[0]){case
9:return g(c[1],c[2]);case
3:case
5:return g(b,[0]);default:return[0,b,[0]]}}}var
al=[a6,cU,aY(0)];function
bu(c){var
d=a(h[103],c);return function(a){function
c(c){try{b(h[24],a,c);var
d=1;return d}catch(a){a=s(a);if(a===ae)return 0;throw a}}return b(aO[7][16],c,d)}}function
cY(D,l,k,h,g,d){var
x=[0,0],y=[0,0],E=bu(d);function
c(l,g,t,h,q){var
p=a(aQ(h),q),n=p[2],d=p[1],k=[0,-1],o=n.length-1,u=0;function
v(h,j){var
g=h[4].length-1;if(o<g)return j;var
i=h[1];if(typeof
i==="number")switch(i){case
0:if(b(e[85],h[3],d))var
f=g,c=1;else
var
c=0;break;case
1:if(b(e[85],h[3],d))var
f=g,c=1;else
var
c=0;break;case
2:if(a(e[45],d))var
f=g,c=1;else
var
c=0;break;case
3:if(a(e[44],d))var
f=g,c=1;else
var
c=0;break;case
4:if(bq(d))var
f=g,c=1;else
var
c=0;break;default:var
f=g,c=1}else
if(0===i[0])if(bt(i[1],d))var
f=g,c=1;else
var
c=0;else
var
l=g+cQ(i[1],d,h)|0,m=o<l?-1:l,f=m,c=1;if(!c)var
f=-1;if(f<g)return j;if(k[1]<f)k[1]=o;return[0,[0,h,f],j]}var
w=i(j[17][16],v,l,u);for(;;){if(0<=k[1]){var
z=k[1];k[1]=-1;var
A=function(i){return function(z){var
p=z[2],c=z[1];if(i<=p)var
u=i<p?1:0;else
if(5===c[1]){k[1]=i-1|0;var
u=0}else{if(k[1]<p)k[1]=p;var
u=1}if(u)return 0;try{var
v=c[1];if(typeof
v==="number")switch(v){case
2:var
q=a(e[67],d),L=q[4],M=q[3],N=q[2],O=q[1],C=a(e[67],c[3]),P=C[4],R=C[2],S=a(f[9],N),T=Q(g,h,a(f[9],R),S),U=a(f[9],L),V=a(f[9],P),o=Q(b(ag[24],[0,O,M],g),T,V,U),l=1;break;case
5:var
l=0;break;case
3:case
4:var
W=a(f[9],d),o=Q(g,h,a(f[9],c[3]),W),l=1;break;default:var
o=h,l=1}else
if(0===v[0])var
_=a(e[72],c[3])[2],o=bl(g,h,_,0,a(e[72],d)[2]),l=1;else
var
l=0;if(!l)var
Y=ax(d,i-(c[4].length-1)|0,n),Z=a(f[9],Y),o=Q(g,h,a(f[9],c[3]),Z);var
F=bl(g,o,c[4],i-(c[4].length-1)|0,n),B=ax(d,i,n),G=a(c[7],B),w=av(0,g,t,F,a(f[9],c[5]),G),H=a(j[9],w),I=a(f[r][1],H),J=a(j[8],w),K=a(D,bs(B,[0,a(j[7],w),J,I],c));return K}catch(b){b=s(b);if(b[1]===al){if(a(E,b[2][1]))throw b}else{if(b===X){x[1]=1;return 0}if(b[1]===bk[1]){var
A=b[4];if(typeof
A!=="number"&&19===A[0]){y[1]=1;return 0}}}if(a(m[18],b))return 0;throw b}}}(z);b(j[17][11],A,w);continue}bo(function(a){return c(l,g,t,h,a)},d);var
B=function(a){return c(l,g,t,h,a)};return b(j[19][13],B,n)}}c(l,k,h,g,d);if(x[1])throw X;return y[1]}function
aS(b,c){return b[1]?0:(b[1]=[0,a(c,0)],0)}function
aT(d){var
b=d[1];if(b)return b[1];var
e=a(c[3],cZ);return i(m[3],0,0,e)}function
c0(e){var
f=e[1];if(f){var
d=f[1],g=d[3],h=d[2];e[1]=[0,[0,d[1],h+1|0,g]];try{var
k=b(j[17][7],g,h);return k}catch(a){a=s(a);if(a[1]===c1)throw x;throw a}}var
l=a(c[3],c2);return i(m[3],0,0,l)}function
A(J,E,q,K,y,w){var
k=w[2],h=w[1],A=J?J[1]:0,G=E?E[1]:0,l=[0,0],B=[0,0];if(y){var
g=y[1];if(0===g[1])var
L=g[2],p=0!==L?1:0,d=L;else
var
R=g[2],p=0===R?1:0,d=R}else
var
p=0,d=0;var
u=i(j[17][16],as[6],d,0),M=o.caml_make_vect(u,1-p);function
T(b){var
a=b-1|0;return I(M,a)[a+1]=p}b(j[17][11],T,d);if(0===u)B[1]=p;var
C=[0,0];function
N(b){return a(e[15],[0,b[3],b[4]])}function
H(d){if(q){var
l=q[1],n=l[2],o=l[1];if(k)if(!k[2]){var
A=k[1],B=a(c[5],0),C=F(d,h,N(A)),D=a(c[6],4),E=a(c[5],0),G=F(d,h,n),H=a(c[3],c5),I=Y(o),J=a(c[3],c6),K=b(c[12],J,I),L=b(c[12],K,H),M=b(c[12],L,G),O=b(c[12],M,E),P=b(c[12],O,D),Q=b(c[12],P,C);return b(c[12],Q,B)}var
s=a(c[13],0),t=F(d,h,n),u=a(c[3],c3),v=Y(o),w=a(c[3],c4),x=b(c[12],w,v),y=b(c[12],x,u),z=b(c[12],y,t);return b(c[12],z,s)}if(k)if(!k[2]){var
e=k[1],S=a(c[13],0),T=F(d,h,N(e)),j=e[1];if(typeof
j==="number")if(5<=j)var
g=0;else
var
r=a(f[9],e[5]),p=1-b(bv[30],h,r),g=1;else
var
g=0;if(!g)var
p=0;var
U=p?a(c[3],c8):a(c[3],c9),V=b(c[12],U,T);return b(c[12],V,S)}var
R=a(c[3],c7);return i(m[3],0,0,R)}var
v=[0,0];function
O(a){return v[1]}function
V(a){if(A){v[1]=b(j[18],v[1],[0,a,0]);return 0}throw[0,al,a]}function
P(a){if(a){var
c=a[1],d=c[3],f=c[1],g=a[2],h=d[4],k=d[3],l=z(f,d[5]),m=z(f,k),n=function(a){return z(f,a)},o=b(j[19][15],n,h),p=function(d){var
a=d[3],c=d[1],k=a[4],n=a[3],p=z(c,a[5]),q=z(c,n);function
r(a){return z(c,a)}var
s=b(j[19][15],r,k),f=b(e[80],l,p);if(f)var
g=b(e[80],m,q),h=g?i(c_[37],e[80],o,s):g;else
var
h=f;return 1-h};return[0,c,P(b(j[17][61],p,g))]}return 0}function
U(ak){var
r=C[1];if(r)var
s=r[1],B=s[1],g=a(j[17][5],s[3]),h=g[3],f=B,d=g[1],w=g[2],v=h[3],t=h[4],k=h;else{if(G)throw x;var
aj=a(c[3],df),A=i(m[3],0,0,aj),o=A[2],p=o[3],f=A[1],d=o[1],w=o[2],v=p[3],t=p[4],k=p}var
n=a(e[15],[0,v,t]);if(u<=l[1])return[0,n,k[6],[0,d,w,k[5]]];if(q)var
y=q[1],E=y[1],H=F(f,d,y[2]),I=a(c[3],c$),J=a(c[5],0),K=F(f,d,n),L=a(c[6],4),M=a(c[5],0),N=Y(E),O=a(c[3],da),P=b(c[12],O,N),Q=b(c[12],P,M),R=b(c[12],Q,L),S=b(c[12],R,K),T=b(c[12],S,J),U=b(c[12],T,I),z=b(c[12],U,H);else
var
af=F(f,d,n),ag=a(c[13],0),ah=a(c[3],de),ai=b(c[12],ah,ag),z=b(c[12],ai,af);var
V=b(j[15][47],l[1],db),W=a(c[3],V),X=a(c[16],u),Z=a(c[3],dc),_=a(c[16],l[1]),$=a(c[3],dd),aa=b(c[12],$,_),ab=b(c[12],aa,Z),ac=b(c[12],ab,X),ad=b(c[12],ac,W),ae=b(c[12],ad,z);return a(D(0),ae)}return[0,function(d,w,Z,W){aS(C,function(U){var
g=[0,0];try{if(1-A){var
C=bu(w),p=function(v){var
q=a(aQ(h),v),o=q[2],g=q[1],l=[0,-1],t=o.length-1,w=0;function
y(f,i){var
j=a(e[29],f[2]),h=9===j[0]?j[2].length-1:0;if(t<h)return i;var
d=f[1];if(typeof
d==="number")switch(d){case
0:var
c=b(e[85],f[3],g);break;case
1:var
c=b(e[85],f[3],g);break;case
2:var
c=a(e[45],g);break;case
3:var
c=a(e[44],g);break;case
4:var
c=bq(g);break;default:l[1]=t;var
c=1}else
if(0===d[0])var
c=bt(d[1],g);else{var
m=d[1],s=a(e[17],m),o=b(e[80],g,s);if(o)var
p=o;else{var
k=a(e[29],g);if(16===k[0])var
r=a(n[62][6],k[1]),q=b(n[17][12],r,m);else
var
q=0;var
p=q}var
c=p}if(c){if(l[1]<h)l[1]=h;return[0,[0,f,h],i]}return i}var
z=i(j[17][16],y,k,w);for(;;){if(0<=l[1]){var
u=l[1];l[1]=-1;var
A=ax(g,u,o),B=function(q,n){return function(y){var
p=y[2],k=y[1];if(q<=p)var
u=q<p?1:0;else
if(5===k[1]){l[1]=q-1|0;var
u=0}else{if(l[1]<p)l[1]=p;var
u=1}if(!u)if(a(aR[2],n))try{var
v=k[1];if(typeof
v==="number")if(2===v){var
z=function(f){var
d=a$(f),g=d[2],c=a(e[67],d[1]),h=c[4],i=c[3],k=c[1],l=b(j[19][45],c[2],g),m=[0,a(e[13],[0,k,i,h]),l];return a(e[15],m)},E=z(n);aM(d,h,z(k[2]),E);var
t=1}else
if(5<=v){var
B=function(c){var
d=e[8],f=[0,b(S[4],0,0),d,c];return a(e[13],f)},N=B(n);aM(d,h,B(k[2]),N);var
t=1}else
var
t=0;else
var
t=0;if(!t)aM(d,h,k[2],n);var
F=a(e[15],[0,k[3],k[4]]);try{var
G=a(f[9],n),H=Q(d,h,a(f[9],F),G)}catch(b){b=s(b);if(a(m[18],b))throw x;throw b}var
A=ax(g,q,o),I=a(k[7],A),w=av(0,d,K,H,a(f[9],k[5]),I),J=a(j[9],w),L=a(f[r][1],J),M=a(j[8],w);throw[0,al,bs(A,[0,a(j[7],w),M,L],k)]}catch(b){b=s(b);if(b[1]===al){if(a(C,b[2][1]))throw b}else
if(b===ae){var
D=a(c[3],cV);return i(m[3],0,0,D)}if(a(m[18],b))return 0;throw b}return 0}}(u,A);b(j[17][11],B,z);continue}bo(p,g);return b(j[19][13],p,o)}};try{p(w)}catch(b){b=s(b);if(b[1]!==cW)throw b;var
o=a(c[3],cX);i(m[3],0,0,o)}}g[1]=cY(V,k,d,K,h,w);throw x}catch(e){e=s(e);if(e[1]===al)return[0,d,0,[0,e[2],0]];var
T=e===x?0:e===X?0:1;if(!T)if(A)if(0!==O(0))return[0,d,0,P(O(0))];if(e===x)if(!G){if(g[1]){var
I=a(c[22],dj),J=H(d),L=b(c[12],J,I);return a(D(0),L)}var
M=a(c[3],dk),N=H(d),R=b(c[12],N,M);return a(D(0),R)}if(e===X){if(G)throw x;if(q)var
l=q[1][1];else
var
F=a(c[3],di),l=i(m[3],0,0,F);var
t=Y(cE(l)),u=a(c[3],dg),v=H(d),y=a(c[3],dh),z=b(c[12],y,v),B=b(c[12],z,u),E=b(c[12],B,t);return a(D(0),E)}throw e}});if(A)var
J=c0(C);else
var
aa=aT(C),ab=a(j[9],aa),J=a(j[17][5],ab);var
g=J[3],E=g[4],o=J[1];if(B[1])return w;var
L=g[1];if(typeof
L==="number")switch(L){case
0:var
y=a(e[85],g[3]),v=1;break;case
1:var
y=a(e[85],g[3]),v=1;break;case
2:var
z=a(e[67],g[3]),N=z[4],R=z[2],T=b(ag[24],[0,z[1],z[3]],d),y=function(f){var
b=a(e[29],f);if(8===b[0]){var
g=b[4],c=aj(d,o,R,b[2]);return c?aj(T,o,N,g):c}return 0},v=1;break;case
3:var
y=function(b){return 7===a(e[29],b)[0]?aj(d,o,g[3],b):0},v=1;break;default:var
v=0}else
var
v=0;if(!v)var
U=g[3],y=function(a){return aj(d,o,U,a)};var
_=E.length-1;function
F(d,s){var
v=d[1],G=d[2];if(B[1])return s;var
w=a(aQ(o),s),h=w[2],i=w[1];if(_<=h.length-1)if(a(y,i)){var
c=0,C=E.length-1;for(;;){var
k=c===C?1:0;if(k)var
m=k;else{var
D=I(h,c)[c+1],n=aj(v,o,I(E,c)[c+1],D);if(n){var
c=c+1|0;continue}var
m=n}if(m){var
x=b(j[19][58],E.length-1,h),H=x[2],z=a(e[15],[0,i,x[1]]);l[1]++;if(l[1]===u)B[1]=p;if(l[1]<=u)var
q=l[1]-1|0,A=I(M,q)[q+1];else
var
A=1-p;var
J=A?t(W,v,g[5],z,G):z,K=function(a){return F(d,a)},L=[0,J,b(j[19][62],K,H)];return a(e[15],L)}break}}function
N(a,c){var
d=c[2],e=c[1],g=0===a[0]?a:[0,a[1],a[3]];return[0,b(f[121],g,e),d+1|0]}function
O(c,b){var
d=F(c,a(f[r][1],b));return a(f[9],d)}var
P=a(f[9],i),Q=$(bv[20],o,N,O,d,P),R=a(f[r][1],Q);function
S(a){return F(d,a)}var
T=[0,R,b(j[19][62],S,h)];return a(e[15],T)}return F([0,d,Z],w)},U]}function
ay(d){switch(d[0]){case
0:return p(d[1]);case
1:var
e=p(d[1]),f=a(c[3],dl);return b(c[12],f,e);case
2:var
g=d[1],h=p(d[2]),i=a(c[3],dm),j=p(g),k=b(c[12],j,i);return b(c[12],k,h);case
3:var
l=d[1],m=p(d[2]),n=a(c[3],dn),o=p(l),q=a(c[3],dp),r=b(c[12],q,o),s=b(c[12],r,n);return b(c[12],s,m);case
4:var
t=d[2],u=d[1],v=p(d[3]),w=a(c[3],dq),x=p(t),y=a(c[3],dr),z=p(u),A=b(c[12],z,y),B=b(c[12],A,x),C=b(c[12],B,w);return b(c[12],C,v);default:var
D=d[2],E=d[1],F=p(d[3]),G=a(c[3],ds),H=p(D),I=a(c[3],dt),J=p(E),K=b(c[12],J,I),L=b(c[12],K,H),M=b(c[12],L,G);return b(c[12],M,F)}}function
bw(d){switch(d[0]){case
0:return p(d[1]);case
1:var
e=p(d[1]),f=a(c[3],du);return b(c[12],f,e);case
2:var
g=d[1],h=p(d[2]),i=a(c[3],dv),j=a(L[6],g),k=b(c[12],j,i);return b(c[12],k,h);case
3:var
l=d[1],m=p(d[2]),n=a(c[3],dw),o=a(L[6],l),q=a(c[3],dx),r=b(c[12],q,o),s=b(c[12],r,n);return b(c[12],s,m);case
4:var
t=d[2],u=d[1],v=p(d[3]),w=a(c[3],dy),x=a(L[6],t),y=a(c[3],dz),z=p(u),A=b(c[12],z,y),B=b(c[12],A,x),C=b(c[12],B,w);return b(c[12],C,v);default:var
D=d[2],E=d[1],F=p(d[3]),G=a(c[3],dA),H=a(L[6],D),I=a(c[3],dB),J=p(E),K=b(c[12],J,I),M=b(c[12],K,H),N=b(c[12],M,G);return b(c[12],N,F)}}function
dK(R,h){var
d=h[2],g=h[1];function
e(b){var
c=aN(g,g,a(f[9],b));return aP(R,g,a(j[9],c))}switch(d[0]){case
0:return e(d[1]);case
1:var
i=e(d[1]),k=a(c[3],dC);return b(c[12],k,i);case
2:var
l=d[1],m=e(d[2]),n=a(c[3],dD),o=e(l),p=b(c[12],o,n);return b(c[12],p,m);case
3:var
q=d[1],r=e(d[2]),s=a(c[3],dE),t=e(q),u=a(c[3],dF),v=b(c[12],u,t),w=b(c[12],v,s);return b(c[12],w,r);case
4:var
x=d[2],y=d[1],z=e(d[3]),A=a(c[3],dG),B=e(x),C=a(c[3],dH),D=e(y),E=b(c[12],D,C),F=b(c[12],E,B),G=b(c[12],F,A);return b(c[12],G,z);default:var
H=d[2],I=d[1],J=e(d[3]),K=a(c[3],dI),L=e(H),M=a(c[3],dJ),N=e(I),O=b(c[12],N,M),P=b(c[12],O,L),Q=b(c[12],P,K);return b(c[12],Q,J)}}var
aU=ch(dL,function(b,a){return ay});function
C(e,a){var
c=a[2][2],f=a[1];if(c)if(!a[3]){var
d=c[1];return[0,f,[0,b(dM[6],e,d)[1],[0,d]],0]}return a}function
bx(x,h){af([ac,function(f){var
d=aG(h),e=a(c[3],dN);return b(c[12],e,d)}]);function
e(b){var
c=C(x,bj(b,0));return a(j[8],c)}function
f(e,d,c){var
f=b(as[17],dO,d),g=[0,a(n[1][6],f)],h=0,i=0,j=0===c?O:b(v[3],0,[4,O,c]);return[0,e,[0,ah(O,b(v[3],0,[5,g,0,O,j])),i],h]}function
l(o,n){var
h=bg(0),f=o[1];if(0===f[0]){var
g=f[1];if(a(M[33],g))var
j=a(M[35],g),d=1;else
var
d=0}else
var
d=0;if(!d)var
k=a(c[3],cj),j=i(m[3],0,0,k);var
l=[4,[0,[0,[0,b(N[1],0,[0,j]),0],cn,h],0],n];return e(au(0,h,b(N[1],0,l)))[1]}function
Q(b){var
c=1-aH(b);return c?a8(a(bh[6],b),dP):c}var
R=h[2],S=R[2],d=h[1],Z=R[1];if(S){var
T=S[1];if(a5===d)return C(x,[0,40,[0,Z,[0,T]],0]);var
g=T[1];if(17===g[0]){var
U=g[1];if(!U[1]){var
o=U[2];if(J(o,dQ))if(J(o,dR))if(J(o,dS)){if(!J(o,dT)){var
p=g[2],y=p[1];if(y){var
z=y[2];if(z){var
A=z[2];if(A)if(!A[2])if(!p[2])if(!p[3])if(!p[4]){var
V=z[1],_=A[1],$=y[1];Q(V);var
aa=[0,l(V,_),0];return f(d,dU,[0,e($)[1],aa])}}}}}else{var
q=g[2],B=q[1];if(B){var
D=B[2];if(D)if(!D[2])if(!q[2])if(!q[3])if(!q[4]){var
E=D[1],k=B[1];try{var
W=e(k),r=e(E),F=W[1];if(W[2])if(r[2])var
X=r[1],ab=aH(k)?f(d,dW,[0,F,[0,X,[0,l(k,E),0]]]):f(d,dX,[0,F,[0,X,0]]),G=ab,w=1;else
var
w=0;else
if(r[2])var
w=0;else
var
G=f(d,dZ,[0,F,[0,r[1],0]]),w=1;if(!w)var
ad=a(c[3],dY),G=i(m[3],0,0,ad);return G}catch(a){a=s(a);if(aH(k))return f(d,dV,[0,l(k,E),0]);throw a}}}}else{var
t=g[2],H=t[1];if(H){var
I=H[2];if(I){var
K=I[2];if(K)if(!K[2])if(!t[2])if(!t[3])if(!t[4]){var
Y=I[1],ae=K[1],ag=H[1];Q(Y);var
ai=[0,l(Y,ae),0];return f(d,d0,[0,e(ag)[1],ai])}}}}else{var
u=g[2],L=u[1];if(L){var
P=L[2];if(P)if(!P[2])if(!u[2])if(!u[3])if(!u[4]){var
aj=L[1],ak=[0,e(P[1])[1],0];return f(d,d1,[0,e(aj)[1],ak])}}}}}return C(x,h)}return h}function
d2(b,a){switch(a[0]){case
0:return[0,bx(b,a[1])];case
1:return[1,C(b,a[1])];case
2:var
c=a[1];return[2,c,C(b,a[2])];case
3:var
d=a[1];return[3,d,C(b,a[2])];case
4:var
e=a[2],f=a[1],g=C(b,a[3]);return[4,C(b,f),e,g];default:var
h=a[2],i=a[1],j=C(b,a[3]);return[5,C(b,i),h,j]}}function
G(c,a){var
d=a[3],e=a[1];return[0,e,b(d3[3],c,a[2]),d]}function
d4(b,a){switch(a[0]){case
0:return[0,G(b,a[1])];case
1:return[1,G(b,a[1])];case
2:var
c=a[1];return[2,c,G(b,a[2])];case
3:var
d=a[1];return[3,d,G(b,a[2])];case
4:var
e=a[2],f=a[1],g=G(b,a[3]);return[4,G(b,f),e,g];default:var
h=a[2],i=a[1],j=G(b,a[3]);return[5,G(b,i),h,j]}}function
w(b,a){return[0,a[1],a[2],[0,b]]}function
d5(c,r,b){switch(b[0]){case
0:var
d=[0,w(c,b[1])];break;case
1:var
d=[1,w(c,b[1])];break;case
2:var
e=b[1],f=w(c,b[2]),d=[2,w(c,e),f];break;case
3:var
g=b[1],h=w(c,b[2]),d=[3,w(c,g),h];break;case
4:var
i=b[2],j=b[1],k=w(c,b[3]),m=w(c,i),d=[4,w(c,j),m,k];break;default:var
n=b[2],o=b[1],p=w(c,b[3]),q=w(c,n),d=[5,w(c,o),q,p]}return[0,a(l[2],r),d]}var
d6=j[7];function
d7(a,b){return[0,a[1],a[2],[0,b]]}function
az(k){var
e=k[2],f=e[2],g=a(v[1],e[1]);if(f){var
d=f[1][1];switch(d[0]){case
0:var
h=d[1];if(a(M[33],h))var
c=[0,a(M[35],h)],b=1;else
var
b=0;break;case
6:if(d[2])var
b=0;else{var
i=d[1][2];if(a(M[33],i))var
c=[0,a(M[35],i)],b=1;else
var
b=0}break;default:var
b=0}}else
if(0===g[0]){var
j=g[1];if(0===j[0])var
c=[0,j[1]],b=1;else
var
b=0}else
var
b=0;if(!b)var
c=0;return c?c[1]:a8(P(k),d8)}function
aA(g,f){var
h=f[3],j=f[2],u=a(l[2],g),v=a(l[5],g),d=j[2],k=j[1];if(d){var
o=d[1];if(h){var
p=n[1][10][1],q=h[1][1],r=function(c,d,a){return b(n[1][10][4],c,a)},s=i(n[1][11][12],r,q,p),e=ba[4];return gy(ba[7],1,v,u,0,0,[0,[0,s,e[2],e[3]]],o)}var
t=a(c[3],cb);return i(m[3],0,0,t)}return k}function
d$(d,c,b){var
e=w(d,b);return[0,a(l[2],c),e]}function
ao(u,h){var
i=h[3],v=h[2];if(i){var
g=d_[13],w=i[1],o=a(B[5],g),p=b(B[7],o,v),d=[0,0],q=b(an[10],w,p),k=function(b){d[1]=[0,b];return a(am[16],0)},l=b(bd[4],q,k),m=a(a(am[72][7],l),u)[2],e=d[1];if(e){var
n=e[1],s=a(B[6],g),t=[0,m,b(an[2][7],s,n)];return b(j[2],f[r][1],t)}throw[0,ak,d9]}var
x=a(c[3],ea);return a(D(0),x)}function
eb(l,d,c){var
m=a(n[1][10][5],l),e=b(aB[3][1],d,c),o=b(aB[3][4],d,c),k=a(h[118],d);try{var
p=a(ag[11],e),q=[0,$(ai[52],e,k,p,o,m)],f=q}catch(a){a=s(a);if(a[1]!==ai[50])throw a;var
f=0}if(f){var
g=f[1],j=i(aB[3][5],g[1],g[2],g[3]);return $(aB[3][7],e,j[3],c,j[1],j[2])}return k}function
by(E,g,D,C){af([ac,function(f){var
d=ay(D),e=a(c[3],ec);return b(c[12],e,d)}]);function
u(b,a){return[2,b,a]}function
al(b,a){return[3,b,a]}function
am(a){return[1,a]}function
k(a,c,b){var
d=a?a[1]:32;return[0,d,[0,c,0],b]}function
q(d,p,y,o){var
e=d[3];try{var
z=aA(g,d),f=a(v[1],z);switch(f[0]){case
1:var
q=f[1];if(a(H[2],e)){var
A=a(H[7],e)[1],r=b(n[1][11][3],q,A);if(r)var
t=1-a(H[3],p),u=t?1-a(H[3],E):t;else
var
u=r;if(u)var
C=a(H[7],e)[1],D=b(n[1][11][23],q,C),F=a(H[7],E),G=a(B[6],F),I=b(an[2][7],G,D),i=b(H[7],p,I),c=1,k=0;else
var
k=1}else
var
k=1;if(k)var
c=0;break;case
14:var
j=f[2];if(typeof
j==="number")var
h=1;else
if(0===j[0]){var
w=j[1];if(bf(f[1]))if(ck(w))var
x=aI(w),i=b(y,x[1],[0,32,[0,x[2],0],e]),c=1,h=0,l=0;else
var
l=1;else
var
l=1;if(l)var
c=0,h=0}else
var
h=1;if(h)var
c=0;break;default:var
c=0}if(!c)var
i=a(o,d);return i}catch(b){b=s(b);if(a(m[18],b))return a(o,d);throw b}}function
r(d,c,b,a){return q(k(0,c,d),0,b,a)}function
y(d,k){var
e=a(c[3],ed),f=a(c[3],d),g=a(c[3],ee),h=b(c[12],g,f),j=b(c[12],h,e);return i(m[3],0,0,j)}function
F(t,k,r,c){var
m=a(e[29],t);if(3===m[0]){var
u=m[1][1],n=a(l[6],g),o=a(S[11][4],n),d=[0,0];try{b(S[11][5],k,n);var
y=function(m){var
e=0===d[1]?1:0;if(e){var
n=b(h[23],c,m),f=a(h[5],n),g=a(S[11][4],f),i=o<g?1:0;if(i){var
p=b(j[17][7],f,(g-o|0)-1|0);d[1]=[0,a(S[11][1][2],p)];var
k=0}else
var
k=i;var
l=k}else
var
l=e;return l},f=d,p=y}catch(a){a=s(a);if(a!==ae)throw a;var
f=[0,[0,k]],p=function(a){return 0}}var
v=a(l[2],g),q=function(d,f){var
g=a(e[29],f);if(3===g[0]){var
c=g[1][1];if(!a0(c,u))if(!b(j[17][25],c,d))if(!b(h[26],v,c)){p(c);return[0,c,d]}return d}return i(e[99],q,d,f)},w=q(0,z(c,r)),x=function(c,d){if(b(h[35],c,d))return c;if(a(H[3],f[1]))return c;var
e=a(H[7],f[1]);af([ac,function(b){return a(L[6],e)}]);return eb(e,c,d)};return i(j[17][15],x,c,w)}throw[0,ak,ef]}function
A(b){switch(b[0]){case
0:var
e=b[1],x=e[2],z=x[1],K=e[1];if(x[2])return q(e,[0,A],u,function(a){return[0,a]});var
c=e[3],g=a(v[1],z);if(14===g[0]){var
h=g[2];if(typeof
h==="number")var
I=0;else
if(0===h[0]){var
B=h[1];if(bf(g[1])){var
M=aI(B)[1],C=a(n[1][8],M),D=8<bR(C)?1:0,N=D?o.caml_string_equal(i(j[15][4],C,0,8),eg):D;if(N){var
E=aI(B),O=E[2],d=a(n[1][8],E[1]),F=i(j[15][4],d,8,bR(d)-8|0),f=a(v[1],O);if(J(F,eh)){if(!J(F,ei))if(4===f[0]){var
l=f[2];if(l){var
m=l[2],p=l[1];if(!m)return r(c,p,u,function(a){return[0,a]});var
s=m[2],G=m[1];if(!s){var
S=function(a){return y(d,a)},T=k(0,p,c);return r(c,G,function(a,b){return[4,T,a,b]},S)}if(!s[2]){var
P=s[1],Q=function(a){return r(c,P,u,function(a){throw[0,ak,ej]})},R=k(0,p,c);return r(c,G,function(a,b){return[4,R,a,b]},Q)}}}}else
if(4===f[0]){var
t=f[2];if(t){var
w=t[2];if(w)if(!w[2]){var
U=w[1],V=t[1],W=function(a){return y(d,a)},X=k(0,V,c);return r(c,U,function(a,b){return[5,X,a,b]},W)}}}return y(d,0)}}var
I=1}else
var
I=0}var
L=function(a){return[0,a]};return q(k([0,K],z,c),[0,A],u,L);case
1:return q(b[1],0,al,am);case
2:var
H=b[1],Y=b[2],Z=function(a){return[2,az(H),a]};return q(Y,0,function(a,b){return[4,H,a,b]},Z);case
3:var
_=b[2];return[3,az(b[1]),_];case
4:var
$=b[3],aa=b[1];return[4,aa,az(b[2]),$];default:var
ab=b[3],ac=b[1];return[5,ac,az(b[2]),ab]}}var
d=A(D);af([ac,function(g){var
e=bw(d),f=a(c[3],ek);return b(c[12],f,e)}]);if(C){var
G=C[1],p=[0,32,G[1],[0,G[2]]];switch(d[0]){case
0:var
I=d[1],ap=P(I),t=[0,aJ(I,p,function(a,b){return au(ap,a,b)},ah)];break;case
2:var
aD=d[2],aE=d[1],aF=aA(g,p),aG=p[3],t=[5,k(0,ah(O,aF),aG),aE,aD];break;case
4:var
ai=d[3],aH=d[2],aK=d[1],aL=p[3],aM=k(0,aA(g,p),aL),aN=P(ai),t=[4,aJ(aK,aM,function(a,b){return au(aN,a,b)},ah),aH,ai];break;case
5:var
aj=d[3],aO=d[2],aP=d[1],aQ=p[3],aS=k(0,aA(g,p),aQ),aT=P(aj),t=[5,aJ(aP,aS,function(a,b){return au(aT,a,b)},ah),aO,aj];break;default:var
t=d}var
f=t}else
var
f=d;af([ac,function(g){var
d=bw(f),e=a(c[3],el);return b(c[12],e,d)}]);function
K(a,d,c){var
e=c[3],f=c[2],g=f[2],h=f[1],i=c[1];if(g){var
k=g[1],l=bg(a),j=[5,b(N[1],a,d),l,0,k];return[0,i,[0,h,[0,b(N[1],a,j)]],e]}var
m=[7,d,b(v[3],a,[13,[1,d],0,0]),0,h];return[0,i,[0,b(v[3],a,m),0],e]}switch(f[0]){case
0:var
M=ao(g,f[1]);return[0,M[1],[0,M[2]]];case
1:var
Q=ao(g,f[1]);return[0,Q[1],[1,Q[2]]];case
2:case
3:var
R=f[1],T=ao(g,K(0,[0,R],f[2])),aq=T[1],U=a(e[67],T[2]),V=U[4],w=U[2],W=F(w,R,V,aq),ar=z(W,V),X=b(aR[14],w,ar),as=2===f[0]?[2,w,X]:[3,w,X];return[0,W,as];default:var
Y=f[2],at=f[1],Z=ao(g,K(0,[0,Y],f[3])),av=Z[1],_=a(e[67],Z[2]),$=_[4],x=_[2],aa=F(x,Y,$,av),aw=z(aa,$),ab=b(aR[14],x,aw),ax=a(h[87],g),ad=ao(b(l[3],ax,aa),at),ag=ad[2],aB=ad[1],aC=4===f[0]?[4,ag,x,ab]:[5,ag,x,ab];return[0,aB,aC]}}function
bz(c,b,a){return by(0,c,[0,b],a)}function
em(d){var
b=d[2];if(0===b[0]){var
c=a(e[29],b[1]);return 1===c[0]?[0,c[1]]:0}return 0}function
bA(w,g,k,o,n,q,p){function
j(b,a){return z(b,a)}function
x(j,e,n){var
d=b(h[23],j,e),l=d[3];if(l)var
m=a(f[r][1],l[1]);else
var
q=a(c[3],en),s=a(c[3],eo),t=a(c[13],0),u=a(aO[1],e),v=a(c[16],u),w=a(c[3],ep),x=i(K[6],g,k,n),y=a(c[3],eq),z=b(c[12],y,x),A=b(c[12],z,w),B=b(c[12],A,v),C=b(c[12],B,t),E=b(c[12],C,s),F=b(c[12],E,q),m=a(D(0),F);var
o=[0,d[1],d[2],0,d[4],d[5],d[6],d[7]],p=b(h[25],j,e);return[0,i(h[22],p,e,o),m]}function
y(c){var
b=a(e[29],c);if(3===b[0])return b[1][1];throw[0,ak,er]}function
m(i,h,g,b,a,f){var
c=b[2],d=b[1],k=a?a[1]:c,e=br(0,i,h,g,[0,d,k],f,0,j(d,c));return[0,e[1],[0,e[2],0]]}if(n){var
H=n[1],l=H[2],d=H[1];switch(l[0]){case
4:var
P=l[2],ah=l[3],ai=j(d,l[1]),u=j(d,ah),aj=y(P),Q=A(0,0,0,k,T,m(et,g,k,[0,d,u],0,E)),al=Q[2],am=Q[1],S=A(0,0,0,d,T,m(0,g,d,[0,d,P],0,E)),an=S[2],ao=S[1],U=A(0,w,0,k,q,m(0,g,k,[0,d,ai],0,E)),ap=U[2],aq=U[1],ar=t(am,g,o,1,function(b,i,q,g){var
k=a(f[9],u),l=a(f[9],i),c=R(b,a(h[V],d),l,k),e=x(c,aj,u),m=e[2],n=e[1];function
o(b,d,c,a){return t(aq,b,m,a,p)}return j(c,t(ao,b,j(n,u),g,o))}),as=a(ap,0)[3][2];a(an,0);a(al,0);return[0,ar,as];case
5:var
B=l[2],at=l[3],C=j(d,l[1]),v=j(d,at),au=y(B),av=a(f[9],C),W=R(g,d,a(f[9],B),av),X=A(0,0,0,k,T,m(eu,g,k,[0,W,j(W,v)],0,E)),aw=X[2],ax=X[1],Y=A(0,0,0,d,q,m(0,g,d,[0,d,B],0,E)),ay=Y[2],az=Y[1],aA=t(ax,g,o,1,function(b,k,q,i){var
l=a(f[9],v),m=a(f[9],k),c=R(b,a(h[V],d),m,l),e=x(c,au,v),g=e[1],n=e[2];function
o(b,i,h,d){var
e=a(f[9],C),c=j(R(b,g,a(f[9],n),e),C);return t(p,b,c,c,d)}return j(c,t(az,b,j(g,v),i,o))});a(ay,0);return[0,aA,a(aw,0)[3][2]];case
0:case
1:var
Z=j(d,l[1]),_=a(h[V],d);if(n)if(0===n[1][2][0])var
I=q,F=1;else
var
F=0;else
var
F=0;if(!F)var
I=T;var
J=A(0,w,0,k,I,m(0,g,k,[0,_,Z],0,E)),$=J[2],aa=t(J[1],g,o,1,p);return[0,aa,a($,0)[3][2]];default:var
L=l[1],s=j(d,l[2]);if(n)if(2===n[1][2][0])var
M=q,G=1;else
var
G=0;else
var
G=0;if(!G)var
M=T;var
ab=y(L),N=A(0,0,0,k,T,m(es,g,k,[0,d,s],0,E)),ac=N[2],ad=N[1],O=A(0,w,0,d,M,m(0,g,d,[0,d,L],0,E)),ae=O[2],af=O[1],ag=t(ad,g,o,1,function(c,k,r,i){var
l=a(f[9],s),m=a(f[9],k),e=R(c,a(h[V],d),m,l),g=x(e,ab,s),n=g[2],o=g[1];function
q(a,c){return b(p,a,n)}return j(e,t(af,c,j(o,s),i,q))});a(ae,0);return[0,ag,a(ac,0)[3][2]]}}var
aB=bn[2];return[0,t(p,g,o,o,1),aB]}function
bB(d,k,b){var
e=b[2],f=b[1],l=d?d[1]:0;switch(e[0]){case
1:case
3:var
o=a(c[3],ew),g=i(m[3],0,0,o);break;default:var
g=e[1]}var
j=l?aC(bm[23],0,0,0,ev,k,f):f,n=a(h[bU],j);return[0,z(j,g),n]}function
bC(m,f,l,k,d,c,j){if(a0(c,ex))var
h=0,g=ey;else
var
h=1,g=c;var
b=[0,0],i=bA(m,f,l,k,[0,d],g,function(g,c,f,d){aS(b,function(a){return c});return h?a(e[1],(d+j|0)-1|0):c}),n=i[2],o=i[1],p=0===b[1]?bB(0,f,d)[1]:aT(b);return[0,[0,p,n],o]}function
aV(g,f,e,d,c,b,a){return br(g,0,f,e,d,c,b,a)}function
ez(g,f,e,d,c,b,a){return bA(g,f,e,d,c,b,a)[1]}function
eA(g,p,o,d,n,c,m,l){var
q=c[2],s=c[1],u=a(f[r][1],n),v=a(f[r][1],p),w=a(h[V],s),i=aV(0,g,d,[0,w,a(f[r][1],q)],m,0,u),j=A(0,eB,0,d,o,[0,i[1],[0,i[2],0]]),x=j[2],y=j[1],z=t(y,g,v,l,function(c,b,a){return e[1]}),k=a(x,0),b=k[3],B=b[3],C=b[2],D=b[1],E=a(f[9],k[1]),F=a(f[9],z);return[0,D,C,a(f[9],B),F,E]}function
eC(g,n,r,d,l){var
e=l[2],j=l[1];try{var
f=eA(g,n,r,d,e,[0,j,e],E,1),p=f[1],F=f[4],G=f[3],H=f[2];if(p!==d)var
I=a(c[3],eF),q=i(m[6],0,0,I);else
var
q=[0,F,[0,b(h[a3],p,H),G]];return q}catch(f){f=s(f);if(f===x)try{var
z=function(a){return 1},k=av(0,g,d,a(h[V],j),e,z),o=k[1],A=k[3],B=k[2];if(o!==d)throw x;var
C=[0,n,[0,b(h[a3],o,B),A]];return C}catch(d){var
t=a(c[3],eD),u=aP(g,j,e),v=a(c[3],eE),w=b(c[12],v,u),y=b(c[12],w,t);return a(D(0),y)}throw f}}function
eG(b,e,d){var
f=a(l[2],b),g=a(l[5],b),c=eC(g,a(l[4],b),e,f,d);return[0,c[1],c[2][2]]}function
eH(a){var
c=[0,[0,n[1][11][1],0,an[3][2]]];return[0,32,[0,b(v[3],0,[0,[0,a],0]),0],c]}function
eI(d){var
b=d[2],c=b[2],e=a(v[1],b[1]),f=c?12===c[1][1][0]?1:0:13===e[0]?1:0;return f?1:0}function
eJ(d,c){var
e=a(l[2],c),f=b(h[a3],e,d),g=a(h[87],c);return b(l[3],g,f)}function
eK(d,c){var
e=a(l[2],c),f=b(h[a4],e,d),g=a(h[87],c);return b(l[3],g,f)}function
bD(a,b){return by([0,aU],a,b,0)}var
eO=[0,function(m,c){var
d=c[1],e=a(n[1][6],eN),g=b(n[1][11][23],e,d),j=a(B[6],aU),A=b(an[2][7],j,g);function
k(c){var
p=bD(c,A),q=a(l[2],c),s=a(l[4],c),t=a(f[r][1],s),e=bC(0,a(l[5],c),q,t,p,T,1),u=e[2],g=a(f[9],e[1][1]),v=a(f[9],u),d=b(l[13],c,g),j=d[2],k=d[1],m=a(h[87],c),o=b(l[3],m,k),w=[0,a(n[1][6],eL)],x=[0,b(S[4],w,0),g,j,v],y=a(f[22],x),z=i(eM[3],0,y,2);return b(am[72][7],z,o)}return b(am[72][1],0,k)}];i(bF[16],0,bE,eO);var
eP=[31,b(N[1],0,[0,[0,bE,0],0])],eR=[28,[0,[0,[0,a(n[1][6],eQ)],0],eP]];function
eS(c){var
b=a(n[1][6],eT);return $(bF[10],1,0,0,b,eR)}b(bG[13],eS,eU);function
bH(n,d){var
o=a(l[4],d),g=a(l[2],d),h=a(l[5],d),p=a(f[r][1],o),j=bz(d,n,0),k=j[2],q=j[1];if(0===k[0])var
e=k[1];else
var
y=a(c[3],e2),e=a(D(0),y);var
u=0,m=aV(0,h,g,[0,q,e],function(a,b){return 1},u,e),v=A(eW,eV,0,g,0,[0,m[1],[0,m[2],0]])[1];function
w(A,f,e,z){var
g=d[2],h=a(l[5],d),j=i(K[6],h,g,e),k=a(c[13],0),m=a(c[3],eX),n=a(c[13],0),o=d[2],p=a(l[5],d),q=i(K[6],p,o,f),r=a(c[13],0),s=a(c[3],eY),t=b(c[12],s,r),u=b(c[12],t,q),v=b(c[12],u,n),w=b(c[12],v,m),x=b(c[12],w,k),y=b(c[12],x,j);b(aE,0,b(c[26],1,y));return e}b(aE,0,a(c[3],eZ));try{for(;;){t(v,h,p,1,w);continue}}catch(e){e=s(e);if(e===x){b(aE,0,a(c[3],e0));return a(e1[1],d)}throw e}}var
k=[0,aU,d2,d4,d5,ay,function(a){return a},bj,bi,bx,G,d$,aG];aX(217,[0,aG,ay,x,X,dK,bB,bD,bz,ez,bC,Y,aV,A,eG,d7,aS,aT,R,cA,d6,P,em,eI,eH,F,aP,eJ,eK,a_,bH,k],"Ssrmatching_plugin__Ssrmatching");var
e3=a(y[6],0);a(bG[9],bI);function
Z(c,b,a){return k[5]}function
e4(b,a){return Z}function
e5(b,a){return Z}var
e6=[0,function(b,a){return Z},e5,e4],e7=[2,k[4]],e8=[0,k[3]],e9=k[2],e_=[0,function(a,c){return[0,a,b(e9,a,c)]}],e$=a(B[6],k[1]),fa=[0,a(W[3],e$)],fb=0;function
fc(c,e){var
d=[0,b(k[7],c,0)];return a(k[6],d)}var
fd=[0,[0,[0,0,[6,q[16][3]]],fc],fb];function
fe(c,f,e){var
d=[1,b(k[7],c,0)];return a(k[6],d)}var
ff=[6,q[16][3]],fh=[0,[0,[0,[0,0,[0,a(y[10],fg)]],ff],fe],fd];function
fi(d,h,c,g){var
e=b(k[7],d,0),f=[2,b(k[7],c,0),e];return a(k[6],f)}var
fj=[6,q[16][3]],fl=[0,a(y[10],fk)],fm=[0,[0,[0,[0,[0,0,[6,q[16][3]]],fl],fj],fi],fh];function
fn(d,i,c,h,g){var
e=b(k[7],d,0),f=[3,b(k[7],c,0),e];return a(k[6],f)}var
fo=[6,q[16][3]],fq=[0,a(y[10],fp)],fr=[6,q[16][3]],ft=[0,[0,[0,[0,[0,[0,0,[0,a(y[10],fs)]],fr],fq],fo],fn],fm];function
fu(e,l,d,j,c,i){var
f=b(k[7],e,0),g=b(k[7],d,0),h=[4,b(k[7],c,0),g,f];return a(k[6],h)}var
fv=[6,q[16][3]],fx=[0,a(y[10],fw)],fy=[6,q[16][3]],fA=[0,a(y[10],fz)],fB=[0,[0,[0,[0,[0,[0,[0,0,[6,q[16][3]]],fA],fy],fx],fv],fu],ft];function
fC(e,l,d,j,c,i){var
f=b(k[7],e,0),g=b(k[7],d,0),h=[5,b(k[7],c,0),g,f];return a(k[6],h)}var
fD=[6,q[16][3]],fF=[0,a(y[10],fE)],fG=[6,q[16][3]],fI=[0,a(y[10],fH)],bJ=b(ap[9],fJ,[0,[1,[0,[0,[0,[0,[0,[0,[0,0,[6,q[16][3]]],fI],fG],fF],fD],fC],fB]],fa,e_,e8,e7,e6]),bK=bJ[2],aq=bJ[1];function
_(c,b,a){return k[12]}function
fK(b,a){return _}function
fL(b,a){return _}var
fM=[0,function(b,a){return _},fL,fK],fN=[2,k[11]],fO=[0,k[10]],fP=k[9],fQ=[0,function(a,c){return[0,a,b(fP,a,c)]}],fR=0,fS=0;function
fT(a,d,c){return b(k[7],a,0)}var
fU=[6,q[16][1]],fW=[0,[1,[0,[0,[0,[0,0,[0,a(y[10],fV)]],fU],fT],fS]],fR,fQ,fO,fN,fM],bL=b(ap[9],fX,fW),bM=bL[2],aW=bL[1];function
fY(d){var
a=b(j[23],0,d);if(typeof
a!=="number"&&0===a[0]){var
c=a[1];if(!J(c,fZ))return 40;if(!J(c,f0))return 64}return 32}var
bN=b(q[2][4],f1,fY),f2=0,f3=0;function
f4(b,a,d){var
c=i(k[8],a,b,0);if(aZ(P(c),[0,d]))if(40===a)return i(k[8],a5,b,0);return c}i(q[19],bM,0,[0,0,[0,[0,0,0,[0,[0,[0,[0,0,[6,bN]],[6,q[16][1]]],f4],f3]],f2]]);function
f5(b,a){return _}function
f6(b,a){return _}var
f7=[0,function(b,a){return _},f6,f5],f8=[2,k[11]],f9=[0,k[10]],f_=k[9],f$=[0,function(a,c){return[0,a,b(f_,a,c)]}],ga=a(B[6],aW),gb=[0,a(W[3],ga)],gc=0;function
gd(a,d,c){return b(k[7],a,0)}var
ge=[6,q[16][3]],gg=[0,[1,[0,[0,[0,[0,0,[0,a(y[10],gf)]],ge],gd],gc]],gb,f$,f9,f8,f7],bO=b(ap[9],gh,gg),bP=bO[2],gi=bO[1],gj=0,gk=0;function
gl(b,a,d){var
c=i(k[8],a,b,0);if(aZ(P(c),[0,d]))if(40===a)return i(k[8],a5,b,0);return c}i(q[19],bP,0,[0,0,[0,[0,0,0,[0,[0,[0,[0,0,[6,bN]],[6,q[16][3]]],gl],gk]],gj]]);function
gm(b,a){return Z}function
gn(b,a){return Z}var
go=[0,function(b,a){return Z},gn,gm],gp=a(B[6],aq),gq=[0,[0,bK],[0,a(W[3],gp)],[1,aq],[1,aq],[1,aq],go];b(ap[9],gr,gq);var
gs=0;function
gt(a,d){function
c(b){return bH(a,b)}return b(am[72][1],0,c)}var
gv=[0,[0,[0,gu,[1,[5,a(B[16],aW)],0]],gt],gs];$(ap[8],bI,gw,0,0,gv);a(y[5],e3);aX(221,[0,bM,aW,bP,gi,bK,aq],"Ssrmatching_plugin__G_ssrmatching");return}
