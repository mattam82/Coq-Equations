function(c$){"use strict";var
Z="Rtauto",ah="{ ",A=246,aj=" pruned",aD=" => ",ai=" }",K="rtauto",ag=" created",Y="",aG="Proof steps : ",aE="can't happen.",af=" created / ",aC="Hypotheses : ",aF="Proof branches : ",X=250,r=c$.jsoo_runtime,W=r.caml_check_bound,d=r.caml_new_string,U=r.caml_obj_tag,T=r.caml_register_global,y=r.caml_wrap_exception;function
b(a,b){return a.length==1?a(b):r.caml_call_gen(a,[b])}function
c(a,b,c){return a.length==2?a(b,c):r.caml_call_gen(a,[b,c])}function
k(a,b,c,d){return a.length==3?a(b,c,d):r.caml_call_gen(a,[b,c,d])}function
aB(a,b,c,d,e){return a.length==4?a(b,c,d,e):r.caml_call_gen(a,[b,c,d,e])}function
V(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):r.caml_call_gen(a,[b,c,d,e,f])}var
h=r.caml_get_global_data(),ae=d("rtauto_plugin"),f=h.Int,l=h.Util,a=h.Pp,D=h.Feedback,B=h.CErrors,z=h.Not_found,_=h.Goptions,I=h.EConstr,ab=h.Retyping,N=h.CamlinternalLazy,ac=h.Names,g=h.Constr,J=h.Proofview,G=h.Coqlib,x=h.System,az=h.Tactics,ax=h.CClosure,ay=h.Reductionops,O=h.UnivGen,aZ=h.Control,cB=h.Evd,cC=h.Termops,cQ=h.Ltac_plugin__Tacinterp,cW=h.Term,bO=h.Explore,c5=h.Mltop,c_=h.Ltac_plugin__Tacentries;T(110,[0,0,0,0],"Rtauto_plugin");var
e=[0,0,0,0,0,0,0,0,0,0],a0=d(" -> "),a1=d(" \\/ "),a2=d(" /\\ "),a4=d(")"),a5=d("("),a3=d("#"),bs=d(aj),bt=d(af),bu=d(aC),bv=d(aj),bw=d(af),bx=d(aF),by=d(aj),bz=d(af),bA=d(aG),bH=d(ag),bI=d(aC),bJ=d(ag),bK=d(aF),bL=d(ag),bM=d(aG),bN=d("Pruning is off"),bB=d(" branches"),bC=d("Non-deterministic choices : "),bD=d(" failures"),bE=d(" successes / "),bF=d("Branch ends: "),bG=d("Proof-search statistics :"),br=d("<complete>"),bi=d(ai),bj=d("goal  ="),bk=d("cnx   ="),bl=d("arrows="),bm=d("norev ="),bn=d("rev   ="),bo=d("ABSURD"),bq=d(Y),bp=d(ah),bh=d(aD),bd=d(aD),bc=d(Y),be=d(ai),bf=d(ah),a$=d(", "),a_=d(Y),ba=d("]"),bb=d("[ "),a7=d(Y),a8=d(ai),a9=d(ah),aY=d("already succeeded."),aT=d(aE),aU=[0,d("search_in_rev_hyps")],aQ=d(aE),aR=[0,d("search_no_rev")],aN=d("not a successful state."),aL=d("wrong arity."),aM=[0,d("add_step")],aI=[0,d(Z),[0,d("Pruning"),0]],aJ=d("Rtauto Pruning"),aO=d("Rtauto_plugin.Proof_search.Here_is"),cN=[0,d("Coq"),[0,d(K),[0,d(Z),0]]],cO=d("goal should be in Prop"),cP=[0,d(K)],cR=d("Starting proof-search ..."),cS=d("rtauto couldn't find any proof"),cT=[0,d(K)],cU=d("Proof tree found in "),cV=d("Building proof term ... "),cX=d("Giving proof term to Coq ... "),cY=d(" nodes (constants)"),cZ=d("Proof term size : "),c0=d(" steps"),c1=d("Proof size : "),c2=d("Proof term built in "),c3=d("Proof term type-checking is on"),c4=d("Internal tactic executed in "),bR=d("core.or.type"),bQ=d("core.and.type"),bP=d("core.False.type"),bS=d("num.pos.xI"),bU=d("num.pos.xO"),bW=d("num.pos.xH"),bY=d("plugins.rtauto.empty"),b0=d("plugins.rtauto.push"),b2=d("plugins.rtauto.Reflect"),b4=d("plugins.rtauto.Atom"),b6=d("plugins.rtauto.Arrow"),b8=d("plugins.rtauto.Bot"),b_=d("plugins.rtauto.Conjunct"),ca=d("plugins.rtauto.Disjunct"),cc=d("plugins.rtauto.Ax"),ce=d("plugins.rtauto.I_Arrow"),cg=d("plugins.rtauto.E_Arrow"),ci=d("plugins.rtauto.D_Arrow"),ck=d("plugins.rtauto.E_False"),cm=d("plugins.rtauto.I_And"),co=d("plugins.rtauto.E_And"),cq=d("plugins.rtauto.D_And"),cs=d("plugins.rtauto.I_Or_l"),cu=d("plugins.rtauto.I_Or_r"),cw=d("plugins.rtauto.E_Or"),cy=d("plugins.rtauto.D_Or"),cF=[0,d(Z),[0,d("Verbose"),0]],cG=d("Rtauto Verbose"),cJ=[0,d(Z),[0,d("Check"),0]],cK=d("Rtauto Check"),c7=[0,d(K),0],c9=d(K);function
ak(a){e[1]=0;e[2]=0;e[3]=0;e[4]=0;e[5]=0;e[6]=0;e[7]=0;e[8]=0;e[9]=0;return 0}var
L=[0,1];function
aH(a){L[1]=a;return 0}var
aK=[0,0,aJ,aI,function(a){return L[1]},aH];c(_[4],0,aK);function
M(g,f){var
b=g,a=f;for(;;)if(typeof
b==="number")return typeof
a==="number"?0:-1;else
switch(b[0]){case
0:var
h=b[1];return typeof
a==="number"?1:0===a[0]?r.caml_int_compare(h,a[1]):-1;case
1:var
i=b[2],j=b[1];if(typeof
a!=="number")switch(a[0]){case
1:var
k=a[2],c=M(j,a[1]);if(0===c){var
b=i,a=k;continue}return c;case
0:break;default:return-1}return 1;case
2:var
l=b[2],m=b[1];if(typeof
a!=="number")switch(a[0]){case
2:var
n=a[2],d=M(m,a[1]);if(0===d){var
b=l,a=n;continue}return d;case
3:return-1}return 1;default:var
o=b[2],p=b[1];if(typeof
a!=="number"&&3===a[0]){var
q=a[2],e=M(p,a[1]);if(0===e){var
b=o,a=q;continue}return e}return 1}}var
t=b(l[21][1],[0,M]);function
al(d,c){if(typeof
d==="number")switch(d){case
0:if(c)if(!c[2])return[1,c[1]];break;case
1:if(c){var
e=c[2];if(e)if(!e[2])return[5,c[1],e[1]]}break;case
2:if(c)if(!c[2])return[8,c[1]];break;default:if(c)if(!c[2])return[9,c[1]]}else
switch(d[0]){case
0:if(!c)return[0,d[1]];break;case
1:if(c)if(!c[2])return[2,d[1],d[2],c[1]];break;case
2:if(c){var
f=c[2];if(f)if(!f[2])return[3,d[1],c[1],f[1]]}break;case
3:if(!c)return[4,d[1]];break;case
4:if(c)if(!c[2])return[6,d[1],c[1]];break;case
5:if(c)if(!c[2])return[7,d[1],c[1]];break;case
6:if(c){var
g=c[2];if(g)if(!g[2])return[10,d[1],c[1],g[1]]}break;default:if(c)if(!c[2])return[11,d[1],c[1]]}var
h=b(a[3],aL);return k(B[3],0,aM,h)}function
am(c){if(0===c[0])return c[1];var
d=b(a[3],aN);return k(B[3],0,0,d)}function
n(a){return[0,a,0,f[2][1]]}function
C(b,c){var
a=b[1];return[0,[0,a[1],a[2],a[3],a[4],a[5],a[6],a[7],c],1,b[3]]}function
p(q,d){e[5]=e[5]+1|0;var
a=q[1],b=a[3]+1|0,i=k(t[4],d,b,a[4]);try{var
K=c(t[23],d,a[5]),L=c(t[6],d,a[5]),M=a[6],N=function(a,c){return[0,[0,b,a[1],d,a[2]],c]},O=k(l[17][16],N,K,M),j=O,g=L}catch(b){b=y(b);if(b!==z)throw b;var
j=a[6],g=a[5]}if(typeof
d==="number")var
m=[0,a[1],a[2],b,i,g,j,[0,b],a[8]];else
switch(d[0]){case
0:var
m=[0,a[1],a[2],b,i,g,j,a[7],a[8]];break;case
1:var
r=d[2],h=d[1];try{var
G=[0,[0,c(t[23],h,a[4]),b,h,r],j],o=G,n=g}catch(a){a=y(a);if(a!==z)throw a;try{var
v=[0,[0,b,r],c(t[23],h,g)],w=k(t[4],h,v,g),u=w}catch(a){a=y(a);if(a!==z)throw a;var
u=k(t[4],h,[0,[0,b,r],0],g)}var
o=j,n=u}if(typeof
h==="number")var
p=0;else
switch(h[0]){case
1:var
A=a[8],B=a[7],C=k(f[3][4],b,d,a[2]),s=[0,a[1],C,b,i,n,o,B,A],p=1;break;case
0:var
p=0;break;default:var
D=a[8],E=a[7],F=a[2],s=[0,k(f[3][4],b,d,a[1]),F,b,i,n,o,E,D],p=1}if(!p)var
s=[0,a[1],a[2],b,i,n,o,a[7],a[8]];var
m=s;break;default:var
H=a[8],I=a[7],J=a[2],m=[0,k(f[3][4],b,d,a[1]),J,b,i,g,j,I,H]}var
x=c(f[2][4],b,q[3]);return[0,m,q[2],x]}var
an=[248,aO,r.caml_fresh_oo_id(0)];function
aP(d){var
e=d[8];if(typeof
e==="number")var
g=0;else
if(3===e[0])var
j=e[2],m=e[1],o=[0,C(n(d),j),0],q=[0,[0,[0,3,1,f[2][1]],o],0],r=[0,C(n(d),m),0],i=[0,[0,[0,2,1,f[2][1]],r],q],g=1;else
var
g=0;if(!g)var
i=0;var
h=[0,i];function
s(i,e){if(typeof
e!=="number"&&1===e[0]){var
g=e[1];if(typeof
g!=="number"&&1===g[0]){var
j=e[2],l=g[2],q=g[1],r=d[8],s=d[7],t=d[6],u=d[5],v=d[4],w=d[3],x=c(f[3][6],i,d[2]),m=[0,d[1],x,w,v,u,t,s,r],y=h[1],z=[0,p(n(m),j),0],A=[0,p(p(C(n(m),l),[1,l,j]),q),z];h[1]=[0,[0,[0,[2,i],0,b(f[2][5],i)],A],y];return 0}}var
o=b(a[3],aQ);return k(B[3],0,aR,o)}c(f[3][11],s,d[2]);return b(l[17][9],h[1])}function
aS(d){try{var
u=d[1];try{var
j=function(b,a){throw[0,an,[0,b,a]]};c(f[3][11],j,u);throw z}catch(j){j=y(j);if(j[1]===an){var
r=j[2],e=r[2],g=r[1],m=function(a){return[0,a,0,b(f[2][5],g)]},v=d[8],w=d[7],x=d[6],A=d[5],C=d[4],D=d[3],E=d[2],l=[0,c(f[3][6],g,d[1]),E,D,C,A,x,w,v];if(typeof
e==="number")var
i=0;else
switch(e[0]){case
1:var
h=e[1];if(typeof
h==="number")var
q=0;else
switch(h[0]){case
2:var
G=[1,h[1],[1,h[2],e[2]]],H=[0,p(n(l),G),0],s=[0,[0,m([5,g]),H],0],q=1;break;case
3:var
t=e[2],I=[1,h[2],t],J=[1,h[1],t],K=[0,p(p(n(l),J),I),0],s=[0,[0,m([7,g]),K],0],q=1;break;default:var
q=0}if(q)var
o=s,i=1;else
var
i=0;break;case
2:var
L=e[2],M=e[1],N=[0,p(p(n(l),M),L),0],o=[0,[0,m([4,g]),N],0],i=1;break;case
3:var
O=e[2],P=e[1],Q=[0,p(n(l),O),0],R=[0,p(n(l),P),Q],o=[0,[0,m([6,g]),R],0],i=1;break;default:var
i=0}if(!i)var
F=b(a[3],aT),o=k(B[3],0,aU,F);return o}throw j}}catch(a){a=y(a);if(a===z)return aP(d);throw a}}function
aV(a){var
i=a[6];if(i){var
j=i[2],e=i[1],g=e[2],m=e[1],o=e[4],l=e[3];if(typeof
l==="number")var
h=0;else
switch(l[0]){case
1:var
s=a[8],t=a[7],u=a[5],v=a[4],w=a[3],x=c(f[3][6],g,a[2]),k=[0,a[1],x,w,v,u,j,t,s],h=1;break;case
0:var
h=0;break;default:var
y=a[8],z=a[7],A=a[5],B=a[4],D=a[3],E=a[2],k=[0,c(f[3][6],g,a[1]),E,D,B,A,j,z,y],h=1}if(!h)var
k=[0,a[1],a[2],a[3],a[4],a[5],j,a[7],a[8]];var
q=[0,p(n(k),o),0],r=b(f[2][5],g);return[0,[0,[0,[1,m,g],0,c(f[2][4],m,r)],q],0]}var
d=a[8];if(typeof
d!=="number")switch(d[0]){case
1:var
F=d[2],G=d[1],H=[0,p(C(n(a),F),G),0];return[0,[0,[0,0,1,f[2][1]],H],0];case
2:var
I=d[2],J=d[1],K=[0,C(n(a),I),0],L=[0,C(n(a),J),K];return[0,[0,[0,1,1,f[2][1]],L],0]}return aS(a)}function
aW(a){var
d=a[7];if(d){var
e=d[1];return[0,[0,[0,[3,e],0,b(f[2][5],e)],0],0]}try{var
g=c(t[23],a[8],a[4]),h=[0,[0,[0,[0,g],1,b(f[2][5],g)],0],0];return h}catch(b){b=y(b);if(b===z)return aV(a);throw b}}var
aX=n([0,f[3][1],f[3][1],0,t[1],t[1],0,0,0]);function
ao(b,a){var
c=C(aX,a);function
d(b,a){return p(a,b[2])}return[1,k(l[17][16],d,b,c)[1],0]}function
ap(a){return 0===a[0]?1:0}function
aq(d){if(0===d[0]){var
h=b(a[3],aY);return k(B[3],0,0,h)}var
x=d[2],i=d[1];b(aZ[3],0);var
g=aW(i);if(g){var
j=b(l[17][1],g[2]);e[9]=e[9]+j|0}else
e[7]=e[7]+1|0;function
m(y){var
p=y[2],g=y[1];e[1]=e[1]+1|0;if(p){var
w=p[2],q=p[1],J=b(l[17][1],w);e[3]=e[3]+J|0;return[1,q[1],[0,[0,0,w,g[1],g[2],g[3],q[2],q[3]],x]]}e[8]=e[8]+1|0;var
K=g[3],M=g[2],h=x,d=[0,al(g[1],0),M,K];for(;;){if(h){var
j=h[2],a=h[1];if(L[1])if(b(l[17][48],a[1])){var
N=a[6]?d[2]?1:0:0;if(!N){var
C=a[7],D=function(b){return function(a){return c(f[2][3],a,b[3])}}(d);if(!c(f[2][17],D,C)){e[2]=e[2]+1|0;var
E=b(l[17][1],a[2]);e[4]=e[4]+E|0;var
F=b(f[2][20],a[7]),G=a[2],H=function(c,a){return c+b(f[2][20],a[3])|0},I=k(l[17][15],H,F,G);e[6]=e[6]+I|0;var
v=b(f[2][20],a[7]),i=d[1],z=12===i[0]?[12,i[1]+v|0,i[2]]:[12,v,i],h=j,d=[0,z,d[2],d[3]];continue}}}var
A=c(f[2][9],d[3],a[7]),r=c(f[2][7],a[5],A),s=a[4];if(s)var
m=s;else
var
u=1-a[6],m=u?d[2]:u;var
t=[0,d[1],a[1]],n=a[2];if(n){var
o=n[1];return[1,o[1],[0,[0,t,n[2],a[3],m,r,o[2],o[3]],j]]}var
B=b(l[17][9],t),h=j,d=[0,al(a[3],B),m,r];continue}return[0,d[1]]}}return c(l[17][68],m,g)}function
ar(d){if(typeof
d==="number")return b(a[3],a3);else{if(0===d[0])return b(a[16],d[1]);var
e=b(a[3],a4),f=u(d),g=c(a[25],2,f),h=b(a[3],a5),i=c(a[12],h,g);return c(a[12],i,e)}}function
aa(d){if(typeof
d!=="number"&&2===d[0]){var
e=d[1],f=ar(d[2]),g=b(a[3],a2),h=aa(e),i=c(a[12],h,g);return c(a[12],i,f)}return ar(d)}function
$(d){if(typeof
d!=="number"&&3===d[0]){var
e=d[1],f=aa(d[2]),g=b(a[3],a1),h=$(e),i=c(a[12],h,g);return c(a[12],i,f)}return aa(d)}function
u(d){if(typeof
d!=="number"&&1===d[0]){var
e=d[1],f=u(d[2]),g=b(a[3],a0),h=$(e),i=c(a[12],h,g);return c(a[12],i,f)}return $(d)}function
a6(a){return u(a)}function
as(e){var
d=[0,b(a[3],a7)];function
g(i,e){var
f=b(a[14],0),g=u(e),h=c(a[12],d[1],g);d[1]=c(a[12],h,f);return 0}c(f[3][11],g,e);var
h=b(a[3],a8),i=c(a[24],0,d[1]),j=b(a[3],a9),k=c(a[12],j,i);return c(a[12],k,h)}function
at(f,e){var
d=[0,b(a[3],a_)];function
g(e){var
g=b(a[3],a$),h=b(f,e),i=c(a[12],d[1],h);d[1]=c(a[12],i,g);return 0}c(l[17][11],g,e);var
h=b(a[3],ba),i=d[1],j=b(a[3],bb),k=c(a[12],j,i);return c(a[12],k,h)}function
bg(d){var
e=d[3],f=u(d[4]),g=b(a[3],bh),h=u(e),i=c(a[12],h,g);return c(a[12],i,f)}function
au(g){if(0===g[0])return b(a[3],br);var
d=g[1],_=b(a[5],0),n=b(a[3],bi),o=u(d[8]),p=b(a[3],bj),q=b(a[14],0),r=at(bg,d[6]),s=b(a[3],bk),v=b(a[14],0),w=d[5],e=[0,b(a[3],bc)];function
h(f,d){var
g=b(a[14],0),h=at(function(a){return u(a[2])},d),i=b(a[3],bd),j=u(f),k=c(a[12],e[1],j),l=c(a[12],k,i),m=c(a[12],l,h);e[1]=c(a[12],m,g);return 0}c(t[11],h,w);var
i=b(a[3],be),j=c(a[12],e[1],i),k=c(a[25],0,j),l=b(a[3],bf),m=c(a[12],l,k),x=b(a[3],bl),y=b(a[14],0),z=as(d[2]),A=b(a[3],bm),B=b(a[14],0),C=as(d[1]),D=b(a[3],bn);if(d[7])var
E=b(a[14],0),F=b(a[3],bo),f=c(a[12],F,E);else
var
f=b(a[3],bq);var
G=c(a[12],f,D),H=c(a[12],G,C),I=c(a[12],H,B),J=c(a[12],I,A),K=c(a[12],J,z),L=c(a[12],K,y),M=c(a[12],L,x),N=c(a[12],M,m),O=c(a[12],N,v),P=c(a[12],O,s),Q=c(a[12],P,r),R=c(a[12],Q,q),S=c(a[12],R,p),T=c(a[12],S,o),U=c(a[12],T,n),V=c(a[25],0,U),W=b(a[3],bp),X=b(a[14],0),Y=c(a[12],X,W),Z=c(a[12],Y,V);return c(a[12],Z,_)}function
av(aJ){if(L[1])var
f=b(a[5],0),g=b(a[3],bs),h=b(a[16],e[6]),i=b(a[3],bt),j=b(a[16],e[5]),k=b(a[3],bu),l=b(a[5],0),m=b(a[3],bv),n=b(a[16],e[4]),o=b(a[3],bw),p=b(a[16],e[3]),q=b(a[3],bx),r=b(a[5],0),s=b(a[3],by),t=b(a[16],e[2]),u=b(a[3],bz),v=b(a[16],e[1]),w=b(a[3],bA),x=c(a[12],w,v),y=c(a[12],x,u),z=c(a[12],y,t),A=c(a[12],z,s),B=c(a[12],A,r),C=c(a[12],B,q),E=c(a[12],C,p),F=c(a[12],E,o),G=c(a[12],F,n),H=c(a[12],G,m),I=c(a[12],H,l),J=c(a[12],I,k),K=c(a[12],J,j),M=c(a[12],K,i),N=c(a[12],M,h),O=c(a[12],N,g),d=c(a[12],O,f);else
var
aj=b(a[5],0),ak=b(a[3],bH),al=b(a[16],e[5]),am=b(a[3],bI),an=b(a[5],0),ao=b(a[3],bJ),ap=b(a[16],e[3]),aq=b(a[3],bK),ar=b(a[5],0),as=b(a[3],bL),at=b(a[16],e[1]),au=b(a[3],bM),av=b(a[5],0),aw=b(a[3],bN),ax=c(a[12],aw,av),ay=c(a[12],ax,au),az=c(a[12],ay,at),aA=c(a[12],az,as),aB=c(a[12],aA,ar),aC=c(a[12],aB,aq),aD=c(a[12],aC,ap),aE=c(a[12],aD,ao),aF=c(a[12],aE,an),aG=c(a[12],aF,am),aH=c(a[12],aG,al),aI=c(a[12],aH,ak),d=c(a[12],aI,aj);var
P=b(a[3],bB),Q=b(a[16],e[9]),R=b(a[3],bC),S=b(a[5],0),T=b(a[3],bD),U=b(a[16],e[7]),V=b(a[3],bE),W=b(a[16],e[8]),X=b(a[3],bF),Y=b(a[5],0),Z=b(a[3],bG),_=c(a[12],Z,Y),$=c(a[12],_,d),aa=c(a[12],$,X),ab=c(a[12],aa,W),ac=c(a[12],ab,V),ad=c(a[12],ac,U),ae=c(a[12],ad,T),af=c(a[12],ae,S),ag=c(a[12],af,R),ah=c(a[12],ag,Q),ai=c(a[12],ah,P);return c(D[6],0,ai)}T(119,[0,am,ao,aq,ap,au,a6,ak,av],"Rtauto_plugin__Proof_search");var
aw=b(bO[1],[0,aq,ap,au]);function
i(d,a){d[1]++;var
c=U(a);return X===c?a[1]:A===c?b(N[2],a):a}var
m=[0,0],q=[0,0],P=[A,function(d){var
a=b(G[2],bP),c=b(O[22],a);return b(g[73],c)}],Q=[A,function(d){var
a=b(G[2],bQ),c=b(O[22],a);return b(g[73],c)}],R=[A,function(d){var
a=b(G[2],bR),c=b(O[22],a);return b(g[73],c)}];function
j(a){return[A,function(d){var
c=b(G[2],a);return b(O[22],c)}]}var
bT=j(bS),bV=j(bU),bX=j(bW),bZ=j(bY),b1=j(b0),b3=j(b2),b5=j(b4),b7=j(b6),b9=j(b8),b$=j(b_),cb=j(ca),cd=j(cc),cf=j(ce),ch=j(cg),cj=j(ci),cl=j(ck),cn=j(cm),cp=j(co),cr=j(cq),ct=j(cs),cv=j(cu),cx=j(cw),cz=j(cy);function
cA(c,b,a){return aB(ay[17],ax[4],c,b,a)}function
H(a,f){var
e=b(I[141][1],f);try{var
h=a[2],i=function(a){return c(g[80],e,a[1])},j=[0,c(l[17][27],i,h)[2]];return j}catch(b){b=y(b);if(b===z){var
d=a[1];a[2]=[0,[0,e,d],a[2]];a[1]=d+1|0;return[0,d]}throw b}}function
v(e,a,d,s){var
f=s;for(;;){var
i=function(b){return aB(ay[16],ax[9],e,a,b)},t=cA(e,a,f),h=c(I[3],a,t);switch(h[0]){case
5:var
f=h[1];continue;case
6:var
m=h[3],n=h[2];if(k(I[120][13],a,1,m))if(1===V(ab[4],0,0,e,a,n)){var
u=v(e,a,d,n);return[1,u,v(e,a,d,m)]}return H(d,i(f));case
9:var
j=h[2],w=h[1];if(2===j.length-1)try{var
o=c(I[84],a,w)[1],p=U(Q),x=X===p?Q[1]:A===p?b(N[2],Q):Q;if(c(ac[37],o,x[1]))var
z=v(e,a,d,W(j,0)[1]),l=[2,z,v(e,a,d,W(j,1)[2])];else{var
q=U(R),B=X===q?R[1]:A===q?b(N[2],R):R;if(c(ac[37],o,B[1]))var
C=v(e,a,d,W(j,0)[1]),l=[3,C,v(e,a,d,W(j,1)[2])];else
var
l=H(d,i(f))}return l}catch(a){a=y(a);if(a===g[59])return H(d,i(f));throw a}break;case
11:var
r=U(P),D=h[1][1],E=X===r?P[1]:A===r?b(N[2],P):P;return c(ac[37],D,E[1])?0:H(d,i(f))}return H(d,i(f))}}function
ad(f,e,h,n,m){var
d=n,a=m;for(;;){if(a){var
b=a[1];if(0===b[0]){var
g=b[2],i=b[1],j=ad(f,e,h,[0,g,d],a[2]),o=function(a){return k(cC[36],cB[16],i[1],a)};if(!c(l[17][22],o,d))if(1===V(ab[4],0,0,f,e,g))return[0,[0,i,v(f,e,h,g)],j];return j}var
d=[0,b[3],[0,b[2],d]],a=a[2];continue}return 0}}function
s(a){if(1<a){if(0===(a&1)){var
c=[0,s(a>>1)],d=[0,i(q,bV),c];return b(g[15],d)}var
e=[0,s(a>>1)],f=[0,i(q,bT),e];return b(g[15],f)}return i(q,bX)}function
E(a){if(typeof
a==="number")return i(q,b9);else
switch(a[0]){case
0:var
c=[0,s(a[1])],d=[0,i(q,b5),c];return b(g[15],d);case
1:var
e=a[1],f=E(a[2]),h=[0,E(e),f],j=[0,i(q,b7),h];return b(g[15],j);case
2:var
k=a[1],l=E(a[2]),m=[0,E(k),l],n=[0,i(q,b$),m];return b(g[15],n);default:var
o=a[1],p=E(a[2]),r=[0,E(o),p],t=[0,i(q,cb),r];return b(g[15],t)}}function
w(b,d){var
a=d;for(;;){if(a){var
c=a[1],e=a[2],f=c[2];if(c[1]<b)return b-f|0;var
a=e;continue}return b}}function
o(k,d,j){var
c=k,a=j;for(;;)switch(a[0]){case
0:var
l=[0,s(w(a[1],c))],n=[0,i(m,cd),l];return b(g[15],n);case
1:var
p=[0,o(c,d+1|0,a[1])],q=[0,i(m,cf),p];return b(g[15],q);case
2:var
r=a[2],t=a[1],u=o(c,d+1|0,a[3]),v=s(w(r,c)),x=[0,s(w(t,c)),v,u],y=[0,i(m,ch),x];return b(g[15],y);case
3:var
z=a[2],A=a[1],B=o(c,d+1|0,a[3]),C=o(c,d+2|0,z),D=[0,s(w(A,c)),C,B],E=[0,i(m,cj),D];return b(g[15],E);case
4:var
F=[0,s(w(a[1],c))],G=[0,i(m,cl),F];return b(g[15],G);case
5:var
H=a[1],I=o(c,d,a[2]),J=[0,o(c,d,H),I],K=[0,i(m,cn),J];return b(g[15],K);case
6:var
L=a[1],M=o(c,d+2|0,a[2]),N=[0,s(w(L,c)),M],O=[0,i(m,cp),N];return b(g[15],O);case
7:var
P=a[1],Q=o(c,d+1|0,a[2]),R=[0,s(w(P,c)),Q],S=[0,i(m,cr),R];return b(g[15],S);case
8:var
T=[0,o(c,d,a[1])],U=[0,i(m,ct),T];return b(g[15],U);case
9:var
V=[0,o(c,d,a[1])],W=[0,i(m,cv),V];return b(g[15],W);case
10:var
X=a[2],Y=a[1],Z=o(c,d+1|0,a[3]),_=o(c,d+1|0,X),$=[0,s(w(Y,c)),_,Z],aa=[0,i(m,cx),$];return b(g[15],aa);case
11:var
ab=a[1],ac=o(c,d+2|0,a[2]),ad=[0,s(w(ab,c)),ac],ae=[0,i(m,cz),ad];return b(g[15],ae);default:var
e=a[1],af=a[2];if(c)var
f=c[1][2],h=[0,[0,d+f|0,f+e|0],c];else
var
h=[0,[0,d+e|0,e],0];var
c=h,a=af;continue}}var
F=[0,0];function
cD(a){var
c=[0,g[8]],d=[0,i(q,bZ),c],e=b(g[15],d),f=a[2];function
h(c,a){var
d=[0,g[8],c[1],a],e=[0,i(q,b1),d];return b(g[15],e)}return k(l[17][16],h,f,e)}function
cE(a){F[1]=a;return 0}var
cH=[0,0,cG,cF,function(a){return F[1]},cE];c(_[4],0,cH);var
S=[0,0];function
cI(a){S[1]=a;return 0}var
cL=[0,0,cK,cJ,function(a){return S[1]},cI];c(_[4],0,cL);function
cM(d){var
A=b(J[68][3],d),e=b(J[68][2],d),f=b(J[68][4],d),h=b(J[68][5],d);b(G[12],cN);var
j=[0,1,0];if(1!==V(ab[4],0,0,f,h,e)){var
C=b(a[3],cO);k(B[6],0,cP,C)}var
H=v(f,h,j,e),p=ad(f,h,j,[0,e,0],A);function
K(b,a){return[1,a[2],b]}var
r=k(l[17][15],K,H,p),s=b(cQ[8],0);if(s)if(0===s[1])var
t=aw[2],n=1;else
var
n=0;else
var
n=0;if(!n)var
t=aw[1];ak(0);if(F[1]){var
L=b(a[3],cR);c(D[6],0,L)}var
M=b(x[26],0);try{var
aP=am(b(t,ao(0,r))),u=aP}catch(c){c=y(c);if(c!==z)throw c;var
N=b(a[3],cS),u=k(B[6],0,cT,N)}var
O=b(x[26],0);if(F[1]){var
P=c(x[28],M,O),Q=b(a[3],cU),R=c(a[12],Q,P);c(D[6],0,R);av(0);var
T=b(a[3],cV);c(D[6],0,T)}var
U=b(x[26],0);m[1]=0;q[1]=0;var
W=o(0,0,u),X=E(r),Y=[0,cD(j),X,W],Z=[0,i(q,b3),Y],_=b(g[15],Z);function
$(a){return b(g[2],a[1][1])}var
aa=c(l[17][14],$,p),ac=c(cW[13],_,aa),ae=b(x[26],0);if(F[1]){var
af=b(a[3],cX),ag=b(a[5],0),ah=b(a[3],cY),ai=b(a[16],m[1]+q[1]|0),aj=b(a[3],cZ),al=b(a[5],0),an=b(a[3],c0),ap=b(a[16],m[1]),aq=b(a[3],c1),ar=b(a[5],0),as=c(x[28],U,ae),at=b(a[3],c2),au=c(a[12],at,as),ax=c(a[12],au,ar),ay=c(a[12],ax,aq),aA=c(a[12],ay,ap),aB=c(a[12],aA,an),aC=c(a[12],aB,al),aD=c(a[12],aC,aj),aE=c(a[12],aD,ai),aF=c(a[12],aE,ah),aG=c(a[12],aF,ag),aH=c(a[12],aG,af);c(D[6],0,aH)}var
aI=b(x[26],0),w=b(I[9],ac),aJ=S[1]?b(az[46],w):b(az[43],w),aK=b(x[26],0);if(S[1]){var
aL=b(a[3],c3);c(D[6],0,aL)}if(F[1]){var
aM=c(x[28],aI,aK),aN=b(a[3],c4),aO=c(a[12],aN,aM);c(D[6],0,aO)}return aJ}var
aA=b(J[68][8],cM);T(137,[0,v,ad,aA],"Rtauto_plugin__Refl_tauto");b(c5[9],ae);var
c6=0,c8=[0,[0,c7,function(a){return aA}],c6];V(c_[8],ae,c9,0,0,c8);T(140,[0,ae],"Rtauto_plugin__G_rtauto");return}
