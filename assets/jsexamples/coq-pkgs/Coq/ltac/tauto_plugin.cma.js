function(ba){"use strict";var
C="f",x="X2",P="Logic",g="X1",l="tauto_flags",w="id",Q="Coq",k=ba.jsoo_runtime,a=k.caml_new_string,O=k.caml_register_global,a_=k.caml_wrap_exception;function
c(a,b){return a.length==1?a(b):k.caml_call_gen(a,[b])}function
b(a,b,c){return a.length==2?a(b,c):k.caml_call_gen(a,[b,c])}function
u(a,b,c,d){return a.length==3?a(b,c,d):k.caml_call_gen(a,[b,c,d])}function
s(a,b,c,d,e){return a.length==4?a(b,c,d,e):k.caml_call_gen(a,[b,c,d,e])}function
a$(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):k.caml_call_gen(a,[b,c,d,e,f])}var
d=k.caml_get_global_data(),y=a("tauto_plugin"),f=d.Names,N=d.Ltac_plugin__Tacenv,q=d.Util,r=d.CAst,D=d.Mltop,z=d.Ltac_plugin__Tacinterp,j=d.Tacticals,e=d.Proofview,G=d.Pp,o=d.EConstr,m=d.Tactics,n=d.Hipattern,E=d.Geninterp,aN=d.Nametab,aM=d.Not_found,aC=d.Locusops,ai=d.Global,W=d.Assert_failure,S=d.Stdlib,$=d.Goptions,aJ=d.Libnames;O(46,[0,0],"Tauto_plugin");c(D[9],y);var
aQ=a(C),aR=a("x"),aD=[22,0],av=[0,a(P),[0,a("Init"),[0,a(Q),0]]],as=a(g),at=a(x),au=a(w),aq=a(g),am=a(g),an=a(x),ao=a(w),ak=a(g),ah=a(g),af=a(g),U=a(l),V=[0,a("_vendor+v8.10+64bit/coq/plugins/ltac/tauto.ml"),61,12],R=a("tauto: anomaly"),T=a(l),Y=[0,a("Intuition"),[0,a("Negation"),[0,a("Unfolding"),0]]],Z=a("unfolding of not in intuition"),ac=[0,0,0],aA=a("not"),aE=[0,a("Classical_Prop"),[0,a(P),[0,a(Q),0]]],aG=a("NNPP"),aO=[0,1,0,1,1,0],aP=[0,0,0,0,0,0],aS=[0,a(l),[0,a(g),0]],aT=a("is_empty"),aU=[0,a(l),[0,a(g),0]],aV=a("is_unit_or_eq"),aW=[0,a(l),[0,a(g),0]],aX=a("is_disj"),aY=[0,a(l),[0,a(g),0]],aZ=a("is_conj"),a0=[0,a(l),[0,a(g),[0,a(x),[0,a(w),0]]]],a1=a("flatten_contravariant_disj"),a2=[0,a(l),[0,a(g),[0,a(x),[0,a(w),0]]]],a3=a("flatten_contravariant_conj"),a4=a("apply_nnpp"),a5=a("reduction_not_iff"),a6=[0,a(C),0],a7=a("with_uniform_flags"),a8=[0,a(C),0],a9=a("with_power_flags");function
h(e,d){var
g=d[1],h=c(f[1][6],e),i=b(f[1][11][23],h,g),a=c(z[2][2],i);return a?a[1]:c(S[3],R)}var
F=c(E[1][1],T);function
t(d){var
e=d[1],g=c(f[1][6],U),a=b(f[1][11][23],g,e),h=a[2];if(b(E[1][2],a[1],F))return h;throw[0,W,V]}var
A=[0,1];function
X(a){A[1]=a;return 0}var
_=[0,0,Z,Y,function(a){return A[1]},X];b($[4],0,_);var
v=c(e[16],0),aa=c(G[7],0),ab=b(j[65][4],0,aa),p=c(e[39],ab),H=m[16];function
I(a,b){var
d=a?[0,[0,a[1]]]:0,f=s(m[143],1,d,0,b);return c(e[39],f)}function
B(a){return c(m[87],a)}function
J(a){return c(m[76],[0,a,0])}var
K=m[42],ad=b(m[117],0,ac);function
ae(d,a){function
c(c){var
d=h(af,a);return b(n[12],c,d)?v:p}return b(e[73][1],e[54],c)}function
ag(d,a){function
c(c){var
d=t(a)[5]?n[15]:n[14];return b(d,c,h(ah,a))?v:p}return b(e[73][1],e[54],c)}function
L(a,d){var
e=b(o[58],a,d);if(e){var
g=b(o[91],a,d)[1],f=b(o[3],a,g);return 11===f[0]?2===c(ai[31],f[1][1])[1][6]?1:0:0}return e}function
aj(d,c){function
a(b){var
a=t(c),d=h(ak,c),e=a[2]?L(b,d)?0:1:0;if(!e)if(s(n[6],[0,a[4]],[0,a[1]],b,d))return v;return p}return b(e[73][1],e[54],a)}function
al(f,a){function
d(d){var
e=t(a),k=h(am,a),l=h(an,a),f=h(ao,a),g=s(n[5],[0,e[3]],[0,e[1]],d,k);if(g){var
i=g[1][2],m=function(b,a){return u(o[35],b,0,a)},r=u(q[17][16],m,i,l),v=function(a){return H},w=b(j[65][23],v,i),x=[0,w,[0,B(f),[0,ad,[0,K,0]]]],y=c(j[65][22],x),z=[0,J(b(o[75],d,f)),0],A=[0,I([0,y],r),z];return c(j[65][22],A)}return p}return b(e[73][1],e[54],d)}function
ap(d,c){function
a(b){var
a=t(c),d=h(aq,c),e=a[2]?L(b,d)?0:1:0;if(!e)if(s(n[4],[0,a[4]],[0,a[1]],b,d))return v;return p}return b(e[73][1],e[54],a)}function
ar(f,a){function
d(d){var
e=t(a),i=h(as,a),k=h(at,a),f=h(au,a),g=s(n[3],[0,e[3]],[0,e[1]],d,i);if(g){var
l=g[1][2],r=function(b,a){var
d=u(o[35],a,0,k),e=[0,s(m[109],0,0,b+1|0,0),[0,K,0]],g=[0,H,[0,B(f),e]];return I([0,c(j[65][22],g)],d)},v=b(q[17][13],r,l),w=J(b(o[75],d,f)),x=c(j[65][22],v);return b(j[65][3],x,w)}return p}return b(e[73][1],e[54],d)}var
aw=b(q[17][68],f[1][6],av),ax=c(f[5][4],aw),ay=c(f[6][4],aA),az=[0,0,[0,[0,[1,b(f[17][3],[0,ax],ay)],0]]];function
aB(d,a){var
c=0===A[1]?aD:[0,b(r[1],0,[10,[5,[0,az,0]],aC[5]])];return b(z[23],a,c)}var
aF=b(q[17][68],f[1][6],aE),aH=c(f[1][6],aG),aI=c(f[5][4],aF),aK=b(aJ[15],aI,aH);function
aL(g,f){function
a(h){try{var
a=c(aN[29],aK),f=c(j[65][61],a),g=b(e[73][1],f,B);return g}catch(a){a=a_(a);if(a===aM){var
d=c(G[7],0);return b(j[65][4],0,d)}throw a}}var
d=c(e[16],0);return b(e[17],d,a)}function
M(e,o,a){var
g=c(f[1][6],aQ),h=b(r[1],0,g),i=c(f[1][6],aR),d=b(r[1],0,i),j=a[3],k=a[2],l=[0,u(f[1][11][4],d[1],[0,F,e],a[1]),k,j],m=[3,b(r[1],0,[0,[1,h],[0,[2,[1,d]],0]])],n=[29,b(r[1],0,m)];return b(z[23],l,n)}function
i(g,a,e){function
h(a){return c(f[1][6],a)}var
i=b(q[17][68],h,e);function
j(a){return[0,a]}var
d=[0,y,a],k=b(q[17][68],j,i);u(N[16],0,d,[0,g]);var
l=[28,[0,k,[31,b(r[1],0,[0,[0,d,0],0])]]];function
m(d){var
b=c(f[1][6],a);return a$(N[10],1,1,0,b,l)}return b(D[13],m,y)}i(ae,aT,aS);i(ag,aV,aU);i(ap,aX,aW);i(aj,aZ,aY);i(ar,a1,a0);i(al,a3,a2);i(aL,a4,0);i(aB,a5,0);i(function(a,b){return M(aO,a,b)},a7,a6);i(function(a,b){return M(aP,a,b)},a9,a8);O(68,[0],"Tauto_plugin__Tauto");return}
