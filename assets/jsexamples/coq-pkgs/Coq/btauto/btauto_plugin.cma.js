function(bg){"use strict";var
g=246,ab="core.bool.type",O=141,aa="to_list",$="btauto",j=250,n=bg.jsoo_runtime,o=n.caml_check_bound,b=n.caml_new_string,i=n.caml_obj_tag,S=n.caml_register_global,_=n.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):n.caml_call_gen(a,[b])}function
c(a,b,c){return a.length==2?a(b,c):n.caml_call_gen(a,[b,c])}function
A(a,b,c,d){return a.length==3?a(b,c,d):n.caml_call_gen(a,[b,c,d])}function
bf(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):n.caml_call_gen(a,[b,c,d,e,f])}var
f=n.caml_get_global_data(),R=b("btauto_plugin"),h=f.CamlinternalLazy,z=f.Proofview,p=f.EConstr,x=f.Tacmach,u=f.Constr,N=f.Tactics,y=f.Tacticals,d=f.Pp,Y=f.Stdlib,Q=f.Refiner,E=f.Stdlib__list,T=f.Coqlib,a1=f.Printer,aV=f.Redexpr,aY=f.CErrors,ay=f.Names,ao=f.Globnames,am=f.Not_found,ad=f.Termops,ac=f.UnivGen,al=f.Stdlib__hashtbl,a$=f.Mltop,be=f.Ltac_plugin__Tacentries;S(43,[0,0,0],"Btauto_plugin");var
a_=b("Cannot recognize a boolean equality"),a8=b("Btauto: Internal error"),aX=b(aa),aW=b(aa),a0=b("true"),a3=b("false"),a2=b(":="),aU=[9,0],a4=b("]"),a5=b(";"),a6=b("["),a7=b("Not a tautology:"),aZ=b("Not a tautology"),aw=[1,0],ax=[1,1],an=b(ab),ae=b("core.list.nil"),af=b("core.list.cons"),ag=b("num.pos.xH"),ah=b("num.pos.xO"),aj=b("num.pos.xI"),ap=b(ab),aq=b("core.bool.true"),ar=b("core.bool.false"),as=b("core.bool.andb"),at=b("core.bool.orb"),au=b("core.bool.xorb"),av=b("core.bool.negb"),az=b("core.eq.type"),aA=b("plugins.btauto.f_var"),aC=b("plugins.btauto.f_btm"),aD=b("plugins.btauto.f_top"),aE=b("plugins.btauto.f_cnj"),aG=b("plugins.btauto.f_dsj"),aI=b("plugins.btauto.f_neg"),aK=b("plugins.btauto.f_xor"),aM=b("plugins.btauto.f_ifb"),aO=b("plugins.btauto.eval"),aQ=b("plugins.btauto.witness"),aS=b("plugins.btauto.soundness"),bb=[0,b($),0],bd=b($);function
e(b){return[g,function(d){var
c=a(T[2],b);return a(ac[22],c)}]}function
B(d,b){var
e=a(p[9],b),f=c(ad[60],d,e),g=a(p[O][1],f);return a(u[29],g)}function
l(b,d){var
c=i(b),e=j===c?b[1]:g===c?a(h[2],b):b;return a(u[15],[0,e,d])}var
k=u[80],v=e(ae),w=e(af);function
U(b,a){if(a){var
c=a[1];return l(w,[0,b,c,U(b,a[2])])}return l(v,[0,b])}var
C=e(ag),ai=e(ah),ak=e(aj);function
V(b){if(1<b){var
c=V(b/2|0);return 0===(b%2|0)?l(ai,[0,c]):l(ak,[0,c])}var
d=i(C);return j===d?C[1]:g===d?a(h[2],C):C}var
D=a(al[25],[0,u[80],u[113]]);function
P(a,b){var
d=a[2],e=a[1];try{var
g=c(D[7],e,b);return g}catch(a){a=_(a);if(a===am){var
f=d[1];A(D[5],e,b,f);d[1]++;return f}throw a}}var
F=[g,function(c){var
b=a(T[2],an);return a(ao[9],b)}],q=e(ap),r=e(aq),s=e(ar),G=e(as),H=e(at),I=e(au),J=e(av);function
W(m,t,q){var
d=i(r),u=j===d?r[1]:g===d?a(h[2],r):r,e=i(s),v=j===e?s[1]:g===e?a(h[2],s):s,f=i(G),w=j===f?G[1]:g===f?a(h[2],G):G,l=i(H),x=j===l?H[1]:g===l?a(h[2],H):H,n=i(I),y=j===n?I[1]:g===n?a(h[2],I):I,p=i(J),z=j===p?J[1]:g===p?a(h[2],J):J;function
b(e){var
f=B(t,e);switch(f[0]){case
9:var
d=f[2],l=f[1];if(c(k,l,w))if(2===d.length-1){var
q=b(o(d,1)[2]);return[2,b(o(d,0)[1]),q]}if(c(k,l,x))if(2===d.length-1){var
r=b(o(d,1)[2]);return[3,b(o(d,0)[1]),r]}if(c(k,l,y))if(2===d.length-1){var
s=b(o(d,1)[2]);return[4,b(o(d,0)[1]),s]}if(c(k,l,z))if(1===d.length-1)return[5,b(o(d,0)[1])];return[0,P(m,e)];case
13:var
n=f[4],p=i(F),A=f[3],C=f[1][1],D=j===p?F[1]:g===p?a(h[2],F):F;if(c(ay[37],C,D)){var
E=b(o(n,1)[2]),G=b(o(n,0)[1]);return[6,b(A),G,E]}return[0,P(m,e)];default:return c(k,e,v)?aw:c(k,e,u)?ax:[0,P(m,e)]}}return b(q)}var
t=e(az),aB=e(aA),K=e(aC),L=e(aD),aF=e(aE),aH=e(aG),aJ=e(aI),aL=e(aK),aN=e(aM),aP=e(aO),aR=e(aQ),M=e(aS);function
m(b){switch(b[0]){case
0:return l(aB,[0,V(b[1])]);case
1:if(0===b[1]){var
c=i(K);return j===c?K[1]:g===c?a(h[2],K):K}var
d=i(L);return j===d?L[1]:g===d?a(h[2],L):L;case
2:var
e=b[1],f=m(b[2]);return l(aF,[0,m(e),f]);case
3:var
k=b[1],n=m(b[2]);return l(aH,[0,m(k),n]);case
4:var
o=b[1],p=m(b[2]);return l(aL,[0,m(o),p]);case
5:return l(aJ,[0,m(b[1])]);default:var
q=b[2],r=b[1],s=m(b[3]),t=m(q);return l(aN,[0,m(r),t,s])}}function
X(e,d){var
b=i(q),f=m(d),c=j===b?q[1]:g===b?a(h[2],q):q;return l(aP,[0,U(c,e),f])}function
aT(n,m,b){var
o=l(aR,[0,n]),q=a(p[9],o),t=a(Q[3],b),u=c(aV[2],t,aU)[1],z=a(Q[2],b),C=A(u,a(Q[3],b),z,q)[2],D=a(p[O][1],C);function
e(u){var
d=B(a(x[2],b),u);if(9===d[0]){var
f=d[2],l=d[1],m=i(v),y=j===m?v[1]:g===m?a(h[2],v):v;if(c(k,l,y))return 0;if(3===f.length-1){var
n=f[2],o=f[3],p=i(w),z=j===p?w[1]:g===p?a(h[2],w):w;if(c(k,l,z)){var
q=i(r),A=j===q?r[1]:g===q?a(h[2],r):r;if(c(k,n,A))return[0,1,e(o)];var
t=i(s),C=j===t?s[1]:g===t?a(h[2],s):s;return c(k,n,C)?[0,0,e(o)]:a(Y[2],aX)}}}return a(Y[2],aW)}function
F(f,b){if(b){var
g=b[2],h=b[1],e=function(b){if(b){var
g=b[1],h=e(b[2]),i=c(d[12],f,g);return c(d[12],i,h)}return a(d[7],0)},i=e(g);return c(d[12],h,i)}return a(d[7],0)}try{var
G=e(D),H=c(E[47],m,G),I=function(e){var
f=e[1],g=e[2]?a(d[3],a0):a(d[3],a3),h=a(x[5],b),i=a(x[2],b),j=A(a1[6],h,i,f),k=a(d[13],0),l=a(d[3],a2),m=a(d[13],0),n=c(d[12],j,m),o=c(d[12],n,l),p=c(d[12],o,k);return c(d[12],p,g)},J=c(E[17],I,H),K=a(d[3],a4),L=a(d[13],0),M=a(d[3],a5),N=F(c(d[12],M,L),J),P=a(d[3],a6),R=c(d[12],P,N),S=c(d[12],R,K),T=a(d[13],0),U=a(d[3],a7),V=c(d[12],U,T),W=c(d[12],V,S),f=W}catch(b){b=_(b);if(!a(aY[18],b))throw b;var
f=a(d[3],aZ)}return A(y[23],0,f,b)}function
a9(o){var
P=a(z[68][2],o),Q=a(p[O][1],P),l=a(x[35][4],o),r=i(t),R=j===r?t[1]:g===r?a(h[2],t):t,s=i(q),S=j===s?q[1]:g===s?a(h[2],q):q,m=B(l,Q);if(9===m[0]){var
b=m[2];if(3===b.length-1){var
v=m[1],w=b[1],U=b[2],V=b[3];if(c(k,w,S))if(c(k,v,R)){var
e=[0,a(D[1],16),[0,1]],Y=W(e,l,U),Z=W(e,l,V),F=e[1],G=function(c,b,a){return[0,[0,b,c],a]},H=A(D[14],G,F,0),I=function(b,a){return n.caml_int_compare(b[1],a[1])},J=c(E[48],I,H),K=function(a){return a[2]},f=c(E[17],K,J),_=X(f,Y),$=[0,v,[0,w,_,X(f,Z)]],aa=a(u[15],$),ab=a(p[9],aa),ac=0,L=function(e){var
l=i(t),n=a(z[68][2],e),o=j===l?t[1]:g===l?a(h[2],t):t,q=a(p[O][1],n),b=B(a(x[35][4],e),q);if(9===b[0]){var
m=b[2];if(3===m.length-1){var
s=m[2];if(c(k,b[1],o)){var
u=function(a){return aT(s,f,a)},v=c(z[72][1],0,u);return c(y[65][11],N[123],v)}}}var
r=a(d[3],a8);return c(y[65][4],0,r)},ad=[0,a(z[68][8],L),ac],C=i(M),ae=[0,N[68],ad],af=j===C?M[1]:g===C?a(h[2],M):M,ag=a(p[9],af),ah=[0,a(N[87],ag),ae],ai=[0,a(N[54],ab),ah];return a(y[65][22],ai)}}}var
T=a(d[3],a_);return c(y[65][4],0,T)}var
Z=[0,a(z[68][8],a9)];S(65,[0,Z],"Btauto_plugin__Refl_btauto");a(a$[9],R);var
ba=0,bc=[0,[0,bb,function(a){return Z[1]}],ba];bf(be[8],R,bd,0,0,bc);S(68,[0,R],"Btauto_plugin__G_btauto");return}
