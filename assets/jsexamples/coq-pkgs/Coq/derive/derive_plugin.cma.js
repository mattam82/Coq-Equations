function(ac){"use strict";var
y="Derive",x=141,w="_vendor+v8.10+64bit/coq/plugins/derive/derive.ml",c=ac.jsoo_runtime,d=c.caml_new_string,k=c.caml_register_global;function
b(a,b){return a.length==1?a(b):c.caml_call_gen(a,[b])}function
g(a,b,d){return a.length==2?a(b,d):c.caml_call_gen(a,[b,d])}function
n(a,b,d,e){return a.length==3?a(b,d,e):c.caml_call_gen(a,[b,d,e])}function
l(a,b,d,e,f){return a.length==4?a(b,d,e,f):c.caml_call_gen(a,[b,d,e,f])}function
m(a,b,d,e,f,g){return a.length==5?a(b,d,e,f,g):c.caml_call_gen(a,[b,d,e,f,g])}function
ab(a,b,d,e,f,g,h){return a.length==6?a(b,d,e,f,g,h):c.caml_call_gen(a,[b,d,e,f,g,h])}var
a=c.caml_get_global_data(),u=d("derive_plugin"),t=a.Proofview,p=a.Pp,q=a.CErrors,s=a.Assert_failure,r=a.Declare,f=a.EConstr,e=a.Evd,i=a.Proof_global,h=a.Stdarg,j=a.Genarg,Q=a.Proof,J=a.Vars,I=a.Constr,C=a.Context,D=a.Environ,F=a.Constrintern,A=a.Global,z=a.Future,U=a.Attributes,O=a.Mltop,aa=a.Vernacextend;k(14,[0,0,0],"Derive_plugin");var
G=d("Admitted isn't supported in Derive."),M=d("Cannot save a proof of Derive with an explicit name."),N=[0,d(w),66,19],H=[1,0],L=[0,d(w),83,18],K=[2,5],E=[0,0],B=[0,2,0,[0,0]],P=[0,[0,[0,1,0]],1],V=d("As"),X=d("SuchThat"),Z=d(y),$=d(y);function
o(h,j,k){var
a=b(A[2],0),d=b(e[17],a),c=l(e[132],0,0,e[126],d),o=c[1],u=b(f[14],c[2]),v=[1,a,o,u,function(d,c){return[1,a,d,c,function(k,i){var
l=b(f[x][1],c),n=b(f[x][1],i),o=[1,b(C[7],h),n,l],d=g(D[37],o,a),e=m(F[16],E,d,k,0,j),p=e[2],q=e[1];return[1,d,q,p,function(a,b){return[0,a]}]}]}];function
w(e){if(0===e[0])var
x=b(p[3],G),f=n(q[6],0,0,x);else{var
E=e[1];if(e[2])var
F=b(p[3],M),t=n(q[6],0,0,F);else{var
u=e[3][2];if(u){var
i=u[2];if(i){var
j=i[2];if(j)if(j[2])var
d=0;else
var
t=[0,1!==E?1:0,i[1],j[1]],d=1;else
var
d=0}else
var
d=0}else
var
d=0;if(!d)throw[0,s,N]}var
f=t}var
a=f[3],c=f[2],y=f[1],A=m(r[3],0,0,h,0,[0,[0,[0,c[1],c[2],c[3],c[4],c[5],0,c[7]]],H]),B=b(I[17],A);function
l(a){return g(J[18],[0,[0,h,B],0],a)}var
o=a[4];if(o){var
C=l(o[1]),D=a[1],v=function(a){var
b=a[1],c=a[2],d=b[2];return[0,[0,l(b[1]),d],c]},w=g(z[16],D,v);m(r[3],0,0,k,0,[0,[0,[0,w,a[2],a[3],[0,C],a[5],y,a[7]]],K]);return 0}throw[0,s,L]}var
y=b(i[8],w),O=ab(i[11],0,k,0,B,v,y);function
P(d,b){var
c=l(t[31],0,1,2,t[41]);return n(Q[28],a,c,b)}return g(i[19],P,O)[1]}k(31,[0,o],"Derive_plugin__Derive");b(O[9],u);function
v(a){return P}var
R=0,S=0;function
T(g,f,e,d,a){b(U[2],d);var
c=[0,o(g,f,e)];return[0,a[1],a[2],c,a[4]]}var
W=[0,V,[1,[5,b(j[16],h[7])],0]],Y=[0,X,[1,[5,b(j[16],h[11])],W]],_=[0,[0,0,[0,Z,[1,[5,b(j[16],h[7])],Y]],T,S],R];l(aa[2],$,[0,v],0,_);k(37,[0,u,v],"Derive_plugin__G_derive");return}
