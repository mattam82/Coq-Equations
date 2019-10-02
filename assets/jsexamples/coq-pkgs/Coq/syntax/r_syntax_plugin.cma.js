function(az){"use strict";var
R="Z",Q="Rdefinitions",y="",P="Reals",r="Coq",h=az.jsoo_runtime,p=h.caml_ml_string_length,d=h.caml_new_string,O=h.caml_register_global,ay=h.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):h.caml_call_gen(a,[b])}function
c(a,b,c){return a.length==2?a(b,c):h.caml_call_gen(a,[b,c])}function
q(a,b,c,d){return a.length==3?a(b,c,d):h.caml_call_gen(a,[b,c,d])}var
i=h.caml_get_global_data(),z=d("r_syntax_plugin"),K=[0,d(r),[0,d(P),[0,d(Q),0]]],x=d("R_scope"),e=i.DAst,f=i.Names,b=i.Bigint,A=i.Mltop,M=i.Stdlib,n=i.Util,N=i.Notation,as=i.NumTok,V=i.Libnames;O(19,[0,0],"R_syntax_plugin");a(A[9],z);var
j=[248,d("R_syntax_plugin.R_syntax.Non_closed_number"),h.caml_fresh_oo_id(0)],ap=d("-"),ar=d(y),aq=d(y),an=d(y),S=[0,d(r),[0,d("Numbers"),[0,d("BinNums"),0]]],X=d("positive"),Z=d(R),$=d("R"),aa=d("IZR"),ac=d("Rmult"),ae=d("Rdiv"),ag=[0,d(r),[0,d("ZArith"),[0,d("BinIntDef"),0]]],ah=d(R),ak=d("pow_pos"),av=[0,d(r),[0,d(P),[0,d(Q),0]]];function
m(b){var
d=c(n[17][14],f[1][6],b);return a(f[5][4],d)}function
g(g,d){var
b=a(e[1],g);return 0===b[0]?c(f[63][1],b[1],d):0}var
B=[0,m(S)],Y=a(f[6][4],X),s=c(f[23][3],B,Y),C=[3,[0,[0,s,0],1]],D=[3,[0,[0,s,0],2]],E=[3,[0,[0,s,0],3]];function
F(g,f){var
h=c(e[3],0,[0,C,0]),i=c(e[3],0,[0,E,0]),j=c(e[3],0,[0,D,0]);function
d(k){var
g=a(b[8],k),f=g[1];if(0===g[2]){var
l=[4,j,[0,d(f),0]];return c(e[3],0,l)}if(c(b[17],f,b[5]))return i;var
m=[4,h,[0,d(f),0]];return c(e[3],0,m)}return d(f)}function
k(m){var
d=a(e[1],m);switch(d[0]){case
0:if(c(f[63][1],d[1],E))return b[6];break;case
4:var
h=d[2];if(h)if(!h[2]){var
i=h[1],l=d[1];if(g(l,D)){var
n=k(i);return a(b[11],n)}if(g(l,C)){var
o=k(i),p=a(b[11],o);return a(b[9],p)}}break}throw j}var
_=a(f[6][4],Z),t=c(f[23][3],B,_),G=[3,[0,[0,t,0],1]],H=[3,[0,[0,t,0],2]],I=[3,[0,[0,t,0],3]];function
J(h,d){if(c(b[17],d,b[5]))return c(e[3],0,[0,G,0]);if(a(b[20],d))var
g=H,f=d;else
var
g=I,f=a(b[22],d);var
i=[0,F(h,f),0],j=[4,c(e[3],0,[0,g,0]),i];return c(e[3],0,j)}function
u(m){var
d=a(e[1],m);switch(d[0]){case
0:if(c(f[63][1],d[1],G))return b[5];break;case
4:var
h=d[2];if(h)if(!h[2]){var
i=h[1],l=d[1];if(g(l,H))return k(i);if(g(l,I)){var
n=k(i);return a(b[22],n)}}break}throw j}var
v=[0,m(K)],T=a(f[1][6],$),U=m(K),W=c(V[15],U,T),ab=a(f[6][4],aa),l=[1,c(f[17][3],v,ab)],ad=a(f[6][4],ac),w=[1,c(f[17][3],v,ad)],af=a(f[6][4],ae),o=[1,c(f[17][3],v,af)],ai=a(f[6][4],ah),aj=[2,[0,m(ag)],ai],al=a(f[6][4],ak),L=[1,c(f[17][3],aj,al)];function
am(s,r){var
g=r[2],d=g[3],t=g[2],B=r[1],C=g[1];function
i(a){var
b=[4,c(e[3],0,[0,l,0]),[0,a,0]];return c(e[3],0,b)}function
u(d){var
f=J(s,a(b[3],10)),g=[0,f,[0,F(0,d),0]],h=[4,c(e[3],0,[0,L,0]),g];return c(e[3],0,h)}var
I=c(M[17],C,t),v=a(b[1],I),K=0===B?v:a(b[22],v),j=i(J(s,K));if(h.caml_string_equal(d,an))var
x=b[5];else{var
y=h.caml_string_get(d,1)-43|0;if(2<y>>>0)var
k=0;else{switch(y){case
0:var
P=q(n[15][4],d,2,p(d)-2|0),A=a(b[1],P),m=1;break;case
1:var
k=0,m=0;break;default:var
Q=q(n[15][4],d,2,p(d)-2|0),R=a(b[1],Q),A=a(b[22],R),m=1}if(m)var
z=A,k=1}if(!k)var
O=q(n[15][4],d,1,p(d)-1|0),z=a(b[1],O);var
x=z}var
N=a(b[3],p(t)),f=c(b[13],x,N);if(a(b[18],f)){var
D=[0,j,[0,i(u(f)),0]],E=[4,c(e[3],0,[0,w,0]),D];return c(e[3],0,E)}if(a(b[19],f)){var
G=[0,j,[0,i(u(a(b[22],f))),0]],H=[4,c(e[3],0,[0,o,0]),G];return c(e[3],0,H)}return j}function
ao(D){var
f=a(e[1],D);if(4===f[0]){var
h=f[2];if(h){var
i=h[2],y=h[1],d=f[1];if(i){if(!i[2]){var
E=i[1],T=g(d,w)?0:g(d,o)?0:1;if(!T){var
m=a(e[1],y),n=a(e[1],E);if(4===m[0]){var
p=m[2];if(p)if(!p[2])if(4===n[0]){var
q=n[2];if(q)if(!q[2]){var
F=q[1],G=n[1],H=p[1];if(g(m[1],l))if(g(G,l)){var
r=a(e[1],F);if(4===r[0]){var
s=r[2];if(s){var
t=s[2];if(t)if(!t[2]){var
I=t[1],J=s[1];if(g(r[1],L)){var
K=u(J),N=a(b[3],10);if(c(b[17],K,N)){var
v=u(H),O=k(I);if(a(b[20],v))var
A=0,z=v;else
var
A=1,z=a(b[22],v);var
P=a(b[2],z),Q=g(d,o)?ap:ar,R=a(b[2],O);return[0,A,[0,P,aq,c(M[17],Q,R)]]}throw j}}}}throw j}}}}throw j}}}else
if(g(d,l)){var
x=u(y);if(a(b[19],x))var
C=1,B=a(b[22],x);else
var
C=0,B=x;var
S=a(b[2],B);return[0,C,a(as[2],S)]}}}throw j}var
au=[0,am,function(a){var
b=a[1];try{var
c=[0,ao(b)];return c}catch(a){a=ay(a);if(a===j)return 0;throw a}}];q(N[19],0,x,au);var
aw=[0,0,x,[0,x],[0,W,av],[0,l,[0,w,[0,o,0]]],0],ax=N[23];function
at(b){return a(ax,aw)}c(A[13],at,z);O(29,[0],"R_syntax_plugin__R_syntax");return}
