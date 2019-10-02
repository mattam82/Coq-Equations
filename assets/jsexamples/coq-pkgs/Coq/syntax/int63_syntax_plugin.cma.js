function(A){"use strict";var
s="Int63",d=A.jsoo_runtime,a=d.caml_new_string,r=d.caml_register_global;function
c(a,b){return a.length==1?a(b):d.caml_call_gen(a,[b])}function
e(a,b,c){return a.length==2?a(b,c):d.caml_call_gen(a,[b,c])}var
b=d.caml_get_global_data(),f=a("int63_syntax_plugin"),i=[0,a("Coq"),[0,a("Numbers"),[0,a("Cyclic"),[0,a(s),[0,a(s),0]]]]],p=a("int63_scope"),j=b.Mltop,h=b.Names,g=b.Libnames,w=b.Nametab,z=b.Notation,t=b.Stdlib__list;r(8,[0,0],"Int63_syntax_plugin");c(j[9],f);var
k=e(g[29],0,a("Coq.Numbers.Cyclic.Int63.Int63.int")),l=e(g[29],0,a("Coq.Numbers.Cyclic.Int63.Int63.id_int")),x=[0,0,1],y=[0,0,1],u=a("int");function
m(a){var
b=e(t[19],h[1][6],a);return c(h[5][4],b)}function
n(b,a){var
d=c(h[1][6],a),f=m(b);return e(g[15],f,d)}var
o=n(i,u);function
q(b,a){function
d(d){return c(b,a)}return e(j[13],d,f)}var
v=0;q(function(b){var
a=c(w[13],l);return c(z[23],[0,0,p,[1,[0,y,a,x,a,k,0]],[0,o,i],0,0])},v);r(15,[0,f,k,l,m,n,i,o,p,q],"Int63_syntax_plugin__Int63_syntax");return}
