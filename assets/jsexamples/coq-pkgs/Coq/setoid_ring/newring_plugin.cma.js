function(jA){"use strict";var
b$="closed",a8="x",b_="ring_lookup",ct=",",J='"',a5="ring",k=246,b9=141,cs="(",a7="_vendor+v8.10+64bit/coq/plugins/setoid_ring/newring.ml",cr="constants",b8="preprocess tactic",aN="Field_tac",ce="with carrier ",cq="postprocess tactic",aM="field",cp="InitialRing",cd="decidable",A="[",ch='and morphisms "',cm="Pphi_pow",cn='Using setoid "',co="tactic recognizing constants",X=104,cl="postprocess",bb="gen_phiZ",aP="setoid",b7="and equivalence relation ",b6=")",aO=103,B="]",b4=":",b5="t",cc="preprocess",a6="power_tac",ck="Print",ba="power",b3="abstract",cj="Ring_polynom",aL="sign",a$="protect_fv",b2="PEeval",a_="Ring",aK="div",cb='and "',a4="newring_plugin",cf="Add",cg="completeness",a3="IDphi",ca="morphism",ci="field_lookup",p=250,b1="Pphi_dev",a9="Coq",H=jA.jsoo_runtime,F=H.caml_check_bound,b=H.caml_new_string,o=H.caml_obj_tag,aJ=H.caml_register_global,z=H.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):H.caml_call_gen(a,[b])}function
c(a,b,c){return a.length==2?a(b,c):H.caml_call_gen(a,[b,c])}function
e(a,b,c,d){return a.length==3?a(b,c,d):H.caml_call_gen(a,[b,c,d])}function
ah(a,b,c,d,e){return a.length==4?a(b,c,d,e):H.caml_call_gen(a,[b,c,d,e])}function
E(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):H.caml_call_gen(a,[b,c,d,e,f])}function
jz(a,b,c,d,e,f,g,h){return a.length==7?a(b,c,d,e,f,g,h):H.caml_call_gen(a,[b,c,d,e,f,g,h])}var
f=H.caml_get_global_data(),bh=[0,b(a4),b("closed_term")],bo=[0,b(a4),b("get_res")],aq=b("setoid_ring"),an=b(a4),Z=f.Constr,g=f.Util,P=f.CClosure,ai=f.Termops,j=f.Names,G=f.Not_found,h=f.EConstr,bN=f.Tacmach,q=f.Proofview,v=f.Ltac_plugin__Tacinterp,O=f.Coqlib,Q=f.Global,w=f.Stdlib,ag=f.Ltac_plugin__Tacintern,bH=f.Lib,n=f.CamlinternalLazy,aV=f.UnivGen,ab=f.Ltac_plugin__Rewrite,x=f.Mod_subst,V=f.Ltac_plugin__Tacsubst,U=f.Libnames,aa=f.Retyping,bv=f.Reductionops,d=f.Pp,Y=f.CErrors,C=f.Printer,aU=f.Assert_failure,az=f.Typing,aj=f.Option,_=f.Evarutil,bB=f.Smartlocate,ao=f.Loc,N=f.CAst,af=f.Feedback,bx=f.Flags,t=f.Stdarg,l=f.Genarg,ac=f.Evd,bm=f.Declare,bl=f.Constrintern,bf=f.Tactics,bi=f.Ltac_plugin__Tacenv,aw=f.Summary,ay=f.Libobject,M=f.Vernacextend,aI=f.Attributes,bU=f.Pfedit,D=f.Ppconstr,aG=f.Ltac_plugin__Pptactic,a0=f.Ltac_plugin__Tacentries,I=f.Pcoq,i=f.CLexer,aH=f.Ltac_plugin__Pltac,bV=f.Ltac_plugin__Tacarg,cz=f.Esubst,cX=f.Refiner,cP=f.Environ,cQ=f.Goal,cL=f.Vars,cM=f.UState,cJ=f.DAst,cF=f.Tacticals,cy=f.Globnames,fz=f.Redexpr,gp=f.Mltop;aJ(251,[0,0,0,0],"Newring_plugin");aJ(252,[0],"Newring_plugin__Newring_ast");var
gn=[0,0,0],go=[0,0,0],gd=b("field kind"),ge=b(co),gf=b(b8),gg=b(cq),gh=b(aP),gi=b(ba),gj=b(aL),gk=b(aK),gl=b("infinite property"),f5=[0,b(aN),0],f6=[0,0,0],f7=b("field_lemmas"),f8=b("_field_lemma1"),f9=b("_field_lemma2"),f_=b("_field_lemma3"),f$=b("_field_lemma4"),ga=b("_lemma5"),gc=[22,0],gb=[22,0],f4=b("core.eq.congr"),f3=b("field inverse should be declared as a morphism"),fQ=b("arguments of field_simplify do not have all the same type"),fR=[0,b(aM)],fP=[0,b(aN),0],fS=b(J),fT=b(J),fU=b("cannot find a declared field structure over"),fV=[0,b(aM)],fW=[0,b(a7),846,12],fK=[0,1],fL=[0,0],fJ=b("bad field structure"),eN=[0,0,0],eO=[0,0,0],eE=b("ring kind"),eF=b(co),eG=b(b8),eH=b(cq),eI=b(aP),eJ=b(ba),eK=b(aL),eL=b(aK),eD=b(" cannot be set twice"),ex=[0,b("Ring_base"),0],ey=b("ring_lemmas"),ez=b("_ring_lemma1"),eA=b("_ring_lemma2"),eC=[22,0],eB=[22,0],ev=[0,1],ew=[0,0],eu=b("bad ring structure"),ed=b("ring addition should be declared as a morphism"),ee=b("ring multiplication should be declared as a morphism"),ef=b("ring opposite should be declared as a morphism"),eg=b(J),eh=b(cb),ei=b(J),ej=b(J),ek=b('",'),el=b(ch),em=b(J),en=b(cn),eo=b(J),ep=b(cb),eq=b(J),er=b(ch),es=b(J),et=b(cn),d$=b("cannot find setoid relation"),dZ=b("arguments of ring_simplify do not have all the same type"),d0=[0,b(a5)],d1=b(J),d2=b(J),d3=b("cannot find a declared ring structure over"),d4=[0,b(a5)],d5=[0,b(a7),348,12],df=[0,b(cj),0],de=b("newring"),c$=b(a_),c_=b(a_),c6=b("ring: cannot find relation (not closed)"),c5=b("ring: cannot find relation"),cW=b(a8),cV=b(a8),cT=b(a8),cR=b("Ring.exec_tactic: anomaly"),cN=[2,1],cO=[0,1],cI=b(b5),cK=b(b5),cE=[0,b(a7),117,7],cB=b("not found"),cC=b("map "),cD=[0,b("lookup_map")],cx=b("dummy"),cv=b("global_head_of_constr."),cY=b("plugins.setoid_ring.Build_Setoid_Theory"),c0=b("core.option.None"),c1=b("core.option.Some"),c2=b("core.eq.type"),c3=b("core.list.cons"),c4=b("core.list.nil"),c7=b(a9),c8=[0,[0,b("Ring_theory"),0],[0,[0,b(cj),0],[0,[0,b("Ring_tac"),0],[0,[0,b(cp),0],[0,[0,b(aN),0],[0,[0,b("Field_theory"),0],0]]]]]],da=[0,b(a9),0],db=b(cp),dg=b("almost_ring_theory"),dh=b("Eqsth"),dj=b("Eq_ext"),dl=b("Eq_s_ext"),dn=b("ring_theory"),dp=b("mk_reqe"),dr=b("semi_ring_theory"),ds=b("mk_seqe"),du=b("Abstract"),dv=b("Computational"),dx=b("Morphism"),dz=b("inv_morph_nothing"),dA=b("mkhypo"),dC=b("hypo"),dF=b(b2),dI=b(cm),dL=b(b1),dO=b(bb),dR=b(a3),dV=b(a5),dW=b("ring-tac-carrier-table"),dX=b("ring-tac-name-table"),d8=b("tactic-new-ring-theory"),eP=[0,b(a9),0],eQ=b(aN),eV=b("FEeval"),eY=b(b2),e1=b(cm),e4=b(b1),e7=b("display_pow_linear"),e_=b("display_linear"),fb=b(bb),fe=b(a3),fi=b(aM),fl=b("PCond"),fo=b(bb),fr=b(a3),fv=b("field_cond"),fw=b(aM),fy=b("simpl_field_expr"),fA=b("almost_field_theory"),fB=b("field_theory"),fC=b("semi_field_theory"),fD=b("AF_AR"),fF=b("F_R"),fH=b("SF_SR"),fM=b("field-tac-carrier-table"),fN=b("field-tac-name-table"),fZ=b("tactic-new-field-theory"),jb=b(b7),jc=b(ce),ja=b("The following field structures have been declared:"),iP=b(cg),ir=b(b7),is=b(ce),iq=b("The following ring structures have been declared:"),g4=[0,0],gA=b(b3),gB=b(cd),gC=b(ca),gD=b(B),gE=b(A),gF=b(cr),gG=b(B),gH=b(A),gI=b(b$),gJ=b(B),gK=b(A),gL=b(cc),gM=b(B),gN=b(A),gO=b(cl),gP=b(aP),gQ=b(B),gR=b(A),gS=b(a6),gT=b(B),gU=b(A),gV=b(a6),gW=b(aL),gX=b(aK),gs=b(a$),gv=b("in"),gx=b(a$),gz=b(a$),g1=b(cd),g5=b(b3),g9=b(ca),ha=b(B),hd=b(A),hf=b(cr),hi=b(B),hl=b(A),hn=b(b$),hq=b(B),ht=b(A),hv=b(cc),hy=b(B),hB=b(A),hD=b(cl),hI=b(aP),hM=b(aL),hP=b(B),hS=b(A),hV=b(ba),hY=b(B),h1=b(A),h4=b(a6),h8=b(aK),h$=b("ring_mod"),id=b(b6),ig=b(ct),ii=b(cs),il=b("ring_mods"),it=[0,b(ck),[0,b("Rings"),0]],iy=b(b4),iA=b(a_),iB=b(cf),iF=b("AddSetoidRing"),iI=b(B),iK=b(A),iM=b(b_),iO=b(b_),iU=b(cg),iX=b("field_mod"),i1=b(b6),i3=b(ct),i5=b(cs),i8=b("field_mods"),jd=[0,b(ck),[0,b("Fields"),0]],ji=b(b4),jk=b("Field"),jl=b(cf),jp=b("AddSetoidField"),js=b(B),ju=b(A),jw=b(ci),jy=b(ci);function
K(b){var
c=a(d[3],b);return e(Y[6],0,0,c)}function
cu(b,f){var
g=c(h[91],b,f)[1];try{var
j=c(ai[aO],b,g)[1];return j}catch(b){b=z(b);if(b===G){var
i=a(d[3],cv);return e(Y[3],0,0,i)}throw b}}function
cw(b){try{var
c=a(cy[16],b);return c}catch(b){b=z(b);if(b===G)return[0,a(j[1][6],cx)];throw b}}function
bc(h,f,e){var
i=a(Z[70],e),j=i[2],b=i[1],k=a(h,cw(b));if(k){var
l=k[1],d=function(d,b){switch(a(l,d)){case
0:var
e=a(cz[1],f);return c(P[45],e,b);case
1:return a(P[24],b);default:return bc(h,f,b)}};if(a(g[19][35],j))return d(-1,b);var
m=c(g[19][16],d,j),n=[5,d(-1,b),m];return a(P[25],n)}return a(P[24],e)}function
bd(b,a){try{var
c=[0,e(g[17][115],j[63][1],a,b)];return c}catch(a){a=z(a);if(a===G)return 0;throw a}}var
aQ=[0,g[15][53][1]];function
aR(b,a){aQ[1]=e(g[15][53][4],b,a,aQ[1]);return 0}function
cA(f){try{var
b=c(g[15][53][23],f,aQ[1]);return b}catch(b){b=z(b);if(b===G){var
h=a(d[3],cB),i=a(d[20],f),j=a(d[3],cC),k=c(d[12],j,i),l=c(d[12],k,h);return e(Y[6],0,cD,l)}throw b}}function
aS(i,g,f,b){function
j(a){return c(_[12],f,a)}var
k=a(h[b9][1],b),l=a(P[33],0),m=e(P[31],[0,j],P[4],g),n=c(cA(i),f,b);function
d(c,f){var
b=a(Z[29],f);if(6===b[0]){var
h=b[2],i=b[1],j=d(c+1|0,b[3]),k=[0,i,d(c,h),j];return a(Z[12],k)}var
g=bc(n,c,f);return e(P[49],m,l,g)}var
o=d(0,k);return a(h[9],o)}function
be(a){var
b=0,c=2,d=[0,function(b,c,d){return aS(a,b,c,d)},c];return e(bf[50],0,d,b)}function
bg(b,a){var
c=[0,[0,a,0]],d=2,f=[0,function(a,c,d){return aS(b,a,c,d)},d];return e(bf[50],0,f,c)}function
aT(a,e,b){var
f=b;for(;;)try{var
m=c(ai[aO],a,f)[1],n=c(j[63][4][3],m,e);return n}catch(b){b=z(b);if(b===G){var
d=c(h[3],a,f);switch(d[0]){case
5:var
f=d[1];continue;case
9:var
k=d[2],i=aT(a,e,d[1]);if(i){var
l=function(b){return aT(a,e,b)};return c(g[19][21],l,k)}return i;default:return 0}}throw b}}var
cG=[0,function(b,s){if(b){var
f=b[2];if(f)if(!f[2]){var
h=f[1],i=a(v[2][2],b[1]),k=a(aj[7],i),m=a(v[2][5],h),n=a(aj[7],m),o=function(b){var
d=a(l[6],t[9]);return c(v[2][7],d,b)},p=c(g[17][68],o,n),r=function(b){if(aT(b,e(g[17][16],j[63][4][4],p,j[63][4][1]),k))return a(q[16],0);var
f=a(d[7],0);return c(cF[65][4],0,f)};return c(q[73][1],q[54],r)}}throw[0,aU,cE]}];e(bi[16],0,bh,cG);var
cH=[0,bh,0];function
bj(b){function
d(a){return[0,c(ao[12],0,a)]}var
e=c(g[17][68],d,b),f=a(l[18],t[9]),h=a(l[5],f),i=[0,[0,c(l[7],h,e)],0],k=[1,a(j[1][6],cI)],m=[0,c(cJ[3],0,k),0],n=a(l[5],t[11]),o=[0,cH,[0,[0,c(l[7],n,m)],i]],p=[31,c(N[1],0,o)];return[28,[0,[0,[0,a(j[1][6],cK)],0],p]]}function
bk(d){var
b=a(Q[2],0),f=a(ac[17],b),c=e(bl[13],b,f,d);return[0,c[1],c[2]]}function
L(c){var
b=a(Q[2],0),d=a(ac[17],b);return ah(bl[10],b,d,0,c)[1]}function
$(e,d,b){var
f=a(cL[27],b),g=[0,[0,c(cM[23],d,f)]],h=[0,[0,jz(bm[2],0,cO,0,0,g,0,b)],cN],i=a(j[1][6],e),k=E(bm[3],0,0,i,0,h);return a(Z[17],k)}var
bn=[0,[0]],cS=[0,bo,0],cU=[0,function(d,b){var
e=a(g[17][5],d),f=a(l[6],t[3]),h=c(v[2][7],f,e);function
i(d){var
e=b[1],f=a(w[22],d),g=c(w[17],cT,f),h=a(j[1][6],g);return c(j[1][11][23],h,e)}bn[1]=c(g[19][2],h,i);return a(q[16],0)}];e(bi[16],0,bo,cU);function
bp(F,E,i,b,D){function
G(g,b){var
d=b[1],h=b[3],i=b[2],k=a(w[22],d),l=c(w[17],cV,k),f=a(j[1][6],l),m=[2,[1,c(N[1],0,f)]],n=a(v[2][1],g);return[0,d+1|0,[0,m,i],e(j[1][11][4],f,n,h)]}var
m=e(g[17][16],G,D,[0,0,0,j[1][11][1]]),H=m[3],I=m[2],r=a(v[31],0),J=[0,H,r[2],r[3]];function
K(b){var
d=a(w[22],b),e=c(w[17],cW,d);return a(j[1][6],e)}var
L=c(g[17][56],i,K),M=a(l[5],t[3]),O=[0,cS,[0,[0,c(l[7],M,i)],0]],P=[31,c(N[1],0,O)];function
Q(a){return[0,a]}var
R=[5,[28,[0,c(g[17][68],Q,L),P]]],A=h[16],B=a(cP[11],F),f=e(cQ[3][5],E,B,A),C=[0,f[1],f[3]],d=o(b),S=c(g[18],I,[0,R,0]),u=p===d?b[1]:k===d?a(n[2],b):b,x=[0,[0,c(ao[12],0,u)],S],y=[3,c(N[1],0,x)],z=[29,c(N[1],0,y)],T=c(v[23],J,z),U=c(q[72][7],T,C),V=a(cX[2],U),s=a(ac[165],V);function
W(c){var
b=a(v[2][2],c);return b?e(h[5],0,s,b[1]):a(w[3],cR)}var
X=a(ac[150],s);return[0,c(g[19][15],W,bn[1]),X]}function
bq(b){return[k,function(e){var
c=a(O[2],b),d=a(aV[22],c);return a(h[9],d)}]}function
ap(b){return[k,function(c){return a(O[2],b)}]}var
cZ=bq(cY),aW=ap(c0),aX=ap(c1),R=bq(c2),ak=ap(c3),al=ap(c4);function
am(b,d){var
c=o(b),e=p===c?b[1]:k===c?a(n[2],b):b;return a(h[23],[0,e,d])}function
r(d,b,g){var
e=o(b),i=p===e?b[1]:k===e?a(n[2],b):b,f=c(_[9],d[1],i),j=f[2];d[1]=f[1];return a(h[23],[0,j,g])}function
br(f,l){var
d=c(h[3],f,l);if(9===d[0]){var
b=d[2],m=d[1];if(2<=b.length-1){var
n=[0,m,e(g[19][7],b,0,b.length-1-2|0)],i=a(h[23],n);if(c(h[120][16],f,i)){var
j=b.length-1-1|0,k=b.length-1-2|0,o=F(b,j)[j+1];return[0,i,F(b,k)[k+1],o]}return K(c6)}}return K(c5)}var
ar=[0,c7,[0,aq,0]];function
c9(a){return c(g[18],ar,a)}var
bs=c(g[17][68],c9,c8);function
S(b){return[k,function(f){var
c=e(O[18],c_,bs,b),d=a(aV[22],c);return a(h[9],d)}]}function
m(a){return[k,function(b){return e(O[18],c$,bs,a)}]}var
dc=c(g[17][68],j[1][6],[0,db,[0,aq,da]]),dd=a(j[5][4],dc);function
bt(b){return[k,function(e){var
d=a(j[6][4],b);return c(j[13][1],[0,dd],d)}]}function
ad(a){var
b=[0,aq,df];return[k,function(c){return e(O[17],de,b,a)}]}var
as=S(dg),di=m(dh),dk=m(dj),dm=m(dl),at=S(dn),dq=S(dp),au=S(dr),dt=S(ds),av=S(du),dw=S(dv),dy=S(dx),T=bt(dz),dB=m(dA),u=m(dC);function
bu(i,d,f){var
b=f;for(;;){var
e=c(h[3],d,b);if(6===e[0]){var
b=e[3];continue}var
j=br(d,b)[1],l=function(c){var
b=c[1],d=o(b),e=c[2],f=p===d?b[1]:k===d?a(n[2],b):b;return[0,f,e]},m=c(g[17][68],l,i),q=function(a){return-1===a?1:2},r=[0,[0,cu(d,j),q],m];return function(a){return bd(r,a)}}}var
dD=0;function
dE(b){var
a=b+1|0;if(!(14<a>>>0))switch(a){case
9:case
13:return 2;case
0:case
11:case
14:return 0}return 1}var
dG=[0,[0,ad(dF),dE],dD];function
dH(b){var
a=b+1|0;if(!(18<a>>>0))switch(a){case
12:case
17:return 2;case
0:case
9:case
10:case
11:case
14:case
16:case
18:return 0}return 1}var
dJ=[0,[0,ad(dI),dH],dG];function
dK(a){if(11<=a)if(14<=a)var
b=15<=a?0:1;else{if(12!==a)return 2;var
b=1}else
var
b=-1===a?1:8<=a?1:0;return b?0:1}var
dM=[0,[0,ad(dL),dK],dJ];function
dN(a){return 0}var
dP=[0,[0,m(dO),dN],dM];function
dQ(a){return 0}var
dS=[0,[0,m(dR),dQ],dP],dT=[0,[0,al,function(a){return-1===a?0:1}],dS],dU=[0,[0,ak,function(a){return-1===a?0:2===a?2:1}],dT];aR(dV,function(a,b){return bu(dU,a,b)});var
ae=a(g[21][1],[0,Z[86]]),aY=e(aw[4],0,dW,ae[1]),ax=e(aw[4],0,dX,U[22][1]);function
dY(a){return c(ae[23],a,aY[1])}function
d6(d){var
a=d[2],b=d[1],e=c(x[46],b,a[1]),f=c(x[46],b,a[2]),g=c(x[46],b,a[3]),h=c(x[46],b,a[4]),i=c(x[46],b,a[5]),j=c(x[46],b,a[6]),k=c(x[46],b,a[9]),l=c(x[46],b,a[10]),m=c(V[1],b,a[7]),n=c(V[1],b,a[8]),o=c(V[1],b,a[11]),p=c(V[1],b,a[12]);if(e===a[1])if(f===a[2])if(c(Z[80],g,a[3]))if(h===a[4])if(i===a[5])if(j===a[6])if(k===a[9])if(l===a[10])if(m===a[7])if(n===a[8])if(o===a[11])if(p===a[12])return a;return[0,e,f,g,h,i,j,m,n,k,l,o,p]}function
d7(b){var
a=b[2],c=b[1][1];aY[1]=e(ae[4],a[1],a,aY[1]);ax[1]=e(U[22][4],c,a,ax[1]);return 0}var
d9=e(ay[16],d8,d7,[0,d6]),d_=a(ay[4],d9);function
bw(c,d,b,a){try{var
e=ah(ab[12],c,d[1],b,a),h=e[2],f=ah(ab[13],c,e[1],b,a),i=f[2],g=ah(ab[14],c,f[1],b,a),j=g[2];d[1]=g[1];var
k=am(cZ,[0,b,a,h,i,j]);return k}catch(a){a=z(a);if(a===G)return K(d$);throw a}}function
ea(h,g,f,e,d,c,b,a){return am(dq,[0,h,g,f,e,d,c,b,a])}function
eb(f,e,d,c,b,a){return am(dt,[0,f,e,d,c,b,a])}function
ec(i,b,j){var
f=j[5],q=j[4],l=j[3],m=j[2],g=j[1],u=c(h[3],b[1],f);if(9===u[0])if(1===u[2].length-1){var
E=o(R),aU=u[1],aV=p===E?R[1]:k===E?a(n[2],R):R;if(e(h[X],b[1],aU,aV)){var
aW=r(b,di,[0,g]),aX=q?r(b,dk,[0,g,m,l,q[1]]):r(b,dm,[0,g,m,l]),F=e(az[6],i,b[1],aW),aY=F[2],H=e(az[6],i,F[1],aX),aZ=H[2];b[1]=H[1];return[0,aY,aZ]}}var
v=[0,[0,[0,[0,g,[0,f]]],[0,[0,[0,g,[0,f]]],0]],[0,[0,g,[0,f]]]],I=bw(a(Q[2],0),b,g,f);try{var
aT=c(ab[15],v,m),w=aT}catch(a){a=z(a);if(a!==G)throw a;var
w=K(ed)}var
s=w[2];try{var
aS=c(ab[15],v,l),x=aS}catch(a){a=z(a);if(a!==G)throw a;var
x=K(ee)}var
t=x[2];if(q){var
y=q[1];try{var
at=c(ab[15],[0,[0,[0,[0,g,[0,f]]],0],[0,[0,g,[0,f]]]],y),A=at}catch(a){a=z(a);if(a!==G)throw a;var
A=K(ef)}var
B=A[2],J=ea(g,m,l,y,f,s,t,B),L=a(d[3],eg),M=e(C[11],i,b[1],B),N=a(d[3],eh),O=a(d[13],0),P=a(d[3],ei),S=e(C[11],i,b[1],t),T=a(d[3],ej),U=a(d[13],0),V=a(d[3],ek),W=e(C[11],i,b[1],s),Y=a(d[3],el),Z=a(d[13],0),_=a(d[3],em),$=e(C[11],i,b[1],f),aa=a(d[3],en),ac=c(d[12],aa,$),ad=c(d[12],ac,_),ae=c(d[12],ad,Z),ag=c(d[12],ae,Y),ah=c(d[12],ag,W),ai=c(d[12],ah,V),aj=c(d[12],ai,U),ak=c(d[12],aj,T),al=c(d[12],ak,S),am=c(d[12],al,P),an=c(d[12],am,O),ao=c(d[12],an,N),ap=c(d[12],ao,M),aq=c(d[12],ap,L),ar=af[6],as=function(a){return c(ar,0,a)};c(bx[21],as,aq);var
D=J}else{var
au=a(d[3],eo),av=e(C[11],i,b[1],t),aw=a(d[3],ep),ax=a(d[13],0),ay=a(d[3],eq),aA=e(C[11],i,b[1],s),aB=a(d[3],er),aC=a(d[13],0),aD=a(d[3],es),aE=e(C[11],i,b[1],f),aF=a(d[3],et),aG=c(d[12],aF,aE),aH=c(d[12],aG,aD),aI=c(d[12],aH,aC),aJ=c(d[12],aI,aB),aK=c(d[12],aJ,aA),aL=c(d[12],aK,ay),aM=c(d[12],aL,ax),aN=c(d[12],aM,aw),aO=c(d[12],aN,av),aP=c(d[12],aO,au),aQ=af[6],aR=function(a){return c(aQ,0,a)};c(bx[21],aR,aP);var
D=eb(g,m,l,f,s,t)}return[0,I,D]}function
by(h,g,f,e,d,c,b,a){return a?a[1]:ec(h,g,[0,f,e,d,c,b])}function
bz(b){if(typeof
b==="number"){var
c=o(av);return p===c?av[1]:k===c?a(n[2],av):av}else
return 0===b[0]?am(dw,[0,b[1]]):am(dy,[0,b[1]])}function
bA(u,t,s,r,q,d){if(d){var
b=d[1];if(0===b[0])return a(ag[2],b[1]);var
f=b[1],h=bB[3],i=function(a){return c(h,0,a)};return bj(c(g[17][68],i,f))}var
e=o(T),j=p===e?T[1]:k===e?a(n[2],T):T,l=[0,[0,c(ao[12],0,j)],0],m=[3,c(N[1],0,l)];return[29,c(N[1],0,m)]}function
aA(c,b,a){return r(b,dB,[0,E(aa[2],0,0,c,b[1],a),a])}function
bC(d,b,m){var
f=o(u),q=p===f?u[1]:k===f?a(n[2],u):u,i=c(_[9],b[1],q),j=i[2];b[1]=i[1];var
s=r(b,al,[0,j]);function
t(c,a){return r(b,ak,[0,j,aA(d,b,c),a])}var
v=e(g[17][16],t,m,s),l=e(az[6],d,b[1],v),w=l[2];b[1]=l[1];var
x=a(h[b9][1],w);return c(_[41],b[1],x)}function
bD(q,b,e){var
f=o(u),s=p===f?u[1]:k===f?a(n[2],u):u,h=c(_[9],b[1],s),i=h[2];b[1]=h[1];if(e){var
j=e[1],d=j[1],t=j[2];if(0===d[0])var
l=a(ag[2],d[1]);else
var
v=d[1],w=bB[3],x=function(a){return c(w,0,a)},l=bj(c(g[17][68],x,v));return[0,l,r(b,aX,[0,i,aA(q,b,L(t))])]}var
m=o(T),y=p===m?T[1]:k===m?a(n[2],T):T,z=[0,c(ao[12],0,y)],A=r(b,aW,[0,i]),B=[3,c(N[1],0,[0,z,0])];return[0,[29,c(N[1],0,B)],A]}function
bE(h,b,d){var
e=o(u),i=p===e?u[1]:k===e?a(n[2],u):u,f=c(_[9],b[1],i),g=f[2];b[1]=f[1];return d?r(b,aX,[0,g,aA(h,b,L(d[1]))]):r(b,aW,[0,g])}function
bF(h,b,d){var
e=o(u),i=p===e?u[1]:k===e?a(n[2],u):u,f=c(_[9],b[1],i),g=f[2];b[1]=f[1];return d?r(b,aX,[0,g,aA(h,b,L(d[1]))]):r(b,aW,[0,g])}function
bG(t,M,aw,L,av,J,aq,ap,ao){var
N=J[2],P=J[1],R=M[2],f=M[1],ax=c(g[18],ar,ex);a(O[12],ax);var
l=a(Q[2],0),ad=E(aa[2],0,0,l,f,R),r=c(h[3],f,ad);if(9===r[0]){var
b=r[2],u=b.length-1-6|0;if(2<u>>>0)var
i=0;else{var
s=r[1];switch(u){case
0:var
v=o(au),ae=b[1],af=b[2],ah=b[3],ai=b[4],aj=b[5],ak=b[6],al=p===v?au[1]:k===v?a(n[2],au):au;if(e(h[X],f,s,al))var
d=[0,ev,ae,af,ah,ai,aj,0,0,ak],i=1;else
var
i=0;break;case
1:var
i=0;break;default:var
x=b[1],y=b[2],z=b[3],A=b[4],B=b[5],C=b[6],D=b[7],G=b[8],H=o(as),am=p===H?as[1]:k===H?a(n[2],as):as;if(e(h[X],f,s,am))var
d=[0,0,x,y,z,A,B,[0,C],[0,D],G],i=1;else{var
I=o(at),an=p===I?at[1]:k===I?a(n[2],at):at;if(e(h[X],f,s,an))var
d=[0,ew,x,y,z,A,B,[0,C],[0,D],G],i=1;else
var
i=0}}}}else
var
i=0;if(!i)var
d=K(eu);var
S=d[9],T=d[8],U=d[6],V=d[5],W=d[2],m=[0,f],ay=d[4],az=d[3],aA=d[1],Y=by(l,m,W,V,U,T,S,aw),Z=Y[1],aB=Y[2],_=bD(l,m,aq),aC=_[2],aD=_[1],aE=bE(l,m,ap),aF=bF(l,m,ao),aG=[0,Z,[0,aB,[0,R,[0,aC,[0,aE,[0,aF,[0,bz(L),0]]]]]]],aH=bt(ey),ab=bp(l,m[1],5,aH,aG),ac=ab[2],q=ab[1],aI=F(q,3)[4],aJ=F(q,4)[5],aK=a(j[1][8],t),aL=$(c(w[17],aK,ez),ac,aI),aM=a(j[1][8],t),aN=$(c(w[17],aM,eA),ac,aJ),aO=bA(l,f,L,aA,[0,az,ay,V,U,T],av),aP=P?a(ag[2],P[1]):eC,aQ=N?a(ag[2],N[1]):eB,aR=e(h[5],0,f,W),aS=e(h[5],0,f,S),aT=e(h[5],0,f,Z),aU=F(q,0)[1],aV=F(q,2)[3],aW=a(d_,[0,aR,aS,aT,F(q,1)[2],aV,aU,aO,aD,aL,aN,aP,aQ]);c(bH[7],t,aW);return 0}function
bI(a){return typeof
a==="number"?0:0===a[0]?[0,L(a[1])]:[1,L(a[1])]}function
s(e,b,d){return a(aj[3],b[1])?(b[1]=[0,d],0):K(c(w[17],e,eD))}function
bJ(q,p,o){var
l=bk(p),b=[0,0],d=[0,0],e=[0,0],f=[0,0],h=[0,0],i=[0,0],j=[0,0],k=[0,0],r=l[2],t=l[1];function
m(a){switch(a[0]){case
0:return s(eE,b,bI(a[1]));case
1:return s(eF,e,a[1]);case
2:return s(eG,f,a[1]);case
3:return s(eH,h,a[1]);case
4:var
c=a[1],g=L(a[2]);return s(eI,d,[0,L(c),g]);case
5:return s(eJ,j,[0,a[1],a[2]]);case
6:return s(eK,i,a[1]);default:return s(eL,k,a[1])}}c(g[17][11],m,o);var
a=b[1],n=a?a[1]:0;return bG(q,[0,t,r],d[1],n,e[1],[0,f[1],h[1]],j[1],i[1],k[1])}function
bK(d,a,c){if(a)return a;var
b=br(d,c);return[0,b[2],[0,b[3],0]]}function
bL(f,a,b,d){var
h=r(a,al,[0,b]);function
i(d,c){return r(a,ak,[0,b,d,c])}var
j=e(g[17][16],i,d,h),c=e(az[6],f,a[1],j),k=c[2];a[1]=c[1];return k}function
y(b){var
c=a(h[9],b);return a(v[2][1],c)}function
W(b){var
d=a(v[31],0);return c(v[2][6],d,b)}function
eM(a){var
b=y(a[2]),c=y(a[3]),d=y(a[4]),e=y(a[5]),f=y(a[6]),g=W(a[7]),h=W(a[8]),i=y(a[9]),j=y(a[10]),k=W([28,[0,eN,a[11]]]);return[0,b,[0,c,[0,d,[0,e,[0,f,[0,g,[0,h,[0,i,[0,j,[0,k,[0,W([28,[0,eO,a[12]]]),0]]]]]]]]]]]}function
bM(J,I,H,F){function
b(m){var
b=a(bN[35][4],m),f=a(q[68][4],m);try{var
i=bK(b,H,F),k=[0,b];if(i){var
n=i[2],j=E(aa[2],0,0,f,b,i[1]),o=function(g){var
h=E(aa[2],0,0,f,b,g),c=1-E(bv[81],0,f,b,j,h);if(c){var
i=a(d[3],dZ);return e(Y[6],0,d0,i)}return c};c(g[17][11],o,n);try{var
D=dY(e(h[5],0,b,j)),l=D}catch(g){g=z(g);if(g!==G)throw g;var
p=a(d[3],d1),r=e(C[11],f,b,j),s=a(d[3],d2),t=a(d[13],0),u=a(d[3],d3),w=c(d[12],u,t),x=c(d[12],w,s),A=c(d[12],x,r),B=c(d[12],A,p),l=e(Y[6],0,d4,B)}var
K=bL(f,k,a(h[9],l[1]),i),L=a(v[2][1],K),M=y(bC(f,k,I)),N=eM(l),O=c(g[18],N,[0,M,[0,L,0]]),P=c(v[2][8],J,O),Q=a(q[66][1],k[1]),R=c(q[18],Q,P);return R}throw[0,aU,d5]}catch(b){b=z(b);if(a(q[72][9],b))return c(q[21],0,b);throw b}}return a(q[68][8],b)}var
eR=c(g[17][68],j[1][6],[0,eQ,[0,aq,eP]]),eS=a(j[5][4],eR),eT=0;function
eU(b){var
a=b+1|0;if(!(16<a>>>0))switch(a){case
11:case
15:return 2;case
0:case
13:case
16:return 0}return 1}var
eW=[0,[0,m(eV),eU],eT];function
eX(b){var
a=b+1|0;if(!(14<a>>>0))switch(a){case
9:case
13:return 2;case
0:case
11:case
14:return 0}return 1}var
eZ=[0,[0,ad(eY),eX],eW];function
e0(b){var
a=b+1|0;if(!(18<a>>>0))switch(a){case
12:case
17:return 2;case
0:case
9:case
10:case
11:case
14:case
16:case
18:return 0}return 1}var
e2=[0,[0,ad(e1),e0],eZ];function
e3(a){if(11<=a)if(14<=a)var
b=15<=a?0:1;else{if(12!==a)return 2;var
b=1}else
var
b=-1===a?1:8<=a?1:0;return b?0:1}var
e5=[0,[0,ad(e4),e3],e2];function
e6(b){var
a=b+1|0;if(!(20<a>>>0))switch(a){case
13:case
18:return 2;case
0:case
10:case
11:case
12:case
15:case
17:case
19:case
20:return 0}return 1}var
e8=[0,[0,m(e7),e6],e5];function
e9(a){if(12<=a)if(15<=a)var
b=17<=a?0:1;else{if(13!==a)return 2;var
b=1}else
var
b=-1===a?1:9<=a?1:0;return b?0:1}var
e$=[0,[0,m(e_),e9],e8];function
fa(a){return 0}var
fc=[0,[0,m(fb),fa],e$];function
fd(a){return 0}var
ff=[0,[0,m(fe),fd],fc],fg=[0,[0,al,function(a){return-1===a?0:1}],ff],fh=[0,[0,ak,function(a){return-1===a?0:2===a?2:1}],fg];aR(fi,function(a,b){return bu(fh,a,b)});var
fj=0;function
fk(b){var
a=b+1|0;if(!(15<a>>>0))switch(a){case
10:case
14:return 2;case
0:case
12:case
15:return 0}return 1}var
fm=[0,[0,m(fl),fk],fj];function
fn(a){return 0}var
fp=[0,[0,m(fo),fn],fm];function
fq(a){return 0}var
fs=[0,[0,m(fr),fq],fp],ft=[0,[0,al,function(a){return-1===a?0:1}],fs],fu=[0,[0,ak,function(a){return-1===a?0:2===a?2:1}],ft];aR(fv,function(e,f){function
b(c){var
b=c[1],d=o(b),e=c[2],f=p===d?b[1]:k===d?a(n[2],b):b;return[0,f,e]}var
d=c(g[17][68],b,fu);return function(a){return bd(d,a)}});function
fx(a,b,c){return aS(fw,a,b,c)}c(fz[3],fy,fx);var
aB=m(fA),aC=m(fB),aD=m(fC),fE=m(fD),fG=m(fF),fI=m(fH),aZ=e(aw[4],0,fM,ae[1]),aE=e(aw[4],0,fN,U[22][1]);function
fO(a){return c(ae[23],a,aZ[1])}function
fX(d){var
a=d[2],b=d[1],e=c(x[46],b,a[1]),f=c(x[46],b,a[2]),g=c(x[46],b,a[5]),h=c(x[46],b,a[6]),i=c(x[46],b,a[7]),j=c(x[46],b,a[8]),k=c(x[46],b,a[9]),l=c(V[1],b,a[3]),m=c(V[1],b,a[4]),n=c(V[1],b,a[10]),o=c(V[1],b,a[11]);if(e===a[1])if(f===a[2])if(g===a[5])if(h===a[6])if(i===a[7])if(j===a[8])if(k===a[9])if(l===a[3])if(m===a[4])if(n===a[10])if(o===a[11])return a;return[0,e,f,l,m,g,h,i,j,k,n,o]}function
fY(b){var
a=b[2],c=b[1][1];aZ[1]=e(ae[4],a[1],a,aZ[1]);aE[1]=e(U[22][4],c,a,aE[1]);return 0}var
f0=e(ay[16],fZ,fY,[0,fX]),f1=a(ay[4],f0);function
f2(f,b,i,d){var
g=c(h[3],f[1],d);if(9===g[0])if(1===g[2].length-1){var
l=o(R),r=g[1],s=p===l?R[1]:k===l?a(n[2],R):R;if(e(h[X],f[1],r,s)){var
t=a(O[2],f4),u=a(aV[22],t),v=[0,a(h[9],u),[0,b,b,i]];return a(h[23],v)}}bw(a(Q[2],0),f,b,d);var
m=[0,[0,[0,[0,b,[0,d]]],0],[0,[0,b,[0,d]]]];try{var
q=c(ab[15],m,i),j=q}catch(a){a=z(a);if(a!==G)throw a;var
j=K(f3)}return j[2]}function
bO(m,bs,br){var
at=[0,0],au=[0,0],av=[0,0],aw=[0,0],ax=[0,0],ay=[0,0],az=[0,0],aA=[0,0],aE=[0,0];function
bo(b){if(0===b[0]){var
a=b[1];switch(a[0]){case
0:return s(gd,at,bI(a[1]));case
1:return s(ge,av,a[1]);case
2:return s(gf,aw,a[1]);case
3:return s(gg,ax,a[1]);case
4:var
c=a[1],d=L(a[2]);return s(gh,au,[0,L(c),d]);case
5:return s(gi,aA,[0,a[1],a[2]]);case
6:return s(gj,az,a[1]);default:return s(gk,aE,a[1])}}return s(gl,ay,L(b[1]))}c(g[17][11],bo,br);var
aF=at[1],R=aF?aF[1]:0,aG=aE[1],aH=az[1],aI=aA[1],aJ=ax[1],aK=aw[1],aL=av[1],aM=ay[1],bq=au[1],aS=c(g[18],ar,f5);a(O[12],aS);var
ah=bk(bs),t=ah[2],u=ah[1],l=a(Q[2],0),d=[0,u],aO=E(aa[2],0,0,l,d[1],t),J=c(h[3],d[1],aO);if(9===J[0]){var
b=J[2],S=b.length-1-8|0;if(2<S>>>0)var
i=0;else{var
M=J[1];switch(S){case
0:var
T=b[1],U=b[2],V=b[3],W=b[4],Y=b[5],_=b[6],ab=b[7],ac=b[8],ad=o(aD),aP=p===ad?aD[1]:k===ad?a(n[2],aD):aD;if(e(ai[X],d[1],aP,M))var
f=[0,fK,T,U,V,W,Y,0,0,_,ab,ac,r(d,fI,[0,T,U,V,W,Y,_,ab,ac,t])],i=1;else
var
i=0;break;case
1:var
i=0;break;default:var
x=b[1],y=b[2],z=b[3],A=b[4],B=b[5],C=b[6],D=b[7],G=b[8],H=b[9],I=b[10],ae=o(aB),aQ=p===ae?aB[1]:k===ae?a(n[2],aB):aB;if(e(ai[X],d[1],aQ,M))var
f=[0,0,x,y,z,A,B,[0,C],[0,D],G,H,I,r(d,fE,[0,x,y,z,A,B,C,D,G,H,I,t])],i=1;else{var
af=o(aC),aR=p===af?aC[1]:k===af?a(n[2],aC):aC;if(e(ai[X],d[1],aR,M))var
f=[0,fL,x,y,z,A,B,[0,C],[0,D],G,H,I,r(d,fG,[0,x,y,z,A,B,C,D,G,H,I,t])],i=1;else
var
i=0}}}}else
var
i=0;if(!i)var
f=K(fJ);var
N=f[11],aj=f[8],ak=f[6],al=f[5],P=f[2],aT=f[12],aU=f[10],aV=f[4],aW=f[3],aX=f[1],am=by(l,d,P,al,ak,aj,N,bq),an=am[2],ao=am[1];bG(m,[0,d[1],aT],[0,[0,ao,an]],R,aL,f6,aI,aH,aG);var
ap=bD(l,d,aI),aY=ap[2],aZ=ap[1],a0=bE(l,d,aH),a1=bF(l,d,aG),a2=f2(d,P,aU,N),a3=[0,ao,[0,an,[0,a2,[0,t,[0,aY,[0,a0,[0,a1,[0,bz(R),0]]]]]]]],aN=[k,function(d){var
b=a(j[6][4],f7);return c(j[13][1],[0,eS],b)}],aq=bp(l,d[1],9,aN,a3),v=aq[2],q=aq[1],a4=F(q,3)[4],a5=F(q,4)[5],a6=F(q,5)[6],a7=F(q,6)[7];if(aM)var
a8=[0,e(h[5],0,u,aM[1])],a9=[0,F(q,8)[9],a8],as=a(Z[15],a9);else
var
as=F(q,7)[8];var
a_=a(j[1][8],m),a$=$(c(w[17],a_,f8),v,a4),ba=a(j[1][8],m),bb=$(c(w[17],ba,f9),v,a5),bc=a(j[1][8],m),bd=$(c(w[17],bc,f_),v,a6),be=a(j[1][8],m),bf=$(c(w[17],be,f$),v,a7),bg=a(j[1][8],m),bh=$(c(w[17],bg,ga),v,as),bi=bA(l,u,R,aX,[0,aW,aV,al,ak,aj],aL),bj=aK?a(ag[2],aK[1]):gc,bl=aJ?a(ag[2],aJ[1]):gb,bm=e(h[5],0,u,P),bn=a(f1,[0,bm,e(h[5],0,u,N),bi,aZ,a$,bb,bd,bf,bh,bj,bl]);c(bH[7],m,bn);return 0}function
gm(a){var
b=y(a[2]),c=W(a[3]),d=W(a[4]),e=y(a[5]),f=y(a[7]),g=y(a[6]),h=y(a[8]),i=y(a[9]),j=W([28,[0,gn,a[10]]]);return[0,b,[0,c,[0,d,[0,e,[0,f,[0,g,[0,h,[0,i,[0,j,[0,W([28,[0,go,a[11]]]),0]]]]]]]]]]}function
bP(K,J,I,H){function
b(m){var
b=a(bN[35][4],m),f=a(q[68][4],m);try{var
i=bK(b,I,H),k=[0,b],n=c(g[18],ar,fP);a(O[12],n);if(i){var
o=i[2],j=E(aa[2],0,0,f,b,i[1]),p=function(g){var
h=E(aa[2],0,0,f,b,g),c=1-E(bv[81],0,f,b,j,h);if(c){var
i=a(d[3],fQ);return e(Y[6],0,fR,i)}return c};c(g[17][11],p,o);try{var
F=fO(e(h[5],0,b,j)),l=F}catch(g){g=z(g);if(g!==G)throw g;var
r=a(d[3],fS),s=e(C[11],f,b,j),t=a(d[3],fT),u=a(d[13],0),w=a(d[3],fU),x=c(d[12],w,u),A=c(d[12],x,t),B=c(d[12],A,s),D=c(d[12],B,r),l=e(Y[6],0,fV,D)}var
L=bL(f,k,a(h[9],l[1]),i),M=a(v[2][1],L),N=y(bC(f,k,J)),P=gm(l),Q=c(g[18],P,[0,N,[0,M,0]]),R=c(v[2][8],K,Q),S=a(q[66][1],k[1]),T=c(q[18],S,R);return T}throw[0,aU,fW]}catch(b){b=z(b);if(a(q[72][9],b))return c(q[21],0,b);throw b}}return a(q[68][8],b)}aJ(307,[0,bg,be,bJ,ax,bM,bO,aE,bP],"Newring_plugin__Newring");a(gp[9],an);var
gq=0;function
gr(a,b){return be(a)}var
gt=[0,[0,[0,gs,[1,[5,a(l[16],t[4])],0]],gr],gq];function
gu(b,a,c){return bg(b,a)}var
gw=[0,gv,[1,[5,a(l[16],t[7])],0]],gy=[0,[0,[0,gx,[1,[5,a(l[16],t[4])],gw]],gu],gt];E(a0[8],an,gz,0,0,gy);function
aF(g,f,b){switch(b[0]){case
0:var
h=b[1];if(typeof
h==="number")return a(d[3],gA);else{if(0===h[0]){var
k=h[1],l=c(D[16],g,f),m=c(d[32],l,k),n=a(d[3],gB);return c(d[12],n,m)}var
o=h[1],p=c(D[16],g,f),q=c(d[32],p,o),r=a(d[3],gC);return c(d[12],r,q)}case
1:var
i=b[1];if(0===i[0]){var
s=i[1],t=a(d[3],gD),u=e(aG[22],g,f,s),v=a(d[3],gE),w=a(d[13],0),x=a(d[3],gF),y=c(d[12],x,w),z=c(d[12],y,v),A=c(d[12],z,u);return c(d[12],A,t)}var
B=i[1],C=a(d[3],gG),E=e(d[39],d[13],D[7],B),F=a(d[3],gH),G=a(d[13],0),H=a(d[3],gI),I=c(d[12],H,G),J=c(d[12],I,F),K=c(d[12],J,E);return c(d[12],K,C);case
2:var
L=b[1],M=a(d[3],gJ),N=e(aG[22],g,f,L),O=a(d[3],gK),P=a(d[13],0),Q=a(d[3],gL),R=c(d[12],Q,P),S=c(d[12],R,O),T=c(d[12],S,N);return c(d[12],T,M);case
3:var
U=b[1],V=a(d[3],gM),W=e(aG[22],g,f,U),X=a(d[3],gN),Y=a(d[13],0),Z=a(d[3],gO),_=c(d[12],Z,Y),$=c(d[12],_,X),aa=c(d[12],$,W);return c(d[12],aa,V);case
4:var
ab=b[2],ac=b[1],ad=c(D[16],g,f),ae=c(d[32],ad,ab),af=c(D[16],g,f),ag=c(d[32],af,ac),ah=a(d[3],gP),ai=c(d[12],ah,ag);return c(d[12],ai,ae);case
5:var
j=b[1];if(0===j[0]){var
aj=b[2],ak=j[1],al=a(d[3],gQ),am=e(aG[22],g,f,ak),an=a(d[3],gR),ao=a(d[13],0),ap=c(D[16],g,f),aq=c(d[32],ap,aj),ar=a(d[3],gS),as=c(d[12],ar,aq),at=c(d[12],as,ao),au=c(d[12],at,an),av=c(d[12],au,am);return c(d[12],av,al)}var
aw=b[2],ax=j[1],ay=a(d[3],gT),az=e(d[39],d[13],D[7],ax),aA=a(d[3],gU),aB=a(d[13],0),aC=c(D[16],g,f),aD=c(d[32],aC,aw),aE=a(d[3],gV),aF=c(d[12],aE,aD),aH=c(d[12],aF,aB),aI=c(d[12],aH,aA),aJ=c(d[12],aI,az);return c(d[12],aJ,ay);case
6:var
aK=b[1],aL=c(D[16],g,f),aM=c(d[32],aL,aK),aN=a(d[3],gW);return c(d[12],aN,aM);default:var
aO=b[1],aP=c(D[16],g,f),aQ=c(d[32],aP,aO),aR=a(d[3],gX);return c(d[12],aR,aQ)}}var
gY=0;function
gZ(a,c,b){return[0,[0,a]]}var
g0=[6,I[16][1]],g2=[0,[0,[0,[0,0,[0,a(i[10],g1)]],g0],gZ],gY];function
g3(b,a){return g4}var
g6=[0,[0,[0,0,[0,a(i[10],g5)]],g3],g2];function
g7(a,c,b){return[0,[1,a]]}var
g8=[6,I[16][1]],g_=[0,[0,[0,[0,0,[0,a(i[10],g9)]],g8],g7],g6];function
g$(e,a,d,c,b){return[1,[0,a]]}var
hb=[0,a(i[10],ha)],hc=[6,aH[18]],he=[0,a(i[10],hd)],hg=[0,[0,[0,[0,[0,[0,0,[0,a(i[10],hf)]],he],hc],hb],g$],g_];function
hh(e,a,d,c,b){return[1,[1,a]]}var
hj=[0,a(i[10],hi)],hk=[1,[6,I[16][7]]],hm=[0,a(i[10],hl)],ho=[0,[0,[0,[0,[0,[0,0,[0,a(i[10],hn)]],hm],hk],hj],hh],hg];function
hp(e,a,d,c,b){return[2,a]}var
hr=[0,a(i[10],hq)],hs=[6,aH[18]],hu=[0,a(i[10],ht)],hw=[0,[0,[0,[0,[0,[0,0,[0,a(i[10],hv)]],hu],hs],hr],hp],ho];function
hx(e,a,d,c,b){return[3,a]}var
hz=[0,a(i[10],hy)],hA=[6,aH[18]],hC=[0,a(i[10],hB)],hE=[0,[0,[0,[0,[0,[0,0,[0,a(i[10],hD)]],hC],hA],hz],hx],hw];function
hF(b,a,d,c){return[4,a,b]}var
hG=[6,I[16][1]],hH=[6,I[16][1]],hJ=[0,[0,[0,[0,[0,0,[0,a(i[10],hI)]],hH],hG],hF],hE];function
hK(a,c,b){return[6,a]}var
hL=[6,I[16][1]],hN=[0,[0,[0,[0,0,[0,a(i[10],hM)]],hL],hK],hJ];function
hO(f,b,e,a,d,c){return[5,[1,b],a]}var
hQ=[0,a(i[10],hP)],hR=[1,[6,I[16][7]]],hT=[0,a(i[10],hS)],hU=[6,I[16][1]],hW=[0,[0,[0,[0,[0,[0,[0,0,[0,a(i[10],hV)]],hU],hT],hR],hQ],hO],hN];function
hX(f,b,e,a,d,c){return[5,[0,b],a]}var
hZ=[0,a(i[10],hY)],h0=[6,aH[18]],h2=[0,a(i[10],h1)],h3=[6,I[16][1]],h5=[0,[0,[0,[0,[0,[0,[0,0,[0,a(i[10],h4)]],h3],h2],h0],hZ],hX],hW];function
h6(a,c,b){return[7,a]}var
h7=[6,I[16][1]],h9=[1,[0,[0,[0,[0,0,[0,a(i[10],h8)]],h7],h6],h5]],h_=[0,function(b,a){return function(c){return aF(b,a,c)}},h9],bQ=c(M[3],h$,h_),a1=bQ[2],ia=bQ[1];function
bR(f,c,b){function
g(a){return aF(f,c,a)}var
h=e(d[39],d[28],g,b);return a(d[46],h)}var
ib=0;function
ic(d,a,c,b){return a}var
ie=[0,a(i[10],id)],ih=[2,[6,a1],[0,a(i[10],ig)]],ij=[1,[0,[0,[0,[0,[0,0,[0,a(i[10],ii)]],ih],ie],ic],ib]],ik=[0,function(b,a){return function(c){return bR(b,a,c)}},ij],bS=c(M[3],il,ik),bT=bS[1],im=bS[2],io=0,ip=[0,M[5]],iu=[0,[0,0,it,function(j,b){a(aI[2],j);var
f=b[3],g=a(d[22],iq);c(af[7],0,g);var
h=ax[1];function
i(k,b){var
g=a(Q[2],0),l=[0,a(ac[17],g),g],h=e(aj[22],bU[4],l,f),i=h[2],j=h[1],m=e(C[6],i,j,b[2]),n=a(d[3],ir),o=a(d[13],0),p=e(C[6],i,j,b[1]),q=a(d[3],is),r=a(d[13],0),s=a(U[18],k),t=a(D[6],s),u=c(d[12],t,r),v=c(d[12],u,q),w=c(d[12],v,p),x=c(d[12],w,o),y=c(d[12],x,n),z=c(d[12],y,m),A=c(d[26],2,z);return c(af[7],0,A)}c(U[22][11],i,h);return[0,b[1],b[2],f,b[4]]},ip],io],iv=0;function
iw(g,f,b,e,d){a(aI[2],e);var
c=b?b[1]:0;bJ(g,f,c);return d}var
ix=[1,[4,[5,a(l[16],bT)]],0],iz=[0,iy,[1,[5,a(l[16],t[11])],ix]],iC=[0,[0,0,[0,iB,[0,iA,[1,[5,a(l[16],t[7])],iz]]],iw,iv],iu],iD=0,iE=[0,function(a){return M[6]}];ah(M[2],iF,iE,iD,iC);var
iG=0;function
iH(e,d,c,f){var
b=a(g[17][aO],c);return bM(e,d,b[2],b[1])}var
iJ=[0,iI,[1,[0,[5,a(l[16],t[11])]],0]],iL=[0,iK,[1,[2,[5,a(l[16],t[11])]],iJ]],iN=[0,[0,[0,iM,[1,[6,a(l[16],bV[8]),0],iL]],iH],iG];E(a0[8],an,iO,0,0,iN);function
a2(f,e,b){if(0===b[0])return aF(f,e,b[1]);var
g=b[1],h=c(D[16],f,e),i=c(d[32],h,g),j=a(d[3],iP);return c(d[12],j,i)}var
iQ=0,iR=[0,[0,[0,0,[6,a1]],function(a,b){return[0,a]}],iQ];function
iS(a,c,b){return[1,a]}var
iT=[6,I[16][1]],iV=[1,[0,[0,[0,[0,0,[0,a(i[10],iU)]],iT],iS],iR]],iW=[0,function(b,a){return function(c){return a2(b,a,c)}},iV],bW=c(M[3],iX,iW),bX=bW[2],iY=bW[1];function
bY(f,c,b){function
g(a){return a2(f,c,a)}var
h=e(d[39],d[28],g,b);return a(d[46],h)}var
iZ=0;function
i0(d,a,c,b){return a}var
i2=[0,a(i[10],i1)],i4=[2,[6,bX],[0,a(i[10],i3)]],i6=[1,[0,[0,[0,[0,[0,0,[0,a(i[10],i5)]],i4],i2],i0],iZ]],i7=[0,function(b,a){return function(c){return bY(b,a,c)}},i6],bZ=c(M[3],i8,i7),b0=bZ[1],i9=bZ[2],i_=0,i$=[0,M[5]],je=[0,[0,0,jd,function(j,b){a(aI[2],j);var
f=b[3],g=a(d[22],ja);c(af[7],0,g);var
h=aE[1];function
i(k,b){var
g=a(Q[2],0),l=[0,a(ac[17],g),g],h=e(aj[22],bU[4],l,f),i=h[2],j=h[1],m=e(C[6],i,j,b[2]),n=a(d[3],jb),o=a(d[13],0),p=e(C[6],i,j,b[1]),q=a(d[3],jc),r=a(d[13],0),s=a(U[18],k),t=a(D[6],s),u=c(d[12],t,r),v=c(d[12],u,q),w=c(d[12],v,p),x=c(d[12],w,o),y=c(d[12],x,n),z=c(d[12],y,m),A=c(d[26],2,z);return c(af[7],0,A)}c(U[22][11],i,h);return[0,b[1],b[2],f,b[4]]},i$],i_],jf=0;function
jg(g,f,b,e,d){a(aI[2],e);var
c=b?b[1]:0;bO(g,f,c);return d}var
jh=[1,[4,[5,a(l[16],b0)]],0],jj=[0,ji,[1,[5,a(l[16],t[11])],jh]],jm=[0,[0,0,[0,jl,[0,jk,[1,[5,a(l[16],t[7])],jj]]],jg,jf],je],jn=0,jo=[0,function(a){return M[6]}];ah(M[2],jp,jo,jn,jm);var
jq=0;function
jr(e,d,c,f){var
b=a(g[17][aO],c);return bP(e,d,b[2],b[1])}var
jt=[0,js,[1,[0,[5,a(l[16],t[11])]],0]],jv=[0,ju,[1,[2,[5,a(l[16],t[11])]],jt]],jx=[0,[0,[0,jw,[1,[5,a(l[16],bV[8])],jv]],jr],jq];E(a0[8],an,jy,0,0,jx);aJ(319,[0,an,aF,ia,a1,bR,bT,im,a2,iY,bX,bY,b0,i9],"Newring_plugin__G_newring");return}
