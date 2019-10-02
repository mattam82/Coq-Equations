function(lh){"use strict";var
cq="*",a2=-16,cA=" 0\n",a1="Equation E",a0=" and E",bC=": ",am=".\n",U=246,cw="(",cz="not a number",B=123,cp="+ ",ct="- ",cm="------------------------\n\n",an="omega",cs="Inequation E",cy="Z",bB="_vendor+v8.10+64bit/coq/plugins/omega/coq_omega.ml",bA=103,cx=")",cE="N",cv="with",cD="X%d",cr=" subsumes E",bE=" E",ac="Omega",cC=" states ",bD=-18,co="positive",cn="Equations E",I=144,cB="nat",cG="Omega: Can't solve a goal with non-linear products",ad=248,ab=100,cu="Coq",cF="E%d subsumes E%d.\n",y=lh.jsoo_runtime,al=y.caml_check_bound,ck=y.caml_equal,aa=y.caml_fresh_oo_id,b=y.caml_new_string,aW=y.caml_notequal,aU=y.caml_register_global,aZ=y.caml_string_notequal,aY=y.caml_trampoline,aX=y.caml_trampoline_return,q=y.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):y.caml_call_gen(a,[b])}function
c(a,b,c){return a.length==2?a(b,c):y.caml_call_gen(a,[b,c])}function
k(a,b,c,d){return a.length==3?a(b,c,d):y.caml_call_gen(a,[b,c,d])}function
aV(a,b,c,d,e){return a.length==4?a(b,c,d,e):y.caml_call_gen(a,[b,c,d,e])}function
cl(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):y.caml_call_gen(a,[b,c,d,e,f])}function
lf(a,b,c,d,e,f,g,h,i,j){return a.length==9?a(b,c,d,e,f,g,h,i,j):y.caml_call_gen(a,[b,c,d,e,f,g,h,i,j])}function
lg(a,b,c,d,e,f,g,h,i,j,k,l){return a.length==11?a(b,c,d,e,f,g,h,i,j,k,l):y.caml_call_gen(a,[b,c,d,e,f,g,h,i,j,k,l])}var
o=y.caml_get_global_data(),le=[11,b(" + "),[2,0,[12,32,[2,0,[11,b(bE),[4,0,0,0,[11,b(am),0]]]]]]],cg=[0,[0,2],[0,0,0]],aS=b("omega_plugin"),l=o.Stdlib__list,t=o.Stdlib__printf,j=o.Stdlib,m=o.Util,C=o.Not_found,P=o.Int,s=o.Stdlib__hashtbl,aC=o.Assert_failure,x=o.Names,e=o.EConstr,w=o.Bigint,N=o.Pp,J=o.CErrors,T=o.Logic,bO=o.Coqlib,g=o.Tactics,h=o.Tacticals,n=o.Proofview,u=o.Context,ar=o.Nameops,z=o.Tacmach,br=o.Reductionops,cb=o.Refine,bp=o.Nametab,bq=o.Libnames,a$=o.Tacred,ap=o.Goptions,cj=o.Ltac_plugin__Tacentries,kG=o.Termops,jZ=o.Contradiction,j4=o.Equality,ii=o.Evarutil,hN=o.Global,hO=o.Evd,d5=o.UnivGen,dx=o.CamlinternalLazy,kR=o.Stdlib__string,kP=o.Ltac_plugin__Tacenv,kQ=o.Ltac_plugin__Tacinterp,kN=o.Mltop,k_=o.Stdarg,k$=o.Genarg;aU(389,[0,0,0,0],"Omega_plugin");var
V=[0,0],c2=[0,[11,b(cs),[4,0,0,0,[11,b(" is divided by "),[2,0,[11,b(" and the constant coefficient is rounded by subtracting "),[2,0,[11,b(am),0]]]]]]],b("Inequation E%d is divided by %s and the constant coefficient is rounded by subtracting %s.\n")],c3=[0,[11,b("Constant in equation E"),[4,0,0,0,[11,b(" is not divisible by the pgcd "),[2,0,[11,b(" of its other coefficients.\n"),0]]]]],b("Constant in equation E%d is not divisible by the pgcd %s of its other coefficients.\n")],c4=[0,[12,69,[4,0,0,0,[11,b(" is trivially satisfiable.\n"),0]]],b("E%d is trivially satisfiable.\n")],c5=[0,[11,b(a1),[4,0,0,0,[11,b(" is divided by the pgcd "),[2,0,[11,b(" of its coefficients.\n"),0]]]]],b("Equation E%d is divided by the pgcd %s of its coefficients.\n")],c6=[0,[11,b("We state "),[2,0,[11,b(bE),[4,0,0,0,[11,b(" = "),[2,0,[12,32,[2,0,[11,b(bE),[4,0,0,0,le]]]]]]]]]],b("We state %s E%d = %s %s E%d + %s %s E%d.\n")],c7=[0,[11,b("We define a new equation E"),[4,0,0,0,[11,b(bC),0]]],b("We define a new equation E%d: ")],c8=b(" 0"),c9=[0,[11,b("We define E"),[4,0,0,0,[11,b(bC),0]]],b("We define E%d: ")],c_=b(cA),c$=[0,[12,69,[4,0,0,0,[11,b(cr),[4,0,0,0,[11,b(am),0]]]]],b(cF)],da=[0,[12,69,[4,0,0,0,[11,b(cr),[4,0,0,0,[11,b(am),0]]]]],b(cF)],db=[0,[11,b(cn),[4,0,0,0,[11,b(a0),[4,0,0,0,[11,b(" imply a contradiction on their constant factors.\n"),0]]]]],b("Equations E%d and E%d imply a contradiction on their constant factors.\n")],dc=[0,[11,b(cn),[4,0,0,0,[11,b(a0),[4,0,0,0,[11,b(" state that their body is at the same time equal and different\n"),0]]]]],b("Equations E%d and E%d state that their body is at the same time equal and different\n")],dd=[0,[12,69,[4,0,0,0,[11,b(a0),[4,0,0,0,[11,b(" can be merged into E"),[4,0,0,0,[11,b(am),0]]]]]]],b("E%d and E%d can be merged into E%d.\n")],de=[0,[11,b(a1),[4,0,0,0,[11,b(cC),[2,0,[11,b(" = 0.\n"),0]]]]],b("Equation E%d states %s = 0.\n")],df=[0,[11,b(cs),[4,0,0,0,[11,b(" states 0 != 0.\n"),0]]],b("Inequation E%d states 0 != 0.\n")],dg=[0,[11,b(a1),[4,0,0,0,[11,b(cC),[2,0,[11,b(" >= 0.\n"),0]]]]],b("Equation E%d states %s >= 0.\n")],dh=[0,[11,b(a1),[4,0,0,0,[11,b(" is split in E"),[4,0,0,0,[11,b(a0),[4,0,0,0,[11,b("\n\n"),0]]]]]]],b("Equation E%d is split in E%d and E%d\n\n")],di=[0,[11,b("To ensure a solution in the dark shadow the equation E"),[4,0,0,0,[11,b(" is weakened by "),[2,0,[11,b(am),0]]]]],b("To ensure a solution in the dark shadow the equation E%d is weakened by %s.\n")],dt=b("depend"),dw=b("solve"),du=[0,b("_vendor+v8.10+64bit/coq/plugins/omega/omega.ml"),602,15],ds=b("disequation in simplify"),dr=b("Product dardk"),dq=[0,0,0,0],dn=b("TL"),dm=b("eliminate_with_in"),dj=[0,[12,88,[4,0,0,0,0]],b(cD)],c0=b(">= 0\n"),c1=b(cm),cX=[0,[12,69,[4,0,0,0,[11,b(bC),0]]],b("E%d: ")],cY=[0,[2,0,[11,b(cA),0]],b("%s 0\n")],cZ=b(cm),cU=b("equation"),cV=b("inequation"),cW=b("disequation"),cR=b("="),cS=b(">="),cT=b("!="),cK=b(ct),cN=b(cp),cO=b(""),cL=[0,[2,0,[12,32,0]],b("%s ")],cM=[0,[2,0,[12,32,[2,0,[12,32,0]]]],b("%s %s ")],cP=[0,[11,b(cp),[2,0,[12,32,0]]],b("+ %s ")],cQ=[0,[11,b(ct),[2,0,[12,32,0]]],b("- %s ")],cH=b("pgcd_l"),cI=b("Omega_plugin.Omega.MakeOmegaSolver(I).UNSOLVABLE"),cJ=b("Omega_plugin.Omega.MakeOmegaSolver(I).NO_CONTRADICTION"),dk=b("Omega_plugin.Omega.MakeOmegaSolver(I).FACTOR1"),dl=b("Omega_plugin.Omega.MakeOmegaSolver(I).CHOPVAR"),dp=b("Omega_plugin.Omega.MakeOmegaSolver(I).SOLVED_SYSTEM"),dv=b("Omega_plugin.Omega.MakeOmegaSolver(I).FULL_SOLUTION"),h_=b(cw),h$=b("+"),ia=b(cx),ib=b(cw),ic=b(cq),id=b(cx),ie=b("?"),ig=b("weight"),iv=[0,2],iw=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]],ix=[0,[0,[0,1],0],[0,[0,[0,2],0],0]],ir=[0,2],is=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]],it=[0,2],iu=[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,1],0]],[0,[0,[0,2],[0,[0,2],0]],0]]],iy=[0,2],iz=[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,1],0]],[0,[0,[0,2],[0,[0,2],0]],0]]],iA=[0,[0,[0,1],0],[0,[0,[0,2],0],0]],i2=[0,[0,[0,1],[0,[0,1],[0,[0,1],0]]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],[0,[0,2],0]],[0,[0,[0,1],[0,[0,1],[0,[0,2],[0,[0,1],0]]]],0]]]],i3=[0,1],i4=[0,2],i5=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]],i6=b(cG),i7=[0,2],i8=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]],je=[0,1],jf=[0,2],jg=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],0]],jh=b(cG),ji=[0,2],jj=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],0]],jk=[0,[0,[0,1],0],0],jl=[0,1],jm=[0,2],jn=[0,1],jo=[0,2],jp=[0,[0,[0,1],0],[0,[0,[0,2],0],0]],jq=[0,1],jH=[0,0,0],jE=[0,1],jF=[0,2],jA=[0,1],jB=[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,1],0]],[0,[0,[0,2],[0,[0,2],0]],0]]],jC=[0,1],jD=[0,2],jG=[0,1],jJ=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,2],0],0]],jI=[0,2],kL=[0,b(cu),[0,b(an),[0,b(ac),0]]],kF=[0,0],kE=[0,0],kH=b("_eqn"),kB=b("_left"),kC=b("_right"),kk=[0,1],kd=[0,2],ke=[0,1],kf=[0,2],kg=[0,1],kh=[0,2],ki=[0,1],kj=[0,1],kl=[0,[0,3],[0,0,0]],km=[0,[0,2],[0,0,0]],kn=[0,[0,2],[0,0,0]],ko=[0,[0,1],[0,0,0]],kp=[0,[0,2],[0,0,0]],kq=[0,[0,1],[0,0,0]],kr=[0,[0,2],[0,0,0]],ks=[0,[0,1],[0,0,0]],kt=[0,[0,2],[0,0,0]],ku=[0,[0,1],[0,0,0]],kv=[0,[0,2],[0,0,0]],kw=[0,[0,1],[0,0,0]],j$=[0,0,0],ka=b("Omega can't solve this system"),j9=b("State"),j7=[0,0,0],jN=[0,[0,3],0],jO=[0,[0,2],0],jP=[0,[0,3],0],jQ=[0,[0,3],0],jR=[0,[0,1],[0,0,0]],jS=[0,[0,2],[0,0,0]],jT=[0,[0,2],[0,0,0]],jU=[0,[0,[0,1],0],0],jV=[0,2],jW=[0,1],jX=[0,1],jY=[0,[0,2],[0,0,0]],j0=[0,[0,1],[0,0,0]],j1=[0,[0,3],0],j2=[0,[0,[0,1],0],0],j3=[0,[0,3],0],j5=[0,[0,2],[0,0,0]],j6=[0,[0,2],[0,0,0]],jK=b("auxiliary"),jL=b("auxiliary_1"),jM=b("auxiliary_2"),jx=b("condense.1"),jy=[0,2],jz=[0,0,0],jw=b("reduce_factor.1"),js=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],[0,[0,2],0]],0]]],jt=[0,[0,[0,2],0],[0,[0,[0,1],[0,[0,2],0]],0]],ju=[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,2],0]],0]],jv=[0,[0,[0,1],0],0],jr=b("shrink.1"),jc=[0,2],jd=[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],0],[0,[0,[0,1],[0,[0,2],0]],0]]]]],ja=[0,2],jb=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]],i9=[0,2],i_=[0,[0,[0,1],[0,[0,1],[0,[0,1],0]]],[0,[0,[0,1],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]]],iP=[0,[0,[0,1],[0,[0,1],[0,[0,1],0]]],[0,[0,[0,1],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],[0,[0,2],0]],0]]]]]],iQ=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,2],0],0]],iR=[0,1],iS=[0,2],iT=[0,2],iU=[0,2],iV=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]],iW=[0,2],iX=[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],[0,[0,2],0]],0]]]]],iY=[0,2],iZ=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],0],0]]],i0=[0,2],i1=[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],[0,[0,2],0]],0]]]]],iC=[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,1],[0,[0,2],0]],[0,[0,[0,2],[0,[0,2],0]],0]]]]]]],iD=[0,[0,[0,1],[0,[0,1],0]],[0,[0,[0,2],0],0]],iE=[0,1],iF=[0,2],iG=[0,2],iH=[0,2],iI=[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],0],[0,[0,[0,1],[0,[0,2],0]],0]]]]],iJ=[0,2],iK=[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],[0,[0,2],0]],0]]]]],iL=[0,2],iM=[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],0],[0,[0,[0,1],[0,[0,2],0]],0]]]]],iN=[0,2],iO=[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,1],0]]]],[0,[0,[0,2],[0,[0,1],[0,[0,1],[0,[0,2],0]]]],[0,[0,[0,1],0],[0,[0,[0,2],[0,[0,1],[0,[0,2],0]]],[0,[0,[0,2],[0,[0,2],0]],0]]]]],ip=[0,b(bB),688,17],io=[0,b(bB),689,13],iq=[0,0],im=[0,b(bB),648,9],ij=b("H"),ik=b("P"),ih=b("compile_equation."),h9=[0,0],h8=b("x"),h7=b("occurrence "),h6=b("abstract_path "),h4=b(cz),h5=b(cz),h1=b("Omega: Not a quantifier-free goal"),hZ=b("not"),hY=b("Z.gt"),hX=b("Z.le"),hV=b("Z.sub"),hT=b("Z.pred"),hR=b("Z.succ"),hP=b(" is not an evaluable constant."),hQ=[0,b("Coq_omega")],d3=b("find_contr"),d1=b("tag_hypothesis"),dZ=[0,1],dX=[0,[12,88,[4,0,0,0,0]],b(cD)],dW=b("WW"),dU=b("Zvar"),dS=b(ac),dz=[0,b(ac),[0,b("System"),0]],dA=b("Omega system time displaying flag"),dD=[0,b(ac),[0,b("Action"),0]],dE=b("Omega action display flag"),dH=[0,b(ac),[0,b("OldStyle"),0]],dI=b("Omega old style flag"),dL=[0,b("Stable"),[0,b(ac),0]],dM=b("Omega automatic reset of generated names"),dP=[0,b(ac),[0,b("UseLocalDefs"),0]],dQ=b("Omega takes advantage of context variables with body"),d6=b("num.pos.xH"),d7=b("num.pos.xO"),d8=b("num.pos.xI"),d9=b("num.Z.Z0"),d_=b("num.Z.Zpos"),d$=b("num.Z.Zneg"),ea=b("num.Z.type"),eb=b("core.comparison.type"),ed=b("core.comparison.Gt"),ee=b("num.Z.add"),ef=b("num.Z.mul"),eg=b("num.Z.opp"),eh=b("num.Z.sub"),ei=b("num.Z.succ"),ej=b("num.Z.pred"),ek=b("num.Z.of_nat"),el=b("num.Nat2Z.inj_add"),en=b("num.Nat2Z.inj_mul"),ep=b("num.Nat2Z.inj_sub"),er=b("plugins.omega.inj_minus2"),et=b("num.Nat2Z.inj_succ"),ev=b("plugins.omega.inj_eq"),ex=b("plugins.omega.inj_neq"),ez=b("plugins.omega.inj_le"),eB=b("plugins.omega.inj_lt"),eD=b("plugins.omega.inj_ge"),eF=b("plugins.omega.inj_gt"),eH=b("plugins.omega.fast_Zplus_assoc_reverse"),eI=b("plugins.omega.fast_Zplus_assoc"),eK=b("plugins.omega.fast_Zmult_assoc_reverse"),eM=b("plugins.omega.fast_Zplus_permute"),eN=b("plugins.omega.fast_Zplus_comm"),eO=b("plugins.omega.fast_Zmult_comm"),eQ=b("plugins.omega.Zmult_le_approx"),eS=b("plugins.omega.OMEGA1"),eU=b("plugins.omega.OMEGA2"),eW=b("plugins.omega.OMEGA3"),eY=b("plugins.omega.OMEGA4"),e0=b("plugins.omega.OMEGA5"),e2=b("plugins.omega.OMEGA6"),e4=b("plugins.omega.OMEGA7"),e6=b("plugins.omega.OMEGA8"),e8=b("plugins.omega.OMEGA9"),e_=b("plugins.omega.fast_OMEGA10"),fa=b("plugins.omega.fast_OMEGA11"),fb=b("plugins.omega.fast_OMEGA12"),fc=b("plugins.omega.fast_OMEGA13"),fe=b("plugins.omega.fast_OMEGA14"),fg=b("plugins.omega.fast_OMEGA15"),fi=b("plugins.omega.fast_OMEGA16"),fk=b("plugins.omega.OMEGA17"),fm=b("plugins.omega.OMEGA18"),fo=b("plugins.omega.OMEGA19"),fq=b("plugins.omega.OMEGA20"),fs=b("plugins.omega.fast_Zred_factor0"),fu=b("plugins.omega.fast_Zred_factor1"),fw=b("plugins.omega.fast_Zred_factor2"),fy=b("plugins.omega.fast_Zred_factor3"),fA=b("plugins.omega.fast_Zred_factor4"),fC=b("plugins.omega.fast_Zred_factor5"),fD=b("plugins.omega.fast_Zred_factor6"),fF=b("plugins.omega.fast_Zmult_plus_distr_l"),fH=b("plugins.omega.fast_Zopp_plus_distr"),fJ=b("plugins.omega.fast_Zopp_mult_distr_r"),fL=b("plugins.omega.fast_Zopp_eq_mult_neg_1"),fM=b("plugins.omega.Zegal_left"),fO=b("plugins.omega.Zne_left"),fQ=b("plugins.omega.Zlt_left"),fS=b("plugins.omega.Zge_left"),fU=b("plugins.omega.Zgt_left"),fW=b("plugins.omega.Zle_left"),fY=b("plugins.omega.new_var"),f0=b("plugins.omega.intro_Z"),f2=b("num.Z.eq_decidable"),f4=b("plugins.omega.dec_Zne"),f6=b("num.Z.le_decidable"),f8=b("num.Z.lt_decidable"),f_=b("plugins.omega.dec_Zgt"),ga=b("plugins.omega.dec_Zge"),gc=b("plugins.omega.not_Zeq"),ge=b("plugins.omega.not_Zne"),gg=b("plugins.omega.Znot_le_gt"),gi=b("plugins.omega.Znot_lt_ge"),gk=b("plugins.omega.Znot_ge_lt"),gm=b("plugins.omega.Znot_gt_le"),go=b("plugins.omega.neq"),gp=b("plugins.omega.Zne"),gq=b("num.Z.le"),gr=b("num.Z.lt"),gt=b("num.Z.ge"),gv=b("num.Z.gt"),gw=b("num.nat.type"),gx=b("num.nat.O"),gy=b("num.nat.S"),gz=b("num.nat.le"),gA=b("num.nat.lt"),gC=b("num.nat.ge"),gE=b("num.nat.gt"),gF=b("num.nat.add"),gH=b("num.nat.sub"),gI=b("num.nat.mul"),gK=b("num.nat.pred"),gM=b("num.nat.pred_of_minus"),gO=b("num.nat.le_gt_dec"),gQ=b("num.nat.eq_dec"),gS=b("num.nat.dec_le"),gU=b("num.nat.dec_lt"),gW=b("num.nat.dec_ge"),gY=b("num.nat.dec_gt"),g0=b("num.nat.not_eq"),g2=b("num.nat.not_le"),g4=b("num.nat.not_lt"),g6=b("num.nat.not_ge"),g8=b("num.nat.not_gt"),g_=b("core.eq.ind_r"),ha=b("core.dec.or"),hc=b("core.dec.and"),he=b("core.dec.imp"),hg=b("core.dec.iff"),hi=b("core.dec.not"),hk=b("core.dec.False"),hm=b("core.dec.not_not"),ho=b("core.dec.True"),hq=b("core.dec.not_or"),hs=b("core.dec.not_and"),hu=b("core.dec.not_imp"),hw=b("core.dec.not_iff"),hy=b("core.dec.dec_not_not"),hA=b("core.dec.imp_simp"),hC=b("core.iff.type"),hE=b("core.not.type"),hF=b("core.and.type"),hG=b("core.or.type"),hH=b("core.eq.type"),hI=b("core.ex.type"),hK=b("core.False.type"),hL=b("core.True.type"),kA=b("Omega_plugin.Coq_omega.Undecidable"),k6=[0,b(cB),[0,b(co),[0,b(cE),[0,b(cy),0]]]],kS=b(cE),kT=b(cy),kU=b(cB),kV=b(co),kX=b("zify_positive"),kY=b("zify_nat"),kZ=b("zify_op"),k0=b("zify_N"),kW=b("No Omega knowledge base for type "),kO=[0,b("PreOmega"),[0,b(an),[0,b(cu),0]]],k2=[0,b(an),0],k4=b(an),k7=[0,b(an),[0,b(cv),[0,b(cq),0]]],la=b(cv),lb=b(an),ld=b("omega'");function
bF(f){var
n=f[1],v=f[2];function
at(b,a){var
d=c(f[2],b,a),e=d||ck(b,a);return e}function
A(b,a){return c(f[2],a,b)}function
M(b,a){var
d=c(f[2],a,b),e=d||ck(b,a);return e}var
h=f[3],o=f[4],i=f[5];function
x(b,a){return c(f[6],b,a)[1]}function
N(b,a){return c(f[6],b,a)[2]}var
d=f[8],e=f[9],y=c(h,e,e),ah=a(f[7],e);function
p(b){return c(f[2],b,d)?a(f[7],b):b}var
g=f[10],w=f[7];function
au(b,a){return b<a?1:0}function
av(b,a){return a<b?1:0}function
aw(b,a){return b<=a?1:0}function
ax(b,a){return a<=b?1:0}function
ay(b){a(j[33],b);a(j[36],0);return a(j[52],j[28])}function
F(b,a){a[1]=[0,b,a[1]];return 0}function
ai(f,e){var
b=f,a=e;for(;;){if(c(n,a,d))return b;var
g=N(b,a),b=a,a=g;continue}}function
aj(b){return b?k(l[20],ai,b[1],b[2]):a(j[3],cH)}function
G(b,a){var
g=M(b,d),f=A(a,d);return 0===g?0===f?x(b,a):c(o,x(c(h,b,e),a),e):0===f?c(o,x(c(o,b,e),a),e):x(b,a)}var
r=[ad,cI,aa(0)],ak=[ad,cJ,aa(0)];function
H(h,f){var
b=f[2],m=f[1],o=0;function
q(i,b){var
l=c(v,b[1],d)?cK:i?cN:cO;a(j[31],l);var
f=p(b[1]);if(c(n,f,e)){var
m=a(h,b[2]);c(t[2],cL,m)}else{var
o=a(h,b[2]),q=a(g,f);k(t[2],cM,q,o)}return 1}k(l[20],q,o,m);if(A(b,d)){var
r=a(g,b);return c(t[2],cP,r)}var
i=c(v,b,d);if(i){var
s=a(g,p(b));return c(t[2],cQ,s)}return i}function
Y(a){function
b(b,a){if(15===a[0]){var
d=a[2][2],f=Y(a[3][2]),g=Y(d);return c(h,c(h,c(h,b,e),g),f)}return c(h,b,e)}return k(l[20],b,d,a)}function
O(a){switch(a){case
0:return cR;case
1:return cS;default:return cT}}function
Q(a){switch(a){case
0:return cU;case
1:return cV;default:return cW}}function
z(d,b){function
e(a){var
b=a[4],e=a[3],f=a[2];c(t[2],cX,a[1]);H(d,[0,e,b]);var
g=O(f);return c(t[2],cY,g)}c(l[15],e,b);return a(j[31],cZ)}function
az(d,b){function
e(b){H(d,b);return a(j[31],c0)}c(l[15],e,b);return a(j[31],c1)}function
R(d,q){var
e=q;for(;;){if(e){var
b=e[1],r=e[2];switch(b[0]){case
0:var
s=b[3],u=b[1],v=a(g,b[4]),w=a(g,s);aV(t[2],c2,u[1],w,v);break;case
1:var
x=b[1],y=a(g,b[2]);k(t[2],c3,x[1],y);break;case
2:c(t[2],c4,b[1]);break;case
3:var
z=b[1],A=a(g,b[2]);k(t[2],c5,z[1],A);break;case
4:var
l=b[3],m=l[2],n=b[2],i=n[2],B=l[1],C=n[1],D=b[1],E=m[1],F=Q(m[2]),G=a(g,B),I=i[1],J=Q(i[2]),K=a(g,C),L=Q(i[2]);lf(t[2],c6,L,D,K,J,I,G,F,E);break;case
5:var
f=b[1][1];c(t[2],c7,f[1]);H(d,[0,f[3],f[4]]);var
M=O(f[2]);a(j[31],M);a(j[31],c8);break;case
6:var
h=b[1];c(t[2],c9,h[1]);H(d,[0,h[3],h[4]]);var
N=O(h[2]);a(j[31],N);a(j[31],c_);break;case
7:k(t[2],c$,b[1],b[2]);break;case
8:k(t[2],da,b[1],b[2]);break;case
9:k(t[2],db,b[1][1],b[2][1]);break;case
10:k(t[2],dc,b[1][1],b[2][1]);break;case
11:aV(t[2],dd,b[2][1],b[3],b[1]);break;case
12:var
P=b[1],S=a(g,b[2]);k(t[2],de,P,S);break;case
13:c(t[2],df,b[1]);break;case
14:var
T=b[1],U=a(g,b[2]);k(t[2],dg,T,U);break;case
15:var
o=b[3],p=b[2],V=o[2],W=p[2];aV(t[2],dh,b[1][1],p[1],o[1]);R(d,W);a(j[36],0);R(d,V);a(j[36],0);break;default:var
X=b[1],Y=a(g,b[2]);k(t[2],di,X,Y)}var
e=r;continue}return a(j[52],j[28])}}function
al(a){return c(t[4],dj,a)}var
Z=[0,0];function
S(a){Z[1]=0;return 0}function
T(a){return Z[1]}function
b(a){if(V[1])R(al,[0,a,0]);return F(a,Z)}function
aA(b,a){return a[2]-b[2]|0}var
am=a(l[48],aA);function
aB(b){var
c=b[2],d=c[2],e=b[1];return[0,e,[0,a(am,c[1]),d]]}function
B(i){function
e(j){var
b=j;for(;;){if(b){var
f=b[2],g=b[1],h=a(i,g[1]);if(c(n,h,d)){var
b=f;continue}var
k=e(f);return[0,[0,h,g[2]],k]}return 0}}return e}function
D(c,b){var
d=a(c,b[4]),e=b[3],f=a(B(c),e);return[0,b[1],b[2],f,d]}function
aD(b){return a(w,b)}function
I(a){return D(aD,a)}function
J(l,k){var
b=l,a=k;for(;;){if(b){if(a){var
g=a[2],f=a[1],i=b[2],e=b[1];if(e[2]===f[2]){var
j=c(h,e[1],f[1]);if(c(n,j,d)){var
b=i,a=g;continue}var
m=J(i,g);return[0,[0,j,e[2]],m]}return f[2]<e[2]?[0,e,J(i,a)]:[0,f,J(b,g)]}return b}return a}}function
_(e,b,d){var
f=c(h,b[4],d[4]),g=J(b[3],d[3]),i=b[2];return[0,a(e,0),i,g,f]}var
$=[ad,dk,aa(0)];function
ab(a){if(a){var
d=a[2],b=a[1];if(c(n,p(b[1]),e))return[0,b,d];var
f=ab(d);return[0,f[1],[0,b,f[2]]]}throw $}var
U=[ad,dl,aa(0)];function
K(c,a){if(a){var
d=a[2],b=a[1];if(b[2]===c)return[0,b,d];var
e=K(c,d);return[0,e[1],[0,b,e[2]]]}throw U}function
u(f){var
g=f[4],m=f[3],j=f[2],k=f[1];if(0===m)switch(j){case
0:if(c(n,g,d))return 0;b([12,k,g]);throw r;case
1:if(M(g,d))return 0;b([14,k,g]);throw r;default:if(aW(g,d))return 0;b([13,k]);throw r}function
v(a){return p(a[1])}var
h=aj(c(l[17],v,m));if(0===j)if(aW(N(g,h),d)){b([1,f,h]);throw r}if(2===j)if(aW(N(g,h),d)){b([2,f[1]]);return 0}if(aW(h,e)){var
s=G(g,h),w=c(o,g,c(i,s,h)),t=[0,k,j,a(B(function(a){return x(a,h)}),m),s];if(0===j)var
q=0;else
if(2===j)var
q=0;else
var
u=[0,f,t,h,w],q=1;if(!q)var
u=[3,f,h];b(u);return[0,t,0]}return[0,f,0]}function
E(o,g,f,d){var
h=g[1],p=d[3],r=g[2];try{var
k=K(r,p)[1],l=c(n,h,e)?a(w,k[1]):c(n,h,ah)?k[1]:a(j[3],dm),m=_(o,d,D(function(a){return c(i,a,l)},f));b([4,m[1],[0,e,d],[0,l,f]]);return m}catch(a){a=q(a);if(a===U)return d;throw a}}function
ac(b,a){var
d=c(i,y,a);return c(o,b,c(i,a,G(c(h,c(i,y,b),a),d)))}function
an(q,f,H,F){var
g=q[1],n=f[3],I=q[3],s=a(q[2],0);if(0===n){z(I,[0,f,0]);a(j[3],dn)}var
J=a(l[6],n),L=a(l[5],n)[2],M=[0,p(a(l[5],n)[1]),L];function
N(b,a){var
c=b[1],d=b[2];if(A(c,p(a[1]))){var
e=a[2];return[0,p(a[1]),e]}return[0,c,d]}var
t=k(l[20],N,M,J),O=t[2],d=c(h,t[1],e),P=ac(f[4],d),Q=f[3],R=a(B(function(a){return ac(a,d)}),Q),S=[0,[0,a(w,d),s],R],v=[0,a(g,0),0,S,P],T=c(i,y,d),U=a(w,G(c(h,c(i,y,f[4]),d),T)),V=f[3],W=a(B(function(b){var
e=c(i,y,d);return a(w,G(c(h,c(i,y,b),d),e))}),V);b([5,[0,v,[0,a(g,0),0,W,U],f,d,s]]);var
X=u(v),o=a(l[5],X),r=K(O,o[3])[1];function
Y(a){return u(E(g,r,o,a))}var
Z=c(m[17][76],Y,H);function
_(a){return u(E(g,r,o,a))}var
$=c(m[17][76],_,F),C=E(g,r,o,f),aa=D(function(a){return x(a,d)},C);b([3,C,d]);var
ab=u(aa);return[0,a(l[5],ab),Z,$]}function
ao(d,i){var
b=i;for(;;){var
f=b[3],e=b[2],a=b[1],g=d[1],j=d[3];if(V[1])z(j,[0,a,e]);try{var
h=ab(a[3])[1],k=function(b,c,d){return function(a){return u(E(c,d,b,a))}}(a,g,h),l=c(m[17][76],k,f),n=function(b,c,d){return function(a){return u(E(c,d,b,a))}}(a,g,h),o=[0,c(m[17][76],n,e),l];return o}catch(c){c=q(c);if(c===$){var
b=an(d,a,e,f);continue}throw c}}}function
ae(j,o){var
f=o;for(;;){var
g=f[2],h=f[1],s=j[3],k=function(a){if(a){var
d=a[2],b=a[1],g=b[3],h=function(a){return c(n,p(a[1]),e)};if(c(l[28],h,g))return[0,b,d];var
f=k(d);return[0,f[1],[0,b,f[2]]]}throw C};if(h){var
t=h[2],u=h[1];try{var
m=k(h),v=m[2],w=m[1],a=w,i=v}catch(b){b=q(b);if(b!==C)throw b;var
a=u,i=t}if(0===a[3]){if(c(n,a[4],d)){b([2,a[1]]);var
f=[0,i,g];continue}b([12,a[1],a[4]]);throw r}var
f=ao(j,[0,a,i,g]);continue}if(V[1])z(s,g);return g}}function
L(m,e){function
y(a){var
b=a[3];if(b)if(c(v,b[1][1],d))return[0,I(a),0];return[0,a,1]}var
f=c(s[1],0,7);function
i(z){var
m=y(z),n=m[2],a=m[1],g=a[3];if(0===g){if(c(v,a[4],d)){b([14,a[1],a[4]]);throw r}return b([2,a[1]])}try{var
o=c(s[6],f,g),i=o[2],j=o[1];if(1===n)if(j)var
l=j[1],D=c(v,l[4],a[4])?(b([7,l[1],a[1]]),l):(b([7,a[1],l[1]]),a),e=[0,[0,D],i];else
var
e=[0,[0,a],i];else
if(i){var
h=i[1];if(A(h[4],a[4]))b([8,h[1],a[1]]);else
b([8,a[1],h[1]]);var
F=A(h[4],a[4])?h:a,e=[0,j,[0,F]]}else
var
e=[0,j,[0,a]];var
p=e[1];if(p){var
t=e[2];if(t){var
u=t[1],w=p[1];if(c(v,w[4],u[4])){b([9,w,I(u)]);throw r}var
x=1}else
var
x=0}else
var
x=0;c(s[10],f,g);var
E=k(s[5],f,g,e);return E}catch(b){b=q(b);if(b===C){var
B=1===n?[0,[0,a],0]:[0,0,[0,a]];return k(s[5],f,g,B)}throw b}}c(l[15],i,e);var
h=[0,0],g=[0,0];function
j(o,f){var
d=f[1];if(d){var
i=f[2];if(i){var
j=i[1],e=d[1];if(c(n,e[4],j[4])){var
k=a(m,0);b([11,k,e,j[1]]);return F([0,k,0,e[3],e[4]],h)}}}var
l=f[2];if(d)F(d[1],g);return l?F(I(l[1]),g):0}c(s[12],j,f);return[0,h[1],g[1]]}var
W=[ad,dp,aa(0)];function
ap(g){var
b=c(s[1],0,7);function
h(e,d){try{var
a=c(s[6],b,e),g=p(d);a[1]=c(j[6],a[1],g);var
h=0;return h}catch(a){a=q(a);if(a===C){var
f=[0,p(d)];return k(s[5],b,e,f)}throw a}}function
i(a){var
b=a[3];function
d(a){return h(a[2],a[1])}return c(l[15],d,b)}c(l[15],i,g);var
e=[0,d],a=[0,-1],f=[0,0];function
m(h,g){var
b=g[1];f[1]++;var
i=c(v,b,e[1]),d=i||(-1===a[1]?1:0),j=d?(a[1]=h,e[1]=b,0):d;return j}c(s[12],m,b);if(f[1]<1)throw W;return a[1]}function
aq(i,b){function
c(c,b){var
e=c[3],f=c[2],g=c[1];try{var
h=K(i,b[3])[1],j=M(h[1],d)?[0,g,[0,[0,h[1],b],f],e]:[0,g,f,[0,[0,a(w,h[1]),b],e]];return j}catch(a){a=q(a);if(a===U)return[0,[0,b,g],f,e];throw a}}return k(l[20],c,dq,b)}function
ar(t,s,d,g){var
f=0;function
h(h,d){var
m=d[2],f=d[1];function
n(l,k){var
n=k[2],g=k[1],v=D(function(a){return c(i,a,f)},n),p=_(t,D(function(a){return c(i,a,g)},m),v);b([4,p[1],[0,g,m],[0,f,n]]);var
h=u(p);if(h){var
d=h[1];if(h[2])return a(j[3],dr);if(s){var
w=c(o,g,e),q=c(i,c(o,f,e),w);b([16,d[1],q]);var
x=c(o,d[4],q),r=[0,d[1],1,d[3],x]}else
var
r=d;return[0,r,l]}return l}return k(l[20],n,h,g)}return k(l[20],h,f,d)}function
af(d,f,b){var
g=d[3],h=d[1],a=aq(ap(b),b),i=a[1],k=ar(h,f,a[2],a[3]),e=c(j[26],i,k);if(V[1])z(g,e);return e}function
aE(d,o,e){var
h=d[1],p=d[3];function
r(a){return 2===a[2]?1:0}if(c(l[28],r,e))a(j[3],ds);S(0);function
s(a){return b([6,a])}c(l[15],s,e);var
t=c(m[17][76],u,e);function
v(a){return 0===a[2]?1:0}var
i=c(l[37],v,t),w=i[1],k=L(h,i[2]),x=k[2],y=[0,c(j[26],w,k[1]),x];function
g(b,c){var
a=ae(d,c);return b<50?f(b+1|0,a):aX(f,[0,a])}function
f(e,f){var
a=L(h,f),b=a[2],c=a[1];if(0===c)return b;var
d=[0,c,b];return e<50?g(e+1|0,d):aX(g,[0,d])}function
A(a){return aY(g(0,a))}function
B(a){return aY(f(0,a))}function
n(b){try{var
a=n(B(af(d,o,b)));return a}catch(a){a=q(a);if(a===W){if(V[1])z(p,b);return b}throw a}}return n(A(y))}function
X(l,k,i){var
f=l,d=k,e=i;for(;;){if(e){var
g=e[2],b=e[1];switch(b[0]){case
0:if(c(P[4][1],b[1][1],f)){var
d=[0,b,d],e=g;continue}var
e=g;continue;case
1:var
f=[0,b[1][1],f],d=[0,b,d],e=g;continue;case
2:var
e=g;continue;case
3:if(c(P[4][1],b[1][1],f)){var
d=[0,b,d],e=g;continue}var
e=g;continue;case
4:var
m=b[3][2],n=b[2][2];if(c(P[4][1],b[1],f)){var
f=[0,n[1],[0,m[1],f]],d=[0,b,d],e=g;continue}var
e=g;continue;case
5:var
h=b[1],o=h[3];if(c(P[4][1],h[1][1],f)){var
f=[0,o[1],f],d=[0,b,d],e=g;continue}var
e=g;continue;case
6:if(c(P[4][1],b[1][1],f)){var
d=[0,b,d],e=g;continue}var
e=g;continue;case
7:var
e=g;continue;case
8:var
e=g;continue;case
9:var
f=[0,b[1][1],[0,b[2][1],f]],d=[0,b,d],e=g;continue;case
10:var
f=[0,b[1][1],[0,b[2][1],f]],d=[0,b,d],e=g;continue;case
11:var
p=b[3],q=b[2];if(c(P[4][1],b[1],f)){var
f=[0,q[1],[0,p,f]],d=[0,b,d],e=g;continue}var
e=g;continue;case
12:var
f=[0,b[1],f],d=[0,b,d],e=g;continue;case
13:var
f=[0,b[1],f],d=[0,b,d],e=g;continue;case
14:var
f=[0,b[1],f],d=[0,b,d],e=g;continue;case
15:return a(j[3],dt);default:if(c(P[4][1],b[1],f)){var
d=[0,b,d],e=g;continue}var
e=g;continue}}return[0,f,d]}}function
as(a){var
g=a[2],h=a[1];function
i(a){return 2===a[2]?1:0}var
j=c(l[37],i,g)[1];function
e(a){var
b=a[3];if(b)if(c(v,b[1][1],d))return[0,I(a),0];return[0,a,1]}var
f=c(s[1],0,7);function
m(a){var
b=e(a),c=b[1];return k(s[5],f,[0,c[3],c[4]],[0,b[2],a])}c(l[15],m,j);function
n(a){if(0===a[2]){var
d=e(a),g=d[1],i=d[2],j=g[4],k=g[3];try{var
h=c(s[6],f,[0,k,j]);b([10,a,h[2],i===h[1]?1:0]);throw r}catch(a){a=q(a);if(a===C)return 0;throw a}}throw[0,aC,du]}return c(l[15],n,h)}var
ag=[ad,dv,aa(0)];return[0,n,v,at,A,M,h,o,i,x,N,d,e,y,ah,p,g,w,au,av,aw,ax,ay,F,ai,aj,G,r,ak,H,Y,O,Q,z,az,g,R,al,b,T,S,am,aB,B,D,I,J,_,$,ab,U,K,u,E,ac,an,ao,ae,L,W,ap,aq,ar,af,aE,X,as,ag,function(d,n){var
f=d[1],E=d[3];S(0);function
F(a){return b([6,a])}c(l[15],F,n);function
i(c,a){as(a);var
b=ae(d,a);return c<50?h(c+1|0,b):aX(h,[0,b])}function
h(k,m){function
n(a){return 2===a[2]?1:0}var
a=c(l[37],n,m),b=a[1],d=L(f,a[2]),e=d[2],g=d[1];if(0===g)return c(j[26],b,e);var
h=[0,g,c(j[26],b,e)];return k<50?i(k+1|0,h):aX(i,[0,h])}function
G(a){return aY(i(0,a))}function
H(a){return aY(h(0,a))}function
p(b){try{var
a=p(H(af(d,0,b)));return a}catch(a){a=q(a);if(a===W){if(V[1])z(E,b);return b}throw a}}function
I(m){var
d=m;for(;;){var
g=d[1];if(g){var
k=d[2],b=g[1],n=d[3],p=g[2],h=a(f,0),i=a(f,0),q=c(o,b[4],e),r=[0,h,1,b[3],q],s=c(o,a(w,b[4]),e),t=b[3],u=[0,i,1,a(B(w),t),s],v=function(b,c,d){return function(a){return[0,[0,[0,b[1],c,0],a[1]],[0,d,a[2]]]}}(b,i,u),x=c(l[17],v,k),y=function(b,c,d){return function(a){return[0,[0,[0,b[1],c,1],a[1]],[0,d,a[2]]]}}(b,h,r),z=c(l[17],y,k),A=c(j[26],z,x),d=[0,p,A,[0,[0,b[1],[0,b,h,i]],n]];continue}return[0,d[2],d[3]]}}try{var
J=c(m[17][76],u,n),K=function(a){return 0===a[2]?1:0},t=c(l[37],K,J),M=t[2],N=t[1],O=function(a){return 2===a[2]?1:0},v=c(l[37],O,M),Q=v[1],x=L(f,v[2]),R=x[1],U=c(j[26],x[2],Q),Y=G([0,c(j[26],N,R),U]),Z=function(a){return 2===a[2]?1:0},y=c(l[37],Z,Y),_=y[2],$=y[1],aa=T(0),A=I([0,$,[0,[0,0,_],0],0]),ab=A[2],ac=A[1],ad=function(a){var
b=a[1],f=a[2];S(0);try{p(f);throw ak}catch(a){a=q(a);if(a===r){var
d=X(0,0,T(0)),e=d[1],g=d[2],h=function(a){return c(P[4][1],a[2],e)},i=c(l[37],h,b)[1],j=function(a){return a[1]};return[0,c(l[17],j,i),e,b,g]}throw a}},ah=c(l[17],ad,ac),ai=function(e){var
b=c(s[1],0,7),a=[0,-1],d=[0,0];function
f(d){try{c(s[6],b,d)[1]++;var
a=0;return a}catch(a){a=q(a);if(a===C)return k(s[5],b,d,[0,1]);throw a}}function
g(a){var
b=a[1];if(b)return c(l[15],f,b);throw[0,ag,a[4],a[2]]}c(l[15],g,e);function
h(e,b){var
c=d[1]<b[1]?1:0,f=c?(a[1]=e,d[1]=b[1],0):c;return f}c(s[12],h,b);return a[1]},g=function(e){try{var
d=ai(e),p=function(g){var
b=g[3];for(;;){if(b){var
c=b[1],e=b[2],f=c[3];if(d===c[1])return f;var
b=e;continue}return a(j[3],dw)}},f=c(l[37],p,e),r=f[2],s=f[1],h=function(a){var
b=a[4],c=a[3],e=a[2],f=a[1];function
g(b,a){return b===a?1:0}return[0,k(m[17][95],g,d,f),e,c,b]},t=c(l[17],h,s),u=c(l[17],h,r),i=g(t),v=i[2],w=i[1],n=g(u),x=n[2],y=n[1],b=c(P[4][2],d,ab),o=b[1],z=b[3],A=b[2],B=function(b,a){return b===a?1:0},C=k(m[17][129],B,v,x),D=[0,[0,[15,o,[0,A,w],[0,z,y]],0],[0,o[1],C]];return D}catch(a){a=q(a);if(a[1]===ag)return[0,a[2],a[3]];throw a}},D=g(ah),aj=X(D[2],D[1],aa)[2];return aj}catch(a){a=q(a);if(a===r)return X(0,0,T(0))[2];throw a}}]}aU(398,[0,V,bF],"Omega_plugin__Omega");var
i=bF([0,w[17],w[16],w[12],w[13],w[14],w[15],w[22],w[5],w[6],w[2]]);function
d(b){var
c=y.caml_obj_tag(b);return 250===c?b[1]:U===c?a(dx[2],b):b}function
ae(b){var
c=a(e[11],b);return a(g[ab],c)}function
aD(b){var
c=a(e[11],b);return a(g[87],c)}var
a3=[0,0],aE=[0,0],aF=[0,0],a4=[0,1],a5=[0,1];function
ao(b,a){b[1]=a;return 0}function
dy(a){return ao(a3,a)}var
dB=[0,0,dA,dz,function(a){return a3[1]},dy];c(ap[4],0,dB);function
dC(a){return ao(aE,a)}var
dF=[0,0,dE,dD,function(a){return aE[1]},dC];c(ap[4],0,dF);function
dG(a){return ao(aF,a)}var
dJ=[0,0,dI,dH,function(a){return aF[1]},dG];c(ap[4],0,dJ);function
dK(a){return ao(a5,a)}var
dN=[0,1,dM,dL,function(a){return a5[1]},dK];c(ap[4],0,dN);function
dO(a){return ao(a4,a)}var
dR=[0,0,dQ,dP,function(a){return a4[1]},dO];c(ap[4],0,dR);var
a6=[0,0];function
aq(a){var
b=[0,a];a6[1]=[0,[0,b,a],a6[1]];return b}var
bG=aq(0);function
Q(e){var
b=a(j[22],bG[1]),d=c(j[17],dS,b);bG[1]++;return a(x[1][6],d)}var
bH=aq(0);function
dT(e){var
b=a(j[22],bH[1]),d=c(j[17],dU,b);bH[1]++;return a(x[1][6],d)}var
bI=aq(0);function
aG(a){bI[1]++;return bI[1]}var
bJ=aq(1000);function
bK(a){bJ[1]++;return bJ[1]}var
bL=aq(0);function
dV(a){bL[1]++;return c(ar[1],dW,[0,bL[1]])}function
as(a){return c(t[4],dX,a)}var
a7=[0,0],aH=c(s[1],0,7),a8=c(s[1],0,7);function
bM(b){try{var
a=c(s[6],a8,b);return a}catch(a){a=q(a);if(a===C){var
d=dV(0);k(s[5],aH,d,b);k(s[5],a8,b,d);return d}throw a}}function
a9(b){try{var
a=c(s[6],aH,b);return a}catch(a){a=q(a);if(a===C){var
d=a7[1];k(s[5],aH,b,d);k(s[5],a8,d,b);a7[1]++;return d}throw a}}function
G(b){return a(h[65][22],b)}function
dY(a){return aV(g[109],0,dZ,1,[0,[0,a,0]])}function
r(b){return a(g[148],b)}function
F(b){var
c=[0,[0,0,d(b)],0];return a(g[69],c)}function
a_(b,a){return k(z[35][1],a$[9],b,a)}var
aI=[0,0];function
d0(c){return function(d){var
a=d;for(;;){if(a){var
b=a[1],e=a[2],f=b[1];if(c===b[2])return f;var
a=e;continue}throw C}}}function
D(b){try{var
c=aI[1],d=a(d0(b),c);return d}catch(b){b=q(b);if(b===C)return a(j[3],d1);throw b}}function
W(b,a){aI[1]=[0,[0,b,a],aI[1]];return 0}var
at=[0,0];function
d2(a){return at[1]}function
bN(a){at[1]=0;return 0}function
d4(d,c,b,a){at[1]=[0,[0,d,[0,c,b,a]],at[1]];return 0}function
f(b){return[U,function(f){var
c=a(bO[2],b),d=a(d5[22],c);return a(e[9],d)}]}var
bP=f(d6),bQ=f(d7),bR=f(d8),ba=f(d9),bb=f(d_),bc=f(d$),af=f(ea),ec=f(eb),bS=f(ed),ag=f(ee),aJ=f(ef),aK=f(eg),bd=f(eh),be=f(ei),bT=f(ej),bU=f(ek),em=f(el),eo=f(en),eq=f(ep),es=f(er),eu=f(et),ew=f(ev),ey=f(ex),eA=f(ez),eC=f(eB),eE=f(eD),eG=f(eF),au=f(eH),eJ=f(eI),eL=f(eK),bV=f(eM),bW=f(eN),eP=f(eO),eR=f(eQ),eT=f(eS),eV=f(eU),eX=f(eW),eZ=f(eY),e1=f(e0),e3=f(e2),e5=f(e4),e7=f(e6),e9=f(e8),e$=f(e_),bf=f(fa),aL=f(fb),fd=f(fc),ff=f(fe),fh=f(fg),fj=f(fi),fl=f(fk),fn=f(fm),fp=f(fo),fr=f(fq),ft=f(fs),fv=f(fu),fx=f(fw),fz=f(fy),fB=f(fA),bg=f(fC),fE=f(fD),fG=f(fF),fI=f(fH),fK=f(fJ),bh=f(fL),fN=f(fM),fP=f(fO),fR=f(fQ),fT=f(fS),fV=f(fU),fX=f(fW),fZ=f(fY),f1=f(f0),f3=f(f2),f5=f(f4),f7=f(f6),f9=f(f8),f$=f(f_),gb=f(ga),gd=f(gc),gf=f(ge),gh=f(gg),gj=f(gi),gl=f(gk),gn=f(gm),bX=f(go),bY=f(gp),bZ=f(gq),gs=f(gr),gu=f(gt),bi=f(gv),bj=f(gw),b0=f(gx),b1=f(gy),b2=f(gz),gB=f(gA),gD=f(gC),b3=f(gE),gG=f(gF),b4=f(gH),gJ=f(gI),gL=f(gK),gN=f(gM),gP=f(gO),gR=f(gQ),gT=f(gS),gV=f(gU),gX=f(gW),gZ=f(gY),g1=f(g0),g3=f(g2),g5=f(g4),g7=f(g6),g9=f(g8),g$=f(g_),hb=f(ha),hd=f(hc),hf=f(he),hh=f(hg),hj=f(hi),hl=f(hk),hn=f(hm),hp=f(ho),hr=f(hq),ht=f(hs),hv=f(hu),hx=f(hw),hz=f(hy),hB=f(hA),hD=f(hC),bk=f(hE),b5=f(hF),b6=f(hG),bl=f(hH),hJ=f(hI),b7=f(hK),hM=f(hL);function
ah(i,h){var
b=a(hN[2],0),l=a(hO[17],b),m=d(h),f=c(e[3],l,m);if(10===f[0]){var
g=f[1][1];if(c(a$[2],b,[1,g]))return[1,g]}var
n=c(j[17],i,hP),o=a(N[3],n);return k(J[3],0,hQ,o)}var
hS=[U,function(a){return ah(hR,be)}],hU=[U,function(a){return ah(hT,bT)}],hW=[U,function(a){return ah(hV,bd)}],b8=[U,function(a){return ah(hX,bZ)}],X=[U,function(a){return ah(hY,bi)}],bm=[U,function(a){return ah(hZ,bk)}];function
O(c,b){var
f=[0,d(ag),[0,c,b]];return a(e[23],f)}function
bn(c,b){var
f=[0,d(aJ),[0,c,b]];return a(e[23],f)}function
h0(c,b){var
f=[0,d(bd),[0,c,b]];return a(e[23],f)}function
b9(f,c,b){var
g=[0,d(bl),[0,f,c,b]];return a(e[23],g)}function
aM(b,a){return b9(d(af),b,a)}function
Y(c,b){var
f=[0,d(bi),[0,c,b]];return a(e[23],f)}function
Z(b){var
c=[0,d(aK),[0,b]];return a(e[23],c)}function
aN(c,b){var
f=[0,d(b5),[0,c,b]];return a(e[23],f)}function
bo(c,b){var
f=[0,d(b6),[0,c,b]];return a(e[23],f)}function
S(b){var
c=[0,d(bk),[0,b]];return a(e[23],c)}function
_(b){var
c=[0,d(bU),[0,b]];return a(e[23],c)}function
A(b){function
f(b){if(c(i[1],b,i[12]))return d(bP);var
g=[0,f(c(i[9],b,i[13]))],h=i[11],j=c(i[10],b,i[13]),k=c(i[1],j,h)?d(bQ):d(bR);return a(e[23],[0,k,g])}if(c(i[1],b,i[11]))return d(ba);var
g=[0,f(a(i[15],b))],h=c(i[4],b,i[11])?d(bb):d(bc);return a(e[23],[0,h,g])}function
ai(i,n){function
g(b,a){return k(e[bA],i,b,a)}var
j=c(e[91],i,n),b=j[2],f=j[1],h=c(e[3],i,f);if(b){var
l=b[2];if(l){var
m=l[2];if(m){if(!m[2])if(g(d(bl),f))return[1,16,b]}else{if(g(f,d(bX)))return[1,17,b];if(g(f,d(bY)))return[1,18,b];if(g(f,d(bZ)))return[1,19,b];if(g(f,d(gs)))return[1,20,b];if(g(f,d(gu)))return[1,21,b];if(g(f,d(bi)))return[1,22,b];if(g(f,d(b5)))return[1,25,b];if(g(f,d(b6)))return[1,26,b];if(g(f,d(hD)))return[1,30,b];if(g(f,d(b2)))return[1,31,b];if(g(f,d(gB)))return[1,32,b];if(g(f,d(gD)))return[1,33,b];if(g(f,d(b3)))return[1,34,b]}}else
if(g(f,d(bk)))return[1,29,b]}else{if(g(f,d(b7)))return[1,27,b];if(g(f,d(hM)))return[1,28,b]}switch(h[0]){case
1:if(!b)return[0,h[1]];break;case
6:if(h[1][1]){if(!b){var
o=a(N[3],h1);return k(J[6],0,0,o)}}else
if(!b)return[2,h[2],h[3]];break;case
10:var
p=a(bp[41],[1,h[1][1]]);return[1,[0,a(bq[20],p)],b];case
11:var
q=a(bp[41],[2,h[1][1]]);return[1,[0,a(bq[20],q)],b];case
12:var
r=a(bp[41],[3,h[1][1]]);return[1,[0,a(bq[20],r)],b]}return 0}var
h2=a$[9];function
av(g,a,j){var
h=k(br[81],0,g,a),l=k(h2,g,a,j),i=c(e[91],a,l),b=i[2],f=i[1];c(e[3],a,f);if(!b){if(c(h,f,d(af)))return[1,23,b];if(c(h,f,d(bj)))return[1,24,b]}return 0}function
aO(g,l){function
f(b,a){return k(e[bA],g,b,a)}var
h=c(e[91],g,l),a=h[2],b=h[1],i=c(e[3],g,b);if(a){var
j=a[2];if(j){if(!j[2]){if(f(b,d(ag)))return[1,0,a];if(f(b,d(aJ)))return[1,1,a];if(f(b,d(bd)))return[1,2,a];if(f(b,d(gG)))return[1,6,a];if(f(b,d(gJ)))return[1,7,a];if(f(b,d(b4)))return[1,8,a]}}else{if(f(b,d(be)))return[1,3,a];if(f(b,d(bT)))return[1,5,a];if(f(b,d(aK)))return[1,4,a];if(f(b,d(gL)))return[1,9,a];if(f(b,d(b1)))return[1,10,a];if(f(b,d(bb)))return[1,13,a];if(f(b,d(bc)))return[1,12,a];if(f(b,d(bU)))return[1,15,a]}}else{if(f(b,d(b0)))return[1,11,a];if(f(b,d(ba)))return[1,14,a];if(1===i[0])return[0,i[1]]}return 0}function
h3(g,o){function
b(b,a){return k(e[bA],g,b,a)}function
f(n){var
l=c(e[91],g,n),h=l[2],k=l[1];if(h){if(!h[2]){var
m=h[1];if(b(k,d(bR))){var
o=f(m),p=c(i[8],i[13],o);return c(i[6],i[12],p)}if(b(k,d(bQ))){var
q=f(m);return c(i[8],i[13],q)}}}else
if(b(k,d(bP)))return i[12];return a(j[3],h4)}var
m=c(e[91],g,o),h=m[2],l=m[1];if(h){if(!h[2]){var
n=h[1];if(b(l,d(bb)))return f(n);if(b(l,d(bc))){var
p=f(n);return a(i[17],p)}}}else
if(b(l,d(ba)))return i[11];return a(j[3],h5)}function
bs(y,x,f,b){function
d(g,f,p){var
b=c(e[3],y,p);if(5===b[0]){var
S=b[3],T=b[2],U=[0,d(g,f,b[1]),T,S];return a(e[19],U)}if(f){var
q=f[1];if(q){var
r=q[1],z=f[2];switch(b[0]){case
9:var
D=b[1],k=a(m[19][8],b[2]),s=r-1|0,t=r-1|0,E=d(g,z,al(k,s)[s+1]);al(k,t)[t+1]=E;return a(e[23],[0,D,k]);case
14:var
i=0;break;default:var
i=1}}else{var
o=f[2];switch(b[0]){case
6:var
I=b[3],J=b[1],K=[0,J,d(g,o,b[2]),I];return a(e[20],K);case
7:var
L=b[3],M=b[1],N=[0,M,d(g,o,b[2]),L];return a(e[21],N);case
8:var
O=b[4],P=b[2],Q=b[1],R=[0,Q,P,d(g,o,b[3]),O];return a(e[22],R);case
14:var
i=0;break;default:var
i=1}}if(i){var
A=a(m[17][1],f),B=a(j[22],A),C=c(j[17],h6,B);return a(j[3],C)}var
u=b[1],l=u[2],n=l[3],v=u[1],h=v[2],F=l[2],G=l[1],w=a(m[19][8],n),H=d(g+(n.length-1)|0,f,al(n,h)[h+1]);al(w,h)[h+1]=H;return a(e[33],[0,v,[0,G,F,w]])}return c(x,g,p)}return d(1,f,b)}function
b_(h,g,f,d){var
b=[0,a(e[10],0)],i=bs(h,function(d,c){b[1]=c;return a(e[10],d)},f,d),j=b[1],k=[0,a(x[1][6],h8)],l=[0,c(u[4],k,0),g,i];return[0,a(e[21],l),j]}function
K(h){function
b(b){var
c=a(z[35][6],b),d=a(m[17][9],h);function
e(c,a){return a_(b,a)}var
f=bs(a(z[35][4],b),e,d,c);return k(g[3],h9,f,2)}return a(n[68][8],b)}function
$(b){switch(b[0]){case
0:var
c=b[2],d=b[1];a(j[31],h_);$(d);a(j[31],h$);$(c);return a(j[31],ia);case
1:var
e=b[2],f=b[1];a(j[31],ib);$(f);a(j[31],ic);$(e);return a(j[31],id);case
2:var
g=a(x[1][8],b[1]);return a(j[31],g);case
3:var
h=a(i[16],b[1]);return a(j[31],h);default:return a(j[31],ie)}}function
H(c){var
b=c;for(;;)switch(b[0]){case
0:return a(j[3],ig);case
1:var
b=b[1];continue;case
2:return a9(b[1]);case
3:return-1;default:return-1}}function
v(b){switch(b[0]){case
0:var
c=b[1],f=v(b[2]),g=[0,v(c),f],h=[0,d(ag),g];return a(e[23],h);case
1:var
i=b[1],j=v(b[2]),k=[0,v(i),j],l=[0,d(aJ),k];return a(e[23],l);case
2:return a(e[11],b[1]);case
3:return A(b[1]);default:return b[1]}}function
E(b){function
c(a){if(a){var
d=a[1],e=d[2],f=d[1],g=c(a[2]);return[0,[1,[2,bM(e)],[3,f]],g]}return[3,b[4]]}return c(b[3])}function
b$(b,a,c){var
d=k(br[19],b,a,c);return lg(ii[4],0,0,0,0,0,0,0,0,b,a,d)}function
ca(f,l,b,j){function
g(g){var
n=a(z[35][6],g),o=a(z[35][5],g),p=a(m[17][9],l),h=b_(a(z[35][4],g),f,p,n),i=h[1],q=h[2];function
r(h){var
l=a(e[10],1),m=[0,f,b,a(e[10],2),l,q,j],n=[0,d(g$),m],p=a(e[23],n),r=[0,a(e[10],1),[0,b,0]],s=a(e[40],r),t=[0,a(x[1][6],ij)],v=[0,c(u[4],t,0),s,p],w=a(e[21],v),y=k(e[35],f,0,e[16]),z=[0,a(x[1][6],ik)],A=[0,c(u[4],z,0),y,w],B=[0,a(e[21],A),[0,i,0]],C=a(e[40],B),g=b$(o,h,a(e[23],[0,i,[0,b]])),D=g[1];return[0,D,a(e[40],[0,C,[0,g[2],0]])]}return c(cb[1],0,r)}return a(n[68][8],g)}function
bt(c,b,a){return ca(d(af),c,b,a)}function
aw(d,c,b){return bt(d,c,a(e[40],[0,b[1],b[2]]))}function
il(f,c,b){var
g=a(e[40],[0,b[1],b[2]]);return ca(d(bj),f,c,g)}function
cc(d,b){function
f(f){var
i=a(z[35][5],d),j=c(z[35][8],d,b),g=c(e[3],f,j);if(6===g[0]){var
h=b$(i,f,g[2]),k=h[1];return[0,k,a(e[40],[0,b,[0,h[2],0]])]}throw[0,aC,im]}return c(cb[1],0,f)}function
p(i,h,f){function
b(g){var
k=a(z[35][6],g),l=a(m[17][9],i),n=d(af),b=b_(a(z[35][4],g),n,l,k),u=b[2],o=b[1];function
p(v){var
b=v,f=u,w=a(z[35][4],g);for(;;){var
d=c(e[3],w,f);if(5===d[0]){var
f=d[1];continue}if(b){var
k=b[1];if(k){var
p=b[2],q=k[1];switch(d[0]){case
9:var
l=q-1|0,b=p,f=al(d[2],l)[l+1];continue;case
14:var
h=0;break;default:var
h=1}}else{var
i=b[2];switch(d[0]){case
6:var
b=i,f=d[2];continue;case
7:var
b=i,f=d[2];continue;case
8:var
b=i,f=d[3];continue;case
14:var
h=0;break;default:var
h=1}}if(h){var
r=a(m[17][1],b),s=a(j[22],r),t=c(j[17],h7,s);return a(j[3],t)}var
n=d[1],o=n[1][2],f=al(n[2][3],o)[o+1];continue}return f}}var
q=c(m[17][68],p,h),r=[0,f,c(m[18],q,[0,o,0])];return cc(g,a(e[40],r))}return a(n[68][8],b)}function
ax(f,h){function
b(b){var
d=a(z[35][4],b);function
j(l,k){if(0===l)return a_(b,k);var
f=c(e[3],d,k);if(9===f[0]){var
g=f[2];if(2===g.length-1){var
m=f[1],n=g[2],h=c(e[3],d,g[1]);if(9===h[0]){var
i=h[2];if(2===i.length-1){var
o=h[1],p=i[1],q=a_(b,i[2]),r=j(l-1|0,n),s=[0,m,[0,a(e[23],[0,o,[0,p,q]]),r]];return a(e[23],s)}}throw[0,aC,ip]}}throw[0,aC,io]}var
i=a(m[17][1],f),l=a(m[17][1],h)-i|0,n=a(z[35][6],b),o=a(m[17][9],f),p=bs(d,function(b,a){return j(l,a)},o,n);return k(g[3],iq,p,2)}return a(n[68][8],b)}function
ay(e,h){var
a=h[2],b=h[1];switch(b[0]){case
0:var
j=b[2],f=b[1];if(0===a[0]){var
k=a[1],r=a[2],s=H(k),t=H(f);if(c(i[19],t,s)){var
l=ay([0,ir,e],[0,j,a]),u=l[1],v=[0,f,l[2]];return[0,[0,p(e,is,d(au)),u],v]}var
m=ay([0,it,e],[0,b,r]),x=m[1],y=[0,k,m[2]];return[0,[0,p(e,iu,d(bV)),x],y]}var
z=H(a),A=H(f);if(c(i[19],A,z)){var
n=ay([0,iv,e],[0,j,a]),B=n[1],C=[0,f,n[2]];return[0,[0,p(e,iw,d(au)),B],C]}return[0,[0,p(e,ix,d(bW)),0],[0,a,b]];case
3:var
M=b[1];switch(a[0]){case
0:var
g=0;break;case
3:var
N=[3,c(w[12],M,a[1])];return[0,[0,K(e),0],N];default:var
g=1}break;default:var
g=0}if(!g)if(0===a[0]){var
o=a[1],D=a[2],E=H(b),F=H(o);if(c(i[19],F,E)){var
q=ay([0,iy,e],[0,b,D]),G=q[1],I=[0,o,q[2]];return[0,[0,p(e,iz,d(bV)),G],I]}return[0,0,[0,b,a]]}var
J=H(a),L=H(b);return c(i[18],L,J)?[0,[0,p(e,iA,d(bW)),0],[0,a,b]]:[0,0,[0,b,a]]}function
iB(k,t,e,s,a){function
b(a,h){var
e=h[1];if(e){var
f=h[2],g=e[2],l=e[1],m=l[2],u=l[1];if(f){var
j=f[2],n=f[1],o=n[2],v=n[1];if(m===o){var
q=p(a,iC,d(e$)),x=i[11],y=c(w[14],s,v),z=c(w[14],t,u),A=c(w[12],z,y);if(c(i[1],A,x)){var
B=p(a,iD,d(bg)),C=[0,B,b(a,[0,g,j])];return[0,q,[0,K([0,iF,[0,iE,a]]),C]]}return[0,q,b([0,iG,a],[0,g,j])]}if(c(i[19],m,o)){var
D=b([0,iH,a],[0,g,f]);return[0,p(a,iI,d(bf)),D]}var
E=b([0,iJ,a],[0,e,j]);return[0,p(a,iK,d(aL)),E]}var
F=b([0,iL,a],[0,g,0]);return[0,p(a,iM,d(bf)),F]}var
r=h[2];if(r){var
G=b([0,iN,a],[0,0,r[2]]);return[0,p(a,iO,d(aL)),G]}return[0,ax(k,a),0]}return b(k,[0,e,a])}function
bu(k,e,s,a){function
b(a,h){var
e=h[1];if(e){var
f=h[2],g=e[2],l=e[1],m=l[2],t=l[1];if(f){var
j=f[2],n=f[1],o=n[2],u=n[1];if(m===o){var
q=p(a,iP,d(fh)),v=i[11],x=c(w[14],s,u),y=c(w[12],t,x);if(c(i[1],y,v)){var
z=p(a,iQ,d(bg)),A=[0,z,b(a,[0,g,j])];return[0,q,[0,K([0,iS,[0,iR,a]]),A]]}return[0,q,b([0,iT,a],[0,g,j])]}if(c(i[19],m,o)){var
B=b([0,iU,a],[0,g,f]);return[0,p(a,iV,d(au)),B]}var
C=b([0,iW,a],[0,e,j]);return[0,p(a,iX,d(aL)),C]}var
D=b([0,iY,a],[0,g,0]);return[0,p(a,iZ,d(au)),D]}var
r=h[2];if(r){var
E=b([0,i0,a],[0,0,r[2]]);return[0,p(a,i1,d(aL)),E]}return[0,ax(k,a),0]}return b(k,[0,e,a])}function
cd(b,a){if(a){var
e=a[2],f=c(i[4],a[1][1],i[11])?d(fd):d(ff),g=p(b,i2,f);return[0,g,cd(b,e)]}return[0,K(b),0]}function
aP(g,f,b){switch(b[0]){case
0:var
n=b[2],h=aP([0,i3,g],f,b[1]),o=h[2],q=h[1],j=aP([0,i4,g],f,n),r=[0,o,j[2]],s=c(m[18],q,j[1]);return[0,[0,p(g,i5,d(fG)),s],r];case
1:var
l=b[2],t=b[1];if(3===l[0]){var
v=[1,t,[3,c(i[8],f,l[1])]],w=[0,K([0,i7,g]),0];return[0,[0,p(g,i8,d(eL)),w],v]}var
u=a(N[3],i6);return k(J[6],0,0,u);case
2:return[0,0,[1,b,[3,f]]];case
3:var
x=[3,c(i[8],f,b[1])];return[0,[0,K(g),0],x];default:var
y=b[1],z=[0,A(f),y],B=[0,d(aJ),z];return[0,0,[4,a(e[23],B)]]}}function
bv(b){function
c(a,e){if(e){var
f=c([0,i9,a],e[2]);return[0,p(a,i_,d(fj)),f]}return[0,ax(b,a),0]}return function(a){return c(b,a)}}function
i$(b){function
c(a,e){if(e){var
f=c([0,ja,a],e[2]);return[0,p(a,jb,d(au)),f]}return[0,ax(b,a),0]}return function(a){return c(b,a)}}function
bw(b){function
c(a,e){if(e){var
f=c([0,jc,a],e[2]);return[0,p(a,jd,d(bf)),f]}return[0,ax(b,a),0]}return function(a){return c(b,a)}}function
bx(f,b){switch(b[0]){case
0:var
l=b[2],g=bx([0,je,f],b[1]),n=g[2],o=g[1],h=bx([0,jf,f],l),q=[0,n,h[2]],r=c(m[18],o,h[1]);return[0,[0,p(f,jg,d(fI)),r],q];case
1:var
j=b[2],s=b[1];if(3===j[0]){var
u=[1,s,[3,a(i[17],j[1])]],v=[0,K([0,ji,f]),0];return[0,[0,p(f,jj,d(fK)),v],u]}var
t=a(N[3],jh);return k(J[6],0,0,t);case
2:var
w=[1,b,[3,i[14]]];return[0,[0,p(f,jk,d(bh)),0],w];case
3:var
x=[3,a(i[17],b[1])];return[0,[0,K(f),0],x];default:var
y=[0,b[1]],z=[0,d(aK),y];return[0,0,[4,a(e[23],z)]]}}function
R(h,g,o){function
r(p,f){try{try{var
l=at[1],n=a(e[104],h),o=k(m[17][115],n,f,l),d=o}catch(b){b=q(b);if(b!==C)throw b;var
d=a(j[3],d3)}var
b=d[1],s=a(e[11],d[2]),t=[0,[0,bt(g,a(e[11],b),s),0],[2,b]];return t}catch(b){b=q(b);if(a(J[18],b)){var
c=dT(0),i=Q(0);d4(f,c,i,p);var
r=a(e[11],i);return[0,[0,bt(g,a(e[11],c),r),0],[2,c]]}throw b}}try{var
l=aO(h,o);if(typeof
l==="number")var
f=0;else
switch(l[0]){case
0:var
s=[0,0,[2,l[1]]],f=1;break;case
1:var
t=l[1];if(typeof
t==="number")if(16<=t)var
f=0;else{switch(t){case
0:var
u=l[2];if(u){var
v=u[2];if(v)if(v[2])var
f=0,b=0;else
var
aa=v[1],L=R(h,[0,jl,g],u[1]),ab=L[2],ac=L[1],M=R(h,[0,jm,g],aa),ad=M[1],N=ay(g,[0,ab,M[2]]),ae=N[2],af=c(m[18],ad,N[1]),n=[0,c(m[18],ac,af),ae],b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
1:var
w=l[2];if(w){var
x=w[2];if(x)if(x[2])var
f=0,b=0;else{var
ah=x[1],O=R(h,[0,jn,g],w[1]),y=O[2],P=O[1],S=R(h,[0,jo,g],ah),z=S[2],U=S[1];if(3===z[0])var
W=aP(g,z[1],y),am=W[2],an=c(m[18],U,W[1]),B=[0,c(m[18],P,an),am];else
if(3===y[0])var
ai=y[1],aj=p(g,jp,d(eP)),V=aP(g,ai,z),ak=V[2],al=c(m[18],U,[0,aj,V[1]]),B=[0,c(m[18],P,al),ak];else
var
B=r(0,o);var
n=B,b=1}else
var
f=0,b=0}else
var
f=0,b=0;break;case
2:var
D=l[2];if(D){var
E=D[2];if(E)if(E[2])var
f=0,b=0;else
var
ao=D[1],ap=[0,E[1]],aq=[0,d(aK),ap],ar=[0,ao,a(e[23],aq)],as=[0,d(ag),ar],X=R(h,g,a(e[23],as)),au=X[2],av=X[1],n=[0,[0,F(hW),av],au],b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
3:var
G=l[2];if(G)if(G[2])var
f=0,b=0;else
var
aw=G[1],ax=[0,aw,A(i[12])],az=[0,d(ag),ax],Y=R(h,g,a(e[23],az)),aA=Y[2],aB=Y[1],n=[0,[0,F(hS),aB],aA],b=1;else
var
f=0,b=0;break;case
4:var
H=l[2];if(H)if(H[2])var
f=0,b=0;else
var
Z=R(h,[0,jq,g],H[1]),aC=Z[1],_=bx(g,Z[2]),aD=_[2],n=[0,c(m[18],aC,_[1]),aD],b=1;else
var
f=0,b=0;break;case
5:var
I=l[2];if(I)if(I[2])var
f=0,b=0;else
var
aE=I[1],aF=[0,aE,A(i[14])],aG=[0,d(ag),aF],$=R(h,g,a(e[23],aG)),aH=$[2],aI=$[1],n=[0,[0,F(hU),aI],aH],b=1;else
var
f=0,b=0;break;case
15:var
K=l[2];if(K)if(K[2])var
f=0,b=0;else
var
n=r(1,K[1]),b=1;else
var
f=0,b=0;break;case
12:case
13:case
14:try{var
aJ=[0,0,[3,h3(h,o)]],n=aJ,b=1}catch(c){c=q(c);if(!a(J[18],c))throw c;var
n=r(0,o),b=1}break;default:var
f=0,b=0}if(b)var
s=n,f=1}else
var
f=0;break;default:var
f=0}if(!f)var
s=r(0,o);return s}catch(b){b=q(b);if(a(T[4],b))return r(0,o);throw b}}function
ce(e,c,b){switch(c[0]){case
1:var
f=c[1],l=c[2];switch(b[0]){case
1:if(2===f[0]){var
m=[1,[2,f[1]],[0,c[2],b[2]]];return[0,p(e,js,d(fB)),m]}break;case
2:var
n=[1,[2,b[1]],[0,l,[3,i[12]]]];return[0,p(e,jt,d(fz)),n]}break;case
2:var
g=c[1];switch(b[0]){case
1:var
o=[1,[2,g],[0,b[2],[3,i[12]]]];return[0,p(e,ju,d(fx)),o];case
2:var
q=[1,[2,g],[3,i[13]]];return[0,p(e,jv,d(fv)),q]}break}$(c);a(j[36],0);$(b);a(j[36],0);a(j[52],j[1][27]);var
h=a(N[3],jr);return k(J[6],0,0,h)}function
aQ(f,b){switch(b[0]){case
1:var
g=b[1];if(2===g[0]){var
h=b[2],l=g[1];if(3===h[0])return[0,0,b];var
e=function(b){switch(b[0]){case
0:var
d=b[1],f=e(b[2]),g=e(d);return c(w[12],g,f);case
3:return b[1];default:var
h=a(N[3],jx);return k(J[6],0,0,h)}},m=[1,[2,l],[3,e(h)]];return[0,[0,K([0,jy,f]),0],m]}break;case
2:var
n=[1,[2,b[1]],[3,i[12]]];return[0,[0,p(f,jz,d(ft)),0],n]}$(b);var
j=a(N[3],jw);return k(J[6],0,0,j)}function
az(a,f){switch(f[0]){case
0:var
b=f[2],e=f[1];switch(b[0]){case
0:var
g=b[1],u=b[2],v=H(g);if(H(e)===v){var
h=ce([0,jA,a],e,g),w=h[2],x=h[1],y=p(a,jB,d(eJ)),j=az(a,[0,w,u]);return[0,[0,y,[0,x,j[1]]],j[2]]}var
k=aQ([0,jC,a],e),z=k[2],A=k[1],l=az([0,jD,a],b),B=[0,z,l[2]];return[0,c(m[18],A,l[1]),B];case
3:var
I=b[1],s=aQ([0,jG,a],e);return[0,s[1],[0,s[2],[3,I]]];default:var
C=H(b);if(H(e)===C){var
n=ce(a,e,b),D=n[1],o=az(a,n[2]);return[0,[0,D,o[1]],o[2]]}var
q=aQ([0,jE,a],e),E=q[2],F=q[1],r=az([0,jF,a],b),G=[0,E,r[2]];return[0,c(m[18],F,r[1]),G]}case
3:return[0,0,f];default:var
t=aQ(a,f),J=t[1],K=[0,t[2],[3,i[11]]],L=[0,p(a,jH,d(fE)),0];return[0,c(m[18],J,L),K]}}function
by(e,a){if(0===a[0]){var
b=a[1];if(1===b[0])if(2===b[1][0]){var
g=b[2];if(3===g[0]){var
j=a[2];if(c(i[1],g[1],i[11])){var
k=p(e,jJ,d(bg)),h=by(e,j);return[0,[0,k,h[1]],h[2]]}}}var
f=by([0,jI,e],a[2]);return[0,f[1],[0,b,f[2]]]}return[0,0,a]}function
cf(aY){var
f=a(x[1][6],jK),j=a(x[1][6],jL),k=a(x[1][6],jM),y=A(i[11]);function
l(aZ){var
m=aZ;for(;;){if(m){var
b=m[1];switch(b[0]){case
0:var
am=b[2],an=b[1],a0=m[2],a1=b[4],a2=b[3],o=D(an[1]),ao=v(E(an)),ap=v(E(am)),J=A(a2),T=A(a1),aq=O(bn(ap,J),T),a3=aM(ao,aq),a4=am[3],a5=a(bw(jN),a4),a6=g[B],a7=G(a5),a8=[0,c(h[65][3],a7,a6),0],a9=[0,g[62],[0,g[B],0]],a_=[0,F(X),a9],a$=[0,a(h[65][22],a_),0],ba=[0,g[62],[0,g[B],0]],bb=[0,F(X),ba],bc=[0,a(h[65][22],bb),0],bd=[0,l(a0),0],be=[0,a(g[25],[0,o,0]),bd],bf=[0,a(g[76],[0,j,[0,k,[0,o,0]]]),be],bg=a(e[11],o),bi=a(e[11],k),bj=[0,J,ap,T,a(e[11],j),bi,bg],bk=[0,d(eR),bj],bo=[0,r([0,a(e[23],bk),0]),bf],bp=[0,a(g[25],[0,j,[0,k,0]]),bo],bq=[0,a(h[65][22],bp),bc],br=Y(J,y),bs=a(g[I],br),bt=[0,c(h[65][21],bs,bq),a$],bx=Y(J,T),by=[0,a(g[I],bx),0],bz=[0,a(g[25],[0,o,0]),by],bA=[0,a(g[76],[0,f,[0,o,0]]),bz],bB=a(e[11],o),bC=[0,ao,aq,a(e[11],f),bB],bD=[0,d(eT),bC],bE=[0,r([0,a(e[23],bD),0]),bA],bF=[0,a(g[25],[0,f,0]),bE],bG=a(h[65][22],bF),bH=[0,c(h[65][21],bG,bt),a8],bI=a(g[I],a3);return c(h[65][21],bI,bH);case
1:var
K=b[2],L=b[1],ar=c(i[26],L[4],K),bJ=c(w[14],ar,K),bK=c(w[13],L[4],bJ),bL=L[3],bN=function(a){return c(i[9],a,K)},bO=c(i[43],bN,bL),as=[0,L[1],0,bO,ar],bP=v(E(as)),at=A(K),U=A(bK),bQ=as[3],bR=a(bw(jO),bQ),bT=[0,g[62],[0,g[B],0]],bU=[0,F(X),bT],bV=[0,a(h[65][22],bU),0],bW=[0,g[62],[0,g[B],0]],bX=[0,F(X),bW],bY=[0,a(h[65][22],bX),0],bZ=[0,g[42],0],b0=[0,G(bR),bZ],b1=[0,aD(f),b0],b2=[0,a(g[25],[0,f,0]),b1],b3=[0,F(bm),b2],b4=[0,a(g[76],[0,j,[0,k,0]]),b3],b5=a(e[11],k),b6=[0,U,at,bP,a(e[11],j),b5],b7=[0,d(eZ),b6],b9=[0,r([0,a(e[23],b7),0]),b4],b_=[0,a(g[25],[0,k,[0,j,0]]),b9],b$=[0,a(h[65][22],b_),bY],ca=Y(at,U),cb=a(g[I],ca),cc=[0,c(h[65][21],cb,b$),bV],ce=Y(U,y),cf=a(g[I],ce);return c(h[65][21],cf,cc);case
3:var
au=m[2],av=b[2],M=b[1],s=D(M[1]),ch=function(a){return c(i[9],a,av)},V=c(i[44],ch,M),_=v(E(M)),$=v(E(V)),N=A(av),aw=aM(_,bn($,N));if(2===M[2]){var
ci=V[3],cj=a(bv(jP),ci),ck=g[B],cl=G(cj),cm=[0,c(h[65][3],cl,ck),0],cn=[0,l(au),0],co=[0,a(g[25],[0,s,0]),cn],cp=[0,a(g[76],[0,j,[0,s,0]]),co],cq=a(e[11],s),cr=[0,_,$,N,a(e[11],j),cq],cs=[0,d(fn),cr],ct=[0,r([0,a(e[23],cs),0]),cp],cu=[0,a(g[25],[0,j,0]),ct],cv=[0,a(h[65][22],cu),cm],cw=a(g[I],aw);return c(h[65][21],cw,cv)}var
cx=V[3],cy=a(bv(jQ),cx),cz=g[B],cA=G(cy),cB=[0,c(h[65][3],cA,cz),0],cC=[0,g[62],[0,g[B],0]],cD=[0,F(X),cC],cE=[0,a(h[65][22],cD),0],cF=[0,l(au),0],cG=[0,a(g[25],[0,s,0]),cF],cH=[0,a(g[76],[0,j,[0,k,[0,s,0]]]),cG],cI=a(e[11],s),cJ=a(e[11],j),cK=[0,_,$,N,a(e[11],k),cJ,cI],cL=[0,d(eX),cK],cM=[0,r([0,a(e[23],cL),0]),cH],cN=[0,a(g[25],[0,k,[0,j,0]]),cM],cO=[0,a(h[65][22],cN),cE],cP=Y(N,y),cQ=a(g[I],cP),cR=[0,c(h[65][21],cQ,cO),cB],cS=a(g[I],aw);return c(h[65][21],cS,cR);case
4:var
ax=m[2],ay=b[3],z=ay[2],P=ay[1],az=b[2],t=az[2],aa=az[1],cT=b[1],ac=Q(0);W(ac,cT);var
aA=D(t[1]),aB=D(z[1]),aC=v(E(t)),aE=v(E(z));if(c(i[1],aa,i[12]))if(0===z[2]){switch(t[2]){case
0:var
ad=d(e1);break;case
1:var
ad=d(e3);break;default:var
ad=d(fr)}var
cU=A(P),cV=2===t[2]?jR:jS,cW=bu(cV,t[3],P,z[3]),cX=[0,l(ax),0],cY=[0,a(g[25],[0,ac,0]),cX],cZ=[0,G(cW),cY],c0=a(e[11],aB),c1=[0,ad,[0,aC,aE,cU,a(e[11],aA),c0]],c2=[0,r([0,a(e[23],c1),0]),cZ];return a(h[65][22],c2)}var
aF=A(aa),aG=A(P),c3=iB(jT,aa,t[3],P,z[3]),c4=[0,g[62],[0,g[B],0]],c5=[0,F(X),c4],c6=[0,a(h[65][22],c5),0],c7=[0,g[62],[0,g[B],0]],c8=[0,F(X),c7],c9=[0,a(h[65][22],c8),0],c_=[0,l(ax),0],c$=[0,a(g[25],[0,ac,0]),c_],da=[0,G(c3),c$],db=[0,a(g[76],[0,j,[0,k,0]]),da],dc=a(e[11],aB),dd=a(e[11],aA),de=a(e[11],k),df=[0,aC,aE,aF,aG,a(e[11],j),de,dd,dc],dg=[0,d(e5),df],dh=[0,r([0,a(e[23],dg),0]),db],di=[0,a(g[25],[0,k,[0,j,0]]),dh],dj=[0,a(h[65][22],di),c9],dk=Y(aG,y),dl=a(g[I],dk),dm=[0,c(h[65][21],dl,dj),c6],dn=Y(aF,y),dp=a(g[I],dn);return c(h[65][21],dp,dm);case
5:var
H=b[1],aH=H[5],aI=H[4],ag=H[3],aJ=H[2],dq=m[2],dr=H[1],aK=Q(0),ds=D(ag[1]);W(aK,dr[1]);var
ah=v(E(aJ)),dt=v(E(ag)),ai=bM(aH),du=aM(a(e[10],1),ah),dv=d(af),dw=[0,c(u[4],[0,ai],0),dv,du],dx=a(e[21],dw),dy=[0,d(af),dx],dz=[0,d(hJ),dy],dA=a(e[23],dz),dB=A(aI),dC=bu(cg,ag[3],aI,[0,[0,i[14],aH],aJ[3]]),dD=[0,p([0,jX,[0,jW,[0,jV,cg]]],jU,d(bh)),dC],dE=g[B],dF=dY(ah),dG=[0,c(h[65][3],dF,dE),0],dH=[0,l(dq),0],dI=[0,a(g[25],[0,aK,0]),dH],dJ=[0,a(g[76],[0,f,0]),dI],dK=[0,G(dD),dJ],dL=a(e[11],f),dM=a(e[11],ds),dN=[0,a(e[11],ai),dt,ah,dB,dM,dL],dO=[0,d(e9),dN],dP=[0,r([0,a(e[23],dO),0]),dK],dQ=[0,a(g[25],[0,ai,[0,f,0]]),dP],dR=[0,a(g[76],[0,f,0]),dQ],dS=[0,ae(f),dR],dT=[0,a(g[25],[0,f,0]),dS],dU=[0,a(h[65][22],dT),dG],dV=a(g[I],dA);return c(h[65][21],dV,dU);case
6:var
aL=m[2],dW=b[1];try{var
dX=l(aL),dZ=D(dW[1]),d0=c(x[1][13][3],dZ,aY),d1=c(h[65][3],d0,dX);return d1}catch(a){a=q(a);if(a===C){var
m=aL;continue}throw a}case
9:var
aN=b[2],aj=b[1],d2=E(aj),d3=E(aN),d4=cd(jY,aj[3]),d5=d(bS),d6=d(bS),d7=[0,d(ec),d6,d5],d8=[0,d(bl),d7],d9=a(e[23],d8),d_=[0,g[42],[0,g[B],0]],d$=[0,a(jZ[1],d9),0],ea=[0,g[62],[0,g[16],d$]],eb=[0,F(b8),ea],ed=a(h[65][22],eb),ee=c(h[65][21],ed,d_),ef=D(aN[1]),eg=a(e[11],ef),eh=D(aj[1]),ei=a(e[11],eh),ej=v(d3),ek=[0,v(d2),ej,ei,eg],el=[0,d(eV),ek],em=a(e[23],el),en=G(d4),eo=r([0,em,0]),ep=c(h[65][3],eo,en);return c(n[18],ep,ee);case
10:var
ak=b[2],al=b[1],eq=b[3],er=E(ak),es=E(al),et=D(ak[1]),eu=D(al[1]),aO=eq?i[14]:i[12],ev=bu(j0,ak[3],aO,al[3]),ew=[0,g[B],0],ex=[0,aD(f),ew],ey=[0,a(g[25],[0,f,0]),ex],ez=[0,G(ev),ey],eA=a(e[11],eu),eB=a(e[11],et),eC=A(aO),eD=v(es),eE=[0,v(er),eD,eC,eB,eA],eF=[0,d(fl),eE],eG=[0,r([0,a(e[23],eF),0]),ez];return a(h[65][22],eG);case
11:var
R=b[2],eH=m[2],eI=b[3],eJ=b[1],aP=Q(0);W(aP,eJ);var
aQ=D(R[1]),aR=D(eI),aS=v(E(R)),aT=v(E(a(i[45],R))),eK=R[3],eL=a(bv(j1),eK),eM=[0,p(j3,j2,d(bh)),eL],eN=g[B],eO=G(eM),eP=[0,c(h[65][3],eO,eN),0],eQ=[0,l(eH),0],eS=[0,a(g[25],[0,aP,0]),eQ],eU=[0,a(g[76],[0,aQ,[0,aR,[0,f,0]]]),eS],eW=a(e[11],f),eY=a(e[11],aR),e0=[0,aS,aT,a(e[11],aQ),eY,eW],e2=[0,d(e7),e0],e4=[0,r([0,a(e[23],e2),0]),eU],e6=[0,a(g[25],[0,f,0]),e4],e8=[0,a(h[65][22],e6),eP],e_=aM(aS,Z(aT)),e$=a(g[I],e_);return c(h[65][21],e$,e8);case
12:var
fa=j4[15],fb=D(b[1]),fc=r([0,a(e[11],fb),0]);return c(h[65][3],fc,fa);case
13:var
fd=g[B],fe=aD(D(b[1]));return c(h[65][3],fe,fd);case
14:var
ff=b[1],fg=[0,g[B],0],fh=[0,aD(f),fg],fi=[0,a(g[25],[0,f,0]),fh],fj=[0,F(bm),fi],fk=[0,g[62],fj],fm=[0,F(b8),fk],fo=D(ff),fq=[0,r([0,a(e[11],fo),0]),fm];return a(h[65][22],fq);case
15:var
aU=b[3],aV=b[2],S=b[1],fs=aU[2],ft=aU[1],fu=aV[2],fv=aV[1],aW=Q(0),aX=Q(0);W(aW,fv);W(aX,ft);var
fw=D(S[1]),fx=S[3],fy=a(i$(j5),fx),fz=S[3],fA=a(bw(j6),fz),fB=v(E(S)),fC=[0,l(fs),0],fD=[0,a(g[25],[0,aX,0]),fC],fE=[0,G(fA),fD],fF=[0,a(h[65][22],fE),0],fG=[0,l(fu),0],fH=[0,a(g[25],[0,aW,0]),fG],fI=[0,G(fy),fH],fJ=[0,a(h[65][22],fI),fF],fK=[0,fB,[0,a(e[11],fw),0]],fL=[0,d(fp),fK],fM=a(e[40],fL),fN=a(g[ab],fM);return c(h[65][21],fN,fJ)}}return a(n[16],0)}}return l}function
aj(T,w,S,P,O,M,L,K,v){var
x=v[2],y=v[1],j=[0,[0,O],j7],q=R(T,j,M),E=q[1],s=az(j,q[2]),F=s[1],t=by(j,s[2]),H=t[2],I=c(m[18],F,t[1]),u=c(m[18],E,I),U=a(g[76],[0,w,0]),V=a(h[65][24],U),X=[0,P,[0,L,K,a(e[11],w)]],Y=r([0,a(e[23],X),0]),Z=c(h[65][3],Y,V);if(a(m[17][48],u))return[0,y,x];var
l=Q(0),f=0,b=H;for(;;){switch(b[0]){case
0:var
i=b[1];if(1===i[0]){var
n=i[1];if(2===n[0]){var
o=i[2];if(3===o[0]){var
B=b[2],C=o[1],f=[0,[0,C,a9(n[1])],f],b=B;continue}var
d=0}else
var
d=0}else
var
d=0;break;case
3:var
D=b[1],p=aG(0);W(l,p);var
z=[0,p,S,a(m[17][9],f),D],d=1;break;default:var
d=0}if(!d)var
A=a(N[3],ih),z=k(J[3],0,0,A);var
_=[0,a(g[25],[0,l,0]),0],$=[0,Z,[0,G(u),_]];return[0,[0,[0,l,a(h[65][22],$)],y],[0,z,x]]}}function
j8(W,h,f,E){var
j=E[1],X=E[2],Y=a(ar[3],j);if(c(m[15][34],Y,j9))return f;try{var
g=ai(h,X);if(typeof
g==="number")var
e=0;else
if(1===g[0]){var
o=g[1];if(typeof
o==="number")if(16<=o){switch(o+a2|0){case
0:var
p=g[2];if(p){var
r=p[2];if(r){var
s=r[2];if(s)if(s[2])var
e=0,b=0;else{var
G=s[1],H=r[1],n=av(W,h,p[1]);if(typeof
n==="number")var
l=0;else
if(1===n[0]){var
J=n[1];if(typeof
J==="number")if(23===J)if(n[2])var
l=0;else
var
I=1,l=1;else
var
l=0;else
var
l=0}else
var
l=0;if(!l)var
I=0;if(I)var
_=O(H,Z(G)),k=aj(h,j,0,d(fN),2,_,H,G,f),b=1;else
var
e=0,b=0}else
var
e=0,b=0}else
var
e=0,b=0}else
var
e=0,b=0;break;case
2:var
t=g[2];if(t){var
u=t[2];if(u)if(u[2])var
e=0,b=0;else
var
K=u[1],L=t[1],$=O(L,Z(K)),k=aj(h,j,2,d(fP),1,$,L,K,f),b=1;else
var
e=0,b=0}else
var
e=0,b=0;break;case
3:var
v=g[2];if(v){var
w=v[2];if(w)if(w[2])var
e=0,b=0;else
var
M=w[1],N=v[1],aa=O(M,Z(N)),k=aj(h,j,1,d(fX),2,aa,N,M,f),b=1;else
var
e=0,b=0}else
var
e=0,b=0;break;case
4:var
x=g[2];if(x){var
y=x[2];if(y)if(y[2])var
e=0,b=0;else
var
P=y[1],Q=x[1],ab=Z(Q),ac=O(O(P,A(i[14])),ab),k=aj(h,j,1,d(fR),2,ac,Q,P,f),b=1;else
var
e=0,b=0}else
var
e=0,b=0;break;case
5:var
z=g[2];if(z){var
B=z[2];if(B)if(B[2])var
e=0,b=0;else
var
R=B[1],S=z[1],ad=O(S,Z(R)),k=aj(h,j,1,d(fT),2,ad,S,R,f),b=1;else
var
e=0,b=0}else
var
e=0,b=0;break;case
6:var
C=g[2];if(C){var
D=C[2];if(D)if(D[2])var
e=0,b=0;else
var
U=D[1],V=C[1],ae=Z(U),af=O(O(V,A(i[14])),ae),k=aj(h,j,1,d(fV),2,af,V,U,f),b=1;else
var
e=0,b=0}else
var
e=0,b=0;break;default:var
e=0,b=0}if(b)var
F=k,e=1}else
var
e=0;else
var
e=0}else
var
e=0;if(!e)var
F=f;return F}catch(b){b=q(b);if(a(T[4],b))return f;throw b}}function
ak(b){var
d=a(g[22],b),e=a(g[76],[0,b,0]),f=a(h[65][24],e);return c(h[65][3],f,d)}function
j_(f){bN(0);var
t=a(z[35][14],f),u=c(z[35][1],j8,f),j=k(m[17][15],u,j$,t),l=j[1],v=j[2],w=d2(0),x=[0,a(n[16],0),0];function
y(k,j){var
c=j[2],l=c[2],f=c[1],m=j[1],n=k[2],o=k[1];if(c[3]){var
b=Q(0),p=aG(0);W(b,p);var
q=i[11],r=a9(f),s=[0,[0,p,1,[0,[0,i[12],r],0],q],n],t=[0,a(g[25],[0,l,[0,b,0]]),[0,o,0]],u=[0,a(g[76],[0,b,0]),t],v=[0,ae(b),u],w=[0,a(g[25],[0,f,[0,b,0]]),v],x=[0,d(f1),[0,m,0]],y=a(e[40],x),z=[0,a(g[ab],y),w];return[0,a(h[65][22],z),s]}var
A=[0,a(g[25],[0,f,[0,l,0]]),[0,o,0]],B=[0,d(fZ),[0,m,0]],C=a(e[40],B),D=[0,a(g[ab],C),A];return[0,a(h[65][22],D),n]}var
o=k(m[17][15],y,x,w),p=o[1],b=c(m[18],v,o[2]);if(a3[1])c(i[33],as,b);if(aF[1])try{k(i[64],[0,aG,bK,as],0,b);var
C=a(n[16],0);return C}catch(b){b=q(b);if(b===i[27]){var
A=a(i[39],0),r=k(i[65],0,0,A)[2];if(aE[1])c(i[36],as,r);var
B=a(cf(l),r);return c(h[65][3],p,B)}throw b}try{var
s=c(i[68],[0,aG,bK,as],b);if(aE[1])c(i[36],as,s);var
E=a(cf(l),s),F=c(h[65][3],p,E);return F}catch(b){b=q(b);if(b===i[28]){var
D=a(N[3],ka);return c(h[65][5],0,D)}throw b}}var
kb=a(n[68][8],j_);function
kc(b){var
f=br[81];function
k(a){return c(f,0,a)}var
R=c(z[35][1],k,b);function
j(k,I){function
b(t){try{var
m=aO(t,I);if(typeof
m==="number")var
f=0;else
if(1===m[0]){var
u=m[1];if(typeof
u==="number")if(12<=u)var
f=0;else{switch(u){case
6:var
v=m[2];if(v){var
w=v[2];if(w)if(w[2])var
f=0,b=0;else
var
x=w[1],y=v[1],R=[0,j([0,kd,k],x),0],S=[0,j([0,ke,k],y),R],U=[0,d(em),[0,y,[0,x,0]]],V=_(x),W=[0,aw(k,O(_(y),V),U),S],r=a(h[65][22],W),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
7:var
z=m[2];if(z){var
B=z[2];if(B)if(B[2])var
f=0,b=0;else
var
C=B[1],D=z[1],X=[0,j([0,kf,k],C),0],Y=[0,j([0,kg,k],D),X],Z=[0,d(eo),[0,D,[0,C,0]]],$=_(C),aa=[0,aw(k,bn(_(D),$),Z),Y],r=a(h[65][22],aa),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
8:var
E=m[2];if(E){var
F=E[2];if(F)if(F[2])var
f=0,b=0;else
var
o=F[1],p=E[1],s=Q(0),ac=[0,d(b3),[0,o,p]],ad=l([0,[0,s,a(e[23],ac)],0]),ae=[0,p,[0,o,[0,a(e[11],s),0]]],af=[0,d(es),ae],ag=aw(k,A(i[11]),af),ah=[0,c(h[65][3],ag,ad),0],ai=[0,j([0,kh,k],o),0],aj=[0,j([0,ki,k],p),ai],ak=[0,d(b2),[0,o,p]],al=[0,l([0,[0,s,a(e[23],ak)],0]),aj],am=[0,p,[0,o,[0,a(e[11],s),0]]],an=[0,d(eq),am],ao=_(o),ap=[0,aw(k,h0(_(p),ao),an),al],aq=[0,a(h[65][22],ap),ah],ar=a(g[25],[0,s,0]),as=[0,d(gP),[0,o,[0,p,0]]],at=a(e[40],as),au=a(g[ab],at),av=c(h[65][3],au,ar),r=c(h[65][21],av,aq),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
9:var
G=m[2];if(G)if(G[2])var
f=0,b=0;else
var
L=G[1],ax=[0,d(b0)],ay=[0,d(b1),ax],az=[0,L,a(e[23],ay)],aA=[0,d(b4),az],M=a(e[23],aA),aB=j(k,M),aC=il([0,kj,k],M,[0,d(gN),[0,L,0]]),r=c(h[65][3],aC,aB),b=1;else
var
f=0,b=0;break;case
10:var
H=m[2];if(H)if(H[2])var
f=0,b=0;else
var
aD=H[1],N=function(i){try{var
d=aO(t,i);if(typeof
d==="number")var
b=0;else
if(1===d[0]){var
e=d[1];if(typeof
e==="number"){if(10===e){var
f=d[2];if(f)if(f[2])var
b=0,c=0;else
var
h=N(f[1]),c=1;else
var
b=0,c=0}else
if(11===e)if(d[2])var
b=0,c=0;else
var
h=1,c=1;else
var
b=0,c=0;if(c)var
g=h,b=1}else
var
b=0}else
var
b=0;if(!b)var
g=0;return g}catch(b){b=q(b);if(a(T[4],b))return 0;throw b}},P=function(f,i){try{var
g=aO(t,i);if(typeof
g==="number")var
b=0;else
if(1===g[0]){var
n=g[1];if(typeof
n==="number")if(10===n){var
k=g[2];if(k)if(k[2])var
b=0;else
var
l=k[1],o=P([0,kk,f],l),p=[0,d(eu),[0,l,0]],r=[0,_(l)],s=[0,d(be),r],u=aw(f,a(e[23],s),p),m=c(h[65][3],u,o),b=1;else
var
b=0}else
var
b=0;else
var
b=0}else
var
b=0;if(!b)var
m=j(f,i);return m}catch(b){b=q(b);if(a(T[4],b))return j(f,i);throw b}},aE=N(aD)?K(k):P(k,I),r=aE,b=1;else
var
f=0,b=0;break;case
11:if(m[2])var
f=0,b=0;else
var
r=K(k),b=1;break;default:var
f=0,b=0}if(b)var
J=r,f=1}else
var
f=0}else
var
f=0;if(!f)var
J=a(n[16],0);return J}catch(b){b=q(b);if(a(T[4],b))return a(n[16],0);throw b}}return c(n[73][1],n[54],b)}function
l(b){if(b){var
i=b[2],f=b[1],g=f[1],S=f[2],k=function(U){try{var
k=ai(U,S);if(typeof
k==="number")var
f=0;else
if(1===k[0]){var
n=k[1];if(typeof
n==="number")if(16<=n){switch(n+a2|0){case
0:var
o=k[2];if(o){var
p=o[2];if(p){var
s=p[2];if(s)if(s[2])var
f=0,b=0;else{var
E=s[1],F=p[1],V=o[1];if(c(R,V,d(bj)))var
W=[0,l(i),0],X=[0,ak(g),W],Y=[0,j(kl,E),X],Z=[0,j(km,F),Y],_=[0,F,E,a(e[11],g)],$=[0,d(ew),_],aa=[0,r([0,a(e[23],$),0]),Z],G=a(h[65][22],aa);else
var
G=l(i);var
m=G,b=1}else
var
f=0,b=0}else
var
f=0,b=0}else
var
f=0,b=0;break;case
1:var
t=k[2];if(t){var
u=t[2];if(u)if(u[2])var
f=0,b=0;else
var
H=u[1],I=t[1],ab=[0,l(i),0],ac=[0,ak(g),ab],ad=[0,j(kn,H),ac],ae=[0,j(ko,I),ad],af=[0,I,H,a(e[11],g)],ag=[0,d(ey),af],ah=[0,r([0,a(e[23],ag),0]),ae],m=a(h[65][22],ah),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
15:var
v=k[2];if(v){var
w=v[2];if(w)if(w[2])var
f=0,b=0;else
var
J=w[1],K=v[1],aj=[0,l(i),0],al=[0,ak(g),aj],am=[0,j(kp,J),al],an=[0,j(kq,K),am],ao=[0,K,J,a(e[11],g)],ap=[0,d(eA),ao],aq=[0,r([0,a(e[23],ap),0]),an],m=a(h[65][22],aq),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
16:var
x=k[2];if(x){var
y=x[2];if(y)if(y[2])var
f=0,b=0;else
var
L=y[1],M=x[1],ar=[0,l(i),0],as=[0,ak(g),ar],at=[0,j(kr,L),as],au=[0,j(ks,M),at],av=[0,M,L,a(e[11],g)],aw=[0,d(eC),av],ax=[0,r([0,a(e[23],aw),0]),au],m=a(h[65][22],ax),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
17:var
z=k[2];if(z){var
A=z[2];if(A)if(A[2])var
f=0,b=0;else
var
N=A[1],O=z[1],ay=[0,l(i),0],az=[0,ak(g),ay],aA=[0,j(kt,N),az],aB=[0,j(ku,O),aA],aC=[0,O,N,a(e[11],g)],aD=[0,d(eE),aC],aE=[0,r([0,a(e[23],aD),0]),aB],m=a(h[65][22],aE),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;case
18:var
B=k[2];if(B){var
C=B[2];if(C)if(C[2])var
f=0,b=0;else
var
P=C[1],Q=B[1],aF=[0,l(i),0],aG=[0,ak(g),aF],aH=[0,j(kv,P),aG],aI=[0,j(kw,Q),aH],aJ=[0,Q,P,a(e[11],g)],aK=[0,d(eG),aJ],aL=[0,r([0,a(e[23],aK),0]),aI],m=a(h[65][22],aL),b=1;else
var
f=0,b=0}else
var
f=0,b=0;break;default:var
f=0,b=0}if(b)var
D=m,f=1}else
var
f=0;else
var
f=0}else
var
f=0;if(!f)var
D=l(i);return D}catch(b){b=q(b);if(a(T[4],b))return l(i);throw b}};return c(n[73][1],n[54],k)}return a(n[16],0)}var
o=a(z[35][14],b);return l(a(m[17][9],o))}var
kx=a(n[68][8],kc);function
ky(a){if(typeof
a==="number")if(18<=a)switch(a+bD|0){case
0:return f5;case
1:return f7;case
2:return f9;case
3:return gb;case
4:return f$;case
13:return gT;case
14:return gV;case
15:return gX;case
16:return gZ}throw C}function
kz(a){if(typeof
a==="number")if(18<=a)switch(a+bD|0){case
0:return gf;case
1:return gh;case
2:return gj;case
3:return gl;case
4:return gn;case
13:return g3;case
14:return g5;case
15:return g7;case
16:return g9}throw C}var
aA=[ad,kA,aa(0)];function
L(g,f,J){var
c=ai(f,J);if(typeof
c!=="number")switch(c[0]){case
1:var
i=c[1];if(typeof
i==="number")if(16<=i)switch(i+a2|0){case
0:var
j=c[2];if(j){var
k=j[2];if(k){var
l=k[2];if(l){if(!l[2]){var
x=l[1],y=k[1],h=av(g,f,j[1]);if(typeof
h!=="number"&&1===h[0]){var
m=h[1];if(typeof
m==="number")if(23===m){if(!h[2]){var
K=[0,d(f3),[0,y,x]];return a(e[23],K)}}else
if(24===m)if(!h[2]){var
M=[0,d(gR),[0,y,x]];return a(e[23],M)}}throw aA}var
b=1}else
var
b=0}else
var
b=1}else
var
b=1;break;case
9:var
p=c[2];if(p){var
r=p[2];if(r){if(!r[2]){var
z=r[1],A=p[1],R=L(g,f,z),S=[0,A,z,L(g,f,A),R],T=[0,d(hd),S];return a(e[23],T)}var
b=1}else
var
b=1}else
var
b=1;break;case
10:var
s=c[2];if(s){var
t=s[2];if(t){if(!t[2]){var
B=t[1],D=s[1],U=L(g,f,B),V=[0,D,B,L(g,f,D),U],W=[0,d(hb),V];return a(e[23],W)}var
b=1}else
var
b=1}else
var
b=1;break;case
11:if(!c[2])return d(hl);var
b=0;break;case
12:if(!c[2])return d(hp);var
b=0;break;case
13:var
u=c[2];if(u){if(!u[2]){var
E=u[1],X=[0,E,L(g,f,E)],Y=[0,d(hj),X];return a(e[23],Y)}var
b=0}else
var
b=1;break;case
14:var
v=c[2];if(v){var
w=v[2];if(w){if(!w[2]){var
F=w[1],G=v[1],Z=L(g,f,F),_=[0,G,F,L(g,f,G),Z],$=[0,d(hh),_];return a(e[23],$)}var
b=1}else
var
b=1}else
var
b=1;break;default:var
b=0}else
var
b=0;else
var
b=0;if(!b){var
n=c[2];if(n){var
o=n[2];if(o)if(!o[2]){var
N=o[1],O=n[1];try{var
P=[0,d(ky(i)),[0,O,N]],Q=a(e[23],P);return Q}catch(a){a=q(a);if(a===C)throw aA;throw a}}}}break;case
2:var
H=c[2],I=c[1],aa=L(g,f,H),ab=[0,I,H,L(g,f,I),aa],ac=[0,d(hf),ab];return a(e[23],ac)}throw aA}function
aR(d,c,b){var
e=a(n[68][4],b);return k(g[13],d,c,e)}function
M(b,e){function
d(f){var
d=aR(x[1][10][1],b,f),i=a(e,d),j=a(g[2],d);return c(h[65][3],j,i)}var
f=a(n[68][8],d),i=a(g[76],[0,b,0]),j=a(h[65][24],i);return c(h[65][3],j,f)}function
ch(b,i){function
d(d){var
j=c(ar[5],b,kB),e=aR(x[1][10][1],j,d),k=c(ar[5],b,kC),f=aR(x[1][10][1],k,d),l=[0,c(i,e,f),0],m=[0,a(g[2],f),l],n=[0,a(g[2],e),m];return a(h[65][22],n)}var
e=a(n[68][8],d),f=a(g[76],[0,b,0]),j=a(h[65][24],f);return c(h[65][3],j,e)}function
kD(j){var
aS=a(z[35][7],j),D=a(n[68][4],j),f=a(n[68][5],j);function
v(a){return L(D,f,a)}function
b(l){if(l){var
t=l[1];if(1===t[0]){var
m=l[2],o=t[3],p=t[1],w=t[2];if(a4[1]){var
y=function(s){try{var
f=av(D,s,o);if(typeof
f==="number")var
d=0;else
if(1===f[0]){var
l=f[1];if(typeof
l==="number")if(1<(l-23|0)>>>0)var
d=0;else
var
t=c(ar[5],p[1],kH),n=aR(x[1][10][1],t,j),r=b9(o,a(e[11],p[1]),w),v=b([0,[0,c(u[4],n,0),r],m]),y=k(g[140],[0,n],r,g[B]),i=c(h[65][3],y,v),d=1;else
var
d=0}else
var
d=0;if(!d)var
i=b(m);return i}catch(c){c=q(c);if(a(T[4],c))return b(m);throw c}};return c(n[73][1],n[54],y)}}var
i=l[2],f=a(u[11][1][2],t),s=function(x){try{var
p=ai(x,a(u[11][1][4],t));if(typeof
p==="number")var
j=0;else
switch(p[0]){case
1:var
K=p[1];if(typeof
K==="number")if(18<=K){switch(K+bD|0){case
7:var
L=p[2];if(L){var
N=L[2];if(N)if(N[2])var
j=0,l=0;else
var
aR=N[1],aT=L[1],aU=ch(f,function(d,a){var
e=[0,[0,c(u[4],a,0),aR],i];return b([0,[0,c(u[4],d,0),aT],e])}),aV=ae(f),y=c(h[65][3],aV,aU),l=1;else
var
j=0,l=0}else
var
j=0,l=0;break;case
8:var
O=p[2];if(O){var
P=O[2];if(P)if(P[2])var
j=0,l=0;else
var
aW=P[1],aX=O[1],aY=0,aZ=[0,M(f,function(a){return b([0,[0,c(u[4],a,0),aW],i])}),aY],a0=[0,M(f,function(a){return b([0,[0,c(u[4],a,0),aX],i])}),aZ],a1=ae(f),y=c(h[65][21],a1,a0),l=1;else
var
j=0,l=0}else
var
j=0,l=0;break;case
9:if(p[2])var
j=0,l=0;else
var
y=ae(f),l=1;break;case
11:var
Q=p[2];if(Q)if(Q[2])var
j=0,l=0;else{var
s=ai(x,Q[1]);if(typeof
s==="number")var
n=0;else
switch(s[0]){case
1:var
E=s[1];if(typeof
E==="number")if(16<=E){switch(E+a2|0){case
0:var
U=s[2];if(U){var
V=U[2];if(V){var
W=V[2];if(W)if(W[2])var
n=0,o=0,m=0;else{var
F=W[1],G=V[1],az=U[1];if(aF[1]){var
X=av(D,x,az);if(typeof
X==="number")var
A=0;else
if(1===X[0]){var
Y=X[1];if(typeof
Y==="number"){if(23===Y)var
a3=0,a4=[0,M(f,function(a){return b(i)}),a3],a5=[0,G,F,a(e[11],f)],a6=[0,d(gd),a5],a7=a(e[23],a6),a8=[0,a(g[ab],a7),a4],aE=a(h[65][22],a8),as=1;else
if(24===Y)var
a9=0,a_=[0,M(f,function(a){return b(i)}),a9],a$=[0,G,F,a(e[11],f)],ba=[0,d(g1),a$],bb=a(e[23],ba),bc=[0,a(g[ab],bb),a_],aE=a(h[65][22],bc),as=1;else
var
A=0,as=0;if(as)var
aB=aE,A=1}else
var
A=0}else
var
A=0;if(!A)var
aB=b(i);var
aC=aB}else{var
Z=av(D,x,az);if(typeof
Z==="number")var
B=0;else
if(1===Z[0]){var
_=Z[1];if(typeof
_==="number"){if(23===_)var
bd=b(i),be=[0,d(bY),[0,G,F]],bf=a(e[23],be),bg=c(u[11][1][7],bf,t),bh=c(g[4],kE,bg),aH=c(h[65][3],bh,bd),at=1;else
if(24===_)var
bi=b(i),bj=[0,d(bX),[0,G,F]],bk=a(e[23],bj),bl=c(u[11][1][7],bk,t),bm=c(g[4],kF,bl),aH=c(h[65][3],bm,bi),at=1;else
var
B=0,at=0;if(at)var
aG=aH,B=1}else
var
B=0}else
var
B=0;if(!B)var
aG=b(i);var
aC=aG}var
z=aC,m=1}else
var
o=1,m=0}else
var
n=0,o=0,m=0}else
var
n=0,o=0,m=0;break;case
9:var
ac=s[2];if(ac){var
ad=ac[2];if(ad)if(ad[2])var
n=0,o=0,m=0;else
var
aJ=ad[1],af=ac[1],bx=v(af),by=0,bz=[0,M(f,function(a){var
d=S(aJ),e=bo(S(af),d);return b([0,[0,c(u[4],a,0),e],i])}),by],bA=[0,af,aJ,bx,a(e[11],f)],bB=[0,d(ht),bA],bC=[0,r([0,a(e[23],bB),0]),bz],z=a(h[65][22],bC),m=1;else
var
n=0,o=0,m=0}else
var
n=0,o=0,m=0;break;case
10:var
ag=s[2];if(ag){var
ah=ag[2];if(ah)if(ah[2])var
n=0,o=0,m=0;else
var
aK=ah[1],aL=ag[1],bE=0,bF=[0,M(f,function(a){var
d=S(aK),e=aN(S(aL),d);return b([0,[0,c(u[4],a,0),e],i])}),bE],bG=[0,aL,aK,a(e[11],f)],bH=[0,d(hr),bG],bI=[0,r([0,a(e[23],bH),0]),bF],z=a(h[65][22],bI),m=1;else
var
n=0,o=0,m=0}else
var
n=0,o=0,m=0;break;case
13:var
aj=s[2];if(aj)if(aj[2])var
o=1,m=0;else
var
ak=aj[1],bJ=v(ak),bK=0,bL=[0,M(f,function(a){return b([0,[0,c(u[4],a,0),ak],i])}),bK],bM=[0,ak,bJ,a(e[11],f)],bN=[0,d(hz),bM],bO=[0,r([0,a(e[23],bN),0]),bL],z=a(h[65][22],bO),m=1;else
var
n=0,o=0,m=0;break;case
14:var
al=s[2];if(al){var
am=al[2];if(am)if(am[2])var
n=0,o=0,m=0;else
var
H=am[1],I=al[1],bP=v(I),bQ=v(H),bR=0,bS=[0,M(f,function(a){var
d=aN(S(I),H),e=bo(aN(I,S(H)),d);return b([0,[0,c(u[4],a,0),e],i])}),bR],bT=[0,I,H,bP,bQ,a(e[11],f)],bU=[0,d(hx),bT],bV=[0,r([0,a(e[23],bU),0]),bS],z=a(h[65][22],bV),m=1;else
var
n=0,o=0,m=0}else
var
n=0,o=0,m=0;break;default:var
o=1,m=0}if(m)var
aD=z,o=2}else
var
o=1;else
var
o=1;switch(o){case
0:var
w=0;break;case
1:var
$=s[2];if($){var
aa=$[2];if(aa)if(aa[2])var
n=0,w=0;else{var
bn=aa[1],bp=$[1];try{var
bq=kz(E),br=0,bs=[0,M(f,function(a){return b(i)}),br],bt=[0,bp,bn,a(e[11],f)],bu=[0,d(bq),bt],bv=[0,r([0,a(e[23],bu),0]),bs],bw=a(h[65][22],bv),aI=bw}catch(a){a=q(a);if(a!==C)throw a;var
aI=b(i)}var
aD=aI,w=1}else
var
n=0,w=0}else
var
n=0,w=0;break;default:var
w=1}if(w)var
R=aD,n=1;break;case
2:var
aM=s[2],an=s[1],bW=v(an),bZ=0,b0=[0,M(f,function(a){var
d=aN(an,S(aM));return b([0,[0,c(u[4],a,0),d],i])}),bZ],b1=[0,an,aM,bW,a(e[11],f)],b2=[0,d(hv),b1],b3=[0,r([0,a(e[23],b2),0]),b0],R=a(h[65][22],b3),n=1;break;default:var
n=0}if(!n)var
R=b(i);var
y=R,l=1}else
var
j=0,l=0;break;case
12:var
ao=p[2];if(ao){var
ap=ao[2];if(ap)if(ap[2])var
j=0,l=0;else
var
aO=ap[1],aP=ao[1],b4=ch(f,function(d,a){var
f=k(e[35],aO,0,aP),g=[0,[0,c(u[4],a,0),f],i],h=k(e[35],aP,0,aO);return b([0,[0,c(u[4],d,0),h],g])}),b5=ae(f),y=c(h[65][3],b5,b4),l=1;else
var
j=0,l=0}else
var
j=0,l=0;break;case
0:case
1:case
2:case
3:case
4:var
aw=p[2];if(aw){var
ax=aw[2];if(ax)if(ax[2])var
j=0,l=0;else
var
ay=b(i),l=2;else
var
j=0,l=0}else
var
j=0,l=0;break;default:var
j=0,l=0}switch(l){case
0:var
au=0;break;case
1:var
ay=y,au=1;break;default:var
au=1}if(au)var
J=ay,j=1}else
var
j=0;else
var
j=0;break;case
2:var
aq=p[2],ar=p[1],b6=a(aS,aq);if(c(kG[107],x,b6))var
b7=v(ar),b8=0,b9=[0,M(f,function(a){var
d=bo(S(ar),aq);return b([0,[0,c(u[4],a,0),d],i])}),b8],b_=[0,ar,aq,b7,a(e[11],f)],b$=[0,d(hB),b_],ca=[0,r([0,a(e[23],b$),0]),b9],aQ=a(h[65][22],ca);else
var
aQ=b(i);var
J=aQ,j=1;break;default:var
j=0}if(!j)var
J=b(i);return J}catch(c){c=q(c);if(c===aA)return b(i);if(a(T[4],c))return b(i);throw c}};return c(n[73][1],n[54],s)}return c(h[65][3],kx,kb)}return b(a(n[68][3],j))}var
bz=a(n[68][8],kD);function
kI(b){var
f=a(n[68][2],b),j=a(n[68][4],b),k=a(n[68][5],b);function
p(a){return L(j,k,a)}function
i(f){function
b(b){function
j(d){var
c=ai(b,f);return a(n[16],c)}function
k(b){if(typeof
b!=="number")switch(b[0]){case
1:var
l=b[1];if(typeof
l==="number"){var
m=l-27|0;if(!(2<m>>>0))switch(m){case
0:if(!b[2])return bz;break;case
1:break;default:var
o=b[2];if(o)if(!o[2]){var
x=g[16],y=F(bm),z=c(h[65][3],y,x);return c(h[65][3],z,bz)}}}break;case
2:var
A=i(b[2]);return c(h[65][3],g[16],A)}try{var
s=p(f),t=g[16],u=function(b){var
c=[0,d(hn),[0,f,s]];return cc(b,a(e[23],c))},v=a(n[68][8],u),w=c(h[65][3],v,t),k=w}catch(b){b=q(b);if(b===aA)var
r=d(b7),j=a(g[108],r);else{if(!a(n[72][9],b))throw b;var
j=c(n[21],0,b)}var
k=j}return c(h[65][3],k,bz)}var
l=a(n[72][10],j);return c(n[73][1],l,k)}return c(n[73][1],n[54],b)}return i(f)}var
kJ=a(n[68][8],kI);function
kK(e){a(bO[12],kL);if(a5[1]){var
b=a6[1],d=function(a){a[1][1]=a[2];return 0};c(m[17][11],d,b);a7[1]=0;a(s[2],aH);aI[1]=0;bN(0)}return kJ}var
kM=a(n[16],0),ci=c(n[73][1],kM,kK);aU(426,[0,ci],"Omega_plugin__Coq_omega");a(kN[9],aS);function
aB(b){var
d=c(l[17],x[1][6],kO),e=a(x[5][4],d),f=a(x[6][4],b),g=c(x[13][1],[0,e],f),h=a(kP[12],g);return a(kQ[22],h)}function
aT(b){var
d=c(m[17][137],kR[33],b);function
e(b){if(aZ(b,kS)){if(aZ(b,kT)){if(aZ(b,kU)){if(aZ(b,kV)){var
d=c(j[17],kW,b),e=a(N[3],d);return k(J[6],0,0,e)}return aB(kX)}return aB(kY)}return aB(kZ)}return aB(k0)}var
f=c(l[17],e,d),g=a(h[65][22],f),i=a(h[65][32],g);return c(h[65][3],i,ci)}var
k1=0,k3=[0,[0,k2,function(a){return aT(0)}],k1];cl(cj[8],aS,k4,0,0,k3);var
k5=0,k8=[0,[0,k7,function(a){return aT(k6)}],k5];function
k9(a,b){return aT(c(l[17],x[1][8],a))}var
lc=[0,[0,[0,lb,[0,la,[1,[0,[5,a(k$[16],k_[7])]],0]]],k9],k8];cl(cj[8],aS,ld,0,0,lc);aU(434,[0,aS,aB,aT],"Omega_plugin__G_omega");return}
