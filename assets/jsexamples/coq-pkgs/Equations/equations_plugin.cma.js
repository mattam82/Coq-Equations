function(M6){"use strict";var
d0=154,m0=";",nf="Pattern-matching lambdas not allowed in refine",fN=",",hL="Subgoal: ",mZ="my_preident",nz="(",mY="Depelim",cp=123,bg="src/splitting.ml",hY="pattern",mX="_equation_",ne="<>",nX="wf_fix",dc="|",nW="mfix",mW="elimination",fM="This is not an equality between constructors.",d6="refine",fL="pattern_of_glob_constr",mV="NoConfusion",bK=139,db="with",ny=131,d4="=>",nV="Covering",nx="binders2",mU="decompose_app",x=122,hH="term: ",hK=167,nd="0",bJ=165,mS="uncurry_call",mT="succeeded",hG="Subterm",nw="Functional induction principle could not be proved automatically: ",hF="_unfold",hX=128,mR=" context map ",nc="Cannot simplify dependent pair",bX=125,cN=248,hE="P",nv="Heq",bY=146,hW="simplify",nU="simp",nu=520,nT="by",hV="Applying ",fK="Below",cO="x",nt="Schemes",mQ="->",q=246,nS="deppat_equations",mP="mutfix",hD=" for ",aQ="src/principles_proofs.ml",mO="interp_eqns",de="y",hP=118,aP=121,ns="_rec",hU="curry",hO=119,cl="equations",co=108,na=127,nb="Equations_common",fF="dependent",fJ=104,nR="is_secvar",nQ="<->",aJ=103,h=120,mN=" Pretype error: ",bw=102,nr="<-",m$="-",nP="\xce\xbb",m9="-!",m_="def",bx="covering",fD=" := ",nO="funelim",dd=" and ",mM="define",nq="split",nN="Syntax",np="With",m8="Proof of mutual induction principle is not guarded ",df=100,hB="Functional elimination principle could not be proved automatically: ",hC="_graph",no="*",nn="split_var",dg=111,cn="}",nM="src/noconf_hom.ml",nL="Building internalization environment",W=107,m7="failed",fC=157,mL="move_after_deps",hT=" Fail error ",mK="Extra_tactics",bI=109,ck="{",a2=136,hJ="",nK="Sigma_types",mJ="get_signature_pack",nJ="eqns_specialize_eqs",mI=137,cm=124,m6="solve_equations",nI=1249,m5="refine_ho",d2=166,nG=150,nH=169,d1=140,nF=" succeeded",nm="Prototype ",d5=135,m4="pattern_call",fI="Derive",m3="Eqdec",fE="src/sigma_types.ml",bv=" : ",fP=":=!",hS="src/simplify.ml",cL=" on ",hR="$",au=141,fO=171,m2="needs_generalization",hI="Type error while building context map: ",bH=149,m1="autounfold_ref",mH="src/equations.ml",hN="?",mG=" with ",nk="deppat_elim",nl=" in context ",cM="src/covering.ml",hA="deppat",dZ=" ",nE="index",cj=")",nj="Noconf",fH=":",ni="where ",a3="Equations",hM="Failed with: ",mF="subterm_relation",nD="_where",d3="_",nC="Splitting",ci="src/principles.ml",hQ="wildcard",ch=":=",nB="============================",hz="Unnexpected goal",fG="where",nA="equations_plugin",u=250,ng="g_simplification_rules",nh="Elimination",am=M6.jsoo_runtime,Y=am.caml_check_bound,mE=am.caml_equal,cK=am.caml_fresh_oo_id,mD=am.caml_lessthan,cf=am.caml_make_vect,e=am.caml_new_string,t=am.caml_obj_tag,aD=am.caml_register_global,v=am.caml_wrap_exception;function
a(a,b){return a.length==1?a(b):am.caml_call_gen(a,[b])}function
b(a,b,c){return a.length==2?a(b,c):am.caml_call_gen(a,[b,c])}function
g(a,b,c,d){return a.length==3?a(b,c,d):am.caml_call_gen(a,[b,c,d])}function
o(a,b,c,d,e){return a.length==4?a(b,c,d,e):am.caml_call_gen(a,[b,c,d,e])}function
y(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):am.caml_call_gen(a,[b,c,d,e,f])}function
a1(a,b,c,d,e,f,g){return a.length==6?a(b,c,d,e,f,g):am.caml_call_gen(a,[b,c,d,e,f,g])}function
at(a,b,c,d,e,f,g,h){return a.length==7?a(b,c,d,e,f,g,h):am.caml_call_gen(a,[b,c,d,e,f,g,h])}function
M5(a,b,c,d,e,f,g,h,i){return a.length==8?a(b,c,d,e,f,g,h,i):am.caml_call_gen(a,[b,c,d,e,f,g,h,i])}function
hy(a,b,c,d,e,f,g,h,i,j){return a.length==9?a(b,c,d,e,f,g,h,i,j):am.caml_call_gen(a,[b,c,d,e,f,g,h,i,j])}function
hw(a,b,c,d,e,f,g,h,i,j,k){return a.length==10?a(b,c,d,e,f,g,h,i,j,k):am.caml_call_gen(a,[b,c,d,e,f,g,h,i,j,k])}function
hx(a,b,c,d,e,f,g,h,i,j,k,l){return a.length==11?a(b,c,d,e,f,g,h,i,j,k,l):am.caml_call_gen(a,[b,c,d,e,f,g,h,i,j,k,l])}function
cg(a,b,c,d,e,f,g,h,i,j,k,l,m){return a.length==12?a(b,c,d,e,f,g,h,i,j,k,l,m):am.caml_call_gen(a,[b,c,d,e,f,g,h,i,j,k,l,m])}var
p=am.caml_get_global_data(),f5=e(mF),cw=[0,[0,0],2],as=e(nA),r=p.CamlinternalLazy,P=p.Evarutil,c=p.EConstr,G=p.Constr,A=p.Termops,I=p.Assert_failure,j=p.Names,ab=p.Univ,f=p.Util,l=p.Evd,aE=p.Sorts,N=p.Reductionops,k=p.Context,Z=p.Inductiveops,iS=p.Reduction,bb=p.Term,ac=p.Typeclasses,aS=p.Globnames,aK=p.Hints,$=p.CErrors,d=p.Pp,L=p.Feedback,M=p.Option,z=p.Printer,i=p.Proofview,bO=p.Refiner,cT=p.Pretype_errors,bP=p.Himsg,C=p.Tacmach,s=p.Tactics,ay=p.Libnames,ax=p.Environ,w=p.Global,af=p.CAst,iN=p.Ltac_plugin__Tacintern,eh=p.Ltac_plugin__Tacarg,E=p.Genarg,ef=p.Ltac_plugin__Tacinterp,aa=p.Stdarg,a6=p.Geninterp,J=p.Stdlib,h4=p.Coqlib,az=p.Nametab,O=p.Not_found,n=p.Tacticals,cu=p.Evarsolve,T=p.Retyping,av=p.Namegen,bM=p.Declare,ae=p.Typing,aB=p.Vars,ea=p.Smartlocate,h1=p.Stdlib__printexc,fT=p.Stdlib__printf,hZ=p.Topfmt,by=p.Goptions,du=p.Stdlib__lazy,i5=p.Evardefine,et=p.Dumpglob,m=p.Stdlib__list,gi=p.CString,V=p.DAst,a7=p.Ppconstr,bk=p.Constrexpr_ops,K=p.Nameops,cZ=p.Impargs,dD=p.Metasyntax,a8=p.Constrintern,gq=p.Lib,dB=p.Loc,Q=p.Int,gu=p.Failure,D=p.CList,bm=p.Invalid_argument,bq=p.CClosure,cD=p.Refine,bd=p.CArray,bS=p.Inductive,dK=p.Locusops,bc=p.Tacred,gG=p.Extraction_plugin__Table,br=p.Evarconv,aY=p.Stdlib__array,jV=p.Typeops,eZ=p.TransparentState,be=p.Obligations,bW=p.Lemmas,kj=p.Pfedit,ki=p.Evar,dQ=p.Proof_global,gS=p.Future,e8=p.Pretyping,ff=p.Cbv,kL=p.UnivNames,kM=p.ComInductive,kW=p.Find_subterm,g_=p.Class_tactics,c_=p.Equality,dV=p.Conv_oracle,cH=p.Type_errors,cG=p.Autorewrite,hk=p.Indschemes,li=p.UnivGen,fp=p.Libobject,dY=p.Vernacextend,bG=p.Attributes,l$=p.Genintern,hr=p.Ftactic,a0=p.Mltop,an=p.Ltac_plugin__Tacentries,cI=p.CLexer,B=p.Pcoq,dX=p.Ltac_plugin__Pptactic,lX=p.Pvernac,p7=[0,e("src/equations_common.ml"),563,9],rn=[0,0,0],rm=[0,0,0],rl=[0,0,0,0,0],ri=e(hL),rh=e(nF),rc=e(cL),rd=e(hD),re=e(hT),rg=e(mN),rf=e(hM),q$=e("================="),ra=e(cL),rb=e(hV),q_=e(hL),q9=e(nF),q4=e(cL),q5=e(hD),q6=e(hT),q8=e(mN),q7=e(hM),q2=e(cL),q3=e(hV),qZ=e(" depends"),q0=e("Found no hypothesis on which "),q1=[0,e("move_before_deps")],qP=[0,0],qI=e("impossible_call"),qG=e("solve_equation"),qF=e(cO),qE=e("find_empty"),qD=e(cl),qB=e("depind"),qA=e("simpl_dep_elim"),qy=e("depelim_nosimpl"),qw=e("do_empty"),qu=e("Equations.Init.depelim"),qt=e("."),qq=e("equations.depelim.module"),qr=e("equations.depelim.module is not defined"),qo=e("Equations.Init.unfold_recursor_ext"),qn=e("Equations.Init.unfold_recursor"),qm=e("Equations.Init.specialize_mutfix"),ql=e("Equations.Init.solve_subterm"),qk=e("Equations.Init.simpl_equations"),qj=e("Equations.Init.solve_eqdec"),qi=e("Equations.Init.solve_noconf_hom"),qh=e("Equations.Init.solve_noconf"),qg=e("Equations.Tactics.set_eos"),qf=e("Equations.Tactics.pi"),qe=e("Equations.Equations.solve_rec"),qc=e("Equations.Subterm.rec_wf_eqns_rel"),qa=e("Equations.Below.rec"),p2=e("Unknown database "),p3=[0,e("autounfold")],p4=[0,1],p5=[0,0],p6=e("Nothing to unfold"),p1=[0,0,0],pY=e("sigma.pr2"),pX=e("sigma.pr1"),pS=e("impossiblecall.class"),pG=e("depelim.class"),pF=e("funelim.class"),pE=e("funind.class"),pD=e("Cannot find tactic "),pB=[0,1],pC=[0,1],oI=[1,10],oF=[0,0],oG=e(" is defined"),oE=[0,0],oD=e("equations."),oC=e("new_global raised an error on:"),ow=[0,[11,e("Exception while typechecking context "),[2,0,[11,e(bv),[2,0,[12,10,0]]]]],e("Exception while typechecking context %s : %s\n")],n2=e("DEPRECATED. Use flag [Equations With UIP] and introduce an axiomn [forall A, Equations.Classes.UIP A] as a type class instance using [Existing Instance] instead."),n3=[0,e(a3),[0,e("WithK"),0]],n4=e("using axiomatic K during simplification."),n7=[0,e(a3),[0,e("WithKDec"),0]],n8=e("using propositional K during simplification. Use flag Equations With UIP instead."),n$=[0,e(a3),[0,e(np),[0,e("UIP"),0]]],oa=e("allow using propositional UIP during simplification"),od=[0,e(a3),[0,e("Transparent"),0]],oe=e("leave definitions transparent"),oh=[0,e(a3),[0,e(np),[0,e("Funext"),0]]],oi=e("use functional extensionality to prove unfolding lemmas"),ol=[0,e(a3),[0,e(fI),[0,e(a3),0]]],om=e("generate propositional equations for each definition"),op=[0,e(a3),[0,e(fI),[0,e("Eliminator"),0]]],oq=e("generate eliminators for each definition"),ot=[0,e(a3),[0,e("Debug"),0]],ou=e("Equations debug output"),oJ=e("nat.zero"),oK=e("nat.succ"),oL=e("nat.type"),oO=e("fixproto"),oP=e("equality.type"),oQ=e("equality.refl"),oR=e("equality.case"),oS=e("equality.elim"),oT=e("bottom.type"),oU=e("bottom.case"),oV=e("bottom.elim"),oW=e("top.type"),oX=e("top.intro"),oY=e("top.elim"),oZ=e("conj.type"),o1=e("conj.intro"),o3=e("unit.type"),o4=e("unit.intro"),o5=e("product.type"),o6=e("product.intro"),o7=e("wellfounded.class"),o8=e("wellfounded.type"),o9=e("relation.type"),o_=e("relation.transitive_closure"),o$=e("tele.type"),pb=e("tele.tip"),pc=e("tele.ext"),pd=e("tele.interp"),pe=e("tele.measure"),pf=e("tele.fix"),pg=e("tele.fix_functional_type"),ph=e("tele.fix_unfold"),pj=e("tele.MR"),pk=e("tele.type_app"),pl=e("tele.forall_type_app"),pm=e("tele.forall_uncurry"),pn=e("tele.forall"),po=e("tele.forall_pack"),pp=e("tele.forall_unpack"),pq=e("eqdec.class"),pr=e("eqdec.dec_eq"),ps=e("uip.class"),pt=e("uip.uip"),pv=e("signature.class"),pw=e("signature.signature"),py=e("signature.pack"),pH=e("noconfusion.class"),pI=e("nocycle.class"),pJ=e("internal.bang"),pK=e("internal.inaccessible_pattern"),pL=e("internal.block"),pM=e("internal.hide_pattern"),pN=e("internal.hidebody"),pO=e("internal.add_pattern"),pP=e("eos"),pQ=e("internal.the_end_of_the_section"),pR=e("internal.end_of_section"),pU=e("sigma.type"),pV=e("sigma.intro"),p8=[0,e(fK),[0,e(a3),0]],rv=[0,0],ry=e("No derive declared for "),rw=e("Expected an inductive type"),rz=e("!"),rA=e("#"),rB=e(cj),rC=e(nz),rD=e(cj),rE=e("?("),rM=e(fN),rH=e(ch),rI=e(fP),rJ=e(cn),rK=e(ck),rL=e(d4),rN=e(db),rO=e(fG),rP=e(cn),rQ=e(ck),rS=e(bv),rR=e("by struct "),rT=e("by wf "),r0=e(fN),rV=e(ch),rW=e(fP),rX=e(cn),rY=e(ck),rZ=e(d4),r1=e(db),r7=e(fN),r2=e(ch),r3=e(fP),r4=e(cn),r5=e(ck),r6=e(d4),r8=e(db),r9=e(fG),r_=e(cn),r$=e(ck),sx=e(nf),sy=e(mO),sz=e(nf),sA=e(mO),sB=e(m_),sC=e(ne),sw=e("_abs_where"),su=e("Expecting a pattern for "),sv=e("interp_pats"),ss=e("Internalizing pattern"),sq=e(nL),sr=e(nL),st=e("While translating pattern to glob constr"),sg=e("Constructor is applied to too few arguments"),sh=e(fL),si=e("Constructor is applied to too many arguments"),sj=e(fL),sm=e(" as a constructor"),sn=e("Cannot interpret "),so=e(fL),sp=e(hQ),sk=e("Cannot interpret globalized term as a pattern"),sl=e(fL),sf=[0,e("src/syntax.ml"),291,9],se=e("?( _ )"),rU=e(dc),rG=e("<constr>"),sb=e("equations_list"),sd=[0,0,0],sF=e(" appears twice"),sG=e("Non-linear pattern: variable "),sH=e(hQ),sZ=[0,e("src/context_map.ml"),274,12],tn=e("Occurs check singleton subst"),tm=[0,1],tj=e(dd),tk=e("Contexts do not agree for composition: "),tl=e("check_eq_context_nolet"),th=[0,1],ti=[0,[11,e("While comparing contexts: "),[2,0,[11,e(dd),[2,0,[11,e(bv),[2,0,[12,10,0]]]]]]],e("While comparing contexts: %s and %s : %s\n")],tg=[0,[11,e("Exception while comparing contexts "),[2,0,[11,e(dd),[2,0,[11,e(bv),[2,0,[12,10,0]]]]]]],e("Exception while comparing contexts %s and %s : %s\n")],tf=[0,0],td=e("split_tele"),tc=e("split_context"),s5=e("Could not generate a permutation: different variables"),s8=e("Could not generate a permutation: irreducible inaccessible"),s6=e(dd),s7=e("Could not generate a permutation, patterns differ: "),s9=e("Could not generate a permutation"),s1=e(" = "),s2=e(dd),s3=e(" in ctx2 is invertible to "),s4=e("Could not generate a permutation: two different instances:"),s0=[0,0,0],sY=[0,0,0],sS=e(hI),sT=e(cl),sU=e("Invalid_argument: "),sV=e(hI),sW=e(cl),sP=e("Anomaly: "),sQ=e(hI),sR=e(cl),sO=[0,0],sK=e(nB),sL=e(nB),sI=e(dZ),sD=[0,0],sE=[0,1],t7=e("No Signature instance found"),t3=e("Goal cannot be curried"),t1=e("No currying to do in "),tQ=[0,e(fE),555,14],tR=[0,e(fE),593,17],tZ=[0,1],tV=e("Could not revert a cut, please report."),tS=[0,1],tT=[0,1],tP=[0,0],tU=[0,1],tW=[0,0],tX=[0,0],tY=[0,1],tN=[0,e(fE),463,22],tO=e("projs"),tL=[0,1],tH=e(".] to avoid this."),tI=e(". Use [Derive Signature for "),tJ=e("Automatically inlined signature for type "),tz=e("_sig"),tA=[1,0],tB=e("_sig_pack"),tC=e("_var"),tD=[1,0],tE=e("_Signature"),tx=e("No signature to derive for non-dependent inductive types"),ty=e("Derive Signature"),tv=e(nE),tw=e(nE),tu=[0,e(fE),hO,10],tt=e("Cannot make telescope out of empty context"),tq=e("constrs_of_coq_sigma"),tG=e("Signature"),vD=e("Equations.Simplify"),vE=[0,1],vF=[0,1],vS=e(hN),vT=e(nQ),vU=e(no),vI=e("NoConfusionOut"),vJ=e("NoCycle"),vK=e("ElimTrue"),vL=e("ElimFalse"),vN=e(m9),vM=e(m$),vP=e(nr),vO=e(mQ),vQ=e(hR),vG=[0,e(hS),1162,19],vH=[0,1],vB=e("a product"),vu=[0,0],vp=[1,0],vq=[1,1],vr=e("Neither side of the equality is a variable."),vs=[1,0],vt=[1,1],vv=[0,0],vw=e("Could not infer a simplification step."),vo=e("[elim_true] The first hypothesis is not the empty type."),vm=e("[elim_true] The first hypothesis is not the unit type."),vn=[0,0,0],vi=e(fM),vj=e("[noConfusion] Cannot find an instance of NoCycle for type "),vk=[0,0,0],vl=e("[noCycle] Cannot infer a proof of "),vf=e("Expected a full application of [opaque_ind_pack_eq_inv]. Maybeyou did not solve completely a NoConfusion step?"),vg=e("[opaque_ind_pack_eq_inv] Anomaly: should be applied to a reflexivity proof."),vh=[0,0,0],vc=e(fM),vd=e("[noConfusion] Cannot find an instance of NoConfusion for type "),ve=[0,0,0],u2=e(fM),u3=e(fM),u4=e(" or NoConfusion for family "),u5=e("[noConfusion] Cannot simplify without UIP on type "),u6=e(" enable [Equations With UIP] to allow this"),u7=e("] if it requires uniqueness of identity proofs and"),u8=e("], or [Derive NoConfusion for "),u9=e("Either [Derive NoConfusionHom for "),u_=e(", which does not have a [NoConfusionHom] instance."),u$=e("[noConfusion] Trying to use a non-definitional noConfusion rule on "),va=[0,0,0],u0=e("[solution] cannot remove dependency in the variable "),uZ=e("[solution] The variable appears on both sides of the equality."),uV=[0,1],uY=[0,0,0],uX=e(" and the 'Equations With UIP' flag is off"),uW=e("[deletion] Cannot simplify without UIP on type "),uO=[0,0,0],uM=e(nc),uN=[0,0,0],uR=[0,0,0],uP=e(nc),uQ=[0,0,0],uS=e("If you see this, please report."),uI=e("The first hypothesis in the goal is not an equality."),uJ=e("The first hypothesis in the goal is not an equality between identical terms."),uK=e("The left-hand side of the first hypothesis in the goal is not a variable."),uL=e("The right-hand side of the first hypothesis in the goal is not a variable."),uH=e("The goal is not a let-in."),uG=e("The goal is not a product."),uD=[0,e(hS),321,12],uA=e("Unexpected mismatch."),uB=[0,e(hS),255,32],t_=e("depelim."),t$=e("apply_noConfusion"),ua=e("apply_noCycle_left"),ub=e("apply_noCycle_right"),uc=e("simplify_ind_pack"),ud=e("simplify_ind_pack_inv"),ue=e("opaque_ind_pack_eq_inv"),uf=e("simpl_sigma"),ug=e("simpl_sigma_dep"),uh=e("simpl_sigma_nondep_dep"),ui=e("simpl_sigma_dep_dep"),uj=e("pack_sigma_eq"),uk=e("simpl_uip"),ul=e("solution_left"),un=e("solution_left_dep"),up=e("solution_right"),ur=e("solution_right_dep"),uz=e("Equations.Simplify.CannotSimplify"),vx=e("Equations.Simplify.Blocked"),xJ=[0,e(bg),1026,9],xK=[0,e(bg),1046,7],x_=[0,e(bg),1307,13],x9=[0,e(bg),1308,24],x6=e("Defining programs, before simplify_evars "),x7=e("Defining programs "),x8=[0,e(bg),1273,4],x2=[0,e(bg),1197,28],x0=e("_obligations"),x1=[0,[0,0]],x3=[0,0],xU=e("_obligation_"),xR=e("Cannot handle admitted proof for equations"),xS=e("end_obligations"),xT=e("Defining the initial evars accoding to the proofs"),xQ=e("evar type"),xP=[0,0],xW=e(" refine them interactively"),xX=e('could not be solved automatically. Use the "Equations?" command to'),xY=e("Equations definition generated subgoals that "),xZ=e(mM),xM=e('Use the "Equations" command to define it.'),xN=e("Equations definition is complete and requires no further proofs. "),xO=e(mM),xL=[0,e(bg),1051,12],xH=[0,1],xB=[1,0],xC=e("functional"),xD=[0,0,0],xE=[1,0],xF=[0,0,0],xG=[1,0],xA=[0,e(bg),896,11],xz=[0,e(bg),870,15],xx=e("make_single_program: more than one program"),xu=[1,5],xv=e("_functional"),xr=e(" mutually with other programs "),xs=e("Cannot define "),xt=e("make_programs"),xw=[1,0],xq=[1,5],xp=[1,5],xh=e("Simplifying term:"),xi=e("... in context:"),xj=e("... named context:"),xk=e("Finished simplifying"),xl=[0,1],xm=[0,1],xn=e("Should not fail here, please report."),xf=[0,e(bg),488,7],xg=[0,[0,0,2],0],xo=[0,0],xe=[0,2],xb=e("H"),xc=[0,e(bg),389,20],wT=e("*impossible case*"),wE=e(fD),wF=e(cj),wG=e(" (where context length : "),wH=e(cj),wI=e("(arity: "),wJ=e(cj),wK=e("(where_term: "),wL=e(cj),wM=e("(path: "),wN=e(") "),wO=e("(program type: "),wB=e("*raised an exception"),wC=e(bv),wD=e(ni),wP=e(nl),wQ=e(bv),wR=e(fD),wS=e(" :=! "),wU=e(nl),wV=e(bv),wW=e(" split: "),wX=e("Mapping "),wY=e("New problem to problem substitution is: "),wZ=e("Revctx is: "),w0=e(" eliminating "),w1=e(" for type "),w2=e("New problem: "),w3=e(" refine args "),w4=e(" refine term "),w5=e(" in "),w6=e(dZ),w7=e(dZ),w8=e(bv),w9=e(fD),w_=e(mG),w$=e("Error pretty-printing splitting"),wq=e(cj),wr=e("nested but not directly recursive"),wv=e("mutually recursive on "),ww=e("mutually recursive on ? "),wx=e("nested on "),wy=e("nested on ? "),wz=e("wellfounded"),wA=e("not recursive"),ws=e(" ( "),wt=e(bv),wu=e(bv),wn=e(fH),vW=e(d3),vV=e(hF),vX=[0,e(bg),44,9],yb=[0,0,0,0,0],yc=[0,0,0],yd=[0,0,0],y5=e("splitting failed for "),y3=e("covering is not faithful to user clauses, trying the next one"),y2=e("covering failed to produce a splitting in one of the branches,trying the next one"),y4=e("covering succeeded"),y1=e("splitting succeded for "),y0=e("trying next blocker "),yZ=e("blockers are: "),yS=e(" extpats "),yT=e(" with problem "),yU=e("Launching covering on "),yV=e(mG),yW=e("Matching "),yY=e("got stuck"),y6=e("Maybe unification is stuck as it cannot refine a context/section variable."),y7=e(" to match a user pattern."),y8=e(" of (reduced) type "),y9=e("Unable to split variable "),y_=e(nn),yX=e(m7),y$=e(mT),za=e(hJ),zn=e(d3),zb=e("clause_"),zc=e("This clause has an empty pattern, it cannot have a right hand side."),zd=e(bx),zg=e("This pattern cannot be empty, it matches value "),zh=e(bx),ze=e("This variable does not have empty type in current problem"),zf=e(bx),zi=e(" matched but its interpretation failed"),zj=e("Clause "),zk=e(nn),zl=e("Empty clauses should have at least one empty pattern."),zm=e(bx),zo=e("Non-exhaustive pattern-matching, no clause found for:"),zp=e(hA),zH=e("And the user patterns are: "),zI=e("Problem is "),zJ=e("Non-matching clause in with subprogram:"),zK=[0,e(bx)],zL=[0,e(cM),1238,56],zG=e("unknown"),zy=e("This pattern must be innaccessible and equal to "),zz=[0,e(bx)],zu=e("Unification failed with "),zv=e("should be unifiable with "),zw=e("Incompatible innaccessible pattern "),zx=[0,e(bx)],zs=e("is not inaccessible, but should refine pattern "),zt=e("Pattern "),zq=e("Unbound variable "),zr=e(cl),zA=e("'s type is empty"),zB=e("Cannot show that "),zC=e(bx),zP=[0,e(cM),1172,14],zD=e(d6),zE=[0,1],zF=[0,0],zM=e("And clauses: "),zN=e("Unable to build a covering for with subprogram:"),zO=e(hA),zQ=[0,0],zR=e("Unable to build a covering for:"),zS=e(hA),yQ=[3,1],yO=e("The carrier type of the recursion order cannot depend on the arguments"),yP=e(nX),yM=[0,e(cM),827,11],yN=[0,e(cM),840,11],yL=[12,0,0,0],yG=e(" found"),yH=e("No argument named "),yI=e("struct_index"),yJ=[0,0],yK=[0,[0,0]],yF=e("Programs: "),yB=[0,e(cM),641,32],yC=e("Mutual well-founded definitions are not supported"),yD=e(cl),yE=[0,e(cM),649,11],yz=e("Unused clause "),yA=e(bx),yw=e("In context: "),yv=e(dZ),yt=e("named_of_rel_context"),yp=[0,e(cM),502,19],ym=e("Ill-typed instance in interp_constr_in_rhs"),yk=[0,[0,0],0,0],yi=[0,0,0],yg=e("This clause has not enough arguments"),yh=e(bx),ye=e("Too many patterns in clauses for this type"),yf=e(bx),x$=e("Equations.Covering.Conflict"),ya=e("Equations.Covering.Stuck"),yR=e("Equations.Covering.UnfaithfulSplit"),Ad=[0,0,1],z_=e("c"),z$=e(hE),Aa=e("step"),Ab=e("rec"),Ac=e("below"),Ae=e("Below_"),Af=[1,0],Ag=e("below_"),Ah=[1,0],z4=[0,e("src/subterm.ml"),238,55],z1=e("_subterm"),z2=e("well_founded_"),z7=e(de),z8=e(cO),z3=[1,0],z5=[0,0],z6=[0,0],zZ=e(d3),z0=e(d3),zY=e("_direct_subterm"),zU=e("not implemented"),zV=e(cO),zW=e(de),zX=e("z"),z9=e(hG),Ai=e(fK),Ap=e("_eqdec"),An=[1,10],Ao=e("_EqDec"),Ak=e(cO),Al=e(de),Aj=e("param"),Aq=e("EqDec"),AS=e("refining with"),AO=e("Generated clauses: "),AP=[0,1,0,0,0],AQ=[0,0,0],AR=e("dummy"),AK=[0,e("src/depelim.ml"),376,19],AL=[0,1],AM=[12,0,0,0],AN=[0,0,0],AT=e("Could not eliminate variable "),AU=e("No such hypothesis: "),AJ=e("Specialization not allowed on dependent hypotheses"),AI=e("Nothing to do in hypothesis "),AG=e("destPolyRef"),AE=[0,0],AF=[0,0],AB=e("DependentElimination_"),Ax=e(hE),Ay=e(hE),Az=e("_dep_elim"),AA=[1,7],Av=[0,0],Aw=[0,0],Au=[0,1],At=[0,1],As=e("Equations.Depelim.Seen"),AD=e("DependentElimination"),A9=e("Not enough products in "),A_=e("Cannot do a fixpoint on a non inductive type."),De=[0,e(aQ),1136,14],Df=[0,0],Db=e("solve methods"),Dc=e("apply eliminator"),Dd=e("prove_methods"),Da=e(nO),Dh=e("applyind"),Dg=e("exception"),C8=e("Proving unfolding lemma of: "),C9=[0,1],C_=e("and of: "),C$=[0,1],CT=e("extensionality proof"),CS=e("program"),CQ=[1,[0,1,0]],CR=[1,[0,1,0]],CW=e(mP),CU=e("program fixpoint"),CV=e("program before unfold"),C6=e("refine after replace"),C5=e("Unexpected unfolding lemma goal"),C3=e("Unexpected unfolding goal"),CX=[0,e(aQ),1013,29],C1=[0,e(aQ),1047,9],CZ=e("compute rhs"),C0=e("compute"),C4=e(nq),C7=e("refined"),C2=[0,e(aQ),1060,14],CP=e("solve_eq"),CN=[1,[0,1,0]],CO=[1,[0,1,0]],CJ=[0,0,0],CK=[0,0],CL=e(hF),CI=[0,e(aQ),875,7],CH=e(nv),CF=e(" and cannot be proven by induction. Consider switching to well-founded recursion."),CG=e(m8),Cy=[0,e(aQ),791,25],Cz=e("after mut -> nested and mut provable"),CA=e(mP),CB=e("splitting nested"),CC=e("assert mut -> nest first subgoal "),Cw=e("and cannot be proven by induction"),Cx=e(m8),Ct=[0,0,1],Cs=e("Proof of mutual induction principle is not guarded, trying induction"),Cu=e("induction on last var"),Cv=e("induction"),Cr=e(nO),CE=[0,0,0],CD=[0,e(aQ),822,13],Cp=e(hL),Co=e(mT),Ck=e(cL),Cl=e(hD),Cm=e(hT),Cn=e(hM),Ci=e(cL),Cj=e(hV),Bu=e("solving nested premises of compute rule"),Bx=e(" lctx "),By=e(" rec args "),Bz=e("Fixpoint on "),Bv=[0,e(aQ),383,23],BB=[0,e(aQ),399,33],BC=[0,0],Bw=e(ns),BA=e("struct fix"),BD=e(nX),BG=[0,e(aQ),336,32],BH=[0,0],BE=e(ns),BF=e("struct fix norec"),Cc=e("Unexpected refinement goal in functional induction proof"),Cd=e("clear body"),Ce=[0,0],Cf=e("convert concl"),Cg=e("letin"),Ca=e("Unexpected goal in functional induction proof"),B3=e(": "),B4=e("Type of induction principle for "),BO=[0,e(aQ),nu,36],BP=e(" assoc "),BQ=e(" type: "),BR=e(hH),BS=e("Unfolded where "),B5=e("Mismatch between hypotheses in named context and program"),BT=e(mR),BU=e("New where term"),BV=e("Unfolded where substitution:  "),B6=e("context "),B7=e(" final term "),B8=e(" subst "),B9=e(hH),B_=e(" where "),BW=e("moving section id"),BX=e("one where"),BY=e("Couldn't find associated args of where"),BZ=e(mR),B0=e(hH),B1=e(" where: "),B2=e("Found path "),B$=[0,e(aQ),587,19],BI=e("solving nested recursive call"),BJ=e("solving premises of compute rule"),BK=e("applying compute rule"),BL=e("wheretac"),BM=e("compute "),BN=e("compute empty"),Cb=e(nq),Ch=e(d6),Bs=[0,e(aQ),284,21],Bt=[0,1],Br=[0,e(aQ),279,13],Bp=[0,20],Bq=e("eauto with below"),Bo=[0,e(aQ),219,4],Bg=e("Fixpoints should be on the same mutual inductive declaration."),Bh=e(" already used in the environment"),Bi=e("Name "),Bj=[0,e("Logic.prim_refiner")],Bk=[0,e(aQ),177,29],Bm=e("fix_"),A$=e(" subgoal"),Ba=e(dd),Bb=e(" index"),Bl=e(" indices"),Bc=e(dZ),Bd=e(" name"),Be=e("Cannot apply mutual fixpoint, invalid arguments: "),Bf=[0,e(nW)],A5=e(cL),A6=e("Trying "),A4=e(m7),A7=e("Couldn't rewrite"),A2=e("_wf_obligations"),A1=[0,e(mF),[0,e(fK),[0,e("rec_decision"),0]]],AW=e(fK),AV=e("Helper not found while proving induction lemma."),Cq=e("Equations.Principles_proofs.NotGuarded"),DD=[0,1],EW=e(mX),EX=e(nD),ES=e("_mut"),EN=[0,e(nh),[0,e(nt),0]],EO=[0,1],EP=[0,e(nh),[0,e(nt),0]],EQ=[0,1],EV=[0,1],ET=[0,1],EU=e(hC),EM=e(mX),EL=e("_refinement_"),EK=e(hC),EI=e("Typing equation "),EJ=e("Typing constructor "),EG=e(" no alias "),EH=e(nm),EE=e("alias: "),EF=e(nm),EC=e("and "),ED=e("Definining principles of: "),Ez=[0,0,0],Es=e(hB),Eu=e(hB),Ev=e(hB),Et=e("FunctionalInduction_"),Er=e(hC),Eq=e("_graph_correct"),Ey=[0,e(ci),nI,12],Ew=e(nw),Ex=e(nw),Eo=e("Functional elimination principle type-checked"),En=e("Type-checking elimination principle: "),Ek=e("FunctionalElimination_"),El=e("Error while typechecking elimination principle type: "),Em=e("_elim"),Ec=[0,e(ci),1091,26],Ed=[0,0,0],Ee=[0,0,0],Ef=[0,0,0],Eg=e("where_instance: "),Eh=[0,0,1],Ei=[0,1,1],Eb=[0,1],Ea=[0,0,0,0],D9=e(hF),D_=[0,1],D$=[0,0,0],D4=[0,-1],D5=[0,e(ci),828,17],D6=e("_unfold_eq"),D7=[0,0,0],D8=[0,0,0],D3=[0,1],D2=e("Declaring wf obligation "),D0=e("Replacing variable with "),D1=e("Fixed hint "),DZ=[1,[0,1,0]],DV=e(fD),DW=e(bv),DX=e(ni),DT=[0,1,0],DR=e("More statemsnts than declarations while computing eliminator"),DL=e(nv),DI=e("abs"),DJ=[0,0,0],DK=e(d6),DP=e("refine_eq"),DQ=e(d6),DN=[0,e(ci),nu,37],DO=[0,e(ci),521,15],DM=[0,0],DH=[0,e(ci),352,10],DF=[0,e(ci),190,15],DE=[0,0,0],DC=e("Hind"),DB=[0,0,0],Dz=[0,e(ci),co,12],Di=[0,0],Dj=[0,1],Dp=e("EQUATIONS_REWRITE_RULE"),Dx=e("EQUATIONS_OPACITY"),E7=e(hz),E5=e("target"),E8=e(hz),E6=e(hz),E4=e(m_),E3=[0,e(mH),d2,63],E0=e("Could not find where clause unfolding lemma "),E1=e(nD),E2=e("_where_rev"),EY=[0,e(mH),44,65],EZ=e("_eq"),Ft=[0,e(nM),262,83],Fu=e("Hom"),Fi=e(hQ),Fg=e(nd),Fh=e("1"),Fj=[0,0,0],Fe=e(cO),Ff=e(de),Fw=[0,0],Fx=[0,1],Fk=e(de),Fl=e(cO),Fm=[0,0,0],Fn=e("NoConfusionHom_"),Fo=[0,0],Fp=[0,1],Fq=[0,0,0],Fr=[0,0,0],Fs=[0,0],Fv=[0,0,0],E9=e(hJ),E_=e(d3),E$=e("noConfusion"),Fa=e("Package_"),Fb=e(mV),Fc=[0,e(nM),81,11],Fd=[0,0],Fz=e("NoConfusionHom"),FA=e(cO),FB=e(de),FF=[0,0],FG=[0,1],FC=e("NoConfusion_"),FD=[1,0],FE=e(hJ),FH=e(mV),FN=[1,0],FP=e("Products do not match"),FO=e("Second-order matching failed"),FM=e("Couldn't find a second-order pattern to match"),FJ=[0,e("src/extra_tactics.ml"),19,11],FK=e("core"),FI=e("f"),Mk=[2,0],Mf=[0,1],Mc=[0,0],Li=e("Not a section variable or hypothesis"),Lb=[0,0,0],K6=[0,0,0],KV=e(dc),KU=e(dc),KB=[0,[0,[0,1,0]],1],J4=[0,0,0],JZ=[0,1],JT=[0,1],JJ=[0,0,0],JD=[0,1],Jx=[0,0],Hu=[0,1,0],Hq=[0,1,1],Hm=[0,0,1],Hi=[0,0,0],GR=e("No generalization needed"),GE=[0,0],FU=e(mU),FW=e(mU),FZ=e(m1),F1=e(m1),F5=e(mJ),F7=e(mJ),F_=e("sigma"),F$=e(hY),Gb=e("pattern_sigma"),Gd=[0,e(hU),0],Gg=e(hU),Gi=e(hU),Gl=e("uncurry_hyps"),Gn=e("curry_hyps"),Gt=e(mS),Gv=e(mS),Gy=e(hY),Gz=e(fF),GB=e("dependent_pattern"),GF=e("from"),GG=e(hY),GH=e(fF),GJ=e("dependent_pattern_from"),GM=e(m4),GO=e(m4),GS=e(m2),GU=e(m2),GY=e(m6),G0=e(m6),G4=e("simpc"),G8=e(nU),G_=e(nU),Hj=e("noind"),Hn=e("ind"),Hr=e("eqns"),Hv=e("noeqns"),Hx=e("equation_user_option"),HI=e(cj),HK=e(nz),HN=e("equation_options"),HY=e("lident"),H1=e(nx),H3=e(nx),H5=e(nS),H8=e(nS),H9=e(nk),Ia=e(nk),Ib=e(cl),Ie=e(cl),Ig=e(mZ),Ij=e(mZ),Ik=e(nP),Il=e("identloc"),Im=e("equation"),In=e("pat"),Io=e(d6),Ip=e("wf_annot"),Iq=e("proto"),Ir=e("where_rhs"),Is=e("where_clause"),It=e("wheres"),Iu=e("local_where_rhs"),Iv=e("local_where"),Iw=e("local_wheres"),Ix=e("rhs"),Iy=e("sub_equations"),IB=[0,0,[0,[2,0]]],II=[0,[0,e(m0)]],IN=[0,[0,e("]")]],IO=[0,[0,e(dc)]],IP=[0,0,[0,[0,e("[")]]],IS=[0,[0,e(cn)]],IT=[0,[0,e(m0)]],IU=[0,[0,0,[0,[0,e(nP)]]],[0,[0,e(ck)]]],IV=[0,e(nd)],I3=[0,[0,e(dc)]],I4=[0,0,[0,[0,e(dc)]]],Jb=[0,[0,e(fN)]],Jf=[0,[0,0,[0,[0,e(nT)]]],[0,[2,[0,e("wf")]]]],Jh=[0,[0,0,[0,[0,e(nT)]]],[0,[0,e("struct")]]],Jn=[0,[0,e(ch)]],Jo=[0,[0,e(fH)]],Jt=[1,[1,0,[0,[0,e(fH)]]],[0,[2,0]]],Jv=[0,[0,e(ch)]],JB=[0,0,[0,[0,e(fG)]]],JE=[0,0,[0,[0,e(db)]]],JP=[1,[1,0,[0,[0,e(fH)]]],[0,[2,0]]],JR=[0,[0,e(ch)]],JX=[0,0,[0,[0,e(fG)]]],J0=[0,0,[0,[0,e(db)]]],J8=[0,0,[0,[0,e(fP)]]],Kc=[1,0,[0,[0,e(ch)]]],Ke=[1,0,[0,[0,e(d4)]]],Kj=[1,0,[0,[0,e(ch)]]],Kl=[1,0,[0,[0,e(d4)]]],Kp=[1,0,[0,[0,e(db)]]],Ku=[0,[0,e(cn)]],Kv=[0,0,[0,[0,e(ck)]]],KG=e(hN),KH=e(a3),KJ=e("Define_equations_refine"),KO=e(a3),KS=e("Define_equations"),K2=e("elim_patterns"),K7=e("as"),K9=e(mW),K_=e(fF),Lc=e(mW),Ld=e(fF),Lf=e("dependent_elimination"),Lj=e(nR),Ll=e(nR),Lo=e(m5),Lq=e(m5),Lt=e("eqns_specialize_eqs_block"),Lw=e(nJ),Ly=e(nJ),LC=e(mL),LE=e(mL),LI=e("for"),LK=e(fI),LO=e(fI),LP=e(ng),LS=e(ng),LT=e("simplification_rule_located"),LU=e("simplification_rule"),LV=e("simplification_step"),LW=e("direction"),L6=[0,0,[0,[0,e(hN)]]],L8=[0,0,[0,[0,e(nQ)]]],L_=[0,0,[0,[0,e(no)]]],Md=[0,0,[0,[0,e(m$)]]],Mg=[0,0,[0,[0,e(m9)]]],Mi=[0,0,[0,[0,e(ne)]]],Ml=[0,0,[0,[0,e(hR)]]],Mn=[0,[0,e(cn)]],Mo=[0,[0,0,[0,[0,e(hR)]]],[0,[0,e(ck)]]],Mt=[0,0,[0,[0,e(mQ)]]],Mv=[0,0,[0,[0,e(nr)]]],MD=e("simplification_rules"),MG=[0,e(hW),0],MJ=e(hW),ML=e(hW),MP=e(nW),MR=e("mutual_fix"),MS=e(nb),MT=e(nK),MU=e(m3),MV=e(hG),MW=e(mY),MX=e(nN),MY=e(nV),MZ=e(nC),M0=e(nj),M1=e(mK),M2=e(a3),M3=e("equations_plugin_mod"),M4=e(nA),qV=p.Pputils,pW=p.Recordops,oH=p.Flags,tK=p.Patternops,xV=p.Proof,yl=p.Implicit_quantifiers,yj=p.Glob_ops,Am=p.Safe_typing,CY=p.Abstract,CM=p.Cc_plugin__Cctac,ER=p.Indrec,Dt=p.Mod_subst,DA=p.Stdlib__map,FL=p.Eauto,KT=p.Goal;function
nY(d,c,b){return a(d,a(c,b))}function
nZ(d,c,b){var
e=b[1],f=a(c,b[2]);return[0,a(d,e),f]}function
n0(a){return a}function
dh(b){var
d=b[1];return[0,d,a(c[2][1],b[2])]}function
cq(d,a){var
e=a[1];return[0,e,b(c[2][2],d,a[2])]}var
bL=[0,0],d7=[0,1],d8=[0,0],d9=[0,1],d_=[0,1];function
n1(b){if(b){var
c=a(d[3],n2);return g($[6],0,0,c)}bL[1]=b;return 0}var
n5=[0,1,n4,n3,function(a){return 0},n1];b(by[4],0,n5);function
n6(a){bL[1]=a;return 0}var
n9=[0,1,n8,n7,function(a){return bL[1]},n6];b(by[4],0,n9);function
n_(a){bL[1]=a;return 0}var
ob=[0,0,oa,n$,function(a){return bL[1]},n_];b(by[4],0,ob);function
oc(a){d8[1]=a;return 0}var
of=[0,0,oe,od,function(a){return d8[1]},oc];b(by[4],0,of);function
og(a){d7[1]=a;return 0}var
oj=[0,0,oi,oh,function(a){return d7[1]},og];b(by[4],0,oj);function
ok(a){d9[1]=a;return 0}var
on=[0,0,om,ol,function(a){return d9[1]},ok];b(by[4],0,on);function
oo(a){d_[1]=a;return 0}var
or=[0,0,oq,op,function(a){return d_[1]},oo];b(by[4],0,or);var
X=[0,0];function
os(a){X[1]=a;return 0}var
ov=[0,0,ou,ot,function(a){return X[1]},os];b(by[4],0,ov);function
aM(d){var
c=X[1];if(c){var
e=a(d,0);return b(L[9],0,e)}return c}function
fQ(f,e){var
c=a(w[2],0),h=g(f,c,a(l[17],c),e);return b(d[48],hZ[7][1],h)}function
fR(d,c,b,a){o(ae[4],d,c,b,a);return 0}function
h0(c,b,a){g(ae[3],c,b,a);return 0}function
fS(j,i,h){try{var
e=function(d,e){h0(e,i,a(k[10][1][4],d));var
f=a(k[10][1][3],d);function
g(b){return fR(e,i,b,a(k[10][1][4],d))}b(M[13],g,f);return b(c[aP],d,e)};g(f[17][16],e,h,j);var
p=0;return p}catch(e){e=v(e);var
l=a(h1[1],e),m=b(c[x],h,j),n=a(A[cp][7],m),o=a(d[49],n);g(fT[3],ow,o,l);throw e}}function
ox(d){var
b=a(c[9],G[8]);return hw(P[5],0,0,0,0,0,0,0,ax[34],l[16],b)[2]}function
F(b){return a(i[72][7],b)}function
ah(a){return b(i[72][1],0,a)}function
h2(c){var
d=[0,c,0];function
e(g,c){var
d=c[1],e=b(f[18],c[2],[0,d,0]);return[0,a(f[17][6],d),e]}return g(f[17][16],e,c,d)[2]}function
h3(e){return function(g,f){var
c=g,a=f;for(;;){if(a){var
h=a[2],d=b(e,c,a[1]);if(d)return d;var
c=c+1|0,a=h;continue}return 0}}}function
oy(a){return g(f[19][7],a,0,a.length-1-1|0)}function
oz(a){return b(f[19][58],a.length-1-1|0,a)}function
oA(e,d){return function(f){var
a=f;for(;;){if(a){var
c=a[1],g=a[2],h=c[1];if(b(e,d,c[2]))return h;var
a=g;continue}throw O}}}function
oB(c,b){var
d=0;function
e(d,b){var
e=a(c,d);function
f(a){return[0,a,b]}return g(M[22],f,b,e)}var
h=g(f[19][18],e,b,d);return a(f[19][12],h)}function
a_(e,c){try{var
j=b(P[9],e,c);return j}catch(e){var
f=a(z[39],c),h=a(d[3],oC),i=b(d[12],h,f);return g($[3],0,0,i)}}function
bh(a,c){var
b=a_(a[1],c),d=b[2];a[1]=b[1];return d}function
fU(c){var
d=b(J[17],oD,c);return a(h4[2],d)}function
H(a){return[q,function(b){return fU(a)}]}function
d$(b,a){return bh(a,fU(b))}function
fV(c){var
d=b(ay[32],0,c),e=a(az[14],d);return a(ea[2],e)}function
cP(d,a,c){var
b=o(ae[2],oE,d,a[1],c),e=b[2];a[1]=b[1];return e}function
h5(z,j,i,f,e){var
r=j?j[1]:0,h=a(w[2],0);if(f)var
k=f[1],s=o(ae[2],0,h,i,k)[1],m=o(ae[4],h,s,e,k);else
var
m=o(ae[2],0,h,i,e)[1];var
d=a(l[bJ],m),n=g(c[5],0,d,e),t=b(c[5],0,d),p=b(M[16],t,f),u=a(aB[27],n),v=g(M[22],aB[27],ab[2][1],p),x=b(ab[2][7],u,v),q=b(l[na],d,x),y=[0,b(l[d0],r,q)];return[0,d,q,at(bM[2],0,0,0,p,y,0,n)]}function
aV(h,o,n,g,m,k){var
f=h5(oF,[0,g],m,n,o),i=f[1],p=f[2],e=y(bM[3],0,0,h,0,[0,[0,f[3]],k]),q=a(j[1][8],h),r=b(J[17],q,oG),s=a(d[3],r),t=L[6];function
u(a){return b(t,0,a)}b(oH[21],u,s);if(g){var
v=a(l[153],p),w=a(ab[36][4],v),x=[0,e,a(c[2][1],w)];return[0,e,[0,i,a(c[25],x)]]}return[0,e,[0,i,a(c[24],e)]]}function
h6(f,a,e,d,c){var
g=a?a[1]:0,b=h5(f,[0,g],e,d,c);return[0,b[1],b[3]]}function
di(l,k,j,e,d,i){var
f=b(ac[15],d,i),m=f[2],n=a(M[7],f[1]),p=b(c[45],n,e),g=aV(l,p,[0,b(c[44],m,e)],k,j,oI),h=g[1],q=g[2],r=o(ac[5],d[1],aK[4],1,[1,h]);a(ac[6],r);return[0,h,q]}var
dj=H(oJ),dk=H(oK),oM=H(oL);function
fW(e,d){if(0===d){var
f=t(dj),j=u===f?dj[1]:q===f?a(r[2],dj):dj;return b(P[9],e,j)}var
g=t(dk),k=u===g?dk[1]:q===g?a(r[2],dk):dk,h=b(P[9],e,k),l=h[2],i=fW(h[1],d-1|0),m=i[1];return[0,m,a(c[23],[0,l,[0,i[2]]])]}function
eb(d){var
b=a(G[29],d);if(9===b[0]){var
c=b[2];if(1===c.length-1)return eb(c[1])+1|0}return 0}function
ec(e,d,c){var
f=a(ax[10],c),g=a(A[77],f),h=a(j[1][10][35],g),i=b(j[1][10][7],e,h);return b(av[27],d,i)}function
oN(d,c,b){return ec(d,c,a(C[5],b))}var
bz=H(oO),a4=H(oP),bi=H(oQ),fX=H(oR),h7=H(oS),aw=[q,function(n){var
e=a(w[2],0),f=t(a4),h=a(l[17],e),i=u===f?a4[1]:q===f?a(r[2],a4):a4,g=b(P[9],h,i),d=g[1],j=y(T[2],0,0,e,d,g[2]),k=b(c[69],d,j)[2],m=b(c[1][2],d,k);return a(aE[12],m)}],bZ=H(oT),cQ=H(oU),h8=H(oV),dl=H(oW),h9=H(oX),h_=H(oY),o0=H(oZ),o2=H(o1),cr=H(o3),cs=H(o4),ed=H(o5),fY=H(o6),fZ=H(o7),h$=H(o8),ia=H(o9),ib=H(o_),pa=H(o$),dm=H(pb),dn=H(pc),cR=H(pd),f0=H(pe),f1=H(pf),ic=H(pg),pi=H(ph),id=H(pj),ie=H(pk),ig=H(pl),ih=H(pm),ii=H(pn),ij=H(po),ik=H(pp),il=H(pq),im=H(pr),io=H(ps),pu=H(pt),f2=H(pv),px=H(pw),pz=H(py);function
aR(d,b){var
c=t(b),e=u===c?b[1]:q===c?a(r[2],b):b;return a_(d,e)}function
ap(b,d){var
c=t(b),e=u===c?b[1]:q===c?a(r[2],b):b;return bh(d,e)}function
ip(f,b,e){var
d=t(b),h=u===d?b[1]:q===d?a(r[2],b):b;return g(c[a2],f,h,e)}function
f3(b,e){var
d=o(l[hK],0,0,b[1],e),f=d[2];b[1]=d[1];return a(c[14],f)}function
pA(c){var
b=t(aw),d=u===b?aw[1]:q===b?a(r[2],aw):aw;return f3(c,d)}function
ct(h,d,b,g){var
e=t(b),i=u===e?b[1]:q===e?a(r[2],b):b,f=a1(c[d5],0,0,0,h,d[1],i),j=f[2];d[1]=f[1];return a(c[23],[0,j,g])}function
ee(d,a,c){var
b=at(cu[6],0,pC,0,pB,d,a[1],c),e=b[2];a[1]=b[1];return e}function
b0(b,a,e,d,c){return ct(b,a,a4,[0,ee(b,a,e),d,c])}function
iq(d,b,g,f,e){if(g){var
i=g[1],h=t(bi),j=[0,ee(d,b,f),e],k=u===h?bi[1]:q===h?a(r[2],bi):bi,l=[0,a(c[38],[0,k,i]),j];return a(c[23],l)}return ct(d,b,bi,[0,ee(d,b,f),e])}var
dp=0;function
aC(e,c){try{var
j=[0,b(ay[29],0,e),c],k=[3,b(af[1],0,j)],l=af[1],m=[29,function(a){return b(l,0,a)}(k)],n=a(ef[26],m);return n}catch(c){c=v(c);if(c===O){var
f=a(d[3],e),h=a(d[3],pD),i=b(d[12],h,f);return g($[3],0,0,i)}throw c}}function
dq(d,c){var
e=b(ac[11],d,c);return a(M[7],e)[2][1]}function
ir(b){var
a=[0,b],c=d$(pE,a),d=dq(a[1],c);return[0,a[1],d]}function
is(b){var
a=[0,b],c=d$(pF,a),d=dq(a[1],c);return[0,a[1],d]}function
it(a){var
b=d$(pG,a);return dq(a[1],b)}var
cS=H(pH),iu=H(pI),dr=H(pJ),a5=H(pK),aW=H(pL),bN=H(pM),ds=H(pN),dt=H(pO),f4=a(j[1][6],pP),iv=H(pQ),cv=H(pR);function
iw(a){return d$(pS,a)}var
pT=[q,function(f){var
b=t(dt),c=0,d=u===b?dt[1]:q===b?a(r[2],dt):dt,e=[0,[0,0,[1,a(aS[8],d)]],c];return a(s[69],e)}],ai=H(pU),aj=H(pV);function
ix(c){var
d=a(aS[8],c),e=a(pW[9],d),f=a(M[7],e);return b(j[62][2],f,0)}var
aq=[q,function(e){var
b=H(pX),c=t(b),d=u===c?b[1]:q===c?a(r[2],b):b;return ix(d)}],ak=[q,function(e){var
b=H(pY),c=t(b),d=u===c?b[1]:q===c?a(r[2],b):b;return ix(d)}];function
pZ(e,g){var
a=g;for(;;){var
h=b(A[57],e,a),f=b(A[60],e,h),d=b(c[3],e,f);switch(d[0]){case
6:var
a=d[3];continue;case
8:var
a=d[4];continue;case
9:var
a=d[1];continue;default:return f}}}function
ag(a){var
b=a[3],c=a[2],d=a[1];return c?[1,d,c[1],b]:[0,d,b]}function
eg(e,i,d){function
j(e,d){if(d){var
l=d[2],f=a(k[10][1][20],d[1]),m=f[3],n=f[2],o=f[1],p=j(e-1|0,l),q=g(c[h][2],i,e,m),r=b(c[h][2],i,e);return[0,ag([0,o,b(M[16],r,n),q]),p]}return 0}return j(a(k[10][4],d)+e|0,d)}function
aT(b,a){return eg(0,b,a)}function
p0(d){var
e=a(c[h][1],1);return b(f[17][68],e,d)}function
f6(t,k,e){var
y=[0,j[1][10][1],j[19][1]];function
z(c,e){var
i=c[2],k=c[1];try{var
q=a(aK[15],e),f=q}catch(c){c=v(c);if(c!==O)throw c;var
l=a(d[3],e),m=a(d[3],p2),n=b(d[12],m,l),f=g($[6],0,p3,n)}var
h=a(aK[14][18],f),o=h[1],p=b(j[19][7],h[2],i);return[0,b(j[1][10][7],o,k),p]}var
q=g(f[17][15],z,y,t),A=k?b(C[16],e,k[1][1]):a(C[4],e),m=a(C[2],e),u=a(C[5],e),w=q[2],x=q[1];function
h(e){var
d=b(c[3],m,e);switch(d[0]){case
1:var
k=d[1];if(b(j[1][10][3],k,x)){var
n=b(ax[45],k,u);return n?[0,1,a(c[9],n[1])]:[0,0,e]}break;case
9:var
o=d[2],p=d[1],q=h(p);if(0===q[1]){var
z=function(f,c,a){var
b=c[2],d=c[1];if(d)return[0,d,[0,a,b]];var
e=h(a);return 0===e[1]?[0,0,[0,a,b]]:[0,1,[0,e[2],b]]},r=g(f[19][48],z,p1,o),A=r[2];if(r[1]){var
B=a(f[17][9],A),C=[0,p,a(f[19][12],B)];return[0,1,a(c[23],C)]}return[0,0,e]}var
D=a(c[23],[0,q[2],o]);return[0,1,b(N[27],l[16],D)];case
10:var
s=d[1],t=s[1],E=s[2];if(b(j[19][3],t,w)){var
F=[0,t,b(c[2][2],m,E)],G=b(ax[65],u,F);return[0,1,a(c[9],G)]}break}var
i=[0,0];function
v(a){if(i[1])return a;var
b=h(a),c=b[2];i[1]=b[1];return c}var
y=g(c[bI],m,v,e);return[0,i[1],y]}var
p=h(A),r=p[2];if(p[1]){if(k){var
B=k[1],D=a(s[48],r),E=o(s[55],p4,0,D,B);return b(i[72][7],E,e)}var
F=g(s[3],p5,r,2);return b(i[72][7],F,e)}var
G=a(d[3],p6);return g(n[23],0,G,e)}function
iy(d){var
c=d;for(;;){var
b=a(G[29],c);switch(b[0]){case
9:var
c=b[1];continue;case
10:var
e=a(j[17][8],b[1][1]);return a(j[6][7],e);default:throw[0,I,p7]}}}var
iz=a(f[17][68],iy),p9=b(f[17][68],j[1][6],p8),iA=a(j[5][4],p9);function
p_(c){var
d=a(j[6][4],c);return b(j[13][1],[0,iA],d)}function
iB(c){var
d=b(af[1],0,[1,[0,c]]),e=a(E[4],eh[1]);return[0,b(E[7],e,d)]}function
p$(c,a){var
d=[0,iB(a),[0,[1,[0,c]],0]],e=[0,b(ay[29],0,qa),d],f=[3,b(af[1],0,e)];return[29,b(af[1],0,f)]}function
qb(e,d,c,a){var
f=[0,iB(c),[0,[1,[0,d]],[0,[1,[0,e]],[0,[1,[0,a]],0]]]],g=[0,b(ay[29],0,qc),f],h=[3,b(af[1],0,g)];return[29,b(af[1],0,h)]}function
qd(a){return aC(qe,0)}function
iC(a){return aC(qf,0)}function
ei(a){return aC(qg,0)}function
iD(a){return aC(qh,0)}function
iE(a){return aC(qi,0)}function
iF(a){return aC(qj,0)}function
iG(a){return aC(qk,0)}function
iH(a){return aC(ql,0)}function
f7(a){return aC(qm,0)}function
iI(a){return aC(qn,0)}function
iJ(a){return aC(qo,0)}function
ej(a){return[2,b(ay[32],0,a)]}function
qp(e){var
b=a(h4[2],qq);if(1===b[0])return a(j[17][7],b[1]);var
c=a(d[3],qr);return g($[3],0,0,c)}var
b1=a(du[3],qp);function
qs(d){var
b=t(b1),c=u===b?b1[1]:q===b?a(r[2],b1):b1;return a(j[10][7],c)}var
ek=a(du[3],qs);function
cx(d){var
c=t(ek),e=b(J[17],qt,d),f=u===c?ek[1]:q===c?a(r[2],ek):ek;return b(J[17],f,e)}function
f8(a){return aC(qu,[0,ej(a),0])}function
qv(a){var
b=[0,ej(a),0];return aC(cx(qw),b)}function
qx(a){var
b=[0,ej(a),0];return aC(cx(qy),b)}function
qz(a){return aC(cx(qA),0)}function
iK(a){var
b=[0,ej(a),0];return aC(cx(qB),b)}function
qC(a){return aC(cx(qD),0)}function
iL(a){return aC(cx(qE),0)}function
iM(y){var
e=t(b1),v=a(j[6][4],qG),w=u===e?b1[1]:q===e?a(r[2],b1):b1,x=b(j[13][1],w,v),d=a(j[1][6],qF),f=a(E[6],aa[11]),h=a(a6[3],f),i=a(G[25],[0,y,ab[29][1]]),k=a(c[9],i),l=b(a6[1][8],h,k),m=a6[5][2],n=[0,g(j[1][11][4],d,l,j[1][11][1]),0,m],o=[0,[0,[0,dp,x]],[0,[2,[1,b(af[1],0,d)]],0]],p=[3,b(af[1],0,o)],s=[29,b(af[1],0,p)];return b(ef[23],n,s)}function
qH(c){var
d=[0,[2,g(az[48],0,j[1][10][1],c)],0],e=cx(qI),f=[0,b(ay[29],0,e),d],h=[3,b(af[1],0,f)],i=[29,b(af[1],0,h)],k=a(iN[2],i),l=a(E[5],eh[8]);return b(E[7],l,k)}function
qJ(d,e){var
f=a(k[10][1][3],d);if(f)return b(c[h][5],f[1],e);var
g=a(k[10][1][4],d),i=[0,a(k[10][1][1],d),g,e];return a(c[20],i)}function
iO(f,e,d){var
i=a(c[10],1);return g(A[38],f,i,d)?b(c[42],e,d):b(c[h][5],c[16],d)}function
iP(c,b,a){function
d(b,a){return iO(c,a,b)}return g(f[17][15],d,b,a)}function
qK(d,e){var
f=a(k[10][1][3],d);if(f)return b(c[h][5],f[1],e);var
g=a(k[10][1][4],d),i=[0,a(k[10][1][1],d),g,e];return a(c[21],i)}function
iQ(j,i,d){var
e=a(k[10][1][20],i),f=e[2],l=e[3],m=e[1];if(f)return b(c[h][5],f[1],d);var
n=a(c[10],1);return g(A[38],j,n,d)?a(c[21],[0,m,l,d]):b(c[h][5],c[16],d)}function
iR(j,i,d){var
e=a(k[10][1][20],i),f=e[2],l=e[3],m=e[1];if(f)return b(c[h][5],f[1],d);var
n=a(c[10],1);return g(A[38],j,n,d)?a(c[20],[0,m,l,d]):b(c[h][5],c[16],d)}function
b2(h,a,e,d){function
i(e,d){var
f=b(c[42],d,e);return b(N[31],a,f)}var
j=g(f[17][15],i,e,d);return g(N[18],h,a,j)}function
f9(j,d,i,e){function
l(f,e){var
g=0===a(k[10][1][2],e)?b(c[h][5],c[16],f):b(c[42],e,f);return b(N[31],d,g)}var
m=g(f[17][15],l,i,e);return g(N[18],j,d,m)}function
dv(d,a){function
e(d,a){return b(c[43],a,d)}var
h=g(f[17][15],e,d,a);return b(N[31],l[16],h)}function
qL(m,e,d){function
i(d,n){var
e=a(k[10][1][20],n),f=e[3],i=e[2],j=e[1];if(i){var
l=i[1];return g(c[h][13],m,1,d)?b(c[h][5],l,d):a(c[22],[0,j,l,f,d])}return a(c[21],[0,j,f,d])}return g(f[17][15],i,e,d)}function
qM(c,b,a){function
d(b,a){return iQ(c,a,b)}return g(f[17][15],d,b,a)}function
qN(c,b,a){function
d(b,a){return iR(c,a,b)}return g(f[17][15],d,b,a)}function
f_(e,d){var
g=a(c[h][1],e);return b(f[17][68],g,d)}function
f$(d,g,i,h){var
m=g?g[1]:0;function
e(g,i){var
h=b(c[3],d,i);switch(h[0]){case
1:return b(j[1][10][4],h[1],g);case
9:var
n=h[2],k=b(c[3],d,h[1]);switch(k[0]){case
11:var
l=k[1][1];break;case
12:var
l=k[1][1][1];break;default:return o(c[hP],d,e,g,i)}var
p=a(w[31],l)[1],q=m?0:p[6];return o(f[19][55],q,e,g,n);default:return o(c[hP],d,e,g,i)}}return e(i,h)}function
ga(j,d,g){var
e=b(c[3],j,d);switch(e[0]){case
11:var
h=e[1][1];break;case
12:var
h=e[1][1][1];break;default:return[0,d,g]}var
k=a(w[31],h)[1][7],i=b(f[19][58],k,g),l=i[2];return[0,a(c[23],[0,d,i[1]]),l]}function
qO(e,a,d,c){try{var
b=at(N[85],0,qP,0,e,a[1],d,c)}catch(a){a=v(a);if(a===iS[6])return 0;throw a}return b?(a[1]=b[1],1):0}function
qQ(h,f,d){var
e=j[1][10][1];function
i(t,l,i){var
e=a(k[11][1][19],l),m=e[3],n=e[2],p=e[1],q=0;function
r(b){var
e=a(c[9],b);return o(A[34],d,h,f,e)}if(!g(M[22],r,q,n)){var
s=a(c[9],m);if(!o(A[34],d,h,f,s))return i}return b(j[1][10][4],p[1],i)}return g(ax[46],i,d,e)}var
qR=j[1][10][1];function
qS(c,a){return b(j[1][10][4],a,c)}var
qT=b(f[17][15],qS,qR);function
qU(a){return b(qV[6],ay[27],a)}function
iT(c){var
b=c[1];return 0===b[0]?a(ay[28],b[1]):b[1][1]}function
qW(b){var
c=iT(b);return a(j[1][6],c)}var
qX=T[2];function
qY(a){return g(qX,0,0,a)}var
el=a(C[20],qY);function
iU(c,n){function
e(e){var
h=a(i[68][5],e),o=a(i[68][3],e),p=b(A[43],h,n),q=b(C[35][16],c,e),r=b(A[43],h,q),t=b(j[1][10][9],p,r);function
u(c){var
d=a(k[11][1][2],c);return b(j[1][10][3],d,t)}var
v=a(f[17][9],o),l=b(f[17][bw],u,v)[2];if(l)var
m=a(k[11][1][2],l[1]);else
var
w=a(d[3],qZ),x=a(j[1][9],c),y=a(d[3],q0),z=b(d[12],y,x),B=b(d[12],z,w),m=g($[6],0,q1,B);return b(s[82],c,[0,m])}return a(i[68][8],e)}function
aA(f,c){return X[1]?function(h){var
e=g(z[65],0,0,h),j=a(d[3],q2),k=a(d[3],f),l=a(d[3],q3),m=b(d[12],l,k),n=b(d[12],m,j),o=b(d[12],n,e);b(L[9],0,o);function
p(j){var
c=j[1];if(c[1]===bO[26])var
e=c[3],n=c[2],o=g(z[65],0,0,h),k=t(e),p=a(d[3],q4),s=u===k?e[1]:q===k?a(r[2],e):e,v=a(d[13],0),w=a(d[3],f),x=a(d[3],q5),y=a(d[16],n),A=a(d[3],q6),B=b(d[12],A,y),C=b(d[12],B,x),D=b(d[12],C,w),E=b(d[12],D,v),F=b(d[12],E,s),G=b(d[12],F,p),l=b(d[12],G,o);else{if(c[1]===cT[1])var
J=g(bP[2],c[2],c[3],c[4]),K=a(d[3],q8),m=b(d[12],K,J);else
var
m=a($[15],j);var
l=m}var
H=a(d[3],q7),I=b(d[12],H,l);b(L[9],0,I);return a(i[16],0)}function
s(c){if(0===c){var
e=a(d[3],q9),h=a(d[3],f),j=b(d[12],h,e);b(L[9],0,j);return a(i[16],0)}return ah(function(c){var
e=g(z[65],0,0,c),f=a(d[3],q_),h=b(d[12],f,e);b(L[9],0,h);return[0,[0,c[1],0],c[2]]})}var
v=b(i[73][1],i[53],s),w=ah(c),x=b(i[18],w,v);return a(F(b(i[23],x,p)),h)}:c}function
aL(h,c){if(X[1]){var
e=function(e){var
j=a(i[68][4],e),k=a(i[68][5],e),f=a(i[68][2],e),l=g(z[11],j,k,f),m=a(d[3],q$),n=b(z[57],j,k),o=a(d[3],ra),p=a(d[3],h),s=a(d[3],rb),v=b(d[12],s,p),w=b(d[12],v,o),x=b(d[12],w,n),y=b(d[12],x,m),A=b(d[12],y,l);b(L[9],0,A);function
B(l){var
c=l[1];if(c[1]===bO[26])var
f=c[3],p=c[2],s=a(i[68][2],e),v=g(z[11],j,k,s),m=t(f),w=a(d[3],rc),x=u===m?f[1]:q===m?a(r[2],f):f,y=a(d[13],0),A=a(d[3],h),B=a(d[3],rd),C=a(d[16],p),D=a(d[3],re),E=b(d[12],D,C),F=b(d[12],E,B),G=b(d[12],F,A),H=b(d[12],G,y),I=b(d[12],H,x),J=b(d[12],I,w),n=b(d[12],J,v);else{if(c[1]===cT[1])var
N=g(bP[2],c[2],c[3],c[4]),O=a(d[3],rg),o=b(d[12],O,N);else
var
o=a($[15],l);var
n=o}var
K=a(d[3],rf),M=b(d[12],K,n);b(L[9],0,M);return a(i[16],0)}function
C(c){if(0===c){var
e=a(d[3],rh),f=a(d[3],h),j=b(d[12],f,e);b(L[9],0,j);return a(i[16],0)}return ah(function(c){var
e=g(z[65],0,0,c),f=a(d[3],ri),h=b(d[12],f,e);b(L[9],0,h);return[0,[0,c[1],0],c[2]]})}var
D=b(i[73][1],i[53],C),E=b(i[18],c,D);return b(i[23],E,B)};return a(i[68][8],e)}return c}function
U(b,a){return g(k[10][15],c[10],b,a)}function
aF(b,a){return g(k[10][14],c[10],b,a)}var
aG=k[10][1][20],cU=k[11][1][19],rj=k[11][1][20];function
iV(a){return b(f[17][68],ag,a)}var
a$=k[10][1][4],gb=k[10][1][3],bA=k[10][1][2],iW=k[10][1][1],gc=k[11][1][4],iX=k[11][1][3];function
rk(b,a){return[0,b,a]}function
ar(c,b,a){return b?[1,c,b[1],a]:[0,c,a]}function
iY(c,b,a){return b?[1,c,b[1],a]:[0,c,a]}var
iZ=k[10][7];function
dw(e,n,i){var
o=e?e[1]:0;function
j(p,d){var
i=d[2],j=d[1],q=d[4],r=d[3],s=a(c[h][4],j),e=b(k[10][1][16],s,p),l=a(bA,e),f=l?l[1]:a(n,0),t=a(a$,e),u=a(gb,e),v=[0,a(k[7],f),u,t],w=a(k[11][1][20],v);if(o)var
g=0;else
if(a(k[10][1][8],e))var
g=0;else
var
m=i,g=1;if(!g)var
m=[0,a(c[11],f),i];return[0,[0,a(c[11],f),j],m,[0,f,r],[0,w,q]]}var
d=g(f[17][16],j,i,rl),l=d[4],m=d[1];return[0,m,a(f[17][9],d[2]),l]}function
em(d){function
e(i,f){var
d=f[2],j=f[1],e=a(cU,i),g=e[1],l=e[2],m=b(c[h][11],d,e[3]),n=a(c[h][11],d),o=b(M[16],n,l);function
p(a){return[0,a]}var
q=ar(b(k[3],p,g),o,m);return[0,[0,q,j],[0,g[1],d]]}return g(f[17][16],e,d,rm)}var
en=aK[4];function
i0(c,b){if(0===b[0]){var
d=b[1];return[0,d,a(c,b[2])]}var
e=b[2],f=b[1],g=a(c,b[3]);return[1,f,a(c,e),g]}function
cV(d,e,a){var
i=[0,d,0];function
j(f,a){var
d=a[1],g=a[2];return[0,d+1|0,[0,i0(b(c[h][3],e,d),f),g]]}return g(f[17][16],j,a,i)[2]}function
dx(e,d){function
i(a,f){var
d=a[1],g=a[2];return[0,d+1|0,[0,i0(b(c[h][3],[0,e,0],d),f),g]]}var
j=g(f[17][15],i,rn,d)[2];return a(f[17][9],j)}function
dy(l,k,j){var
e=1,g=0,d=j;for(;;){if(d){var
i=d[2],m=d[1];if(e===l){var
n=a(f[17][9],g),o=cV(0,[0,b(c[h][1],-e|0,k),0],n);return b(f[18],o,i)}var
e=e+1|0,g=[0,m,g],d=i;continue}return 0}}function
i1(n,m,l){var
e=1,g=0,d=l;for(;;){if(d){var
j=d[2],i=d[1];if(e===n){var
o=a(k[10][1][4],i),p=b(c[h][1],-e|0,m),q=[0,[1,a(k[10][1][1],i),p,o],j],r=a(f[17][9],g);return b(f[18],r,q)}var
e=e+1|0,g=[0,i,g],d=j;continue}return 0}}function
b3(b){return a(k[11][1][2],b)}var
eo=k[11][9],cy=k[10][8],bj=k[10][1][16],i2=k[11][1][16],ro=k[11][7],rp=k[11][5];function
rq(g,m,l){var
e=0,d=l;for(;;){if(d){var
i=d[2],k=d[1],n=b3(k);if(b(j[1][1],n,g)){var
o=a(f[17][9],e);return b(f[18],o,i)}var
e=[0,b(i2,a(c[h][9],[0,[0,g,m],0]),k),e],d=i;continue}return 0}}function
ep(a){return b(L[6],0,a)}function
ad(a){return g($[6],a[1],[0,a[2]],a[3])}function
ba(b){var
c=a(d[3],b);return g($[6],0,0,c)}function
cz(b,a){return g($[6],0,[0,b],a)}var
i3=$[4];function
rr(a){return b($[14],0,a)}var
eq=N[22];function
bB(b,a){return g($[3],0,b,a)}function
i4(h,f,e,c,d){var
a=b(l[3],h,e),i=c?[0,a[1],a[2],a[3],a[4],a[5],c[1],a[7]]:a;return g(l[22],d,f,i)}function
cA(d,c,b,a){return hx(P[4],b,0,0,0,0,0,0,0,d,c,a)}function
gd(d,c,b,a){return M5(P[7],b,0,0,0,0,d,c,a)}function
rs(a){return a}function
rt(a){return a}var
i6=i5[7];function
ru(c,b,a){return g(aK[22],0,[0,a,0],[4,[0,[0,[1,c],0]],b])}function
cW(g,e,d){var
f=a(c[au][1],d);return b(aS[11],e,f)}function
er(d,b){var
e=cq(d,b),f=a(G[25],e);return a(c[9],f)}function
cX(h,d){var
e=b(f[17][68],c[au][3],d),g=a(A[88],e);return b(f[17][68],c[bK],g)}function
aX(d,a){var
e=b(A[7],d,a);return b(f[19][15],c[9],e)}function
i7(d,b){return a(c[40],[0,d,b])}function
ge(d,c,a){return b(ac[15],c,a)}function
b4(e,d){var
a=b(c[3],e,d);return 9===a[0]?[0,a[1],a[2]]:[0,d,[0]]}function
cY(e){var
d=a(Z[6],e),g=d[1],h=b(f[17][68],c[9],d[2]);return[0,dh(g),h]}var
es=a(c[5],rv);function
gf(d,g,e){var
h=a(es,d),i=b(f[19][15],h,e),j=b(es,d,g),k=b(bb[28],j,i);return a(c[9],k)}function
b5(d,g,e){var
h=a(es,d),i=b(f[19][15],h,e),j=b(es,d,g),k=b(iS[22],j,i);return a(c[9],k)}function
dz(d,c,b){var
a=g(Z[70],d,c,b);return[0,a[1],a[2]]}function
i8(s,i,r){var
x=k[10][2];return function(y){var
f=s,h=r,e=x,d=y;for(;;){if(0===h)return[0,e,d];var
j=g(N[30],f,i,d),a=b(c[3],i,j);switch(a[0]){case
5:var
d=a[1];continue;case
6:var
m=a[2],n=a[1],t=a[3],u=b(k[10][3],[0,n,m],e),f=b(c[aP],[0,n,m],f),h=h-1|0,e=u,d=t;continue;case
8:var
o=a[3],p=a[2],q=a[1],v=a[4],w=b(k[10][3],[1,q,p,o],e),f=b(c[aP],[1,q,p,o],f),h=h-1|0,e=w,d=v;continue;default:var
l=g(N[29],f,i,j);if(g(c[aJ],i,j,l))return[0,e,j];var
d=l;continue}}}}function
gg(d,b){var
c=a(d,b[1]),e=c[2];b[1]=c[1];return e}function
aH(e,a,d){var
c=b(e,a[1],d),f=c[2];a[1]=c[1];return f}function
gh(k,d,e){var
f=a(ab[3][9],e);if(f){var
c=f[1];if(a(ab[1][5],c))return[0,d,c,e];var
g=b(l[134],d,c);if(g)if(0!==g[1]){var
m=a(ab[3][4],c);return[0,b(l[a2],d,c),c,m]}return[0,d,c,e]}var
h=o(l[130],0,0,l[bX],d),i=h[2],n=h[1],j=a(ab[3][4],i),p=a(aE[18],j),q=a(aE[18],e);return[0,o(l[au],k,n,q,p),i,j]}function
cB(n,m,g,l){var
d=gh(n,m,l),h=d[2],i=d[1],o=d[3];if(a(ab[1][7],h))var
p=a(ab[3][4],ab[1][2]),e=ab[1][2],j=p;else
var
e=h,j=o;if(g)var
q=b(c[2][2],i,g[1]),r=a(ab[29][4],q),s=b(f[19][5],r,[0,e]),t=a(ab[29][3],s),k=a(c[2][1],t);else
var
u=a(ab[29][3],[0,e]),k=a(c[2][1],u);return[0,i,k,j]}aD(1181,[0,bL,d7,d8,d9,d_,X,aM,fQ,F,ah,nY,nZ,n0,oy,oz,oA,oB,h2,h3,pZ,cw,dp,ec,oN,aC,eg,aT,p0,f_,ox,fR,h0,fS,qO,cP,qJ,iO,iP,qK,iQ,iR,b2,f9,dv,qM,qN,qL,f$,qQ,qT,ga,ee,a_,bh,fV,dq,h6,aV,di,fU,H,aw,a4,bi,fX,h7,dl,h9,h_,bZ,cQ,h8,o0,o2,cr,cs,ed,fY,ia,h$,fZ,ib,il,im,io,pu,f2,px,pz,aR,ap,ip,ai,aj,aq,ak,pa,dm,dn,cR,f0,f1,ic,pi,id,ie,ig,ih,ii,ij,ik,dj,dk,oM,fW,eb,bz,f3,pA,ct,b0,iq,f5,ir,is,it,cS,iu,dr,a5,aW,bN,ds,dt,f4,iv,cv,iw,pT,aA,aL,iA,p_,iI,iJ,qC,ei,qd,iL,iH,iC,iD,iE,iF,iG,iM,qH,f8,qv,qx,qz,iK,p$,qb,f6,f7,iy,iz,qU,iT,qW,el,iU,U,aF,aG,cU,ag,rj,a$,bA,iW,gb,rk,ar,iY,iV,dw,em,cV,b3,gc,iX,iZ,eo,cy,bj,i2,ro,rp,rs,rt,ep,ad,ba,cz,i3,rr,bB,eq,dx,dy,i1,rq,i4,cA,gd,en,i6,ru,dh,cq,cW,er,cX,aX,i7,ge,b4,cY,gf,b5,dz,aH,gg,i8,gh,cB],nb);function
i9(f,e,d){var
b=a(w[2],0),g=a(l[17],b),c=a1(l[fO],0,[0,l[cm]],0,b,g,d);return o(f,b,c[1],e,c[2])}function
b6(i,f,e){return i9(function(l,e,k,j){var
f=b(c[3],e,j);if(11===f[0]){var
h=f[1];return o(i,l,e,k,[0,h[1],h[2]])}var
m=a(d[3],rw);return g($[6],0,0,m)},f,e)}var
gj=[0,gi[53][1]];function
b7(a){gj[1]=g(gi[53][4],a[1],a[2],gj[1]);return 0}function
rx(e){try{var
c=b(gi[53][23],e,gj[1]);return c}catch(c){c=v(c);if(c===O){var
f=a(d[3],e),h=a(d[3],ry),i=b(d[12],h,f);return g($[6],0,0,i)}throw c}}function
i_(d,c,a){function
e(a){var
c=a[2];b(et[12],a[1],c);return c}var
f=b(m[17],e,a);function
g(e){var
a=rx(e);function
c(c){return b(a,d,c)}return b(m[15],c,f)}return b(m[15],g,c)}aD(1185,[0,i9,b6,b7,i_],"Ederive");function
bC(e,i){function
c(y,c){if(typeof
c==="number")return a(d[3],rz);else
switch(c[0]){case
0:var
i=c[1],k=c[2]?a(d[3],rA):a(d[7],0),l=a(j[1][9],i);return b(d[12],l,k);case
1:var
g=c[3],h=b(z[43],e,c[1]);if(a(f[17][48],g))return h;var
m=a(d[3],rB),n=bC(e,g),o=a(d[13],0),p=a(d[3],rC),q=b(d[12],p,h),r=b(d[12],q,o),s=b(d[12],r,n);return b(d[12],s,m);default:var
t=c[1],u=a(d[3],rD),v=b(z[27],e,t),w=a(d[3],rE),x=b(d[12],w,v);return b(d[12],x,u)}}var
h=a(V[10],c);return g(d[39],d[13],h,i)}function
rF(b){return ep(bC(a(w[2],0),b))}function
gk(e,f,c){switch(c[0]){case
0:return g(a7[16],e,f,c[1]);case
1:return b(z[27],e,c[1]);default:return a(d[3],rG)}}function
i$(h,e,k){if(k){var
c=k[1];switch(c[0]){case
0:var
l=c[2][1],m=c[1];if(a(f[17][48],l))var
i=a(d[7],0);else
var
Z=function(c){var
f=c[2],g=c[1],i=a(d[3],rP),j=a(gm(h,e),f),k=a(d[3],rQ),l=ja(h,e,g),m=b(d[12],l,k),n=b(d[12],m,j);return b(d[12],n,i)},_=g(d[39],d[5],Z,l),$=a(d[13],0),aa=a(d[3],rO),ab=b(d[12],aa,$),i=b(d[12],ab,_);var
n=a(d[13],0),o=gk(h,e,m),p=a(d[13],0),q=a(d[3],rH),r=a(d[13],0),s=b(d[12],r,q),t=b(d[12],s,p),u=b(d[12],t,o),v=b(d[12],u,n);return b(d[12],v,i);case
1:var
w=a(j[1][9],c[1][2]),x=a(d[13],0),y=a(d[3],rI),z=a(d[13],0),A=b(d[12],z,y),B=b(d[12],A,x);return b(d[12],B,w);default:var
C=c[2],D=c[1],E=a(d[3],rJ),F=a(gm(h,e),C),G=a(d[3],rK),H=b(d[12],G,F),I=b(d[12],H,E),J=b(d[26],1,I),K=a(d[13],0),L=a(d[3],rL),M=a(d[13],0),N=b(a7[16],h,e),O=function(b){return a(d[3],rM)},P=g(d[39],O,N,D),Q=a(d[13],0),R=a(d[3],rN),S=a(d[13],0),T=b(d[12],S,R),U=b(d[12],T,Q),V=b(d[12],U,P),W=b(d[12],V,M),X=b(d[12],W,L),Y=b(d[12],X,K);return b(d[12],Y,J)}}return a(d[7],0)}function
ja(f,e,c){var
i=c[5],n=c[4],o=c[3],p=c[1][2];if(i){var
h=i[1];if(0===h[0])var
q=h[1],r=function(b){return a(a7[6],b[2])},s=b(d[34],r,q),t=a(d[3],rR),k=b(d[12],t,s);else
var
m=h[1],A=m[2],B=m[1],C=b(a7[16],f,e),D=b(d[34],C,A),E=g(a7[16],f,e,B),F=a(d[3],rT),G=b(d[12],F,E),k=b(d[12],G,D);var
l=k}else
var
l=a(d[7],0);function
u(c){var
h=g(a7[16],f,e,c),i=a(d[3],rS);return b(d[12],i,h)}var
v=b(d[34],u,n),w=g(a7[13],f,e,o),x=a(j[1][9],p),y=b(d[12],x,w),z=b(d[12],y,v);return b(d[12],z,l)}function
gl(c,e,a){var
f=a[2],g=i$(c,e,a[3]),h=bC(c,f);return b(d[12],h,g)}function
gm(c,a){function
e(b){return gl(c,a,b)}return b(d[39],d[5],e)}function
jb(e,c,h){var
f=h[1],o=h[2];function
n(f){switch(f[0]){case
0:var
h=f[1],i=jd(e,c,f[2]),k=a(d[13],0),l=gk(e,c,h),m=a(d[13],0),n=a(d[3],rV),o=a(d[13],0),p=b(d[12],o,n),q=b(d[12],p,m),r=b(d[12],q,l),s=b(d[12],r,k);return b(d[12],s,i);case
1:var
t=a(j[1][9],f[1][2]),u=a(d[13],0),v=a(d[3],rW),w=a(d[13],0),x=b(d[12],w,v),y=b(d[12],x,u);return b(d[12],y,t);default:var
z=f[2],A=f[1],B=a(d[3],rX),C=a(jc(e,c),z),D=a(d[3],rY),E=b(d[12],D,C),F=b(d[12],E,B),G=b(d[26],1,F),H=a(d[13],0),I=a(d[3],rZ),J=a(d[13],0),K=b(a7[16],e,c),L=function(b){return a(d[3],r0)},M=g(d[39],L,K,A),N=a(d[13],0),O=a(d[3],r1),P=a(d[13],0),Q=b(d[12],P,O),R=b(d[12],Q,N),S=b(d[12],R,M),T=b(d[12],S,J),U=b(d[12],T,I),V=b(d[12],U,H);return b(d[12],V,G)}}var
p=a(a(d[34],n),o);if(0===f[0])var
i=g(a7[16],e,c,f[1]);else
var
k=f[1],l=b(a7[16],e,c),m=function(b){return a(d[3],rU)},i=g(d[39],m,l,k);return b(d[12],i,p)}function
jc(c,a){function
e(b){return jb(c,a,b)}return b(d[39],d[5],e)}function
jd(e,c,i){var
h=i[1];if(a(f[17][48],h))return a(d[7],0);function
j(f){var
g=f[2],h=f[1],i=a(d[3],r_),j=a(jc(e,c),g),k=a(d[3],r$),l=ja(e,c,h),m=b(d[12],l,k),n=b(d[12],m,j);return b(d[12],n,i)}var
k=g(d[39],d[5],j,h),l=a(d[13],0),m=a(d[3],r9),n=b(d[12],m,l);return b(d[12],n,k)}function
eu(e,f,c){var
i=c[3],k=c[2];function
h(c){switch(c[0]){case
0:var
h=c[1],i=jd(e,f,c[2]),k=a(d[13],0),l=gk(e,f,h),m=a(d[13],0),n=a(d[3],r2),o=a(d[13],0),p=b(d[12],o,n),q=b(d[12],p,m),r=b(d[12],q,l),s=b(d[12],r,k);return b(d[12],s,i);case
1:var
t=a(j[1][9],c[1][2]),u=a(d[13],0),v=a(d[3],r3),w=a(d[13],0),x=b(d[12],w,v),y=b(d[12],x,u);return b(d[12],y,t);default:var
z=c[2],A=c[1],B=a(d[3],r4),C=a(dA(e,f),z),D=a(d[3],r5),E=b(d[12],D,C),F=b(d[12],E,B),G=b(d[26],1,F),H=a(d[13],0),I=a(d[3],r6),J=a(d[13],0),K=b(a7[16],e,f),L=function(b){return a(d[3],r7)},M=g(d[39],L,K,A),N=a(d[13],0),O=a(d[3],r8),P=a(d[13],0),Q=b(d[12],P,O),R=b(d[12],Q,N),S=b(d[12],R,M),T=b(d[12],S,J),U=b(d[12],T,I),V=b(d[12],U,H);return b(d[12],V,G)}}var
l=a(a(d[34],h),i),m=bC(e,k);return b(d[12],m,l)}function
dA(c,a){function
e(b){return eu(c,a,b)}return b(d[39],d[5],e)}function
sa(c){var
b=a(w[2],0);return ep(gl(b,a(l[17],b),c))}var
ev=a(E[3],sb);function
gn(d,a){var
c=b(av[26],d,a[1]);a[1]=b(j[1][10][4],c,a[1]);return c}function
ew(f,e,c,b){return a(d[7],0)}function
ex(f,e,c,b){return a(d[7],0)}function
sc(a){if(a){var
b=a[1];if(b)if(0===b[1][0])return 1}return 0}function
go(a){function
c(a){if(a)if(0!==a[1][0])return 1;return 0}return b(f[17][22],c,a)}function
je(g,e,f){var
d=b(c[3],g,f);switch(d[0]){case
1:return b(j[1][1],e,d[1]);case
10:var
h=a(j[17][8],d[1][1]),i=a(j[6][6],h);return b(j[1][1],e,i);default:return 0}}var
jf=a(dB[4],sd);function
ey(s,c){var
d=j[1][10][1];function
e(e,d){function
f(i,c,h){var
e=h[1];switch(e[0]){case
0:var
k=e[1];if(a(ay[33],k)){var
d=a(ay[35],k);if(b(j[1][13][2],d,i))return c;var
o=a(j[1][1],d);if(g(M[22],o,0,s))return c;try{var
p=b(ay[32],0,d),l=a(az[14],p);if(0===l[0])var
q=a(aS[4],l[1])?c:b(j[1][10][4],d,c),m=q;else
var
m=c;return m}catch(a){a=v(a);if(a===O)return b(j[1][10][4],d,c);throw a}}break;case
17:var
n=e[1];if(!n[1])if(!am.caml_string_notequal(n[2],se))return c;break}function
r(b,a){return[0,b,a]}return y(bk[29],r,f,i,c,h)}var
c=f(0,j[1][10][1],d);return b(j[1][10][7],e,c)}return g(f[17][15],e,d,c)}function
gp(e,d){var
k=d[9],l=d[8],m=d[7],n=a(e,d[6]),o=b(cy,e,d[5]),g=a(aE[18],d[4]),h=a(e,a(c[14],g)),i=a(c[au][1],h),f=a(G[29],i);if(4===f[0]){var
j=a(aE[17],f[1]),p=a(e,d[3]);return[0,d[1],d[2],p,j,o,n,m,l,k]}throw[0,I,sf]}function
dC(v,s,i,c){function
k(g,e,c){var
h=a(Z[37],e[1]),i=a(Z[49],e),j=a(f[17][1],c)<i?ad([0,g,sh,a(d[3],sg)]):a(f[17][1],c)===(h+i|0)?b(f[17][bI],h,c):a(f[17][1],c)===i?c:ad([0,g,sj,a(d[3],si)]);b(et[12],g,[3,e]);var
k=a(V[7],l);return[1,e,h,b(f[17][68],k,j)]}function
l(e,c){switch(c[0]){case
0:var
g=c[1];switch(g[0]){case
1:var
l=t(dr),w=u===l?dr[1]:q===l?a(r[2],dr):dr;if(b(j[63][1],g,w))return 0;break;case
3:return k(e,g[1],0)}break;case
1:return[0,c[1],0];case
4:var
m=c[2],n=c[1],o=a(V[1],n);if(0===o[0]){var
h=o[1];switch(h[0]){case
1:var
p=t(a5),C=u===p?a5[1]:q===p?a(r[2],a5):a5;if(b(j[63][1],h,C)){var
D=a(f[17][6],m);return[2,a(f[17][5],D)]}break;case
3:return k(e,h[1],m)}}var
x=a(d[3],sm),y=b(z[27],v,n),A=a(d[3],sn),B=b(d[12],A,y);return ad([0,e,so,b(d[12],B,x)]);case
13:var
E=i?i[1]:a(j[1][6],sp);return[0,gn(E,s),1]}return ad([0,e,sl,a(d[3],sk)])}return b(V[7],l,c)}function
bQ(a){return b(c[44],a[6],a[5])}function
gr(m,F,t,i,E){var
n=t?t[1]:[0,j[1][10][1]],p=a(l[17],m),e=a(j[1][10][21],n[1]);function
G(a){return c[16]}var
q=b(f[17][68],G,e);function
H(a){return 0}var
I=b(f[17][68],H,e);try{var
Q=at(a8[3],m,p,0,2,e,q,I),r=Q}catch(b){b=v(b);if(b!==O)throw b;var
r=bB(0,a(d[3],sq))}if(i){var
o=i[1][1],u=bQ(o);try{var
P=at(a8[3],m,p,[0,r],0,[0,o[2],0],[0,u,0],[0,o[8],0]),w=P}catch(b){b=v(b);if(b!==O)throw b;var
w=bB(0,a(d[3],sr))}var
y=[0,o[2],e],x=[0,u,q],s=w}else
var
y=e,x=q,s=r;function
J(d,b){var
e=a(c[au][1],b);return[0,a(k[7],d),e]}var
z=g(f[17][69],J,y,x),h=b(ax[38],z,m),K=0;function
L(i){var
c=b(ax[38],z,h),e=b(dD[10],c,s);b(f[17][11],e,F);try{var
g=at(a8[7],1,h,p,[0,s],0,0,E);return g}catch(b){b=v(b);if(b===O)return bB(0,a(d[3],ss));throw b}}var
A=b(dD[16],L,K);try{if(i)var
B=i[1],C=B[1][2],M=B[2],N=function(g,c){if(4===c[0])var
f=c[1],e=c[2];else
var
f=b(V[3],g,c),e=0;function
i(g,f){if(1===f[0])if(b(j[1][1],f[1],C)){var
c=function(b,a){if(b){var
d=b[2],e=b[1];if(a){var
f=a[1],g=c(d,a[2]);return[0,dC(h,n,f,e),g]}var
i=c(d,0);return[0,dC(h,n,0,e),i]}return 0};return c(e,M)}var
i=a(j[1][9],C),k=a(d[3],su);return ad([0,g,sv,b(d[12],k,i)])}return b(V[10],i,f)},D=b(V[10],N,A);else
var
D=[0,dC(h,n,0,A),0];return D}catch(b){b=v(b);if(b===O)return bB(0,a(d[3],st));throw b}}function
gs(n,m,g,e){var
c=[0,j[1][10][1]],i=[0,b(K[5],g[2],sw)],p=g[5];function
q(b){return a(k[10][1][2],b)}var
z=b(f[17][14],q,p),u=g[9];function
v(b){return a(cZ[14],b)?[0,a(cZ[16],b)]:0}var
A=b(f[17][68],v,u);function
r(a){var
b=[0,c];return function(c,d){return gr(n,a,b,c,d)}}function
s(e,B,u){var
k=u[1],C=u[2];if(0===k[0]){var
l=k[1],D=ey([0,g[2]],[0,l,0]);c[1]=b(j[1][10][7],c[1],D);var
E=a(bk[6],l),m=[0,E,b(r(e),[0,[0,g,z]],l)]}else{var
n=k[1],o=[0,ey(0,n)],p=function(k,c){if(typeof
c==="number")return c;else
switch(c[0]){case
0:var
d=c[1];if(0!==c[2])if(b(j[1][10][3],d,o[1]))return[0,gn(d,o),1];return c;case
1:var
e=c[3],g=c[2],h=c[1],i=a(V[7],p);return[1,h,g,b(f[17][68],i,e)];default:return c}},y=a(V[7],p),q=b(f[17][68],y,B);c[1]=b(j[1][10][7],c[1],o[1]);var
H=a(f[17][5],n),I=a(bk[6],H),J=a(r(e),0),K=b(f[17][68],J,n),L=function(b){return a(f[17][5],b)},w=b(f[17][68],L,K);if(0===q)var
i=function(c,a){if(c){var
d=c[1];if(d){var
e=d[1],f=i(c[2],a);return[0,b(V[3],0,[0,e,0]),f]}var
g=c[2];if(a){var
h=a[1];return[0,h,i(g,a[2])]}return 0}return a},x=i(A,w);else
var
x=b(f[18],q,w);var
m=[0,I,x]}var
v=m[2],F=m[1];function
G(g){switch(g[0]){case
0:var
k=g[2],l=k[2],i=g[1],n=k[1],o=t(c,n,b(f[18],l,e));switch(i[0]){case
0:var
p=i[1],q=function(a,b){return h(e,a,b)},m=b(af[6],q,p),j=[0,m[1],[0,m[2]]];break;case
1:var
j=[0,0,[1,i[1]]];break;default:var
j=[0,0,[2,i[1]]]}var
r=j[2];return[0,r,[0,b(f[17][57],j[1],o),l]];case
1:return[1,g[1]];default:var
u=g[2],w=g[1],x=function(i){function
j(a,b){return h(e,a,b)}var
c=b(af[6],j,i),g=c[2];if(1-a(f[17][48],c[1])){var
k=a(d[3],sz);ad([0,a(bk[6],g),sA,k])}return g},y=function(a){return s(e,v,a)},z=b(f[17][68],y,u);return[2,b(f[17][68],x,w),z]}}return[0,F,v,b(M[16],G,C)]}function
l(j,e){var
g=e[2],i=e[1];function
k(e){switch(e[0]){case
0:var
k=e[2],m=k[2],g=e[1],p=k[1],n=b(f[18],m,j),q=t(c,p,n);switch(g[0]){case
0:var
r=g[1],s=function(a,b){return h(n,a,b)},o=b(af[6],s,r),i=[0,o[1],[0,o[2]]];break;case
1:var
i=[0,0,[1,g[1]]];break;default:var
i=[0,0,[2,g[1]]]}var
u=i[2];return[0,u,[0,b(f[17][57],i[1],q),m]];case
1:return[1,e[1]];default:var
v=e[2],w=e[1],x=function(g){function
i(a,b){return h(j,a,b)}var
c=b(af[6],i,g),e=c[2];if(1-a(f[17][48],c[1])){var
k=a(d[3],sx);ad([0,a(bk[6],e),sy,k])}return e},y=function(a){return l(j,a)},z=b(f[17][68],y,v);return[2,b(f[17][68],x,w),z]}}return[0,i,b(M[16],k,g)]}function
t(e,c,g){function
d(c){var
d=c[1],e=d[1],h=c[2],i=e[1],k=a(j[1][8],e[2]);o(et[17],[0,i],sC,k,sB);function
m(a){return l(g,a)}return[0,d,b(f[17][68],m,h)]}return b(f[17][68],d,c)}function
h(q,d,g){var
k=d?d[1]:jf,e=[0,0];function
h(r,k,g){var
m=k?k[1]:jf;if(12===g[0]){var
n=g[3];if(n){var
p=n[1],u=a(E[4],ev);if(b(E[9],p,u)){var
v=a(E[4],ev),w=b(E[8],v,p),d=i[1];i[1]=a(K[11],d);c[1]=b(j[1][10][4],d,c[1]);var
x=function(a){return l(q,a)},y=b(f[17][68],x,w);e[1]=[0,[0,[0,[0,m,d],0,0,0,0],y],e[1]];return a(bk[9],d)}}}var
s=b(af[1],[0,m],g);function
t(b){function
c(a,c){return h(b,a,c)}return a(af[6],c)}return o(bk[30],j[1][10][4],t,r,s)}var
m=h(c[1],[0,k],g);return[0,e[1],m]}return s(m,0,e)}function
ez(e,c){function
d(a){var
g=a[1];function
i(a){return h(a[2])}var
c=b(f[17][22],i,g);if(c)return c;var
j=a[2];function
d(a){return b(bk[33],e,a[2])}return b(f[17][22],d,j)}function
h(a){return b(f[17][22],g,a)}function
g(m){var
i=m[2];if(i){var
c=i[1];switch(c[0]){case
0:var
g=c[2],j=c[1];switch(j[0]){case
0:var
k=b(bk[33],e,j[1]);return k?k:d(g);case
1:return d(g);default:return d(g)}case
1:break;default:var
n=c[2],o=c[1],p=a(bk[33],e),l=b(f[17][22],p,o);return l?l:h(n)}}return 0}return d(c)}aD(1195,[0,bC,bC,rF,i$,gl,gm,eu,dA,jb,sa,sc,go,je,gn,ew,ex,bQ,gp,ey,dC,gr,gs,ev,ez],nN);function
jg(b,a,d){var
e=y(T[2],0,0,b,a[1],d),c=at(cu[6],[0,l[bX]],sE,0,sD,b,a[1],e),f=c[2];a[1]=c[1];return f}function
jh(f,d,b){var
e=t(a5),g=[0,jg(f,d,b),b],h=u===e?a5[1]:q===e?a(r[2],a5):a5,i=[0,bh(d,h),g];return a(c[23],i)}function
ji(f,d,b){var
e=t(bN),g=[0,jg(f,d,b),b],h=u===e?bN[1]:q===e?a(r[2],bN):bN,i=[0,bh(d,h),g];return a(c[23],i)}function
b8(d){switch(d[0]){case
0:return a(c[10],d[1]);case
1:var
e=d[2],g=a(c[30],d[1]),h=b(f[17][68],b8,e),i=[0,g,a(f[19][12],h)];return a(c[23],i);case
2:return d[1];default:return a(c[10],d[1])}}function
jj(g,e,d,b){switch(b[0]){case
0:return a(c[10],b[1]);case
1:var
j=b[2],k=a(c[30],b[1]),l=jk(g,e,d,j),m=[0,k,a(f[19][12],l)];return a(c[23],m);case
2:var
h=b[1];if(g)try{var
n=jh(e,d,h);return n}catch(a){return h}return h;default:var
i=b[1];return g?ji(e,d,a(c[10],i)):a(c[10],i)}}function
jk(e,d,c,a){function
g(a){return jj(e,d,c,a)}return b(f[17][68],g,a)}function
gt(a,e,d,c){var
f=a?a[1]:1,b=[0,d],g=jj(f,e,b,c);return[0,b[1],g]}function
jl(a,e,d,c){var
f=a?a[1]:1,b=[0,d],g=jk(f,e,b,c);return[0,b[1],g]}function
jn(c){var
d=Q[2][1];function
e(c,f){var
d=jm(f),e=b(Q[2][8],d,c);if(a(Q[2][2],e))return b(Q[2][7],d,c);var
g=a(Q[2][26],e),h=a(J[22],g),i=b(J[17],h,sF);return ba(b(J[17],sG,i))}return g(f[17][15],e,d,c)}function
jm(b){switch(b[0]){case
0:return a(Q[2][5],b[1]);case
1:return jn(b[2]);case
2:return Q[2][1];default:return Q[2][1]}}function
dE(a){function
c(a){return[2,a]}return b(f[17][68],c,a)}function
jo(c,a){function
d(a){return dF(c,a)}return b(f[17][68],d,a)}function
dF(d,j){var
e=b(c[3],d,j);switch(e[0]){case
0:return[0,e[1]];case
9:var
i=e[2],h=e[1];if(2===i.length-1){var
k=i[2],l=t(a5),p=u===l?a5[1]:q===l?a(r[2],a5):a5;if(g(c[a2],d,p,h))return[2,k];var
m=t(bN),s=u===m?bN[1]:q===m?a(r[2],bN):bN;if(g(c[a2],d,s,h))return[3,b(c[73],d,k)]}if(b(c[63],d,h)){var
n=b(c[85],d,h),v=a(Z[37],n[1][1]),o=b(f[19][58],v,i),w=o[1],x=jo(d,a(f[19][11],o[2])),y=dE(a(f[19][11],w));return[1,n,b(f[18],y,x)]}break;case
12:return[1,e[1],0]}return[2,j]}function
jp(c,d,m,e){var
n=c?c[1]:[0,j[1][10][1]],u=[0,n];function
g(e){var
c=u?n:[0,j[1][10][1]];switch(e[0]){case
0:var
o=b(f[17][7],m,e[1]-1|0),p=a(k[10][1][2],o),g=b(av[29],p,c[1]);c[1]=b(j[1][10][4],g,c[1]);return[0,b(V[3],d,[0,g,0])];case
1:var
h=e[1][1],q=e[2],i=a(Z[37],h[1]),r=[1,h,i,jp([0,c],d,m,b(f[17][W],i,q)[2])];return[0,b(V[3],d,r)];case
2:var
s=c[1],t=a(j[1][6],sH),l=b(av[26],t,s);c[1]=b(j[1][10][4],l,c[1]);return[0,b(V[3],d,[0,l,1])];default:return 0}}return b(f[17][65],g,e)}function
jq(c,d,b){var
e=b[2],g=b[1],h=c?c[1]:j[1][10][1],i=jp([0,[0,h]],d,g,e);return a(f[17][9],i)}function
eA(q,p,d){var
e=[0,j[1][10][1],0];function
h(r,i){var
e=i[2],d=i[1],f=a(aG,r),g=f[3],k=f[2],h=f[1],l=h[1];if(l){var
m=b(av[26],l[1],d),s=[0,ar([0,[0,m],h[2]],k,g),e];return[0,b(j[1][10][4],m,d),s]}var
t=b(c[x],e,q),u=o(av[10],t,p,g,0),n=b(av[26],u,d),v=[0,ar([0,[0,n],h[2]],k,g),e];return[0,b(j[1][10][4],n,d),v]}return g(f[17][16],h,d,e)[2]}function
jr(c,b,a){return g(z[11],c,b,a)}function
dG(a,d,c){var
b=gt(0,a,d,c);return jr(a,b[1],b[2])}function
eB(e,c,b){var
h=a(f[17][9],b);function
i(a){return dG(e,c,a)}function
j(b){return a(d[3],sI)}return g(d[39],j,i,h)}function
b9(f,i,e){var
h=[0,f,a(d[7],0)];function
j(f,e){var
h=e[1],j=e[2],k=a(c[au][3],f),l=g(z[55],h,i,k),m=a(d[6],2),n=b(d[12],j,m),o=b(d[12],n,l);return[0,b(c[aP],f,h),o]}var
l=g(k[10][11],j,e,h)[2];return b(d[25],0,l)}function
sJ(a){return fQ(b9,a)}function
aI(h,g,e){var
i=e[1],j=e[3],k=e[2],l=b(c[x],i,h),m=b9(h,g,i),n=b9(h,g,j),o=a(d[14],0),p=a(d[3],sK),q=a(d[14],0),r=eB(l,g,k),s=a(d[14],0),t=a(d[3],sL),u=a(d[14],0);a(f[17][48],i);var
v=b(d[12],m,u),w=b(d[12],v,t),y=b(d[12],w,s),z=b(d[12],y,r),A=b(d[24],0,z),B=b(d[12],A,q),C=b(d[12],B,p),D=b(d[12],C,o),E=b(d[12],D,n);return b(d[24],0,E)}function
sM(c,b,a){return ep(aI(c,b,a))}function
sN(a){return fQ(aI,a)}function
js(g,e,d){var
i=d[3],j=d[1],l=d[2];fS(g,e,j);fS(g,e,i);var
k=b(c[x],j,g),m=[0,e,0];function
n(l,j,d){var
e=d[2],m=d[1],n=a(aG,l)[3],f=gt(sO,k,m,j),g=f[2],i=f[1];fR(k,i,g,b(c[h][4],e,n));return[0,i,[0,g,e]]}o(f[17][20],n,i,l,m);return 0}function
bl(c,h,f,e){var
k=c?c[1]:0;if(X[1])if(!k)try{js(h,f,e);return e}catch(c){c=v(c);if(c[1]===cT[1]){var
i=c[4];if(typeof
i!=="number"&&17===i[0]){var
j=c[2],t=g(bP[1],j,f,i[1]),u=a(d[13],0),w=aI(j,f,e),x=a(d[3],sS),y=b(d[12],x,w),z=b(d[12],y,u);return cz(sT,b(d[12],z,t))}}else
if(c[1]===bm){var
A=a(d[3],c[2]),B=a(d[3],sU),C=a(d[13],0),D=aI(h,f,e),E=a(d[3],sV),F=b(d[12],E,D),G=b(d[12],F,C),H=b(d[12],G,B);return cz(sW,b(d[12],H,A))}if(a(i3,c)){var
l=b($[14],0,c),m=a(d[3],sP),n=a(d[13],0),o=aI(h,f,e),p=a(d[3],sQ),q=b(d[12],p,o),r=b(d[12],q,n),s=b(d[12],r,m);return cz(sR,b(d[12],s,l))}throw c}return e}function
bn(a,f,e,d,c,b){var
g=a?a[1]:0;return bl([0,g],f,e,[0,d,c,b])}function
jt(e,d){function
g(d){switch(d[0]){case
1:var
f=d[2],g=a(e,a(c[30],d[1])),h=b(c[85],l[16],g);return[1,h,jt(e,f)];case
2:return[2,a(e,d[1])];default:return d}}return b(f[17][68],g,d)}function
bo(c,a){var
d=a[2],e=a[1],f=b(cy,c,a[3]),g=jt(c,d);return[0,b(cy,c,e),g,f]}function
eC(e,d,k,a){function
g(d,a){var
i=b(c[3],e,a);if(0===i[0]){var
j=i[1]-d|0;if(0<j)try{var
l=b8(b(f[17][7],k,j-1|0)),m=b(c[h][1],d,l);return m}catch(b){b=v(b);if(b[1]===gu)return a;throw b}return a}function
n(a){return a+1|0}return y(c[dg],e,n,g,d,a)}return g(d,a)}function
sX(e,d,a){function
c(f,a){var
c=a[1],g=a[2];return[0,c+1|0,[0,b(bj,function(a){return eC(e,c,d,a)},f),g]]}return g(f[17][16],c,a,sY)[2]}function
eD(g,d,c){switch(c[0]){case
0:var
h=c[1];try{var
i=b(f[17][7],d,h-1|0);return i}catch(a){a=v(a);if(a[1]===gu)return c;throw a}case
1:var
j=c[2],k=c[1];return[1,k,a(eE(g,d),j)];case
2:return[2,bp(g,d,c[1])];default:var
e=b(f[17][7],d,c[1]-1|0);switch(e[0]){case
0:return[3,e[1]];case
1:throw[0,I,sZ];case
2:return[2,e[1]];default:return[3,e[1]]}}}function
bp(c,b,a){return eC(c,0,b,a)}function
eE(c,b){function
d(a){return eD(c,b,a)}return a(f[17][68],d)}function
dH(e,d,a){function
c(f,a){var
c=a[1],g=a[2];return[0,c+1|0,[0,b(bj,function(a){return eC(e,c,d,a)},f),g]]}return g(f[17][16],c,a,s0)[2]}function
R(d,c,b){return bp(d,a(f[8],c),b)}function
gv(j,e,f,d){switch(d[0]){case
0:var
i=d[1];return i===e?[2,f]:e<i?[0,i-1|0]:d;case
1:var
k=d[2],l=d[1];return[1,l,a(ju(j,e,f),k)];case
2:return[2,g(c[h][3],[0,f,0],e-1|0,d[1])];default:var
m=a(c[10],d[1]),n=g(c[h][3],[0,f,0],e-1|0,m);return[3,b(c[73],j,n)]}}function
ju(d,c,b){function
e(a){return gv(d,c,b,a)}return a(f[17][68],e)}function
gw(f,e,d){switch(d[0]){case
0:var
i=d[1];return e<=i?[0,i+f|0]:d;case
1:var
j=d[2],k=d[1];return[1,k,a(gx(f,e),j)];case
2:return[2,g(c[h][2],f,e+1|0,d[1])];default:var
m=a(c[10],d[1]),n=g(c[h][2],f,e+1|0,m);return[3,b(c[73],l[16],n)]}}function
gx(c,b){function
d(a){return gw(c,b,a)}return a(f[17][68],d)}function
cC(b,a){return gw(b,0,a)}function
bD(c,b){return a(gx(c,0),b)}function
jv(e,d,a){switch(d[0]){case
0:if(0===a[0])return d[1]===a[1]?1:0;break;case
1:if(1===a[0]){var
i=a[2],k=d[2],h=b(j[46],d[1][1],a[1][1]);if(h){var
l=function(a,b){return jv(e,a,b)};return g(f[17][23],l,k,i)}return h}break;case
2:if(2===a[0])return g(c[aJ],e,d[1],a[1]);break;default:if(3===a[0])return d[1]===a[1]?1:0}return 0}function
jw(n,h,m,l){var
p=l[1],e=m[1],s=l[2],t=m[2],k=n?n[1]:a(w[2],0),q=a(f[17][1],e),i=cf(q,0);function
u(f,c){var
h=c-1|0,k=Y(i,h)[h+1];if(k){var
l=k[1];if(f===l)return 0;var
g=function(c,e){var
f=a(bA,b(iZ,c,e)),g=a(j[2][8],f),h=a(d[3],s1),i=a(d[16],c),k=b(d[12],i,h);return b(d[12],k,g)},n=g(f,e),o=a(d[3],s2),q=g(l,e),r=a(d[3],s3),s=g(c,p),t=a(d[3],s4),u=b(d[12],t,s),v=b(d[12],u,r),w=b(d[12],v,q),x=b(d[12],w,o),y=b(d[12],x,n),z=a(d[49],y);return a(J[3],z)}var
m=c-1|0;return Y(i,m)[m+1]=[0,f]}function
y(d,c,a){var
e=b(bq[3][12],bq[4],bq[3][2]);return o(N[17],e,d,c,a)}var
z=b(c[x],e,k);function
r(n,m){var
e=n,c=m;for(;;){if(2===c[0])return 0;switch(e[0]){case
0:var
j=e[1];switch(c[0]){case
1:var
i=1;break;case
3:var
i=0;break;default:var
o=c[1];if(j<=q)try{var
p=u(j,o);return p}catch(b){b=v(b);if(b[1]===bm)return a(J[3],s5);throw b}return 0}break;case
1:var
E=e[2];switch(c[0]){case
1:var
F=c[2],G=function(b,a){return r(b,a)};return g(f[17][17],G,E,F);case
3:var
i=0;break;default:var
i=1}break;case
3:var
e=[0,e[1]];continue;default:var
i=0}if(i){var
s=dG(k,h,c),t=a(d[3],s6),w=dG(k,h,e),x=a(d[3],s7),A=b(d[12],x,w),B=b(d[12],A,t),C=b(d[12],B,s),D=a(d[49],C);return a(J[3],D)}if(3===c[0]){var
c=[0,c[1]];continue}var
l=dF(h,y(z,h,e[1]));if(jv(h,e,l))return a(J[3],s8);var
e=l;continue}}g(f[17][17],r,t,s);function
A(b){return b?[0,b[1]]:a(J[3],s9)}var
B=b(f[19][15],A,i);return bn(0,k,h,e,a(f[19][11],B),p)}function
s_(d,c,b){return bp(d,a(f[8],c),b)}function
dI(c){var
d=a(f[17][1],c);return b(A[8],0,d)}function
gy(d){var
c=a(f[17][1],d);function
e(a){return[0,c-a|0]}return b(D[56],c,e)}function
s$(a){function
c(a){return[0,a+1|0]}return b(D[56],a,c)}var
ta=Q[2][1];function
tb(c,a){return b(Q[2][4],a,c)}var
jx=b(f[17][15],tb,ta);function
eF(e,d){var
c=b(f[17][W],e,d),a=c[2],g=c[1];if(a)return[0,g,a[1],a[2]];throw[0,bm,tc]}function
jy(g,e){var
d=0,c=g,b=e;for(;;){if(0===c){if(b){var
h=b[2],i=b[1];return[0,h,i,a(f[17][9],d)]}}else
if(b){var
d=[0,b[1],d],c=c-1|0,b=b[2];continue}throw[0,bm,td]}}function
gz(d,c){var
e=a(f[17][1],d);function
g(a){return c+(a+1|0)|0}return a(jx,b(D[56],e-c|0,g))}function
jz(d,h){var
e=b(c[3],d,h);if(8===e[0]){var
f=t(bz),i=e[2],j=u===f?bz[1]:q===f?a(r[2],bz):bz;return g(c[a2],d,j,i)}return 0}function
jA(d,c){var
e=Q[2][1],g=1;function
h(f,c,e){return jz(d,a(a$,e))?b(Q[2][4],f,c):c}return o(f[17][85],h,g,e,c)}function
jB(k,j,i,e,d,g){var
l=a(aG,b(f[17][7],e,d-1|0)),n=l[3],o=l[2],p=a(c[h][1],d),m=b(M[16],p,o),q=b(c[h][1],d,n),r=m?bR(k,j,i,e,m[1],g):Q[2][1],s=bR(k,j,i,e,q,g),t=b(Q[2][7],r,s),u=a(Q[2][5],d);return b(Q[2][7],u,t)}function
bR(i,h,c,l,f,e){var
j=b(A[37],c,f);if(i)if(b(Q[2][3],e,j))var
m=g(eq,h,c,f),k=b(A[37],c,m),d=1;else
var
d=0;else
var
d=0;if(!d)var
k=j;var
n=Q[2][1];function
o(b){var
d=jB(i,h,c,l,b,e);return a(Q[2][7],d)}return g(Q[2][15],o,k,n)}function
te(i,a,e){var
d=Q[2][1],j=1;function
k(d,a,f){var
j=f[3],k=b(c[h][1],-d|0,e);return g(A[38],i,k,j)?a:b(Q[2][4],d,a)}return o(f[17][85],k,j,d,a)}function
jC(i,e,d){var
j=[0,e,1,0];function
k(j,d){var
f=d[2],g=d[1],k=d[3],e=a(aG,j),l=e[3],m=e[2],n=e[1],p=a(c[10],f),q=[0,ar(n,m,o(A[51],i,g,p,l)),k];return[0,b(c[h][1],1,g),f+1|0,q]}return g(f[17][16],k,d,j)[3]}function
gA(x,w,v,d,n,e,u){var
G=x?x[1]:1,H=w?w[1]:0,I=jA(d,n),J=bR(1,v,d,n,u,e),K=b(Q[2][7],J,I),L=G?gz(n,e):a(Q[2][5],e),p=b(Q[2][7],L,K),M=1;function
N(a,c){if(b(Q[2][3],a,p))if(a<e){var
f=e-a|0;return b(bj,function(a){var
c=b(A[37],d,a);return b(Q[2][3],f,c)?g(eq,v,d,a):a},c)}return c}var
q=g(f[17][71],N,M,n),O=a(f[17][1],q),y=a(Q[2][20],p),m=1,r=1,l=0,o=1,k=0,j=0,i=q,P=O-y|0;for(;;){if(i){var
z=i[2],B=i[1];if(b(Q[2][3],m,p)){var
m=m+1|0,R=[0,[0,r],j],r=r+1|0,l=[0,B,l],k=dx(a(c[10],(y+P|0)-(o-1|0)|0),k),j=R,i=z;continue}var
m=m+1|0,l=dx(c[16],l),S=[0,[1,o],j],o=o+1|0,k=[0,B,k],j=S,i=z;continue}var
s=a(f[17][9],k),C=a(f[17][9],l),t=a(f[17][1],s),D=a(f[17][9],j),T=1,U=function(b,a){return 0===a[0]?[0,a[1]+t|0,b]:[0,a[1],b]},V=g(f[17][71],U,T,D),W=function(a){return 0===a[0]?[0,a[1]+t|0]:[0,a[1]]},E=b(f[17][68],W,D);if(H)var
X=bp(d,E,u),Y=jC(d,b(c[h][1],-t|0,X),s),F=b(f[18],Y,C);else
var
F=b(f[18],s,C);return[0,[0,F,E,q],V]}}function
gB(n,e,p,m,u,F){var
G=u?u[1]:gz(p,m),H=bR(1,n,e,p,F,m),q=b(Q[2][7],G,H),I=1;function
J(a,c){if(b(Q[2][3],a,q))if(a<m){var
d=m-a|0;return b(bj,function(a){var
c=b(A[37],e,a);return b(Q[2][3],d,c)?g(eq,n,e,a):a},c)}return c}var
o=g(D[71],J,I,p),v=a(k[10][4],o),w=v-a(Q[2][20],q)|0,r=cf(v,tf),d=1,t=0,s=0,i=1,l=0,j=o;for(;;){if(j){var
x=j[2],K=j[1],y=b(bj,a(c[h][1],d),K);if(b(Q[2][3],d,q)){var
z=(d+w|0)-i|0;Y(r,z)[z+1]=[0,d];var
L=[0,[0,((w+d|0)-i|0)+1|0],l],d=d+1|0,t=[0,y,t],l=L,j=x;continue}var
B=i-1|0;Y(r,B)[B+1]=[0,d];var
d=d+1|0,s=[0,y,s],M=[0,[0,i],l],i=i+1|0,l=M,j=x;continue}var
C=a(D[9],l),N=b(f[18],t,s),O=a(D[9],N),P=a(f[19][11],r),R=1,S=function(d,a){return b(bj,function(f){var
a=bp(e,C,f);return b(c[h][1],-d|0,a)},a)},E=g(D[71],S,R,O),T=bn(0,n,e,E,C,o);return[0,T,bn(0,n,e,o,P,E)]}}function
gC(b){var
c=gy(b);return a(f[17][9],c)}function
_(a){return[0,a,gC(a),a]}function
jD(h,e,j,i){try{var
s=[0,h,1],t=function(l,p,k){var
m=k[2],f=k[1];if(m){var
h=a(a$,l),i=a(a$,p),n=g(c[aJ],e,h,i);if(n)var
j=n;else
var
B=b(P[30],e,h),C=b(P[30],e,i),j=y(N[81],0,f,e,B,C);if(0===j){var
q=o(A[hP],th,0,f,e),r=a(d[49],q),s=a(c[au][1],i),t=g(z[6],f,e,s),u=a(d[49],t),v=a(c[au][1],h),w=g(z[6],f,e,v),x=a(d[49],w);o(fT[3],ti,x,u,r)}return[0,b(c[aP],l,f),j]}return[0,f,m]},u=o(f[17][20],t,j,i,s)[2];return u}catch(e){e=v(e);if(e[1]===bm)return 0;var
k=a(h1[1],e),l=b(c[x],i,h),m=a(A[cp][7],l),n=a(d[49],m),p=b(c[x],j,h),q=a(A[cp][7],p),r=a(d[49],q);o(fT[3],tg,r,n,k);throw e}}function
jE(e,c,g,f){if(jD(e,c,g[3],f[1]))return 0;var
h=aI(e,c,f),i=a(d[3],tj),j=aI(e,c,g),k=a(d[3],tk),l=b(d[12],k,j),m=b(d[12],l,i);return cz(tl,b(d[12],m,h))}function
ao(g,f,e,c,b){var
j=b[3],k=b[2],m=c[2],n=c[1],h=g?g[1]:0,d=e?e[1]:l[16],i=X[1],o=i?1-h:i;if(o)jE(f,d,c,b);return bn([0,h],f,d,n,a(eE(d,m),k),j)}function
jF(e,c,a){var
d=a[2],g=a[3],h=a[1],i=b(bj,function(a){return bp(e,d,a)},c),j=[0,c,g],k=1;function
l(a){return cC(k,a)}return[0,[0,i,h],[0,tm,b(f[17][68],l,d)],j]}function
gD(d,a,c,b){function
e(c,b){return jF(a,c,b)}return bl(0,d,a,g(f[17][16],e,b,c))}function
c0(p,k,e,d,n,i){var
q=p?p[1]:0,j=b8(n),u=a(c[10],d);if(g(c[aJ],e,j,u))return _(i);if(o(c[h][14],e,1,d,j)){var
v=dy(d,j,i),w=function(b){var
a=b+1|0;return a===d?cC(-1,n):d<a?[0,a-1|0]:[0,a]},x=a(f[17][1],i);return bn([0,q],k,e,v,b(D[56],x,w),i)}var
l=gA(0,0,k,e,i,d,j)[1],m=l[2],y=l[3],z=l[1],r=b(f[17][7],m,d-1|0),s=0===r[0]?r[1]:ba(tn),t=bp(e,m,j),A=dy(s,t,z),B=1;function
C(d,a){return gv(e,s,b(c[h][1],-1,t),a)}return bn([0,q],k,e,A,g(f[17][71],C,B,m),y)}function
b_(e,d){var
f=a(bA,b(c[ny],d,e));return a(K[13][8],f)}function
jG(d,c){var
e=b(f[17][7],c,d-1|0);return a(k[10][1][9],e)}function
eG(a){var
c=a[1],d=a[2];function
e(a){switch(a[0]){case
0:if(jG(a[1],c))return 0;break;case
3:if(jG(a[1],c))return 0;break}return[0,a]}return b(D[65],e,d)}aD(1201,[0,jh,ji,b8,gt,jl,jm,jn,dE,jo,dF,jq,jr,dG,eB,b9,sJ,aI,sM,sN,b_,eA,js,bl,bn,bo,eC,sX,eD,bp,eE,dH,R,gv,ju,gw,gx,cC,bD,jw,s_,dI,gy,s$,jx,eF,jy,gz,jz,jA,jB,bR,te,jC,gA,gB,gC,_,jD,jE,ao,jF,gD,c0,eG],"Context_map");function
jH(b,e){var
d=t(b),f=u===d?b[1]:q===d?a(r[2],b):b,g=[0,a(aS[10],f),e];return a(c[30],g)}function
c1(e,d,b){var
f=[0,bh(e,d),b];return a(c[23],f)}function
to(d,c,b){return c1(d,c,a(f[19][12],b))}function
tp(f,b){var
d=b[2],e=t(ai),g=[0,d,a(c[21],[0,b[1],d,b[3]])],h=u===e?ai[1]:q===e?a(r[2],ai):ai;return c1(f,h,g)}function
eH(f,d,e,h){function
j(m,h,l,v){var
i=b(c[3],d[1],l);if(9===i[0]){var
e=i[2],n=t(aj),w=i[1],x=u===n?aj[1]:q===n?a(r[2],aj):aj;if(g(c[a2],d[1],x,w))if(4===e.length-1){var
z=Y(e,1)[2],A=y(T[2],0,0,m,d[1],z),f=b(c[3],d[1],A);if(6===f[0]){var
o=f[1],p=t(aq),B=f[3],C=f[2],D=u===p?aq[1]:q===p?a(r[2],aq):aq,s=t(ak),E=a(c[26],[0,D,h]),F=u===s?ak[1]:q===s?a(r[2],ak):ak,G=a(c[26],[0,F,h]),H=Y(e,3)[4],I=ag([0,o,0,C]),J=j(b(c[aP],I,m),G,H,B),K=Y(e,0)[1];return[0,[0,o,Y(e,2)[3],E,K],J]}throw[0,bm,tq]}}return[0,[0,k[9],l,h,v],0]}return j(f,h,e,y(T[2],0,0,f,d[1],e))}function
eI(d,j){var
h=t(ai),k=u===h?ai[1]:q===h?a(r[2],ai):ai,e=b(c[3],d,j);if(9===e[0]){var
f=e[2],i=e[1];if(g(c[a2],d,k,i))if(2===f.length-1){var
l=b(c[84],d,i)[2],m=Y(f,1)[2];return[0,[0,l,Y(f,0)[1],m]]}}return 0}function
tr(j,d,g){var
e=b(c[3],j,d);switch(e[0]){case
11:var
h=e[1][1];break;case
12:var
h=e[1][1][1];break;default:return[0,d,g]}var
k=a(w[31],h)[1][7],i=b(f[19][58],k,g),l=i[2];return[0,a(c[23],[0,d,i[1]]),l]}function
ts(k,d,f,e){function
l(e,s){var
v=g(N[29],k,d,s),h=b(c[3],d,v);if(9===h[0]){var
i=h[2];if(2===i.length-1){var
m=i[2],w=i[1],x=b(c[84],d,h[1])[2],f=b(c[3],d,m);if(7===f[0])var
o=f[2],p=f[1],D=f[3],E=b(c[aP],[0,p,o],k),F=[0,p,o,g(N[29],E,d,D)],j=a(c[21],F);else
var
j=m;var
y=[0,j,[0,a(c[10],e),0]],z=l(e-1|0,b(N[57],d,y)),n=t(aj),A=[0,w,j,a(c[10],e),z],B=u===n?aj[1]:q===n?a(r[2],aj):aj,C=[0,a(c[38],[0,B,x]),A];return a(c[23],C)}}return a(c[10],e)}return l(f,e)}function
jI(p,n,m){var
d=t(cR),s=u===d?cR[1]:q===d?a(r[2],cR):cR,e=a_(n,s),g=e[2],h=e[1],i=b(c[82],h,g)[2];function
j(b){if(b){var
e=b[2],d=b[1];if(e){var
f=a(a$,d),k=j(e),l=[0,a(iW,d),f,k],g=t(dn),m=[0,f,a(c[21],l)],n=u===g?dn[1]:q===g?a(r[2],dn):dn,o=[0,a(c[38],[0,n,i]),m];return a(c[23],o)}var
h=t(dm),p=[0,a(a$,d)],s=u===h?dm[1]:q===h?a(r[2],dm):dm,v=[0,a(c[38],[0,s,i]),p];return a(c[23],v)}throw[0,bm,tt]}var
k=j(a(f[17][9],m)),l=a(c[23],[0,g,[0,k]]);return[0,o(ae[2],0,p,h,l)[1],k,l]}function
c2(v,d,k){if(k){var
e=k[2],w=k[1];if(e){var
y=a(aG,w),m=y[3],K=y[1],L=a(f[17][1],e)+1|0,M=d[1],N=b(c[x],e,v),O=o(T[3],0,N,M,m),j=[0,m,a(aE[17],O),0],i=e;for(;;){var
n=j[3],z=j[1],P=j[2];if(i){var
A=i[2],B=a(aG,i[1]),p=B[3],C=a(c[21],[0,B[1],p,z]),D=t(ai),Q=[0,p,C],R=u===D?ai[1]:q===D?a(r[2],ai):ai,E=c1(d,R,Q),S=b(c[81],d[1],E)[1],F=b(c[84],d[1],S)[2],U=b(c[2][2],d[1],F),V=Y(a(ab[29][4],U),0)[1],s=a(ab[3][4],V),W=b(c[x],A,v),$=g(ab[23],P,s,ab[17][1]),X=o(T[3],0,W,d[1],p),Z=a(aE[17],X),_=g(ab[23],Z,s,$);d[1]=b(l[37],d[1],_);var
j=[0,E,s,[0,[0,F,C],n]],i=A;continue}var
aa=[0,a(c[10],1),2],ac=function(g,f){var
e=f[2],k=f[1],l=g[1],i=b(c[h][1],e,g[2]),m=b(c[79],d[1],i)[2],j=t(aj),n=[0,m,i,a(c[10],e),k],o=u===j?aj[1]:q===j?a(r[2],aj):aj,p=[0,er(d[1],[0,o,l]),n];return[0,a(c[23],p),e+1|0]},ad=g(f[17][16],ac,n,aa)[1],ae=[0,a(c[10],1),1,0],af=a(f[17][9],n),ah=function(y,l,d){var
e=d[2],f=d[1],m=d[3],i=a(aG,l),j=t(aq),n=i[3],o=i[1],p=u===j?aq[1]:q===j?a(r[2],aq):aq,k=t(ak),s=a(c[26],[0,p,f]),v=u===k?ak[1]:q===k?a(r[2],ak):ak,w=a(c[26],[0,v,f]),x=[0,ag([0,o,[0,s],g(c[h][2],1,e,n)]),m];return[0,b(c[h][1],1,w),e+1|0,x]},G=o(f[17][20],ah,af,e,ae),al=G[3],am=G[1];return[0,z,[0,ag([0,K,[0,am],g(c[h][2],1,L,m)]),al],ad]}}var
H=a(aG,w),J=H[3],an=H[1],ao=a(c[10],1),ap=b(c[h][1],1,J);return[0,J,[0,ag([0,an,[0,a(c[10],1)],ap]),0],ao]}throw[0,I,tu]}function
gE(an,w,d,o,n){var
p=b(c[x],o,w),F=y(T[2],0,0,p,d[1],n),G=g(N[70],p,d[1],F)[1],s=c2(p,d,cX(d[1],G)),i=s[2],m=s[1],H=s[3],e=a(f[17][1],i),I=aX(0,e),J=[0,b(c[h][1],e+1|0,n),I],K=a(c[23],J),L=b(c[44],K,i),O=a(j[1][6],tv),P=[0,a(k[8],O),m,L],z=a(c[21],P),A=t(ai),Q=[0,m,z],R=u===A?ai[1]:q===A?a(r[2],ai):ai,B=t(aq),S=c1(d,R,Q),U=u===B?aq[1]:q===B?a(r[2],aq):aq,C=t(ak),V=u===C?ak[1]:q===C?a(r[2],ak):ak;function
W(b){var
c=a(aG,b),d=a(f[8],c);return a(M[7],d)}var
X=h2(b(f[17][68],W,i));function
Y(d){var
e=a(f[17][5],d),g=a(f[17][6],d);return b(c[h][4],g,e)}var
Z=b(f[17][14],Y,X),v=b(c[h][1],e+1|0,m),_=eg(1,e+1|0,i),$=aX(0,e),aa=[0,b(c[h][1],2*(e+1|0)|0,n),$],ab=a(c[23],aa),ac=b(c[44],ab,_),ad=a(j[1][6],tw),ae=[0,a(k[8],ad),v,ac],af=a(c[21],ae);b(c[h][1],e,v);var
ag=a(c[10],1),D=t(aj),ah=[0,v,af,b(c[h][1],1,H),ag],al=u===D?aj[1]:q===D?a(r[2],aj):aj,am=c1(d,al,ah),E=b(c[45],z,o);cP(w,d,E);d[1]=a(l[bJ],d[1]);return[0,m,E,o,Z,U,V,am,S]}function
jJ(b){return a(az[46],[2,b])}function
dJ(m,i,e){var
n=a(w[31],e[1])[1],o=cq(i,e),p=a(Z[43],o),g=cX(i,b(f[17][68],c[bK],p)),q=n[7],j=a(f[17][1],g)-q|0;if(0===j)ad([0,0,ty,a(d[3],tx)]);var
k=b(f[17][W],j,g)[2],r=U(0,k),s=[0,a(c[28],e),r],t=a(c[23],s),u=U(0,g),v=[0,a(c[28],e),u],l=[0,i],x=a(c[23],v),h=gE(0,m,l,k,t);return[0,l[1],h[2],h[3],x,h[7],g,j,h[1]]}function
jK(c,a){return b(P[30],c,a)}function
gF(o,B,e,n){var
p=n[1],d=dJ(o,B,[0,p,n[2]]),q=d[7],g=d[6],r=d[1],C=d[8],D=d[5],E=d[4],F=d[3],G=d[2],f=jJ(p),H=b(bc[9],o,r),i=a(l[bJ],r),s=jK(i,E),I=jK(i,C),t=aV(b(K[5],f,tz),G,0,e,i,tA)[2],J=t[2],L=t[1],u=b(K[5],f,tB),N=b(K[5],f,tC),O=[0,ag([0,a(k[8],N),0,s]),g],v=aV(u,a(H,b(c[45],D,O)),0,e,L,tD)[2],P=v[2],Q=v[1];if(e)var
x=Q;else
var
Z=a(w[2],0),x=a(l[17],Z);var
j=aR(x,f2),m=j[1],z=b(ac[11],m,j[2]),A=a(M[7],z)[2][1],y=b(K[5],f,tE),R=[0,P,U(0,g)],S=[0,a(c[23],R),0],T=[0,J,U(q,F)],V=[0,a(c[23],T),S],W=di(y,e,m,g,A,[0,s,[0,b(c[h][1],q,I),V]]),X=[0,b(ay[32],0,u),0];b(gG[88],1,X);var
Y=[0,b(ay[32],0,y),0];b(gG[88],1,Y);return W}function
tF(d,c,b,a){gF(d,c,b,a);return 0}b7([0,tG,function(a,b){return b6(tF,a,b)}]);function
jL(e,j,n){try{var
t=gd(e,j,[0,[0,dp,0]],l[bX]),u=t[2][1],w=gd(e,t[1],[0,[0,dp,0]],l[bX]),_=w[1],$=b(c[h][1],1,w[2][1]),x=cA(e,_,0,a(c[20],[0,k[9],u,$])),y=x[2],A=aR(x[1],f2),aa=A[1],ab=a(c[23],[0,A[2],[0,n,u,y]]),B=o(ac[24],0,e,aa,ab),q=B[1],ad=g(N[29],e,q,B[2]),ae=b(P[30],q,ad),af=[0,j,b(P[30],q,y),ae];return af}catch(h){h=v(h);if(h===O){var
C=g(c[5],0,j,n),r=b(bS[1],e,C),p=r[1],D=r[2],m=dJ(e,j,dh(p)),i=m[1],E=m[6],F=m[5],G=m[2],H=a(d[3],tH),I=g(z[47],e,i,p),J=a(d[3],tI),K=g(z[47],e,i,p),M=a(d[3],tJ),Q=b(d[12],M,K),R=b(d[12],Q,J),S=b(d[12],R,I),T=b(d[12],S,H);b(L[8],0,T);var
U=[0,ag([0,k[9],0,n]),E],V=b(c[45],F,U),s=b(f[17][68],c[9],D),W=b(N[57],i,[0,V,s]),X=b(P[30],i,W),Y=[0,G,a(f[19][12],s)],Z=a(c[23],Y);return[0,i,b(P[30],i,Z),X]}throw h}}function
jM(k,v,u,j,t){var
e=[0,t],h=eH(j,e,v,a(c[11],u));if(k)var
d=h;else{if(h)if(h[2])var
r=h[1],G=eH(j,e,r[2],r[3]),d=b(f[18],G,h),m=1;else
var
m=0;else
var
m=0;if(!m)var
d=h}if(k)var
l=d;else{if(d)if(d[2])var
q=d[1],E=eH(j,e,q[2],q[3]),l=b(f[18],d,E),p=1;else
var
p=0;else
var
p=0;if(!p)var
l=d}function
w(b){var
f=b[2],h=a(s[48],b[3]),d=g(c[5],0,e[1],f);return[0,g(tK[8],j,e[1],d),h]}var
x=b(f[17][68],w,l);function
y(a){return F(o(s[72],tL,[0,a[1]],a[2],dK[7]))}var
z=k?f[17][14]:f[17][68],A=b(z,y,x),B=a(n[6],A),C=a(bO[8],e[1]),D=b(n[5],C,B);return b(i[72][1],0,D)}function
tM(s,d,p,j){function
k(o,B,n,m,l,f,k){var
e=b(c[79],d,f),p=e[3],q=[0,ag([0,e[1],0,e[2]]),0],i=[0,ag([0,n,0,p]),q],r=a(c[10],1),s=a(c[10],2),t=b(c[h][1],2,f),u=[0,b(c[h][1],2,l),t,s,r],v=[0,jH(aj,m),u],j=a(c[23],v),w=[0,b(c[h][1],2,o),[0,j]],x=a(c[23],w),y=b(c[45],x,i),z=g(c[h][2],2,2,k),A=b(c[h][5],j,z);return[0,y,b(c[44],A,i)]}function
l(i,e){var
g=b(c[3],d,e);if(6===g[0]){var
t=g[3],u=g[1],m=eI(d,g[2]);if(m){var
j=m[1],n=k(i,e,u,j[1],j[2],j[3],t),o=n[2],p=n[1],h=b(c[3],d,o);if(6===h[0]){var
q=h[2],r=h[1],v=h[3],w=b(c[79],d,p),s=l(a(f[9],w),v),x=s[1],y=a(c[20],[0,r,q,s[2]]);return[0,a(c[21],[0,r,q,x]),y]}return[0,p,o]}return[0,i,e]}return[0,i,e]}var
e=b(c[3],d,j);if(6===e[0]){var
q=e[3],r=e[1],m=eI(d,e[2]);if(m){var
i=m[1],n=k(p,j,r,i[1],i[2],i[3],q),o=l(n[1],n[2]);return[0,[0,o[1],o[2]]]}return 0}return 0}function
gH(d,i,e){function
n(A,e){var
o=eI(d,e);if(o){var
j=o[1],i=j[3],p=j[2],B=j[1];if(b(c[59],d,i))var
s=b(c[79],d,i),l=s[1],v=s[3];else
var
J=[0,i,[0,a(c[10],1)]],K=a(c[23],J),l=k[9],v=K;var
w=n(l,v),x=w[1],C=w[2],m=a(f[17][1],x),D=a(c[10],m+1|0),E=b(c[h][1],m+1|0,i),F=[0,b(c[h][1],m+1|0,p),E,D,C],G=[0,jH(aj,B),F],H=a(c[23],G),I=[0,ag([0,l,0,p]),0];return[0,b(f[18],x,I),H]}var
y=t(cr),L=u===y?cr[1]:q===y?a(r[2],cr):cr;if(g(c[a2],d,L,e)){var
z=t(cs),M=b(c[84],d,e)[2],N=u===z?cs[1]:q===z?a(r[2],cs):cs;return[0,0,er(d,[0,N,M])]}var
O=a(c[10],1);return[0,[0,ag([0,A,0,e]),0],O]}return n(i,e)}function
jN(m){function
d(d){var
n=a(i[68][3],d),p=a(i[68][4],d),h=a(i[68][5],d);function
v(b){var
d=t(cv),f=a(gc,b),i=u===d?cv[1]:q===d?a(r[2],cv):cv,e=g(c[a2],h,i,f);if(e)return e;var
j=b3(b);return a(A[bw],j)}var
w=b(f[17][bw],v,n)[1];function
x(d,v){var
w=d[3],x=d[2],y=d[1],h=a(cU,v),i=h[3],j=h[1],k=t(aj),z=u===k?aj[1]:q===k?a(r[2],aj):aj,l=a_(y,z),m=l[2],n=l[1],A=b(c[85],n,m)[2],o=[0,i,g(c[46],j,i,w)],B=[0,a(c[11],j[1]),x],C=[0,m,b(f[19][5],o,B)],e=t(ai),D=a(c[23],C),p=u===e?ai[1]:q===e?a(r[2],ai):ai,s=[0,a(aS[9],p),A],E=[0,a(c[28],s),o];return[0,n,D,a(c[23],E)]}var
j=aR(h,cs),z=j[2],k=aR(j[1],cr),e=g(eo,x,[0,k[1],z,k[2]],w),l=e[2],B=e[3],C=o(ae[2],0,p,e[1],l)[1],D=y(s[bY],0,[0,m],l,[0,B],cw),E=a(i[66][1],C);return b(i[73][2],E,D)}return a(i[68][8],d)}function
jO(e,d,B,A){var
C=b(c[91],d,B)[2],q=b(c[91],d,A),D=q[2],E=q[1],F=a(f[17][1],C),r=b(f[17][W],F,D),s=r[2],t=a(c[40],[0,E,r[1]]),G=y(T[2],0,0,e,d,t),H=g(N[70],e,d,G)[1];function
l(g,f,a){if(f){var
e=f[1];if(0!==e[0])return[0,e,l(g,f[2],a)];if(a){var
h=a[2],i=f[2],j=a[1],k=e[1];if(b(c[56],d,e[2])){var
m=y(T[2],0,0,g,d,j);return[0,[0,k,m],l(g,i,h)]}return[0,e,l(g,i,h)]}}else
if(a)throw[0,I,tN];return 0}var
J=l(e,a(f[17][9],H),s),m=[0,d],n=c2(e,m,a(f[17][9],J)),u=n[2],i=n[1],K=n[3],L=a(f[17][9],s),M=b(c[h][4],L,K),O=[0,t,aX(0,a(f[17][1],u))],v=dv(a(c[23],O),u),P=a(j[1][6],tO),p=a(k[8],P),Q=m[1],R=b(c[x],[0,[0,p,i],0],e),S=y(T[2],0,0,R,Q,v),w=aR(m[1],aj),U=w[2],V=w[1],X=a(c[10],1),Y=[0,U,[0,i,a(c[21],[0,p,i,S]),X,v]],z=a(c[23],Y),Z=b(c[x],[0,[0,p,i],0],e);return[0,o(ae[2],0,Z,V,z)[1],M,z,i]}function
jP(e,d,n,S,aa){var
aK=eF(S-1|0,n)[2],aL=a(k[10][1][4],aK),aM=b(c[h][1],S,aL),aN=a(G[1],S),aO=g(c[5],tP,d[1],aM),ab=b(bS[2],e,aO),E=ab[1],aP=ab[2],ac=a(w[32],E),i=ac[2],ad=ac[1],ae=b(f[17][W],ad[6],aP),af=ae[1],aQ=b(f[18],ae[2],[0,aN,0]),aR=a(Z[5],[0,E,af]),s=o(Z[64],e,d[1],1,aR),aS=a(f[17][9],s),ag=b(f[17][68],c[9],af),ah=b(f[17][68],c[9],aQ),u=0,K=ah,t=aS,H=0,T=0,F=0;for(;;){if(K){if(t){var
z=K[1],aT=t[2],aU=t[1],aV=K[2];if(b(c[51],d[1],z)){var
aW=b(A[38],d[1],z);if(b(f[17][22],aW,ag))var
B=0,L=0;else{var
aZ=b(A[38],d[1],z);if(b(f[17][22],aZ,u))var
B=0,L=0;else
var
ai=b(c[73],d[1],z),a0=a(k[10][1][4],aU),a1=b(A[37],d[1],a0),a2=1,a3=function(i){return function(e,c){if(c)try{var
g=b(f[17][7],i,e-1|0),h=a(M[2],g);return h}catch(a){a=v(a);if(a[1]!==gu)if(a[1]!==bm)throw a;var
d=1}else
var
d=c;return d}}(H),a4=[0,ai],a5=g(Q[2][15],a3,a1,a2)?[0,ai]:0,B=a5,L=a4}}else
var
B=0,L=0;var
aY=a(M[2],B)?F:F+1|0,u=[0,z,u],K=aV,t=aT,H=[0,B,H],T=[0,L,T],F=aY;continue}}else
if(!t){var
m=0,p=H,l=T,j=u,U=F;for(;;){if(p){var
aj=p[1];if(aj){if(l)if(j){var
m=[0,[0,aj[1]],m],p=p[2],l=l[2],j=j[2];continue}}else
if(l){var
ak=l[1];if(ak){if(j){var
al=j[2],am=l[2],V=ak[1],an=p[2],a6=[0,k[9],aa],a7=[0,a6,b(D[co],V-1|0,n)],a8=0,a9=function(m,n){return function(e,i){var
j=a(k[10][1][4],i),l=a(c[10],n-e|0),h=1-g(A[38],d[1],l,j);return h?h:b(f[17][25],[0,e],m)}}(m,V);if(g(D[50],a9,a8,a7)){var
m=[0,[0,V],m],p=an,l=am,j=al,U=U-1|0;continue}var
m=[0,0,m],p=an,l=am,j=al;continue}}else
if(j){var
m=[0,0,m],p=p[2],l=l[2],j=j[2];continue}}}else
if(!l)if(!j){var
X=a(f[17][9],m),a_=_(b(f[18],s,n)),a$=[0,a_,_(b(f[18],s,n))],ba=function(h,g){var
j=h[2],f=h[1],l=f[1];if(g){var
m=g[1],n=a(c[10],1),o=R(d[1],f,n),p=a(c[10],(m+i[6]|0)+1|0),q=R(d[1],f,p),r=b(c[73],d[1],q),k=gB(e,d[1],l,r,0,o),s=k[2],t=ao(0,e,[0,d[1]],k[1],f);return[0,t,ao(0,e,[0,d[1]],j,s)]}return[0,f,j]},ap=g(f[17][15],ba,a$,X),aq=ap[2],ar=ap[1],bb=a(c[10],1),bc=R(d[1],ar,bb),as=b(c[73],d[1],bc)-1|0,bd=a(f[9],aq),O=b(f[17][bI],(as+i[6]|0)+1|0,bd),be=a(f[8],aq),bf=b(f[17][bI],(as+i[6]|0)+1|0,be),bg=bD(-(i[6]+1|0)|0,bf),at=bn(0,e,d[1],n,bg,O),bh=0,bi=function(h,g,f){var
j=f[2],k=f[1];if(g){var
l=g[1],m=eD(d[1],j,[0,(i[6]+1|0)-h|0]),n=a(c[10],(l+i[6]|0)+1|0),o=R(d[1],f,n),p=b(c[73],d[1],o),q=c0(tS,e,d[1],p,m,k);return ao(tT,e,[0,d[1]],q,f)}return f},q=o(D[84],bi,bh,X,ar),bj=a(c[10],1),bk=R(d[1],q,bj),r=b(c[73],d[1],bk)-1|0,bl=_(n),bo=a(f[8],bl),bp=bD(i[6]+1|0,bo),bq=b(f[18],s,n),br=bn(0,e,d[1],bq,bp,n),P=ao(tU,e,[0,d[1]],q,br),au=R(d[1],P,aa),bs=a(f[7],q),av=b(f[17][W],r,bs),C=av[1],aw=b(f[17][co],i[6]+1|0,av[2]),bt=function(g){var
j=a(f[8],q),e=-i[6]|0,d=j;for(;;){if(d){var
h=d[1];if(0===h[0])if(g===h[1])return 0===b(f[17][7],C,g-1|0)[0]?[0,a(c[10],e)]:0;var
e=e+1|0,d=d[2];continue}return a(J[3],tV)}},bu=function(a){return a+1|0},bv=b(D[56],r,bu),bw=b(D[68],bt,bv),bx=a(f[17][9],bw),by=function(a){return a},ax=b(D[65],by,bx);if(0===U)var
aA=au,az=0,ay=0;else
var
b4=a(f[8],P),b5=dH(d[1],b4,s),b6=d[1],b7=function(a){return R(b6,P,a)},b8=b(f[17][68],b7,u),b9=[0,r+1|0,0,0,0],b_=function(b,k,j,h){var
e=b[4],f=b[3],g=b[2],d=b[1];return h?[0,d+1|0,dx(a(c[10],(r+i[6]|0)+1|0),g),f,e]:[0,d+1|0,[0,k,g],[0,j,f],[0,a(c[10],d),e]]},$=y(D[87],b_,b9,b5,b8,X),b$=$[4],ca=$[3],cb=a(f[17][9],$[2]),cc=a(f[7],q),aE=c2(b(c[x],cc,e),d,cb),aF=aE[3],aG=aE[1],cd=a(f[17][9],ca),aH=b(c[h][4],cd,aF),ce=a(f[17][9],b$),aI=b0(e,d,aG,b(c[h][4],ce,aF),aH),cf=b(c[81],d[1],aI)[1],cg=b(c[84],d[1],cf)[2],ch=b(c[h][1],1,au),ci=a(c[20],[0,k[9],aI,ch]),aJ=function(a){var
e=b(c[45],a,C),g=b(c[45],e,aw),h=R(d[1],at,g),i=[0,h,b(f[18],ah,ax)];return b(N[57],d[1],i)},cj=aJ(aH),aA=ci,az=[0,iq(e,d,[0,cg],aJ(aG),cj),0],ay=1;var
bz=d[1],bA=function(a){return R(bz,P,a)},bB=b(f[17][68],bA,ag),bC=a(c[h][1],-((r+i[6]|0)+1|0)|0),bE=b(f[17][68],bC,bB),bF=b(A[13],aA,C),aB=b(c[45],bF,aw),bG=b(c[5],tW,d[1]),aC=b(f[17][68],bG,bE),bH=g(c[5],tX,d[1],aB),bJ=o(bS[23],E,[0,ad,i],aC,bH),bL=a(Z[5],[0,E,aC]),aD=b(Z[60],e,bL),Y=_(n),bM=Y[3],bN=Y[1],bO=bD(i[6]+1|0,Y[2]),bP=b(f[18],s,bN),bQ=bn(0,e,d[1],bP,bO,bM),bR=ao(tY,e,[0,d[1]],q,bQ),bT=_(O),bU=a(f[8],bT),bV=_(C),bW=a(f[8],bV),bX=function(g){var
j=g[5],k=a(f[19][12],g[2]),l=b(f[19][15],c[9],k),m=b(f[19][15],c[9],j),n=dh(g[1]),o=[0,a(c[30],n),l],p=a(c[23],o),s=b(c[h][1],g[3],p),t=[0,s,aX(0,g[3])],u=[0,a(c[23],t),0],v=a(f[19][11],m),w=b(f[18],v,u),x=b(f[17][68],c[bK],g[4]),y=a(f[17][9],w),z=d[1];function
A(a){return dF(z,a)}var
B=b(f[17][68],A,y),D=bD(g[3],bU),i=b(f[18],B,D),E=dH(d[1],i,C),F=bD(r,i),G=b(f[18],bW,F),H=a(f[7],q),I=b(f[18],x,O),J=b(f[18],E,I),K=bn(0,e,d[1],J,G,H);return ao(tZ,e,[0,d[1]],K,bR)},bY=b(f[19][15],bX,aD),bZ=function(a){return a[3]},b1=b(f[19][15],bZ,aD),b2=function(e,d,b){return[0,a(c[9],e),d,b]},b3=o(f[19][60],b2,bJ,b1,bY);return[0,O,aB,b3,r,at,b(f[18],ax,az),ay]}throw[0,I,tR]}}throw[0,I,tQ]}}function
t0(e){function
f(f){var
r=a(cU,b(C[15],f,e)),t=r[2],G=r[3],m=a(C[2],f),H=a(C[5],f),k=b(c[3],m,G);if(6===k[0])var
x=k[3],o=gH(m,k[1],k[2]),p=o[2],q=o[1],z=[0,a(c[11],e),[0,p]],A=a(c[23],z),B=b(c[h][5],p,x),D=g(N[19],H,m,B),E=b(c[44],D,q),l=[0,[0,b(c[45],A,q),E]];else
var
l=0;if(l){var
u=l[1],v=u[2],w=u[1];if(t){var
I=b(c[h][9],[0,[0,e,t[1]],0],w),J=F(y(s[bY],0,[0,e],I,[0,v],cw)),K=F(a(s[76],[0,e,0]));return g(n[5],K,J,f)}var
L=a(c[au][1],w),M=b(bO[5],0,L),O=b(s[d5],e,v),P=a(i[72][7],O);return a(b(n[8],P,M),f)}var
Q=a(j[1][9],e),R=a(d[3],t1),S=b(d[12],R,Q);return g(n[23],0,S,f)}return b(i[72][1],0,f)}function
t2(k){var
p=a(i[68][4],k),l=a(i[68][5],k),m=a(i[68][2],k),e=b(c[3],l,m);if(6===e[0]){var
s=e[2],v=e[1],P=e[3],w=function(i){var
l=gH(i,v,s),d=l[1],A=b(c[h][5],l[2],P),B=b(c[45],A,d),C=[0,B,U(0,d)],D=a(c[23],C),E=b(c[44],D,d);function
k(b){var
c=t(b),d=u===c?b[1]:q===c?a(r[2],b):b,e=a(j[62][6],d);return a(bq[3][8],e)}var
w=[0,bq[3][1],[0,bq[3][4],0]],x=[0,k(ak),w],y=[0,k(aq),x],z=a(bq[3][15],y),F=g(a(N[16],z),p,i,E);function
m(h,l,d){var
b=d[2],e=d[1];if(h)return[0,[0,b,e],b];var
f=t(aq),i=u===f?aq[1]:q===f?a(r[2],aq):aq,g=t(ak),j=a(c[26],[0,i,b]),k=u===g?ak[1]:q===g?a(r[2],ak):ak;return[0,[0,j,e],a(c[26],[0,k,b])]}if(d){var
n=d[2],G=d[1];if(n)var
H=[0,0,a(c[10],1)],I=0,J=function(a,b){return m(I,a,b)},e=m(1,G,g(f[17][16],J,n,H))[1];else{a(c[10],1);var
e=[0,a(c[10],1),0]}}else{a(c[10],1);var
e=[0,a(c[10],1),0]}var
o=cA(p,i,0,F),K=o[2],L=o[1],M=[0,K,a(bd[70],e)],O=[0,v,s,a(c[23],M)];return[0,L,a(c[21],O)]};return b(cD[1],1,w)}var
o=a(d[3],t3);return b(n[65][4],0,o)}var
t4=a(i[68][8],t2);function
t5(m,l,e,k){function
d(f){var
g=a(i[68][4],f),d=jO(g,a(i[68][5],f),m,l),j=d[2],n=d[4],p=d[3],q=o(ae[2],0,g,d[1],j)[1],r=a(c[11],e),t=b(c[h][5],r,p),u=y(s[bY],0,[0,k],t,0,cw),v=y(s[bY],0,[0,e],j,[0,n],cw),w=a(i[66][1],q),x=b(i[73][2],w,v);return b(i[73][2],x,u)}return a(i[68][8],d)}function
t6(f,j){function
e(e){var
k=a(i[68][4],e),g=a(i[68][5],e);try{var
h=jL(k,g,b(C[35][16],f,e)),m=h[3],o=h[1],p=[0,m,[0,a(c[11],f),0]],q=b(N[57],g,p),r=y(s[bY],0,[0,j],q,0,cw),t=a(i[66][1],o),u=b(i[73][2],t,r);return u}catch(c){c=v(c);if(c===O){var
l=a(d[3],t7);return b(n[65][4],0,l)}throw c}}return a(i[68][8],e)}var
c3=[0,t0,t4,t5,function(d){function
c(c){var
e=a(i[68][4],c),f=a(i[68][5],c),g=a(iX,b(C[35][15],d,c));return jM(1,a(M[7],g),d,e,f)}return a(i[68][8],c)},t6];aD(1209,[0,c1,to,tp,eH,eI,tr,ts,jI,c2,gE,jJ,gF,jL,jM,tM,dJ,jN,gH,jO,jP,c3],nK);function
gI(b){var
c=t(b);return u===c?b[1]:q===c?a(r[2],b):b}function
dL(b){return[q,function(d){var
c=gI(b);return a(aS[9],c)}]}function
jQ(b){return[q,function(d){var
c=gI(b);return a(aS[10],c)}]}function
dM(b){return[q,function(d){var
c=gI(b);return a(aS[8],c)}]}var
b$=dL(a4),ca=jQ(bi),eJ=dM(io),cb=dL(bZ),cc=dL(dl),eK=dM(h_),eL=dM(cQ),eM=dM(h8),t8=dL(cS),t9=dL(iu);function
aN(a){return dM(H(b(J[17],t_,a)))}var
eN=aN(t$),eO=aN(ua),eP=aN(ub),eQ=aN(uc),eR=aN(ud),cd=aN(ue),eS=aN(uf),eT=aN(ug),eU=aN(uh),eV=aN(ui);aN(uj);var
eW=aN(uk),um=aN(ul),uo=aN(un),uq=aN(up),us=aN(ur),eX=jQ(aj);function
jR(b,d){var
c=t(b),e=u===c?b[1]:q===c?a(r[2],b):b;return bh(d,[2,e])}function
eY(b,e){var
d=t(b),f=u===d?b[1]:q===d?a(r[2],b):b;return a(c[38],[0,[1,f],e])}function
ut(e){var
b=t(b$),d=u===b?b$[1]:q===b?a(r[2],b$):b$;return a(c[38],[0,[2,d],e])}function
jS(d){var
b=t(eJ),c=u===b?eJ[1]:q===b?a(r[2],eJ):eJ;return bh(d,[1,c])}function
jT(a){return jR(t8,a)}function
uu(a){return jR(t9,a)}function
uv(a){return eY(um,a)}function
uw(a){return eY(uo,a)}function
ux(a){return eY(uq,a)}function
uy(a){return eY(us,a)}var
S=[cN,uz,cK(0)];function
cE(f,e,l,d,k){var
g=d[2],h=d[1],m=d[3],n=l[1],o=b(c[x],h,f),i=aH(hy(P[4],0,0,0,0,0,0,0,0,o),e,g),j=a(k,i),p=b(c[x],n,f);aH(b(ae[2],0,p),e,j);return[0,[0,[0,[0,h,g,m],b(c[83],e[1],i)]],j]}function
jU(e,d,A,ad,f,o,n){var
B=A[3];if(o){var
p=o[1],q=a(c[38],[0,f,p]),C=b(ax[97],e,f),E=b(c[2][2],d[1],p),F=b(ab[37][6],E,C),r=b(l[37],d[1],F),H=y(T[2],0,0,e,r,q);d[1]=r;var
t=q,s=H}else{switch(f[0]){case
0:throw[0,I,uB];case
1:var
Q=f[1],w=aH(b(l[168],0,e),d,Q),R=a(G[18],w),S=b(jV[16],e,w),U=a(c[9],S),k=[0,a(c[9],R),U];break;case
2:var
V=f[1],x=aH(b(l[nH],0,e),d,V),W=a(G[21],x),X=b(Z[1],e,x),Y=a(c[9],X),k=[0,a(c[9],W),Y];break;default:var
_=f[1],z=aH(b(l[170],0,e),d,_),$=a(G[23],z),aa=b(Z[2],e,z),ac=a(c[9],aa),k=[0,a(c[9],$),ac]}var
t=k[1],s=k[2]}var
j=s,i=n;for(;;){var
g=b(c[3],d[1],j);switch(g[0]){case
5:var
j=g[1];continue;case
6:if(i){var
u=i[1],K=g[3],L=g[2];if(u){var
O=i[2],j=b(c[h][5],u[1],K),i=O;continue}var
v=L,m=1}else
var
m=0;break;case
8:var
j=b(c[h][5],g[2],g[4]);continue;default:var
m=0}if(!m)var
v=a(J[3],uA);var
P=b(N[26],d[1],v);return[0,function(d){var
e=a(M[23],d),f=b(D[68],e,n),g=[0,t,a(aY[12],f)];return a(c[23],g)},P,B]}}function
c4(e,d,a,c,k,j,i){var
f=a[3],g=a[2],h=a[1],b=jU(e,d,[0,h,g,f],c,k,j,i);return cE(e,d,[0,h,g,f],[0,c,b[2],b[3]],b[1])}var
uC=b(br[1],0,eZ[2]);function
jW(g,f,e,d,a){var
h=b(c[x],e,g);return at(N[85],0,0,0,h,f,d,a)?1:0}function
jX(C,d,i,f){var
j=i[1],p=f[2],q=f[1],r=i[2];if(j){var
n=j[1],e=n[2][1],s=n[1][1],t=b(l[23],d[1],e),u=a(l[5],t),v=a(m[1],s),w=b(D[co],v,u),x=function(b){var
d=a(k[11][1][2],b);return a(c[11],d)},z=b(m[17],x,w),o=b(c[h][4],z,p);d[1]=g(l[31],e,o,d[1]);var
A=d[1],B=a(br[2],br[20]);d[1]=y(cu[16],B,uC,A,e,o);return[0,q,r]}throw[0,I,uD]}function
jY(d,c,b,a){var
e=a[2],f=b[2],g=jX(d,c,b[1],a[1]);return[0,g,ao(0,d,[0,c[1]],e,f)]}function
uE(j,e,d,a){var
f=a[2],h=a[1],i=g(j,e,d,[0,h,f,a[3]]),k=i[1][2],l=b(c[x],h,e);d[1]=o(ae[4],l,d[1],k,f);return i}function
bT(h,f,b,a,e){var
c=g(f,b,a,e),d=c[1][1];return d?jY(b,a,c,g(h,b,a,d[1][1])):c}function
bs(c,b,a){var
d=_(a[1]);return[0,cE(c,b,a,a,function(a){return a}),d]}function
uF(h,d,c,b){function
e(c,b,i){var
a=g(h,c,b,i),f=a[1][1];if(f){var
j=f[1][1];try{var
d=[0,b[1]],k=jY(c,d,a,e(c,d,j));b[1]=d[1];return k}catch(b){b=v(b);if(b[1]===S)return a;throw b}}return a}try{var
a=e(d,c,b);return a}catch(a){a=v(a);if(a[1]===S)return bs(d,c,b);throw a}}function
dN(b,a){var
c=[2,a];return function(a){return cW(b,c,a)}}function
jZ(b,a){var
c=[1,a];return function(a){return cW(b,c,a)}}function
bt(g,f){try{var
e=b(c[78],g,f)}catch(b){b=v(b);if(b===G[59])throw[0,S,a(d[3],uG)];throw b}return[0,e[1],e[2],e[3]]}function
j0(g,f){try{var
e=b(c[80],g,f)}catch(b){b=v(b);if(b===G[59])throw[0,S,a(d[3],uH)];throw b}return[0,e[1],e[2],e[3],e[4]]}function
bU(x,e,w,k,j,i,v){var
l=k?k[1]:0,m=j?j[1]:0,n=i?i[1]:0,o=b4(e,v),f=o[2],p=o[1],s=t(b$),y=u===s?b$[1]:q===s?a(r[2],b$):b$;if(1-a(dN(e,y),p))throw[0,S,a(d[3],uI)];var
z=b(c[84],e,p)[2],A=Y(f,0)[1],g=Y(f,2)[3],h=Y(f,1)[2],B=l?1-jW(x,e,w,h,g):l;if(B)throw[0,S,a(d[3],uJ)];var
C=m?1-b(c[51],e,h):m;if(C)throw[0,S,a(d[3],uK)];var
D=n?1-b(c[51],e,g):n;if(D)throw[0,S,a(d[3],uL)];return[0,z,A,h,g]}function
e0(e,i){var
f=b4(e,i),d=f[2],g=f[1],h=t(eX),j=u===h?eX[1]:q===h?a(r[2],eX):eX;if(cW(e,[3,j],g)){var
k=b(c[85],e,g)[2],l=Y(d,3)[4],m=Y(d,2)[3],n=Y(d,1)[2];return[0,[0,k,Y(d,0)[1],n,m,l]]}return 0}function
gJ(m,e,d,h){var
n=h[3],o=h[2],f=h[1];try{var
t=[0,d[1]],K=g(m,e,t,[0,f,o,n]);d[1]=t[1];return K}catch(h){h=v(h);if(h[1]===S){var
i=function(a){var
h=b(c[x],f,e);return g(bc[11],h,d[1],a)},p=i(o);try{var
k=b(c[78],d[1],p),u=k[3],w=k[1],y=[0,w,i(k[2]),u],r=a(c[20],y);try{var
l=bt(d[1],r),z=l[3],A=l[1],j=bU(e,d[1],f,0,0,0,l[2]),B=j[4],C=j[2],D=j[1],E=i(j[3]),F=[0,C,E,i(B)],H=[0,ut(D),F],I=[0,A,a(c[23],H),z],J=a(c[20],I),s=J}catch(a){a=v(a);if(a[1]!==S)throw a;var
s=r}var
q=s}catch(a){a=v(a);if(a!==G[59])throw a;var
q=p}return g(m,e,d,[0,f,q,n])}throw h}}function
e1(D,y,e,x){var
E=x[2],j=x[1],T=x[3],F=D?D[1]:0,z=bt(e[1],E),f=z[3],B=z[2],H=z[1],I=bU(y,e[1],j,0,0,0,B),U=I[4],J=e0(e[1],I[3]),K=e0(e[1],U);if(J)if(K){var
L=K[1],k=L[5],l=L[4],i=J[1],m=i[5],n=i[4],o=i[3],p=i[2],V=i[1];if(g(c[h][13],e[1],1,f))try{var
N=b(c[79],e[1],o)[3];if(!g(c[h][13],e[1],1,N))throw G[59];var
O=t(eS),$=u===O?eS[1]:q===O?a(r[2],eS):eS,ab=a(A[47],N),aa=[1,$],ac=[0,[0,p],[0,[0,ab],[0,[0,a(A[47],f)],[0,[0,n],[0,[0,l],[0,[0,m],[0,[0,k],uO]]]]]]],w=aa,s=ac}catch(b){b=v(b);if(b!==G[59])throw b;if(F)throw[0,S,a(d[3],uM)];var
M=t(eT),W=u===M?eT[1]:q===M?a(r[2],eT):eT,w=[1,W],s=[0,[0,p],[0,[0,o],[0,[0,a(A[47],f)],[0,[0,n],[0,[0,l],[0,[0,m],[0,[0,k],uN]]]]]]]}else
try{var
Q=b(c[79],e[1],o)[3];if(!g(c[h][13],e[1],1,Q))throw G[59];var
R=t(eU),ae=u===R?eU[1]:q===R?a(r[2],eU):eU,ag=a(A[47],Q),af=[1,ae],ah=[0,[0,p],[0,[0,ag],[0,[0,n],[0,[0,l],[0,[0,m],[0,[0,k],[0,[0,a(c[21],[0,H,B,f])],uR]]]]]]],w=af,s=ah}catch(b){b=v(b);if(b!==G[59])throw b;if(F)throw[0,S,a(d[3],uP)];var
P=t(eV),ad=u===P?eV[1]:q===P?a(r[2],eV):eV,w=[1,ad],s=[0,[0,p],[0,[0,o],[0,[0,n],[0,[0,l],[0,[0,m],[0,[0,k],[0,[0,a(c[21],[0,H,B,f])],uQ]]]]]]]}var
C=cB(y,e[1],[0,V],T),X=C[3],Y=C[2];e[1]=C[1];var
Z=_(j);return[0,c4(y,e,[0,j,E,X],j,w,[0,Y],s),Z]}throw[0,S,a(d[3],uS)]}function
uT(a){var
b=0;return function(c,d){return e1(b,a,c,d)}}function
uU(a,b,c){return uF(uT,a,b,c)}function
j1(Q,i,e,j){var
k=j[3],l=j[2],f=j[1],m=bt(e[1],l),n=m[3],o=m[2],s=m[1],w=bU(i,e[1],f,uV,0,0,o),p=w[2],C=w[3],y=_(f);if(g(c[h][13],e[1],1,n)){var
D=function(d){var
e=[0,s,o,b(c[h][1],1,d)];return a(c[21],e)};return[0,cE(i,e,[0,f,l,k],[0,f,a(A[47],n),k],D),y]}var
E=a(c[21],[0,s,o,n]);try{if(bL[1]){var
B=t(eW),K=u===B?eW[1]:q===B?a(r[2],eW):eW,L=[0,jS(e),[0,p]],M=a(c[23],L),N=b(c[x],f,i),P=[0,c4(i,e,[0,f,l,k],f,[1,K],0,[0,[0,p],[0,[0,aH(b(ac[24],0,N),e,M)],[0,[0,C],[0,[0,E],uY]]]]),y];return P}throw O}catch(h){h=v(h);if(h===O){var
F=b(c[x],f,i),G=bL[1]?a(d[7],0):a(d[3],uX),H=g(z[11],F,e[1],p),I=a(d[3],uW),J=b(d[12],I,H);throw[0,S,b(d[12],J,G)]}throw h}}function
j2(ah,i,e,x){var
y=x[3],z=x[2],o=x[1],p=0===ah?1:0,B=bt(e[1],z),L=B[2],M=B[1],ai=B[3],s=bU(i,e[1],o,0,[0,p],[0,1-p],L),N=s[4],O=s[3],v=s[1],aj=s[2];if(p)var
C=O,w=N;else
var
C=N,w=O;var
E=b(c[73],e[1],C),ak=bR(1,i,e[1],o,w,E);if(b(Q[2][3],E,ak))throw[0,S,a(d[3],uZ)];var
P=gB(i,e[1],o,E,0,w),j=P[1],F=j[1],al=P[2],G=R(e[1],j,C),f=b(c[73],e[1],G),l=R(e[1],j,w),m=R(e[1],j,aj),T=R(e[1],j,L),V=eF(f-1|0,F),H=V[1],X=a(k[10][1][1],V[2]),n=g(c[h][13],e[1],1,ai);if(a(c[2][4],v))var
Z=v,Y=y;else{var
J=cB(i,e[1],[0,v],y),aJ=J[3],aK=J[2];e[1]=J[1];var
Z=aK,Y=aJ}var
am=0===p?0===n?uy:ux:0===n?uw:uv,_=am(Z),an=R(e[1],j,z),$=b(c[78],e[1],an)[3];if(n)var
aa=a(A[47],$),ap=b(c[44],aa,H),aq=[0,X,b(c[h][1],-f|0,m),ap],ab=a(c[21],aq),I=aa;else
var
aC=g(c[h][2],1,f+1|0,$),aD=a(c[10],f),af=b(c[h][5],aD,aC),aE=aT(1,H),aF=b(c[44],af,aE),aG=[0,M,b(c[h][1],1-f|0,T),aF],aH=a(c[21],aG),aI=[0,X,b(c[h][1],-f|0,m),aH],ab=a(c[21],aI),I=af;var
ac=b(c[h][1],f,ab),ar=U(1,H),ad=dy(f,l,F),as=b(D[W],f-1|0,ad)[1];if(n)var
at=[0,b(c[h][1],-f|0,l),0],ae=g(c[h][3],at,f-1|0,I);else
var
K=t(ca),ax=[0,m,l],ag=u===K?ca[1]:q===K?a(r[2],ca):ca,ay=[0,a(c[38],[0,[3,ag],v]),ax],az=a(c[23],ay),aA=[0,b(c[h][1],-f|0,l),0],aB=[0,b(c[h][1],-f|0,az),aA],ae=g(c[h][3],aB,f-1|0,I);var
au=dF(e[1],l),av=c0(0,i,e[1],f,au,F),aw=ao(0,i,[0,e[1]],av,j);return[0,cE(i,e,[0,o,z,y],[0,ad,ae,Y],function(g){var
i=b(c[45],g,as),d=b(c[h][1],f,i),j=n?a(c[23],[0,_,[0,m,ac,l,d,G]]):a(c[23],[0,_,[0,m,l,ac,d,G]]),k=b(c[h][1],1,j),o=[0,k,[0,a(c[10],1)]],p=[0,a(c[23],o),ar],q=[0,M,T,a(c[23],p)],r=a(c[21],q);return R(e[1],al,r)}),aw]}function
c5(a,d){var
e=e0(a,d),f=e?e[1][5]:d,g=b(c[91],a,f)[1];return b(c[63],a,g)}function
u1(i,e,n){var
o=n[3],j=n[2],f=n[1],p=bt(e[1],j),E=p[2],R=p[3],T=p[1],s=bU(i,e[1],f,0,0,0,E),F=s[4],G=s[3],w=s[2],H=c5(e[1],G),U=H?c5(e[1],F):H;if(1-U)throw[0,S,a(d[3],u2)];try{var
V=e[1],W=b(c[x],f,i),X=g(Z[70],W,V,w)}catch(b){b=v(b);if(b===O)throw[0,S,a(d[3],u3)];throw b}var
I=a(Z[13],X),J=I[2],ad=I[1];if(a(D[48],J))return bs(i,e,[0,f,j,o]);var
Y=[0,jT(e),[0,w]],$=a(c[23],Y),aa=b(c[x],f,i);try{aH(b(ac[24],0,aa),e,$);var
ab=1,K=ab}catch(a){a=v(a);if(a!==O)throw a;var
K=0}if(K)return bs(i,e,[0,f,j,o]);var
L=cY(ad),P=L[2],k=L[1],l=dJ(i,e[1],k),ae=l[8],af=l[5],ag=l[2];e[1]=l[1];var
ah=a(m[9],P),y=b(c[h][4],ah,ae),ai=[0,jS(e),[0,y]],aj=a(c[23],ai),B=b(c[x],f,i);try{var
aq=aH(b(ac[24],0,B),e,aj)}catch(c){c=v(c);if(c===O){var
ak=b(z[44],B,k[1]),al=a(d[3],u4),am=g(z[11],B,e[1],y),an=a(d[3],u5),ao=b(d[12],an,am),ap=b(d[12],ao,al);throw[0,S,b(d[12],ap,ak)]}throw c}if(1-bL[1]){var
C=b(c[x],f,i),ar=a(d[3],u6),as=a(d[3],u7),at=b(z[44],C,k[1]),au=a(d[3],u8),av=b(z[44],C,k[1]),aw=a(d[3],u9),ax=a(d[13],0),ay=a(d[3],u_),az=g(z[11],C,e[1],w),aA=a(d[3],u$),aB=b(d[12],aA,az),aC=b(d[12],aB,ay),aD=b(d[12],aC,ax),aE=b(d[12],aD,aw),aF=b(d[12],aE,av),aG=b(d[12],aF,au),aI=b(d[12],aG,at),aJ=b(d[12],aI,as);throw[0,S,b(d[12],aJ,ar)]}var
aK=e0(e[1],af),aL=a(M[7],aK)[4],aM=a(A[47],aL),aN=a(D[9],J),Q=t(eQ),aO=b(c[h][4],aN,aM),aP=u===Q?eQ[1]:q===Q?a(r[2],eQ):eQ,aQ=b(N[57],e[1],[0,ag,P]),aR=b(c[x],f,i),aS=g(bc[9],aR,e[1],aQ),aT=[0,[0,y],[0,[0,aq],[0,[0,aS],[0,[0,aO],[0,[0,G],[0,[0,F],[0,[0,a(c[21],[0,T,E,R])],va]]]]]]],aU=_(f);return[0,c4(i,e,[0,f,j,o],f,[1,aP],0,aT),aU]}function
vb(h,e,j){var
n=j[3],o=j[2],f=j[1],k=bt(e[1],o),p=k[2],F=k[3],G=k[1],i=bU(h,e[1],f,0,0,0,p),s=i[4],w=i[3],l=i[2],y=i[1],A=c5(e[1],w),H=A?c5(e[1],s):A;if(1-H)throw[0,S,a(d[3],vc)];var
I=[0,jT(e),[0,l]],J=a(c[23],I),B=b(c[x],f,h);try{var
M=aH(b(ac[24],0,B),e,J)}catch(c){c=v(c);if(c===O){var
K=g(z[11],B,e[1],l),L=a(d[3],vd);throw[0,S,b(d[12],L,K)]}throw c}var
C=t(eN),N=u===C?eN[1]:q===C?a(r[2],eN):eN,Q=[0,[0,l],[0,[0,M],[0,[0,w],[0,[0,s],[0,[0,a(c[21],[0,G,p,F])],ve]]]]],P=[1,N];if(a(c[2][4],y))var
E=0,D=n;else{var
m=cB(h,e[1],[0,y],n),T=m[3],U=m[2];e[1]=m[1];var
E=[0,U],D=T}var
R=_(f);return[0,c4(h,e,[0,f,o,D],f,P,E,Q),R]}function
j3(k,f,j){var
l=j[3],i=j[2],h=j[1];try{var
w=function(a){var
d=b(c[x],h,k);return g(bc[11],d,f[1],a)},m=function(h){var
b=b4(f[1],h),c=b[2],e=b[1],g=t(cd),i=u===g?cd[1]:q===g?a(r[2],cd):cd,j=1-a(jZ(f[1],i),e),k=j||1-(8===c.length-1?1:0);if(k)throw[0,S,a(d[3],vf)];return[0,e,c]};try{var
K=m(i)[2],e=K,o=i}catch(a){a=v(a);if(a[1]!==S)throw a;var
n=w(i),e=m(n)[2],o=n}var
y=Y(e,0)[1],z=Y(e,1)[2],A=Y(e,2)[3],B=Y(e,3)[4],C=Y(e,4)[5],D=Y(e,6)[7],E=Y(e,7)[8],p=t(ca),F=b(c[91],f[1],E)[1],G=u===p?ca[1]:q===p?a(r[2],ca):ca;if(1-g(c[a2],f[1],[3,G],F))throw[0,S,a(d[3],vg)];var
s=t(eR),H=u===s?eR[1]:q===s?a(r[2],eR):eR,I=_(h),J=[0,c4(k,f,[0,h,o,l],h,[1,H],0,[0,[0,y],[0,[0,z],[0,[0,A],[0,[0,B],[0,[0,C],[0,[0,D],vh]]]]]]),I];return J}catch(a){a=v(a);if(a[1]===S)return bs(k,f,[0,h,i,l]);throw a}}function
gK(a,b,c){return bT(vb,u1,a,b,c)}function
j4(h,e,j){var
n=j[3],o=j[2],f=j[1],k=bt(e[1],o),p=k[2],I=k[3],J=k[1],i=bU(h,e[1],f,0,0,0,p),s=i[4],w=i[3],l=i[2],m=i[1],y=c5(e[1],w),K=c5(e[1],s),L=y||K;if(1-L)throw[0,S,a(d[3],vi)];var
M=[0,uu(e),[0,l]],N=a(c[23],M),A=b(c[x],f,h);try{var
R=aH(b(ac[24],0,A),e,N)}catch(c){c=v(c);if(c===O){var
P=g(z[11],A,e[1],l),Q=a(d[3],vj);throw[0,S,b(d[12],Q,P)]}throw c}if(y)var
B=t(eP),T=u===B?eP[1]:q===B?a(r[2],eP):eP,C=[1,T];else
var
H=t(eO),ae=u===H?eO[1]:q===H?a(r[2],eO):eO,C=[1,ae];var
U=[0,[0,l],[0,[0,R],[0,[0,w],[0,[0,s],[0,[0,a(c[21],[0,J,p,I])],vk]]]]];if(a(c[2][4],m))var
D=m;else{var
G=cB(h,e[1],[0,m],n),ad=G[2];e[1]=G[1];var
D=ad}var
E=jU(h,e,[0,f,o,n],f,C,[0,D],U),F=E[2],V=E[1],W=_(f);try{var
aa=b(c[x],f,h),ab=[0,[0,0,a(V,aH(b(ac[24],0,aa),e,F))],W];return ab}catch(i){i=v(i);if(i===O){var
X=e[1],Y=b(c[x],f,h),Z=g(z[11],Y,X,F),$=a(d[3],vl);throw[0,S,b(d[12],$,Z)]}throw i}}function
j5(k,e,j){var
i=j[3],l=j[2],f=j[1],m=bt(e[1],l),n=m[3],o=m[2],s=m[1],v=t(cc),D=u===v?cc[1]:q===v?a(r[2],cc):cc;if(1-a(dN(e[1],D),o))throw[0,S,a(d[3],vm)];var
x=_(f);if(g(c[h][13],e[1],1,n)){var
E=function(d){var
e=[0,s,o,b(c[h][1],1,d)];return a(c[21],e)};return[0,cE(k,e,[0,f,l,i],[0,f,a(A[47],n),i],E),x]}var
y=t(eK),F=a(c[21],[0,s,o,n]),G=u===y?eK[1]:q===y?a(r[2],eK):eK,z=[1,G];if(a(w[48],z)){var
p=cB(k,e[1],0,i),H=p[3],I=p[2];e[1]=p[1];var
C=I,B=H}else
var
C=c[2][3],B=i;return[0,c4(k,e,[0,f,l,B],f,z,[0,C],[0,[0,F],vn]),x]}function
j6(l,e,f){var
m=f[1],C=f[3],i=bt(e[1],f[2]),j=i[3],n=i[2],o=t(cb),D=i[1],E=u===o?cb[1]:q===o?a(r[2],cb):cb;if(1-a(dN(e[1],E),n))throw[0,S,a(d[3],vo)];var
F=_(m);if(g(c[h][13],e[1],1,j))var
p=t(eL),G=a(A[47],j),H=u===p?eL[1]:q===p?a(r[2],eL):eL,s=G,k=[1,H];else
var
B=t(eM),L=a(c[21],[0,D,n,j]),M=u===B?eM[1]:q===B?a(r[2],eM):eM,s=L,k=[1,M];if(a(w[48],k)){var
v=cB(l,e[1],0,C),I=v[2];e[1]=v[1];var
y=I}else
var
y=c[2][3];var
J=[0,a(c[38],[0,k,y]),[0,s]],z=a(c[23],J),K=b(c[x],m,l);aH(b(ae[2],0,K),e,z);return[0,[0,0,z],F]}function
e2(E,C,i,e,n){var
o=n[2],j=n[1],p=t(cd),F=b4(e[1],o)[1],G=u===p?cd[1]:q===p?a(r[2],cd):cd;if(a(jZ(e[1],G),F))return 0;var
k=bt(e[1],o)[2],s=t(cb),H=u===s?cb[1]:q===s?a(r[2],cb):cb;if(a(dN(e[1],H),k))return 3;var
w=t(cc),I=u===w?cc[1]:q===w?a(r[2],cc):cc;if(a(dN(e[1],I),k))return 2;var
l=bU(i,e[1],j,0,0,0,k),f=l[4],h=l[3],J=l[2];function
y(b,a){return mD(b,a)?0:1}if(C){if(b(c[51],e[1],h))if(b(c[51],e[1],f)){var
K=b(c[73],e[1],f);return[1,y(b(c[73],e[1],h),K)]}if(b(c[51],e[1],h))return vp;if(b(c[51],e[1],f))return vq;throw[0,S,a(d[3],vr)]}function
m(f,d){var
a=b(c[73],e[1],f),g=bR(1,i,e[1],j,d,a);return 1-b(Q[2][3],a,g)}if(b(c[51],e[1],h))if(b(c[51],e[1],f))if(m(h,f)){var
L=b(c[73],e[1],f);return[1,y(b(c[73],e[1],h),L)]}if(b(c[51],e[1],h))if(m(h,f))return vs;if(b(c[51],e[1],f))if(m(f,h))return vt;function
M(a){var
d=b(c[91],e[1],a)[1];try{var
f=g(c[5],vu,e[1],d);b(bS[1],i,f);var
h=1;return h}catch(a){a=v(a);if(a===O)return 0;throw a}}function
z(a){var
d=b(c[91],e[1],a)[1],f=b(c[x],j,i),h=g(bc[11],f,e[1],d);return b(c[63],e[1],h)}if(M(J))if(z(h))if(z(f))return[2,[0,[0,E,2],0]];if(jW(i,e[1],j,h,f))return vv;function
B(d,i){function
a(d){if(g(c[aJ],e[1],d,i))throw A[28];var
f=b(c[91],e[1],d),j=f[2],h=b(c[63],e[1],f[1]);return h?b(D[11],a,j):h}try{a(d);var
f=0;return f}catch(a){a=v(a);if(a===A[28])return 1;throw a}}if(!B(h,f))if(!B(f,h))throw[0,S,a(d[3],vw)];return 1}function
c6(b,e,d,a,c){var
f=a[1];try{var
h=g(b,d,a,c);return h}catch(b){b=v(b);if(b[1]===S){a[1]=f;return g(e,d,a,c)}throw b}}function
j7(b,f,d,a,c){var
e=a[1];try{var
j=g(b,d,a,c);return j}catch(b){b=v(b);if(b[1]===S){var
h=b[2];a[1]=e;try{var
i=g(f,d,a,c);return i}catch(b){b=v(b);if(b[1]===S){a[1]=e;throw[0,S,h]}throw b}}throw b}}var
j8=[cN,vx,cK(0)];function
vy(e,b,c){var
d=t(aW),f=j0(b[1],c[2])[2],g=u===d?aW[1]:q===d?a(r[2],aW):aW;if(cW(b[1],g,f))throw j8;return bs(e,b,c)}function
vz(j,e,a){var
f=a[3],g=a[2],d=a[1],i=j0(e[1],g),k=i[4],l=i[2],m=_(d);function
n(a){return a}return[0,cE(j,e,[0,d,g,f],[0,d,b(c[h][5],l,k),f],n),m]}function
vA(i,e,f){var
j=f[2],k=f[1];try{b(c[80],e[1],j);var
h=bs(i,e,f);return h}catch(h){h=v(h);if(h===G[59])try{var
l=b(c[x],k,i),m=g(N[29],l,e[1],j);b(c[78],e[1],m);throw[0,S,a(d[3],vB)]}catch(a){a=v(a);if(a===G[59])return bs(i,e,f);throw a}throw h}}function
gL(c,b,a){function
d(a){var
b=0;return function(c,d){return e1(b,a,c,d)}}return c6(gK,function(a,b,c){return bT(gL,d,a,b,c)},c,b,a)}function
j9(e){if(typeof
e==="number")switch(e){case
0:return j3;case
1:return j4;case
2:return j5;default:return j6}else
switch(e[0]){case
0:var
f=e[1];return function(a,b,c){return j1(f,a,b,c)};case
1:var
z=e[1],h=function(h,e,s){var
l=s[3],m=s[2],f=s[1],i=0===z?1:0,n=bt(e[1],m),t=n[2],A=n[3],B=n[1],o=bU(h,e[1],f,0,[0,i],[0,1-i],t),u=o[4],v=o[3],w=o[2];if(i)var
j=v,p=u;else
var
j=u,p=v;var
k=b(c[73],e[1],j),C=a(c[23],[0,w,[0,p]]),D=bR(0,h,e[1],f,C,k);if(b(Q[2][3],k,D)){var
E=e[1],F=b(c[x],f,h),q=g(N[29],F,E,w),G=e[1],H=b(c[x],f,h),r=g(N[29],H,G,p),I=a(c[23],[0,q,[0,r]]),J=bR(1,h,e[1],f,I,k);if(b(Q[2][3],k,J))throw[0,S,a(d[3],u0)];var
K=function(a){return a},y=b4(e[1],t)[1],L=i?a(c[23],[0,y,[0,q,j,r]]):a(c[23],[0,y,[0,q,r,j]]),M=a(c[20],[0,B,L,A]),O=_(f);return[0,cE(h,e,[0,f,m,l],[0,f,M,l],K),O]}return bs(h,e,[0,f,m,l])},i=function(a,b,c){return j2(z,a,b,c)};return function(a,b,c){return bT(i,h,a,b,c)};default:var
j=e3(e[1]),k=function(a,b,c){return bT(j,gK,a,b,c)};return function(a,b,c){return bT(j3,k,a,b,c)}}}function
vC(e){var
a=e[2],b=e[1];function
c(e,d,c,a){try{var
f=g(e,d,c,a);return f}catch(a){a=v(a);if(a[1]===S)return ad([0,b,vD,a[2]]);throw a}}function
d(d){function
a(c,b,a){return g(j9(g(d,c,b,a)),c,b,a)}function
b(b,c,d){return bT(a,uU,b,c,d)}function
c(c,d,e){return c6(a,b,c,d,e)}return function(a,b,d){return gJ(c,a,b,d)}}function
f(a){var
b=d(a);return function(a,d,e){return c(b,a,d,e)}}if(typeof
a==="number")switch(a){case
0:var
i=function(a,b,c){return e1(vE,a,b,c)},j=0,k=d(function(a,c,d){return e2(b,j,a,c,d)}),l=function(a,b,c){return j7(k,i,a,b,c)},m=function(a,b,c){return gJ(gL,a,b,c)},n=function(a,b,c){return c6(m,l,a,b,c)};return function(a,b,d){return c(n,a,b,d)};case
1:var
o=1;return f(function(a,c,d){return e2(b,o,a,c,d)});default:var
h=function(f,e,c){var
a=0,g=d(function(c,d,e){return e2(b,a,c,d,e)});function
i(a,b,c){return gJ(gL,a,b,c)}function
j(a,b,c){return c6(i,g,a,b,c)}function
k(a,b,c){return c6(vy,j,a,b,c)}try{var
l=bT(function(a,b,c){return c6(vA,h,a,b,c)},k,f,e,c);return l}catch(a){a=v(a);if(a===j8)return vz(f,e,c);throw a}},p=function(a,b,c){return e1(vF,a,b,c)},q=function(a,b,c){return j7(h,p,a,b,c)};return function(a,b,d){return c(q,a,b,d)}}var
r=a[1];return f(function(c,b,a){return r})}function
e3(c){var
a=b(m[19],vC,c);return a?g(m[20],bT,a[1],a[2]):bs}function
gM(r){function
d(d){var
e=a(i[68][4],d),s=a(i[68][5],d),f=a(i[68][2],d),p=o(T[3],0,e,s,f),q=a(aE[17],p),t=a(i[68][3],d),u=a(ax[48],e);function
v(b){var
c=a(k[11][1][2],b);return a(A[bw],c)}var
j=b(D[bw],v,t),w=j[1],x=b(c[bX],j[2],u),l=em(w),n=l[1],y=l[2],z=dw(vH,function(a){throw[0,I,vG]},n)[2],B=b(c[h][11],y,f);function
C(e){var
d=[0,e],f=g(e3(r),x,d,[0,n,B,q])[1][2],i=a(m[9],z),j=b(c[h][4],i,f);return[0,d[1],j]}return b(cD[1],1,C)}return a(i[68][8],d)}function
vR(e){var
c=e[2];if(typeof
c==="number")switch(c){case
0:return a(d[3],vS);case
1:return a(d[3],vT);default:return a(d[3],vU)}var
b=c[1];if(typeof
b==="number")switch(b){case
0:return a(d[3],vI);case
1:return a(d[3],vJ);case
2:return a(d[3],vK);default:return a(d[3],vL)}else
switch(b[0]){case
0:return 0===b[1]?a(d[3],vM):a(d[3],vN);case
1:return 0===b[1]?a(d[3],vO):a(d[3],vP);default:return a(d[3],vQ)}}var
dO=b(d[39],d[13],vR);aD(1214,[0,S,jX,uE,bT,j1,j2,gK,j4,j5,j6,bs,j9,e2,e3,gM,dO],"Simplify");function
bu(d,h){var
i=d?d[1]:0,c=a(f[17][9],h);if(c){var
e=c[1],k=c[2],l=i?b(K[5],e,vV):e,m=function(d,c){var
e=a(j[1][8],c),f=b(K[5],d,vW);return b(K[5],f,e)};return g(f[17][15],m,l,k)}throw[0,I,vX]}function
j_(f,e){var
c=f,a=e;for(;;){if(c){var
g=c[2],h=c[1];if(a){var
i=a[2],d=b(j[1][2],h,a[1]);if(0===d){var
c=g,a=i;continue}return d}return-1}return a?1:0}}var
al=a(f[21][1],[0,j_]),vY=al[1],vZ=al[2],v0=al[3],v1=al[4],v2=al[5],v3=al[6],v4=al[7],v5=al[8],v6=al[9],v7=al[10],v8=al[11],v9=al[12],v_=al[13],v$=al[14],wa=al[15],wb=al[16],wc=al[17],wd=al[18],we=al[19],wf=al[20],wg=al[21],wh=al[22],wi=al[23],wj=al[24],wk=al[25],wl=al[26];function
aU(b){return a(c[40],[0,b[1][5],b[3]])}function
j$(a){switch(a[0]){case
0:return a[1];case
1:return a[1];case
2:return a[1];default:return a[1]}}function
wm(f){var
c=j[1][9];function
e(b){return a(d[3],wn)}return b(d[39],e,c)}function
ka(f,e){var
c=f,a=e;for(;;){if(c){if(a){var
g=a[2],h=c[2],d=b(j[1][1],c[1],a[1]);if(d){var
c=h,a=g;continue}return d}}else
if(!a)return 1;return 0}}function
bV(a){return a[1][2]}function
gN(a){return bQ(a[1])}function
e4(a){return a[1][5]}function
kb(a){return a[1][8]}function
wo(a){return a[1][7]}function
kc(a){return a[1][6]}function
bE(a){return a[1][1][2]}function
e5(c){function
d(b){var
c=b[7],d=[0,aU(b)],e=bE(b);return ar(a(k[8],e),d,c)}return b(f[17][68],d,c)}function
wp(a){return gN(a[1])}function
e6(k,i,e){var
t=a(d[3],wq),l=e[7];if(l){var
m=l[1];if(0===m[0]){var
f=m[1];if(typeof
f==="number")var
h=a(d[3],wr);else
if(0===f[0]){var
p=f[1];if(p)var
J=a(d[16],p[1][1]),K=a(d[3],wv),q=b(d[12],K,J);else
var
q=a(d[3],ww);var
h=q}else{var
r=f[1];if(r)var
L=a(d[16],r[1][1]),M=a(d[3],wx),s=b(d[12],M,L);else
var
s=a(d[3],wy);var
h=s}var
n=h}else
var
n=a(d[3],wz);var
o=n}else
var
o=a(d[3],wA);var
u=a(d[3],ws),v=a(c[18],e[4]),w=g(z[11],k,i,v),x=a(d[3],wt),y=bQ(e),A=g(z[11],k,i,y),B=a(d[3],wu),C=a(j[1][9],e[2]),D=b(d[12],C,B),E=b(d[12],D,A),F=b(d[12],E,x),G=b(d[12],F,w),H=b(d[12],G,u),I=b(d[12],H,o);return b(d[12],I,t)}function
ce(h,e,i,k){var
l=i?i[1]:0;function
n(b){return l?b:a(d[7],0)}function
o(d,c,b){return eB(d,c,a(f[8],b))}function
m(i){switch(i[0]){case
0:var
r=i[4],A=i[2],p=i[1],D=i[3],E=a(f[7],p),q=b(c[x],E,h),F=function(c){try{var
s=m(c[1][4]),t=a(d[5],0),u=a(d[3],wE),v=a(d[3],wF),w=a(d[16],c[6]),x=a(d[3],wG),y=a(d[3],wH),A=g(z[11],h,e,c[1][1][6]),B=a(d[3],wI),C=a(d[3],wJ),D=aU(c),E=g(z[11],h,e,D),F=a(d[3],wK),G=a(d[13],0),H=a(d[3],wL),I=bu(0,c[4]),J=a(j[1][9],I),K=a(d[3],wM),L=e6(h,e,c[1][1]),M=a(d[3],wN),N=wp(c),O=g(z[11],h,e,N),P=a(d[3],wO),Q=b(d[12],P,O),R=b(d[12],Q,M),S=b(d[26],1,R),T=g(z[11],q,e,c[7]),U=b(d[12],T,S),V=b(d[12],U,L),W=b(d[12],V,K),X=b(d[12],W,J),Y=b(d[12],X,H),Z=b(d[12],Y,G),_=b(d[12],Z,F),$=b(d[12],_,E),aa=b(d[12],$,C),ab=b(d[12],aa,B),ac=b(d[12],ab,A),ad=b(d[12],ac,y),ae=b(d[12],ad,x),af=b(d[12],ae,w),ag=b(d[12],af,v),ah=b(d[12],ag,u),ai=b(d[12],ah,t),aj=b(d[12],ai,s),f=aj}catch(b){var
f=a(d[3],wB)}var
i=a(d[3],wC),k=bE(c),l=a(j[1][9],k),n=a(d[3],wD),o=b(d[12],n,l),p=b(d[12],o,i),r=b(d[12],p,f);return b(d[26],2,r)},G=g(d[39],d[5],F,A),H=e5(A),s=b(c[x],H,q),I=aI(h,e,p),J=a(d[3],wP),K=n(b(d[12],J,I)),L=a(d[5],0);if(0===r[0])var
M=r[1],N=g(z[11],s,e,D),O=a(d[3],wQ),P=n(b(d[12],O,N)),Q=g(z[11],s,e,M),S=a(d[3],wR),T=o(q,e,p),U=b(d[12],T,S),V=b(d[12],U,Q),B=b(d[12],V,P);else
var
Y=b_(s,r[1]),Z=a(d[3],wS),_=o(q,e,p),$=b(d[12],_,Z),B=b(d[12],$,Y);var
W=b(d[12],B,L),X=b(d[12],W,G);return b(d[12],X,K);case
1:var
t=i[1],aa=i[4],ab=i[3],ac=i[2],ad=a(f[7],t),u=b(c[x],ad,h),ae=a(d[7],0),af=function(f,c){if(c)var
e=m(c[1]);else
var
h=a(d[5],0),i=a(d[3],wT),e=b(d[12],i,h);var
g=b(d[23],2,e);return b(d[12],f,g)},ag=g(f[19][17],af,ae,aa),ah=a(d[13],0),ai=aI(h,e,t),aj=a(d[3],wU),ak=g(z[11],u,e,ab),al=a(d[3],wV),am=b(d[12],al,ak),an=b(d[12],am,aj),ao=b(d[12],an,ai),ap=n(b(d[12],ao,ah)),aq=a(d[5],0),ar=b_(u,ac),as=a(d[3],wW),at=o(u,e,t),au=b(d[12],at,as),av=b(d[12],au,ar),aw=b(d[12],av,aq),ax=b(d[12],aw,ap);return b(d[12],ax,ag);case
2:var
ay=i[1],az=m(i[2]),aA=a(d[5],0),aB=aI(h,e,ay),aC=a(d[3],wX),aD=b(d[12],aC,aB),aE=b(d[12],aD,aA),aF=b(d[12],aE,az);return b(d[26],2,aF);default:var
k=i[2],v=i[1],w=k[8],C=k[7],y=k[1],aG=i[3],aH=k[10],aJ=k[3],aK=k[2],aL=y[3],aM=y[2],aN=y[1],aO=a(f[7],v),l=b(c[x],aO,h),aP=m(aG),aQ=a(d[14],0),aR=aI(h,e,k[9]),aS=a(d[3],wY),aT=a(d[13],0),aV=aI(h,e,C),aW=a(d[3],wZ),aX=a(d[13],0),aY=aJ[2],aZ=a(f[7],w),a0=b_(b(c[x],aZ,h),aY),a1=a(d[3],w0),a2=a(d[13],0),a3=a(d[13],0),a4=a(f[7],w),a5=b(c[x],a4,h),a6=g(z[11],a5,e,aH),a7=a(d[3],w1),a8=aI(h,e,w),a9=a(d[3],w2),a_=k[6],a$=b(z[11],l,e),ba=g(d[39],d[13],a$,a_),bb=a(d[3],w3),bc=g(z[11],l,e,k[5]),bd=a(d[3],w4),be=a(d[13],0),bf=aI(h,e,v),bg=a(d[3],w5),bh=a(d[3],w6),bi=g(z[11],l,e,aK),bj=a(d[3],w7),bk=g(z[11],l,e,aL),bl=a(d[3],w8),bm=b(d[12],bl,bk),bn=b(d[12],bm,bj),bo=b(d[12],bn,bi),bp=b(d[12],bo,bh),bq=b(d[12],bp,bg),br=b(d[12],bq,bf),bs=b(d[12],br,be),bt=b(d[12],bs,bd),bv=b(d[12],bt,bc),bw=b(d[12],bv,bb),bx=b(d[12],bw,ba),by=b(d[12],bx,a9),bz=b(d[12],by,a8),bA=b(d[12],bz,a7),bB=b(d[12],bA,a6),bC=b(d[12],bB,a3),bD=b(d[12],bC,a2),bF=b(d[12],bD,a1),bG=b(d[12],bF,a0),bH=b(d[12],bG,aX),bI=b(d[12],bH,aW),bJ=b(d[12],bI,aV),bK=b(d[12],bJ,aT),bL=b(d[12],bK,aS),bM=b(d[12],bL,aR),bN=n(b(d[12],bM,aQ)),bO=a(d[14],0),bP=R(e,C,aM),bQ=g(z[11],l,e,bP),bR=a(d[3],w9),bS=a(j[1][9],aN),bT=a(d[3],w_),bU=o(l,e,v),bV=b(d[12],bU,bT),bW=b(d[12],bV,bS),bX=b(d[12],bW,bR),bY=b(d[12],bX,bQ),bZ=b(d[12],bY,bO),b0=b(d[12],bZ,bN),b1=b(d[12],b0,aP);return b(d[26],2,b1)}}try{var
p=m(k);return p}catch(b){return a(d[3],w$)}}function
kd(e,c,f){function
h(f){var
g=ce(e,c,0,f[4]),h=a(d[5],0),i=e6(e,c,f[1]),j=b(d[12],i,h);return b(d[12],j,g)}return g(d[39],d[5],h,f)}function
xa(e){var
c=a(w[2],0),f=ce(c,a(l[17],c),0,e);return b(d[48],hZ[9][1],f)}function
e7(c,d){var
e=a(c,d[5]),f=gO(c,d[4]),g=d[3];function
h(d){var
f=d[6];if(0===f[0])var
e=f[1],i=a(c,e[4]),j=a(c,e[3]),k=b(M[16],c,e[2]),h=[0,[0,a(c,e[1]),k,j,i]];else
var
g=f[1],h=[1,[0,g[1],g[2]]];var
l=d[5],m=a(c,d[4]),n=b(cy,c,d[3]),o=b(cy,c,d[2]);return[0,bo(c,d[1]),o,n,m,l,h]}var
i=b(M[16],h,g),j=bo(c,d[2]);return[0,gp(c,d[1]),j,i,f,e]}function
gO(c,d){function
g(d){switch(d[0]){case
0:var
h=d[4],j=d[3],k=d[2],l=d[1];if(0===h[0]){var
m=h[1],n=function(d){var
e=a(c,d[7]),g=d[6],h=d[5],i=d[4],j=b(f[17][68],c,d[3]),k=gp(c,d[2]);return[0,e7(c,d[1]),k,j,i,h,g,e]},o=b(f[17][68],n,k),p=bo(c,l),q=[0,a(c,m)];return[0,p,o,a(c,j),q]}var
r=bo(c,l);return[0,r,k,a(c,j),h];case
1:var
s=d[4],t=d[3],u=d[2],v=bo(c,d[1]),w=a(M[16],g),x=b(f[19][15],w,s);return[1,v,u,a(c,t),x];case
2:var
y=d[2],z=bo(c,d[1]);return[2,z,g(y)];default:var
e=d[2],A=d[3],B=bo(c,d[1]),i=e[1],C=i[3],D=i[2],E=i[1],F=e[6],G=g(A),H=a(c,e[10]),I=bo(c,e[9]),J=bo(c,e[8]),K=bo(c,e[7]),L=b(f[17][68],c,F),N=a(c,e[5]),O=e[4],P=e[3],Q=a(c,e[2]),R=a(c,C);return[3,B,[0,[0,E,a(c,D),R],Q,P,O,N,L,K,J,I,H],G]}}return g(d)}function
gP(d){var
a=d[7];if(a){var
b=a[1];if(0===b[0]){var
c=b[1];if(typeof
c==="number")return 1;else
if(0!==c[0])return 1}}return 0}function
gQ(E,p,v,n){function
V(a){return 1-gP(a[1])}var
i=b(f[17][61],V,n);function
W(f){var
b=f[1][7];if(b){var
c=b[1];if(0===c[0]){var
a=c[1];if(typeof
a==="number")var
e=0;else
if(1===a[0])var
e=0;else{var
d=a[1];if(d)return[0,d[1][1]];var
e=1}}}return 0}var
X=b(f[19][57],W,i),Z=a(f[17][1],i),q=a(f[17][1],n)-Z|0,B=a(f[17][1],i),m=0,d=0,l=n;a:for(;;){if(l){var
t=l[2],G=l[1],H=G[2],e=G[1],J=e[7];if(J){var
K=J[1];if(0===K[0]){var
C=K[1];if(typeof
C==="number"){var
aA=aX(0,a(f[17][1],i)),aB=[0,a(v,H),aA],m=m+1|0,d=[0,[0,1,a(c[23],aB)],d],l=t;continue}else
if(0!==C[0]){var
L=C[1],aD=L?L[1][1]:a(f[17][1],e[5])-1|0,aE=function(a){return bQ(a[1])},aF=b(f[17][68],aE,t),r=a(f[17][1],e[5]),_=aX(r+(q-1|0)|0,a(f[17][1],i)),$=[0,a(v,H),_],aa=a(c[23],$),w=(q-1|0)-m|0,ab=b(c[h][1],1,aa),ad=cf(1,a(k[8],e[2])),ae=cf(1,bQ(e)),af=b(A[8],r+1|0,m),ap=[0,a(c[10],r+1|0),0],y=[0,b(f[18],af,ap),0],x=0,s=aF,ac=[0,cf(1,aD),0];for(;;){var
F=y[2],z=y[1];if(x===w){var
aq=[0,b(c[h][1],w,ab),z],ar=a(c[40],aq),as=[0,ar,U(w,e[5])],at=a(c[23],as),av=b(c[45],at,F),aw=b(c[45],av,e[5]),ax=function(a){return[0,k[9],c[16]]},ay=b(f[17][56],q-1|0,ax),az=a(c[33],[0,ac,[0,ad,ae,cf(1,aw)]]),m=m+1|0,d=[0,[0,1,b(c[45],az,ay)],d],l=t;continue a}if(s){var
ag=s[2],ah=s[1],ai=[0,a(c[10],r+q|0),z],aj=a(c[40],ai),ak=a(j[1][6],xb),al=[0,[1,a(k[8],ak),aj,ah],F],am=[0,a(c[10],1),0],an=a(c[h][1],1),ao=b(f[17][68],an,z),y=[0,b(f[18],ao,am),al],x=x+1|0,s=ag;continue}throw[0,I,xc]}}}}var
aC=[0,[0,0,a(c[10],B)],d],B=B-1|0,d=aC,l=t;continue}var
aG=a(f[17][9],d),aH=function(a){return a[1]},M=b(f[17][30],aH,aG),aI=M[2],aJ=M[1],aK=0,aL=function(d,b){return[0,a(c[40],[0,d[2],b]),b]},aM=g(f[17][16],aL,aJ,aK),aN=0,aO=function(b,d){var
e=[0,d,a(f[17][9],b)];return[0,a(c[40],e),b]},aQ=g(f[17][15],aO,aN,aM),aR=b(N[18],E,p[1]),O=b(f[17][14],aR,aQ),aS=function(a){return a[2]},aU=b(f[17][68],aS,aI),aV=function(g){var
d=g[1],i=g[2],j=a(k[8],d[2]),l=bQ(d),e=d[5],m=a(f[19][12],O),n=a(f[19][12],aU),o=b(f[19][5],n,m),q=a(v,i),r=b5(p[1],q,o),s=U(0,e),t=a(f[17][1],e),u=b(c[h][1],t,r),w=b5(p[1],u,s),x=aT(1,e);return[0,j,l,b(c[45],w,x)]},aW=b(f[17][68],aV,i),D=a(f[17][aP],aW),aY=D[2],aZ=D[1],a0=a(f[19][12],D[3]),a1=a(f[19][12],aY),u=[0,a(f[19][12],aZ),a1,a0],a2=function(a){return gP(a[1])},P=b(f[17][30],a2,n),Q=u[3],R=u[2],S=p[1],a3=P[2],a4=P[1],a5=u[1],a6=function(a,k,d){if(a)return[0,a[1],0];var
e=b(A[66],S,d),h=g(c[df],S,e,d)[1],i=0;function
j(a,b){return a}return g(f[17][71],j,i,h)},a7=o(f[19][60],a6,X,Q,R),a8=b(f[19][15],c[au][1],R),a9=[0,a5,a8,b(f[19][15],c[au][1],Q)],a_=a(f[19][11],a7),T=o(e8[2],0,E,a_,a9),a$=function(d,e){var
b=e[1],f=e[2],g=Y(T,d)[d+1],h=[0,b[1],b[2],b[3],b[4],b[5],b[6],[0,[0,[0,[0,[0,g,0]]]]],b[8],b[9]];return[0,h,f,a(c[33],[0,[0,T,d],u])]},ba=b(f[17][13],a$,a3),bb=function(a,b){return[0,a[1],a[2],b]};return[0,ba,g(f[17][69],bb,a4,O)]}}function
xd(e,d,i,h,g){var
b=o(P[57],xe,i,e,h),j=b[3],k=i4(b[1],d,b[2],[0,g],e),l=[0,d,a(f[19][12],j)];return[0,k,a(c[13],l)]}function
bF(m,n,j,i){function
p(e,s,w,j){switch(j[0]){case
0:var
A=j[4],F=j[3],S=j[2],V=j[1],B=V[1];if(0===A[0]){var
aA=A[1],aB=function(c,b){var
d=b[3],e=b[2],f=b[1],g=c[7],h=[0,aU(c)],i=bE(c);return[0,f,e,[0,ar(a(k[8],i),h,g),d]]},G=g(f[17][16],aB,S,[0,e,s,B]),Y=G[3],_=G[2],aC=G[1],aD=b(c[45],aA,Y);return[0,_,aD,b2(aC,_,F,Y)]}var
aE=A[2],aF=A[1];if(a(f[17][48],S)){var
$=t(bZ),aG=u===$?bZ[1]:q===$?a(r[2],bZ):bZ,aa=a_(s,aG),ab=p(e,aa[1],w,[1,V,aF,aa[2],aE]),ac=t(cQ),aH=ab[2],aI=ab[1],aJ=u===ac?cQ[1]:q===ac?a(r[2],cQ):cQ,ad=a_(aI,aJ),H=ad[1],aK=ad[2],aL=[0,aK,[0,F,b5(H,aH,U(0,B))]],aM=a(c[23],aL),aN=b(c[45],aM,B);return[0,H,aN,b2(e,H,F,B)]}throw[0,I,xf];case
1:var
af=j[3],C=j[2],ag=j[1],D=ag[1],aO=j[4],ah=aR(s,aW),ai=ah[2],K=ah[1],aP=b(c[h][1],1,af),aQ=y(T[2],0,0,e,K,ai),i=[0,K],m=jP(e,i,D,C,a(c[22],[0,k[9],ai,aQ,aP])),aj=m[7],ak=m[5],E=m[1],aS=m[6],aT=m[4],aV=m[3],aX=m[2],aY=aj?b(e3(xg),e,i):function(a){return bs(e,i,a)},aZ=function(s,r){var
S=s[3],y=g(c[df],n[1],s[2],s[1]),T=y[2],j=g(av[20],e,n[1],y[1]),V=b(f[18],j,E),A=b(c[x],V,e),B=a(i8(A,n[1],aT),T),C=B[2],m=B[1];if(aj)var
Y=i[1],Z=b(c[x],m,A),t=g(bc[11],Z,Y,C);else
var
t=C;if(X[1]){var
_=b(f[18],j,E),D=b(f[18],m,_),$=a(d[3],xh);b(L[6],0,$);var
aa=b(c[x],D,e),ab=g(z[11],aa,i[1],t);b(L[6],0,ab);var
ac=a(d[3],xi);b(L[6],0,ac);var
ad=b9(e,i[1],D);b(L[6],0,ad);var
ae=a(d[3],xj);b(L[6],0,ae);var
af=a(c[hX],e),ah=a(c[au][5],af),ai=g(z[56],e,i[1],ah);b(L[6],0,ai)}var
ak=b(f[18],j,E),F=a(aY,[0,b(f[18],m,ak),t,w]),G=F[1],u=G[2],H=G[1],al=F[2];if(X[1]){var
am=a(d[3],xk);b(L[9],0,am);var
an=b(f[18],j,E),ap=b(f[18],m,an),aq=b(c[x],ap,e),ar=g(z[11],aq,i[1],u);b(L[6],0,ar)}var
as=ao(xl,e,[0,i[1]],S,ag),at=ao(xm,e,[0,i[1]],al,as);if(H)if(r){var
I=r[1],K=H[1],M=K[2],N=K[1],aw=N[1],O=p(e,i[1],N[3],I),o=O[1],ay=O[2],P=jw([0,e],o,at,j$(I)),az=U(0,a(f[9],P)),aA=R(o,P,b5(i[1],ay,az)),aB=b(l[24],o,M[1]),aC=a(l[5],aB),aD=function(b){var
d=a(k[11][1][2],b);return a(c[11],d)},aE=b(f[17][68],aD,aC),aF=a(f[17][1],aw),Q=b(f[17][W],aF,aE),aG=Q[2],aH=Q[1],aI=a(ax[10],e),aJ=function(c,b){return[0,a(k[11][1][2],c),b]},aK=g(f[17][69],aJ,aI,aG),aL=b(c[h][9],aK,aA),aM=b(c[h][4],aH,aL);i[1]=g(l[31],M[1],aM,o);var
v=u,q=1}else
var
q=0;else
if(r)var
q=0;else
var
v=u,q=1;if(!q)var
v=a(J[3],xn);var
aN=b(f[18],m,j);return b(c[45],v,aN)},a0=g(f[19][20],aZ,aV,aO),a1=R(i[1],ak,aX),a2=i[1],a3=function(a){return R(a2,ak,a)},a4=b(f[19][15],a3,a0),M=function(k){var
d=k;for(;;){var
e=b(c[3],i[1],d);if(8===e[0]){var
f=e[2],j=t(aW),l=e[4],m=u===j?aW[1]:q===j?a(r[2],aW):aW;if(cW(i[1],m,f)){var
d=b(c[h][5],f,l);continue}}return g(c[bI],i[1],M,d)}},a5=M(a1),a6=b(f[19][15],M,a4),a7=eF(C-1|0,D)[2],a8=a(k[10][1][4],a7),a9=b(c[h][1],C,a8),a$=a(c[10],C),al=g(Z[71],e,i[1],a9),am=al[1],ba=al[2],bb=o(Z[75],e,am[1],0,4),bd=[0,cq(i[1],am),ba],be=a(Z[5],bd),bf=at(Z[76],e,i[1],be,bb,a5,a$,a6),bg=[0,bf,a(f[19][12],aS)],bh=a(c[23],bg),bi=b(c[45],bh,D),an=b2(e,K,af,D),ap=b(P[30],i[1],bi);i[1]=o(ae[4],e,i[1],ap,an);return[0,i[1],ap,an];case
2:var
aq=j[1],as=aq[1],bj=aq[2],O=p(e,s,w,j[2]),v=O[1],bk=O[3],bl=O[2],bm=jl(xo,e,v,bj)[2],aw=a(f[19][70],bm),bn=a(c[23],[0,bl,aw]),bo=b(N[26],v,bn),bp=b(c[45],bo,as);return[0,v,bp,b2(e,v,gf(v,bk,aw),as)];default:var
Q=j[2],ay=j[1][1],bq=Q[6],br=Q[5],bt=Q[2],az=p(e,s,w,j[3])[1],bu=a(c[40],[0,br,bq]),bv=b(c[45],bu,ay);return[0,az,bv,b2(e,az,bt,ay)]}}var
e=p(m,n[1],j,i),s=e[3],v=e[2];n[1]=e[1];return[0,v,s]}function
gR(g,k,a,j,i){var
d=gQ(k,a,function(c){return b(j,a,c)},i),l=d[2],m=d[1];function
n(c){var
b=c[1],f=c[2],d=aV(b[2],c[3],[0,b[3]],g[1],a[1],xp),e=d[2],h=e[2],i=d[1];a[1]=e[1];o(cZ[26],0,[1,i],0,b[8]);return[0,b,f,h]}var
e=b(f[17][68],n,m);function
p(a){return a[3]}var
q=b(f[17][14],p,e);function
r(e){var
d=e[1],j=e[2],k=d[3],l=b(c[h][4],q,e[3]),f=aV(d[2],l,[0,k],g[1],a[1],xq),i=f[2],m=i[2],n=f[1];a[1]=i[1];o(cZ[26],0,[1,n],0,d[8]);return[0,d,j,m]}return[0,e,b(f[17][68],r,l)]}function
ke(p,k,d,o,e,m){if(m){var
j=m[1],s=d[4],t=_(j[2]),q=j[6];if(0===q[0]){var
u=q[1],v=u[2],H=v?v[1]:bF(p,k,s,e)[1],I=U(0,a(f[7],t)),J=[0,b5(k[1],H,I)],K=b5(k[1],u[1],J),L=a(f[7],t);return[0,d,o,m,e,b(c[45],K,L)]}var
w=q[1],M=bF(p,k,s,e)[1],x=U(0,j[2]),N=b5(k[1],M,x),y=b(D[W],j[5],j[3]),O=y[1],z=b(D[W],w[2],y[2]),P=z[2],Q=z[1],R=a(f[19][11],x),S=a(f[17][9],R),T=function(a){return c[16]},V=b(f[17][68],T,Q),A=b(f[17][57],V,S),X=cV(0,A,O),Y=g(c[h][3],A,j[5],j[4]),i=[0,d[1],d[2],d[3],d[4],X,Y,d[7],d[8],d[9]],B=d[7];if(B){var
C=B[1];if(0===C[0]){var
l=C[1];if(typeof
l==="number")var
n=0;else
if(1===l[0])if(l[1])var
n=0;else{if(1===e[0])var
Z=e[2],$=w[2],aa=a(f[7],e[1]),G=[1,[0,[0,(a(f[17][1],aa)-Z|0)-$|0,0]]];else
var
G=l;var
E=G,n=1}else
var
n=0;if(!n)var
E=l;var
F=[0,i[1],i[2],i[3],i[4],i[5],i[6],[0,[0,E]],i[8],i[9]],r=1}else
var
r=0}else
var
r=0;if(!r)var
F=i;return[1,F,o,j,e,P,N]}return[0,d,o,m,e,bF(p,k,d[4],e)[1]]}function
e9(n,e,m,s,B){var
t=s?s[1]:0;function
C(a){return ke(n,e,a[1],a[2],a[3],a[4])}var
p=b(f[17][68],C,B);if(p){var
i=p[1];if(0===i[0])if(!p[2]){var
l=i[1],R=i[4],S=i[3],T=i[2],v=g(N[18],n,e[1],i[5]);if(t){var
y=aV(l[2],v,[0,l[3]],m[1],e[1],xw),z=y[2],U=z[2],V=y[1];e[1]=z[1];o(cZ[26],0,[1,V],0,l[8]);a(bM[7],l[2]);var
A=U}else
var
A=v;return[0,[0,l,T,S,R,A],0]}}function
D(e){if(0===e[0]){var
f=e[1],g=a(d[3],xr),i=a(j[1][9],f[2]),k=a(d[3],xs),l=b(d[12],k,i),m=b(d[12],l,g);return ad([0,[0,f[1]],xt,m])}var
n=e[5],o=e[4],p=e[3],q=e[2],r=e[1];return[0,r,[0,q,p,o,n,b(c[h][1],1,e[6])]]}var
k=b(f[17][68],D,p);if(t){if(1<a(f[17][1],k)){var
E=function(a){return gP(a[1])};if(b(f[17][22],E,k))var
r=0;else
var
L=function(d){var
a=d[2],f=a[4],g=d[1],i=a[3],j=a[2],k=a[1],l=b(c[45],a[5],f),n=e[1],o=m[1],h=aV(b(K[5],g[2],xv),l,0,o,n,xu)[2],p=h[2];e[1]=h[1];return[0,g,[0,k,j,i,f,p]]},M=b(f[17][68],L,k),O=function(f,b){var
d=b[5],e=[0,d,aF(0,b[4])];return a(c[40],e)},q=gR(m,a(w[2],0),e,O,M),r=1}else
var
r=0;if(!r)var
F=function(d,a){return b(c[45],a[5],a[4])},q=gR(m,a(w[2],0),e,F,k)}else
var
P=a(f[17][5],k)[2][4],Q=b(c[x],P,n),q=gQ(Q,e,function(a){return a[5]},k);var
G=q[2],H=q[1];function
u(j){var
h=j[2],o=h[4],d=h[2],a=j[1],r=h[3],s=h[1],t=b(c[45],j[3],o),u=g(N[18],n,e[1],t),k=a[7],l=d[6];if(k){var
m=k[1];if(0===m[0]){var
q=m[1];if(0===l[0])var
i=0;else
var
p=[0,d[1],d[2],d[3],d[4],d[5],[1,[0,q,l[1][2]]]],i=1}else
var
i=0}else
var
i=0;if(!i)var
p=d;var
v=a[9],w=a[8],x=a[7],y=a[6],z=b(f[18],a[5],o);return[0,[0,a[1],a[2],a[3],a[4],z,y,x,w,v],s,[0,p],r,u]}var
I=b(f[17][68],u,H),J=b(f[17][68],u,G);return b(f[18],I,J)}function
c7(h,g,f,e,d,c,b){var
a=e9(h,g,f,0,[0,[0,e,d,c,b],0]);if(a)if(!a[2])return a[1];throw[0,bm,xx]}function
dP(g,c){var
d=c[3],e=c[2],h=c[1];function
i(c){if(1===c[0]){var
d=c[1][1];if(d){var
e=d[1],h=c[3];try{var
i=b(f[17][31],e,g),j=[1,a(k[8],e),i,h];return j}catch(a){a=v(a);if(a===O)return c;throw a}}}return c}return[0,b(f[17][68],i,h),e,d]}function
xy(e,h,d){function
i(d,a){var
f=b(c[x],d,e);o(ae[2],0,f,h,a);return 0}function
n(f,d,a){var
g=b(c[x],f,e);o(ae[4],g,h,d,a);return 0}function
l(r){var
d=r;for(;;)switch(d[0]){case
0:var
m=d[4],o=d[3],p=d[1],s=d[2];bl(0,e,h,p);var
C=function(g,d){var
j=d[1];i(0,gN(j));bl(0,e,h,j[2]);var
o=j[3];if(o){var
m=o[1];i(0,b(c[45],m[4],m[3]));var
p=m[6];if(0===p[0])i(0,p[1][1])}l(j[4]);i(g,d[7]);var
q=d[7];n(g,a(c[40],[0,d[1][5],d[3]]),q);var
r=a(f[17][1],g);if(d[6]===r){var
s=d[7],t=[0,aU(d)],u=bE(d);return[0,ar(a(k[8],u),t,s),g]}throw[0,I,xz]},D=a(f[7],p),q=g(f[17][15],C,D,s);i(q,o);if(0===m[0])n(q,m[1],o);return 0;case
1:var
j=d[1],t=d[4],u=d[3],v=d[2];bl(0,e,h,j);var
w=a(f[7],j),y=b(c[x],w,e);b(c[ny],v,y);i(a(f[7],j),u);var
z=a(M[13],l);return b(f[19][13],z,t);case
2:var
A=d[2];bl(0,e,h,d[1]);var
d=A;continue;default:var
B=d[3];bl(0,e,h,d[1]);var
d=B;continue}}return l(d)}function
kf(k,n,d,q,e){if(a(l[20],d[1]))throw[0,I,xA];var
h=[0,0];function
r(g,f,c,v){var
m=c[3];if(m){var
d=m[1],n=d[6];if(0===n[0]){var
e=n[1],o=i(g,f,c[4]),p=o[2],q=[0,o[1]],x=a(w[2],0),r=bF(x,q,c[1][4],p),y=r[1],z=q[1],A=k[1],B=[0,r[2]],s=aV(bu(0,[0,a(j[1][6],xC),v]),y,B,A,z,xB),t=s[2],C=t[2],D=t[1];h[1]=[0,[0,s[1],xD],h[1]];var
E=a(w[2],0),F=b(l[d2],D,E);return[0,F,[0,c[1],c[2],[0,[0,d[1],d[2],d[3],d[4],d[5],[0,[0,e[1],[0,C],e[3],e[4]]]]],p,c[5]]]}}var
u=i(g,f,c[4]);return[0,u[1],[0,c[1],c[2],c[3],u[2],c[5]]]}function
i(m,j,d){switch(d[0]){case
0:var
n=d[4],s=d[3],t=d[2],u=d[1];if(0===n[0]){var
H=n[1],I=function(c,j){var
e=j[3],m=c[4],d=c[1],z=j[4],A=j[2],B=j[1],C=dP(e,d[2]),D=d[4];function
i(a){switch(a[0]){case
0:var
c=a[4],d=a[3],g=a[2];return[0,dP(e,a[1]),g,d,c];case
1:var
h=a[4],j=a[3],k=a[2],l=a[1],m=function(a){return b(M[16],i,a)},n=b(f[19][15],m,h);return[1,dP(e,l),k,j,n];case
2:var
o=a[1],p=i(a[2]);return[2,dP(e,o),p];default:var
q=a[2],r=a[1],s=i(a[3]);return[3,dP(e,r),q,s]}}var
y=i(D),n=r(B,A,[0,d[1],d[2],d[3],y,d[5]],m),o=n[2],E=n[1],p=a(w[2],0),s=[0,b(l[d2],E,p)],g=c7(p,s,k,d[1],C,o[4],o[3]),F=g[5],G=s[1],H=k[1],t=aV(bu([0,q],m),F,0,H,G,xE),u=t[2],I=u[2],J=u[1];h[1]=[0,[0,t[1],xF],h[1]];var
v=a(w[2],0),K=b(l[d2],J,v),x=[0,[0,g[1],g[2],g[3],g[4],I],c[2],c[3],c[4],c[5],c[6],c[7]],L=aU(x);return[0,v,K,[0,[0,bE(c),L],e],[0,x,z]]},v=g(f[17][16],I,t,[0,m,j,0,0]);return[0,v[2],[0,u,v[4],s,[0,H]]]}return[0,j,[0,u,t,s,[1,n[1],n[2]]]];case
1:var
J=d[4],K=d[3],L=d[2],N=d[1],O=function(b,a){if(a){var
c=i(m,b,a[1]);return[0,c[1],[0,c[2]]]}return[0,b,0]},y=g(bd[64],O,j,J);return[0,y[1],[1,N,L,K,y[2]]];case
2:var
P=d[1],z=i(m,j,d[2]);return[0,z[1],[2,P,z[2]]];default:var
e=d[2],A=d[1],B=i(m,j,d[3]),C=B[2],p=[0,B[1]],D=a(w[2],0),Q=e[2],R=p[1],S=a(f[7],A),U=b(c[x],S,D),V=o(T[3],0,U,R,Q),E=bF(D,p,a(aE[17],V),C),W=E[1],X=p[1],Y=k[1],Z=[0,E[2]],F=aV(bu([0,q],e[4]),W,Z,Y,X,xG),G=F[2],_=G[2],$=G[1];h[1]=[0,[0,F[1],e[3]],h[1]];return[0,$,[3,A,[0,e[1],e[2],e[3],e[4],_,e[6],e[7],e[8],e[9],e[10]],C]]}}var
m=r(n,d[1],e,[0,e[1][2],0]),p=m[2];d[1]=m[1];return[0,h[1],p]}function
kg(e,j,d,c,i){var
k=c?c[1]:0,l=0;function
m(g,c){var
a=kf(e,j,d,k,c),h=a[2];return[0,b(f[18],g,a[1]),h]}var
h=g(f[17][89],m,l,i),n=h[2],o=h[1],p=a(w[2],0);function
q(a){return[0,a[1],a[2],a[4],a[3]]}return[0,o,e9(p,d,e,xH,b(f[17][68],q,n))]}function
xI(f,d,b){if(d){var
g=d[1];if(typeof
b!=="number"&&0===b[0]){var
e=b[1];if(1===e[0]){var
h=a(c[24],e[1]);return je(f,g[2],h)}}return 0}return 0}function
c8(b){return a(f[8],b[4])}function
kh(f){var
c=a(d[3],xM),e=a(d[3],xN);return ad([0,0,xO,b(d[12],e,c)])}function
gT(d,e){function
h(e){var
k=a(c[au][1],e),i=a(G[29],k);switch(i[0]){case
3:return b(P[30],d,e);case
9:var
j=i[1],l=i[2];if(3===a(G[29],j)[0]){var
m=a(c[9],j),n=b(P[30],d,m),o=[0,n,b(f[19][56],c[9],l)];return b(N[57],d,o)}return g(c[bI],d,h,e);default:return g(c[bI],d,h,e)}}return h(e)}function
x4(c){if(c){var
a=c[1];if(0===a[0]){var
d=a[1],e=function(a){return a[1]};return b(f[17][68],e,d)}return[0,a[1][2],0]}return 0}var
x5=a(D[76],x4);function
kk(O,m,aM,aV,e,V,x,M){var
aN=V?V[1]:0;function
Y(k,c,i,h,g,f,d){var
l=[0,g,e[1],0],m=bV(c),n=a(j[1][8],m);return b(d,c,[0,f,h,n,l,i,k,j[1][10][1]])}function
B(r,q,p){var
s=a(l[bJ],p),c=a(P[40],s);if(X[1]){var
t=kd(O,c,x),u=a(d[3],x6),v=b(d[12],u,t);b(L[9],0,v)}function
w(a){return gT(c,a)}function
z(a){return e7(w,a)}var
i=b(f[17][68],z,x);if(X[1]){var
A=kd(O,c,i),B=a(d[3],x7),C=b(d[12],B,A);b(L[9],0,C)}var
k=[0,c],m=kg(e,O,k,[0,aN],i),n=m[1],h=k[1],D=m[2];function
E(a){return gT(h,a)}function
F(a){return e7(E,a)}var
G=b(f[17][68],F,D),H=a(P[30],h);function
I(a){return e7(H,a)}var
o=b(f[17][68],I,G),J=a(l[bH],h);function
K(c){var
d=c[1],e=bV(a(f[17][5],o)),b=[0,a(j[1][8],e),0];return g(aK[22],1,b,[3,[0,[1,d],0]])}b(f[17][11],K,n);return y(r,q,n,J,2,o)}a(x5,aM);if(0===M[0]){var
aO=M[1];if(a(l[20],m[1]))throw[0,I,x8];var
aP=function(i,h,g,j,e){var
d=a(f[17][5],e);return Y(i,d,h,g,2,[1,b(c[82],m[1],d[5])[1]],aO)};return[0,B(aP,0,m[1]),0]}var
aQ=M[1];function
Q(h,g,e,j,d){function
i(f,d){var
i=b(c[82],m[1],d[5])[1];return Y(h,d,g,e,2,[1,i],a(aQ,f))}return b(f[17][12],i,d)}if(a(l[20],m[1])){if(e[2]){var
q=m[1],Z=bV(a(f[17][5],x)),_=[0,1,e[1],xP],$=a(l[38],q),aa=a(ki[8][18],$),r=a(w[2],0),ab=function(h){var
e=h[2],k=h[1];if(X[1]){var
m=g(z[11],r,q,e[1]),n=a(d[3],xQ),o=b(d[12],n,m);b(L[9],0,o)}var
p=a(c[hX],r),s=a(f[17][1],p),i=a(l[5],e),t=a(f[17][1],i)-s|0,j=b(f[17][W],t,i)[1],u=b(A[16],e[1],j);return[0,r,k,e,j,g(N[18],r,q,u)]},C=b(f[17][68],ab,aa),t=[0,q],E=[0,0],R=function(e,h){if(e){var
d=e[1],i=e[2],j=d[5],m=d[4],n=d[2],o=b(P[37],t[1],d[1]),p=function(e,d){var
h=t[1],j=b(k[11][13],c[11],m),o=[0,d,a(f[17][9],j)],p=a(c[40],o);t[1]=g(l[31],n,p,h);E[1]=[0,d,E[1]];return R(i,e)};return[1,o,h,b(P[30],t[1],j),p]}return[0,h]},ac=a(l[bH],q),ae=R(C,a(l[18],ac)),af=function(i){if(0===i[0])return ad([0,0,xS,a(d[3],xR)]);var
j=i[3];if(X[1]){var
m=a(d[3],xT);b(L[9],0,m)}var
F=[0,1],e=a(f[9],j[3]),ae=0===e[0]?[1,e[1]]:[2,e[1]],v=[0,q],n=j[2],o=a(f[17][9],E[1]),p=b(D[h],o,C);function
r(ad,e){var
D=ad[2],E=D[4],H=D[2],L=b(l[61],H,q);if(L)var
M=L[1];else{var
ak=F[1];F[1]++;var
al=a(J[22],ak),am=b(J[17],xU,al),M=b(K[5],Z,am)}var
A=e[4];if(A){var
V=A[1],B=a(gS[17],e[1]),C=B[1],W=B[2],X=C[2],Y=C[1],n=a(f[17][1],E),r=Y,p=V,m=0;for(;;){if(0===n){var
o=m,j=E,i=r,h=p,t=0;for(;;){if(o){if(j){var
w=j[2],x=o[2],u=o[1],Q=j[1];if(b(aB[3],1,i))if(b(aB[3],1,h)){var
R=b(aB[14],G[8],i),o=x,j=w,i=R,h=b(aB[14],G[8],h);continue}var
S=b(bb[10],u,i),T=b(bb[6],u,h);if(a(k[10][1][8],u))var
U=a(k[11][1][2],Q),z=[0,a(G[2],U),t];else
var
z=t;var
o=x,j=w,i=S,h=T,t=z;continue}}else
if(!j){var
_=e[7],$=e[6],aa=e[5],ab=e[3],ac=e[2],af=[0,[0,[0,b(gS[6],0,[0,[0,i,X],W]),ac,ab,[0,h],aa,$,_]],ae],N=y(bM[3],0,0,M,0,af),O=b(P[9],v[1],[1,N]),ag=O[2],ah=O[1],ai=[0,ag,b(f[17][68],c[9],t)],aj=a(c[40],ai);v[1]=g(l[31],H,aj,ah);return N}throw[0,I,xK]}}var
d=a(G[29],r),s=a(G[29],p);switch(d[0]){case
7:if(6===s[0]){var
n=n-1|0,r=d[3],p=s[3],m=[0,[0,d[1],d[2]],m];continue}break;case
8:if(8===s[0]){var
n=n-1|0,r=d[4],p=s[4],m=[0,[1,d[1],d[2],d[3]],m];continue}break}throw[0,I,xJ]}}throw[0,I,xL]}var
s=g(D[69],r,p,n);return B(Q,s,v[1])},ag=function(c){var
d=s[16],e=a(f[17][1],c[4]);return b(n[65][31],e,d)},ah=b(f[17][68],ag,C),ai=a(dQ[8],af),aj=a1(dQ[11],0,Z,0,_,ae,ai),ak=function(d,b){var
c=a(i[36],ah);return y(kj[5],0,1,0,c,b)[1]},al=b(dQ[20],ak,aj),am=function(d,b){var
c=a(n[65][24],be[6][1]);return y(kj[5],0,1,0,c,b)[1]},F=b(dQ[20],am,al),an=a(dQ[6],F);if(a(xV[8],an))var
H=e[2]?kh(0):o(bW[10],0,[0,F],1,0);else
if(e[2])var
H=[0,F];else
var
ao=a(d[3],xW),ap=a(d[3],xX),aq=a(d[3],xY),ar=b(d[12],aq,ap),H=ad([0,0,xZ,b(d[12],ar,ao)]);return[0,0,H]}var
aT=m[1],aU=bV(a(f[17][5],x)),as=[0,1,e[1],0],au=a(w[2],0),S=aR(aT,h9),av=S[2],T=aR(S[1],dl),aw=T[2],ax=a(l[bJ],T[1]),ay=a(l[162],ax)[1],p=a(P[40],ay),U=b(K[5],aU,x0),az=g(c[5],0,p,aw),aA=g(c[5],0,p,av),u=at(be[5],au,U,p,0,x1,aA,az),aS=0,aC=u[4],aD=u[3],aE=u[2][2],aF=u[1],aG=function(i,e,r,q){var
h=b(l[fC],p,i);function
m(a){return g(f[17][115],j[1][1],a,e)}function
n(e,h,d){var
i=a(l[6],h);function
j(b){var
c=a(k[11][1][2],b);return a(G[2],c)}var
n=b(f[17][68],j,i),o=[0,e,a(f[19][12],n)],p=b(aE,m,a(G[5],o)),q=a(c[9],p),r=b(N[26],d,q);return g(l[31],e,r,d)}var
d=g(l[28],n,h,h);function
o(e){var
f=a(c[9],e[2]),g=b(c[93],d,f)[2],h=b(c[91],d,g)[1];try{var
i=b(c[82],d,h)[1];return i}catch(a){a=v(a);if(a===G[59])throw[0,I,x2];throw a}}return B(Q,b(f[17][68],o,e),d)},aH=a(bW[1],aG),aI=[0,aH],aJ=[0,function(b){var
d=bq[6],e=a(c[9],b),f=a(w[2],0),h=o(N[16],d,f,p,e);return g(c[5],0,p,h)}],aL=a(l[bH],p);cg(be[7],U,[0,aD],aC,aL,0,0,[0,as],0,aJ,aI,x3,aF);return[0,0,aS]}return e[2]?kh(0):[0,B(Q,0,m[1]),0]}function
kl(g,f,e,d,c,a,b){var
h=a?a[1]:0;return kk(g,f,e,d,c,[0,h],[0,b,0],[0,function(b,a){return[0,b,a]}])}function
gU(h,g,f,e,d,a,c,b){var
i=a?a[1]:0;return kk(h,g,f,e,d,[0,i],c,[1,b])[2]}function
km(g,d,c){if(0===c[0])return[0,R(g,d,c[1])];var
h=c[2],i=c[1];try{var
j=a(f[8],d),e=b(f[17][7],j,i-1|0);if(0===e[0]){var
k=[1,e[1],h];return k}throw[0,I,x_]}catch(a){a=v(a);if(a===O)throw[0,I,x9];throw a}}function
gV(d,c,b){if(0===b[0])return[0,a(d,b[1])];var
e=b[2];return[1,a(c,b[1]),e]}var
a9=[0,vY,vZ,v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v_,v$,wa,wb,wc,wd,we,wf,wg,wh,wi,wj,wk,wl];aD(1223,[0,bu,[0,j_],a9,bE,aU,bV,gN,e4,kc,kb,wo,wm,ka,ce,xa,e5,e6,j$,xy,xd,bF,ke,e9,c7,kf,kg,xI,c8,gQ,gR,gU,kl,km,gV,gO,gT],nC);var
bf=[cN,x$,cK(0)],aO=[cN,ya,cK(0)];function
dR(c,b,e,h,g,d){if(g){if(d){var
k=d[2],l=d[1],m=g[2],n=g[1];try{var
j=gW(c,b,e,h,n,l),t=j[2],u=j[1],w=function(a){return bp(b,t,a)},p=a(f[17][68],w),x=a(p,m),y=ao(0,c,[0,b],dR(c,b,e,u,x,a(p,k)),j);return y}catch(d){d=v(d);if(d===aO){var
i=dR(c,b,e,h,m,k),q=a(f[8],i),o=function(a){return bp(b,q,a)},r=o(n),s=o(l);return ao(0,c,[0,b],gW(c,b,e,a(f[7],i),r,s),i)}throw d}}}else
if(!d)return _(h);throw bf}function
gW(j,a,i,f,e,d){if(g(c[aJ],a,e,d))return _(f);var
m=b(c[3],a,e);if(0===m[0]){var
k=m[1];if(!b(c[51],a,d))if(!g(c[h][13],a,k,d))throw bf;if(b(Q[2][3],k,i))return c0(0,j,a,k,[2,d],f);throw aO}var
n=b(c[3],a,d);if(0===n[0]){var
l=n[1];if(g(c[h][13],a,l,e)){if(b(Q[2][3],l,i))return c0(0,j,a,l,[2,e],f);throw aO}throw bf}var
o=b(c[91],a,e),p=o[1],s=o[2],q=b(c[91],a,d),r=q[1],t=q[2];if(b(c[63],a,p))if(b(c[63],a,r)){if(g(c[aJ],a,p,r))return dR(j,a,i,f,s,t);throw bf}throw aO}function
kn(c,a){var
d=[0,1,Q[2][1]];function
e(c,e,f){var
d=c[2],a=c[1];return 2===e[0]?[0,a+1|0,b(Q[2][4],a,d)]:[0,a+1|0,d]}return o(f[17][19],e,d,c,a)[2]}function
kp(a){var
c=Q[2][1];function
d(c,a){var
d=ko(a);return b(Q[2][7],c,d)}return g(f[17][15],d,c,a)}function
ko(b){switch(b[0]){case
0:return a(Q[2][5],b[1]);case
1:return kp(b[2]);default:return Q[2][1]}}function
e_(a){return 3===a[0]?1:0}function
e$(e,a){if(e){if(a){var
i=a[2],j=a[1],k=e[2],l=e[1];try{var
x=[0,kq(l,j)],g=x}catch(a){a=v(a);if(a!==aO)throw a;var
g=0}try{var
w=[0,e$(k,i)],h=w}catch(a){a=v(a);if(a!==aO)throw a;var
h=0}if(g)if(h){var
c=h[1],d=g[1],m=c[3],n=c[2],o=c[1],p=d[3],q=d[2],r=d[1],s=b(f[18],d[4],c[4]),t=b(f[18],p,m),u=b(f[18],q,n);return[0,b(f[18],r,o),u,t,s]}throw aO}}else
if(!a)return yb;throw bf}function
kq(e,c){var
d=a(V[1],e);if(typeof
d!=="number")switch(d[0]){case
0:var
i=d[2],k=d[1];if(2!==c[0])return[0,[0,[0,[0,k,i],c],0],0,0,0];break;case
1:var
l=d[3],m=d[2],n=d[1];switch(c[0]){case
1:var
o=c[2];if(b(j[46],n,c[1][1]))return e$(l,b(f[17][W],m,o)[2]);throw bf;case
2:break;default:throw aO}break;default:return[0,0,[0,[0,d[1],c],0],0,0]}if(2===c[0])return[0,0,0,[0,[0,e,c[1]],0],0];var
g=0;function
h(a,b){return[0,a,c]}return[0,0,0,0,[0,b(V[10],h,e),g]]}function
kr(d,c){var
e=c[2];try{var
g=a(f[17][9],e),h=function(a){return 1-e_(a)},i=[0,e$(d,b(f[17][61],h,g))];return i}catch(a){a=v(a);if(a===bf)return 0;if(a===aO)return 1;throw a}}function
fa(c,a){if(c){if(a){var
i=a[2],j=a[1],k=c[2],l=c[1];try{var
q=[0,ks(l,j)],d=q}catch(a){a=v(a);if(a!==aO)throw a;var
d=0}try{var
p=[0,fa(k,i)],e=p}catch(a){a=v(a);if(a!==aO)throw a;var
e=0}if(d)if(e){var
g=e[1],h=d[1],m=g[1],n=h[1],o=b(f[18],h[2],g[2]);return[0,b(f[18],n,m),o]}throw aO}}else
if(!a)return yd;throw bf}function
ks(d,e){var
c=a(V[1],e);switch(d[0]){case
0:return[0,[0,[0,d[1],c],0],0];case
1:var
g=d[2],h=d[1][1];if(typeof
c!=="number")switch(c[0]){case
2:break;case
0:return[0,0,[0,[0,c[1],d],0]];default:var
i=c[3],k=c[2];if(b(j[46],c[1],h))return fa(b(f[17][W],k,g)[2],i);throw bf}break;case
2:return yc}throw aO}function
kt(d,c){var
e=d[2];try{var
g=a(f[17][9],e),h=function(a){return 1-e_(a)},i=[0,fa(b(f[17][61],h,g),c)];return i}catch(a){a=v(a);if(a===bf)return 0;if(a===aO)return 1;throw a}}function
ku(g,e){var
c=b(f[17][W],g,e)[2],d=a(f[17][1],c);function
h(b){return a(k[10][1][9],b)}return[0,d,d-b(f[17][79],h,c)|0]}function
gX(j,r,e,o){if(o)var
u=0,v=function(d,c){var
e=a(f[17][1],c[2]);return b(J[6],d,e)},p=g(f[17][15],v,u,o);else
var
p=a(k[10][6],e[5]);var
h=r,q=p,m=0,l=b2(j,r,e[6],e[5]);for(;;){if(0===q)var
n=[0,h,m,l];else{var
w=b(c[x],m,j),y=g(N[29],w,h,l),i=b(c[3],h,y);switch(i[0]){case
3:var
s=g(i5[11],j,h,i[1]),h=s[1],l=s[2];continue;case
6:var
q=q-1|0,m=[0,[0,i[1],i[2]],m],l=i[3];continue;default:var
n=ad([0,0,yf,a(d[3],ye)])}}var
t=n[1],z=n[3],A=n[2],B=function(b){var
c=b[1];return a(f[17][1],b[2])<p?ad([0,c,yh,a(d[3],yg)]):0};b(f[17][11],B,o);var
C=eA(j,t,A);return[0,t,[0,e[1],e[2],e[3],e[4],C,z,e[7],e[8],e[9]]]}}function
gY(l,e,q,i){var
r=b(c[x],e,l),m=[0,0,0,0,0,j[1][10][1]];function
n(d,l){var
g=l[2],e=l[1],m=d[5],f=d[4],n=d[3],o=d[2],p=d[1],i=b8(g);if(0===g[0]){var
s=g[1];return[0,p,o,[0,[0,s,e],n],f,b(j[1][10][4],e,m)]}var
t=cP(r,q,i),u=b(j[1][10][4],e,m),v=b(c[h][1],f,t),w=[0,b(c[h][1],f,i)];return[0,[0,ar(a(k[8],e),w,v),p],[0,i,o],n,f+1|0,u]}var
d=g(f[17][15],n,m,i),o=d[5],p=d[3],s=d[2],t=d[1],u=[0,o,a(f[17][1],e),0];function
w(n,c){var
h=c[3],d=c[2],e=c[1],g=a(aG,n),i=g[3],l=g[2],o=g[1];try{var
r=b(f[17][31],d,p),s=[0,e,d-1|0,[0,ar(a(k[8],r),l,i),h]];return s}catch(c){c=v(c);if(c===O){var
m=b(av[29],o[1],e),q=[0,ar(a(k[8],m),l,i),h];return[0,b(j[1][10][4],m,e),d-1|0,q]}throw c}}return[0,s,t,g(f[17][16],w,e,u)[3]]}function
fb(o,k,j,n,i){var
p=b(c[x],k,j);function
q(f,d){var
e=d[2],g=d[1],i=a(aG,f)[2],j=a(M[7],i);return[0,[0,b(c[h][1],-e|0,j),g],e+1|0]}var
l=g(f[17][16],q,i,yi),d=l[2],r=l[1];function
s(a){var
b=a[1];return[0,b,cC(d,a[2])]}var
t=b(f[17][68],s,n),e=gY(j,b(f[18],i,k),o,t),m=e[2],u=e[3],v=e[1],w=a(f[17][1],m),y=b(f[18],m,u),z=a(c[h][1],-d|0),A=b(f[17][68],z,v);return[0,y,p,w+d|0,b(f[18],A,r)]}function
kv(e,c){if(go(e)){var
a=function(c){function
g(c){return b(yj[14],a,c)}function
d(k,d){if(4===d[0]){var
h=d[1],m=d[2],i=function(i,d){if(1===d[0]){var
n=d[1],k=function(a){if(a){var
c=a[1];if(0!==c[0])return b(j[1][1],n,c[1][2])}return 0};if(b(f[17][22],k,e)){var
o=[0,b(V[3],i,[13,[3,yk],0,0]),0],l=b(f[17][68],a,m),p=[4,h,b(f[17][57],l,o)];return b(V[3],i,p)}}return g(c)};return b(V[10],i,h)}return g(c)}return b(V[10],d,c)};return a(c)}return c}function
kw(i,h,j,f,e,g){var
c=kv(f[1],g);b(yl[9],[0,0===e?1:0],c);var
a=e8[5],d=y(e8[7],[0,[0,a[1],a[2],a[3],a[4],f[4],a[6]]],i,h,[0,e],c);return[0,d[1],d[2]]}function
kx(a){return a?[0,a[1]]:1}function
gZ(i,g,d,e,k,j){var
l=0;function
m(H){var
C=b(f[17][68],c[au][3],d),D=e[6],E=e[5],F=b(ax[25],C,i),G=b(dD[10],F,E);b(f[17][11],G,D);switch(k[0]){case
0:var
q=k[1],m=b(c[x],d,i),n=kx(j);return kw(m,g,d,e,n,at(a8[7],n,m,g,[0,e[5]],0,0,q));case
1:var
r=k[1],s=b(c[x],d,i);return kw(s,g,d,e,kx(j),r);default:var
t=k[1],u=a(ax[11],i),v=b(ax[49],u,i),p=b(c[x],d,v),w=0,y=1,z=function(f,b,e){var
d=a(bA,e);if(d){var
g=d[1];return[0,[0,g,a(c[10],f)],b]}return b},A=o(f[17][85],z,y,w,d),l=b(c[h][9],A,t),B=j?o(ae[4],p,g,l,j[1]):o(ae[2],0,p,g,l)[1];return[0,B,l]}}return b(dD[16],m,l)}function
g0(e,a,m,d,f,l,k){var
i=d[4],n=d[1],s=d[3],t=d[2];if(k){var
u=b(c[h][1],s,k[1]),o=b(P[30],a[1],u),p=gZ(e,a[1],n,m,l,[0,o]),v=p[2];a[1]=a1(ac[23],[0,ac[16]],0,0,0,e,p[1]);var
w=g(c[h][3],i,f,v),x=b(P[30],a[1],w),z=g(c[h][3],i,f,o);return[0,x,b(P[30],a[1],z)]}var
q=gZ(e,a[1],n,m,l,0),A=q[1],B=g(c[h][3],i,f,q[2]),j=a1(ac[23],[0,ac[16]],0,0,0,e,A),r=b(P[30],j,B);a[1]=j;return[0,r,y(T[2],0,0,t,j,r)]}function
g1(c,j,b,i,h,g,f,e){try{var
k=g0(c,b,i,fb(b,j,c,g,f),0,e,h);return k}catch(b){b=v(b);if(b[1]===cu[15])return bB(0,a(d[3],ym));throw b}}function
ky(j,d,e,R,u,t){try{var
w=a(A[76],t),y=a(A[76],e),l=[0,b(f[18],y,w)],z=function(c){var
d=a(a8[27],c);return d?d:b(f[17][25],c,l[1])},m=function(c){var
a=b(av[25],c,z);l[1]=[0,a,l[1]];return a},i=b(c[x],e,j),B=b(P[30],d[1],u),n=dz(i,d[1],B),C=n[2],p=cY(n[1]),q=p[1],D=p[2],E=b(bc[10],i,d[1]),r=b(f[17][68],E,C),F=b(bc[10],i,d[1]),s=b(f[17][68],F,D),G=b(f[18],s,r),H=[0,a(c[28],q),G],I=a(c[40],H),J=cq(d[1],q),K=b(Z[3],i,J),L=function(l,u){var
v=a(c[9],u),w=g(A[58],d[1],v,s),n=b(c[99],d[1],w),y=n[2],z=n[1],B=0;function
C(l,e){var
f=a(aG,l),g=f[3],h=f[2],j=f[1][1];if(j){var
n=m(j[1]);return[0,ar(a(k[8],n),h,g),e]}var
p=d[1],q=b(c[x],e,i),r=m(o(av[10],q,p,g,0));return[0,ar(a(k[8],r),h,g),e]}var
e=g(f[17][16],C,z,B),p=b(c[x],e,j),q=dz(p,d[1],y),D=q[2],r=cY(q[1]),t=r[2],h=r[1],E=dI(e),F=b(f[18],t,E),G=[0,a(c[31],[0,h,l+1|0]),F],H=a(c[40],G),I=dE(dI(e)),J=gy(e),K=dE(t),L=b(f[18],K,J);return[0,p,e,H,[1,[0,[0,h[1],l+1|0],h[2]],L],I,D]},M=b(f[19][16],L,K),N=function(g){var
k=g[2],m=g[6],n=g[5],o=g[4],p=g[3];a(f[17][1],e);var
i=a(f[17][1],k),l=b(f[18],k,e);try{var
q=a(c[h][1],i),s=b(f[17][68],q,r),t=bD(i,dE(dI(e))),u=kn(b(f[18],t,n),l),w=[0,[0,dR(j,d[1],u,l,s,m),i,p,o]];return w}catch(a){a=v(a);if(a===bf)return 0;if(a===aO)return 1;throw a}},Q=[0,[0,I,b(f[19][15],N,M)]];return Q}catch(a){a=v(a);if(a===O)return 0;throw a}}function
kz(d,c){var
e=c[2];function
k(l,q){var
d=q;for(;;){if(l){if(d){var
e=d[1],r=l[2],s=l[1];if(3===e[0]){var
d=d[2];continue}var
t=k(r,d[2]),h=a(V[1],s);if(typeof
h==="number")var
c=0;else
switch(h[0]){case
0:var
g=0,c=2;break;case
1:var
m=h[3],n=h[2],o=h[1];switch(e[0]){case
0:var
c=0;break;case
1:var
p=e[2];if(b(j[46],o,e[1][1]))var
g=k(m,b(f[17][W],n,p)[2]),c=2;else
var
g=0,c=2;break;default:var
c=1}break;default:var
g=0,c=2}switch(c){case
0:if(0===e[0])var
g=[0,e[1],0],i=1;else
var
i=0;break;case
1:var
i=0;break;default:var
i=1}if(!i)var
g=0;return b(f[18],g,t)}}else
if(!d)return 0;return 0}}return k(d,a(f[17][9],e))}function
yn(e,d,k,a){function
g(d,a){var
i=b(c[3],e,a);if(0===i[0]){var
j=i[1]-d|0;if(0<=j)try{var
l=b(f[17][31],j,k),m=b(c[h][1],d,l);return m}catch(b){b=v(b);if(b===O)return a;throw b}return a}function
n(a){return a+1|0}return y(c[dg],e,n,g,d,a)}return g(d,a)}function
yo(a){var
c=a[2];function
d(a){switch(a[0]){case
0:return 1;case
1:return 0;default:return 1}}return b(f[17][21],d,c)}function
fc(l,k,r){var
c=l[2],d=l[1],g=jy(k-1|0,r),h=g[3],m=g[2],e=g[1],i=a(aG,m),j=i[1],s=i[2],n=ky(d,c,e,j,i[3],h);function
t(a){if(typeof
a==="number"){if(0===a)return 0;throw[0,I,yp]}var
g=a[1],i=g[1],j=i[2],k=g[2],l=i[1],n=eD(c[1],j,g[4]),o=eA(d,c[1],l),p=[0,o,[0,n,b(f[17][W],k,j)[2]],[0,m,e]],q=bl(0,d,c[1],p);return[0,gD(d,c[1],q,h)]}if(n){var
o=n[1],p=o[2],q=o[1],u=function(a){return 1===a?1:0};if(b(f[19][22],u,p))return[0,[1,j[1],e,q]];var
v=[0,ar(j,s,q),e],w=b(f[18],h,v),x=b(f[19][15],t,p);return[0,[0,[0,k,eA(d,c[1],w),x]]]}return 0}function
g2(h,g,f){var
c=fc(h,f,g);if(c){var
d=c[1];if(0===d[0]){var
a=d[1],e=a[3],i=a[2],j=a[1],k=function(a){return 0===a?1:0};if(b(bd[21],k,e)){var
l=function(a){return 0};return[0,[0,j,i,b(bd[15],l,e)]]}return 0}return 0}return 0}function
kA(e,c){function
g(a){return a+1|0}var
h=a(f[17][1],c),i=b(D[56],h,g);function
j(a){return g2(e,c,a)}var
d=b(f[17][65],j,i);return d?[0,d[1]]:0}function
kB(c){function
e(d,c){function
h(d,c){switch(d[0]){case
0:return[0,[0,d[1],0],c];case
1:var
g=e(0,a(f[17][9],d[2]));return b(f[18],g,c);case
2:return c;default:return[0,[0,d[1],1],c]}}return g(f[17][16],h,c,d)}var
d=e(0,c);function
h(b,a){return b[1]-a[1]|0}return b(f[17][39],h,d)}function
yq(a){var
b=a[1];return a[2]?[3,b]:[0,b]}var
yr=a(f[17][68],yq);function
ys(e,d){return b(bj,a(c[h][1],e),d)}function
fd(e){var
h=1;return function(i){var
c=h,a=i;for(;;){if(a){var
d=a[1],f=a[2],g=b3(d);if(b(j[1][1],e,g))return[0,c,d];var
c=c+1|0,a=f;continue}throw O}}}function
kC(w,l,k,d){var
h=dw(0,function(a){throw[0,bm,yt]},k),i=h[3],m=h[1],n=a(c[75],l),j=b(f[17][68],n,m),o=0;function
p(d,c){return[0,a(fd(b(f[17][7],j,d[1]-1|0)),i)[2],c]}var
e=g(f[17][16],p,d,o),q=1;function
r(g,f){var
c=a(fd(f),e)[1];function
h(a){var
b=a[2];if(a[1]===g){var
d=b?[3,c]:[0,c];return[0,d]}return 0}return b(D[99],h,d)}var
s=g(f[17][71],r,q,j),t=1;function
u(c,e){var
f=a(fd(a(cU,e)[1][1]),i)[1];function
g(a){var
b=a[2];if(a[1]===f){var
d=b?[3,c]:[0,c];return[0,d]}return 0}return b(D[99],g,d)}var
v=g(f[17][71],u,t,e);return[0,em(e)[1],s,v]}function
kD(f,d,e){if(0===a(c[hX],d))return b(c[x],f,d);var
g=ap(cv,e),h=[0,ap(iv,e)],i=iY(a(k[7],f4),h,g),j=b(c[cm],i,d);return b(c[x],f,j)}function
yu(d,c){function
e(b){return ip(d,cv,a(gc,b))}return b(f[17][bw],e,c)}function
cF(m,i,h,g){var
e=g[1],n=g[2],o=b(c[x],e,i),k=b9(i,h,e);if(a(f[17][48],e))var
l=k;else
var
u=a(d[5],0),v=a(d[3],yw),w=a(d[5],0),y=b(d[12],w,v),z=b(d[12],y,u),l=b(d[12],z,k);var
p=eB(o,h,n),q=a(d[3],yv),r=a(j[1][9],m[2]),s=b(d[12],r,q),t=b(d[12],s,p);return b(d[12],t,l)}function
yx(d,c){var
e=b(f[17][7],d,c-1|0),g=a(f[7],e);return a(K[13][16],g)}var
yy=a(f[17][16],c[cm]);function
kE(i,h,g){function
j(a){return 0===a[2][2]?1:0}var
c=b(f[17][61],j,g);if(c){var
e=c[1][1],k=e[1],l=eu(i,h,e),m=a(d[3],yz);return ad([0,k,yA,b(d[12],m,l)])}return 0}function
fe(e,c){function
i(a){return a[7]?0:1}if(b(f[17][21],i,c))return[0,0,e];function
j(b){var
a=b[7];if(a)if(0!==a[1][0])return 0;return 1}if(b(f[17][21],j,c)){var
k=function(a){var
b=a[7];if(b){var
c=b[1];if(0!==c[0])throw[0,I,yB];var
d=c[1]}else
var
d=0;return[0,a[2],d]};return[0,[0,[0,b(f[17][68],k,c)]],e]}if(1!==a(f[17][1],c))ad([0,0,yD,a(d[3],yC)]);var
g=a(f[17][5],c)[7];if(g){var
h=g[1];if(0!==h[0])return[0,[0,[1,h[1][3]]],e]}throw[0,I,yE]}function
kF(h,f,e){var
c=X[1];if(c){var
i=function(a){return e6(h,f,a)},j=g(d[39],d[5],i,e),k=a(d[3],yF),l=b(d[12],k,j);return b(L[9],0,l)}return c}function
kG(h,d,n,m){function
o(a){var
d=b(c[44],a[6],a[5]);return[0,a[2],d,a[8]]}var
p=b(f[17][68],o,m),e=a(f[17][aP],p),i=e[2],j=e[1],q=at(a8[3],h,d[1],n,0,j,i,e[3]);function
r(e){var
b=ap(bz,d),f=y(T[2],0,0,h,d[1],b);return a(c[22],[0,k[9],b,f,e])}var
l=b(f[17][68],r,i);function
s(c,b){return ag([0,a(k[8],c),0,b])}var
t=g(f[17][69],s,j,l);return[0,q,a(f[17][9],t),l]}function
g3(h,e,ao,W,V,U,D){var
i=D[1],E=i[5],F=i[4],r=i[2],G=i[1],k=G[2],m=G[1],X=i[3],H=aH(y(a8[25],0,0,0,0,h),e,X)[2],I=H[1],Y=H[2],Z=I[2],_=I[1],$=F?F[1]:b(af[1],[0,m],yL),aa=b(a8[19],0,_),J=aH(function(a){return b(aa,a,0)},e,$),ab=J[1],s=b(f[18],Y,J[2]),g=b(P[36],e[1],Z),n=b(P[30],e[1],ab);function
u(b,a){if(b)if(0===b[1])return[1,a];return[0,a]}if(E){var
w=E[1];if(0===w[0]){var
K=w[1];if(K){var
t=K[1];try{var
am=b(A[6],t[2],g)[1],an=[0,[0,u(r,[0,[0,a(f[17][1],g)-am|0,[0,t]]])]],L=an}catch(c){c=v(c);if(c!==O)throw c;var
ac=a(d[3],yG),ae=a(j[1][9],t[2]),ag=a(d[3],yH),ah=b(d[12],ag,ae),ai=b(d[12],ah,ac),L=ad([0,[0,t[1]],yI,ai])}var
M=L}else
var
M=[0,[0,u(r,0)]];var
N=M}else
var
S=w[1],N=[0,[1,[0,S[1],S[2]]]];var
p=N}else
if(W){if(mE(r,yJ))if(ez(k,[0,[0,D,0],U]))var
C=0;else
var
p=yK,C=1;else
var
C=0;if(!C)var
p=[0,[0,u(r,0)]]}else
var
p=0;var
aj=b(c[45],n,g);if(1-V)o(e8[13],h,l[16],e[1],aj);var
q=b(c[44],n,g),ak=o(T[3],0,h,e[1],q),al=a(aE[17],ak),Q=gh(h,e[1],al),x=Q[3];e[1]=Q[1];var
z=y(cZ[20],h,e[1],q,0,s);e[1]=a(l[bJ],e[1]);if(p){var
B=p[1];if(0===B[0])return[0,m,k,q,x,g,n,[0,[0,B[1]]],s,z];var
R=B[1];return[0,m,k,q,x,g,n,[0,[1,[0,R[1],R[2],[0,m,k]]]],s,z]}return[0,m,k,q,x,g,n,0,s,z]}function
g4(c){function
d(c){var
d=a(k[10][1][2],c),e=[0,a(K[13][16],d),0];return b(V[3],0,e)}return b(f[17][14],d,c)}function
g5(e,d,m,L,az,K,J,H){var
n=jI(e,d[1],m),s=n[2],M=n[3];d[1]=n[1];var
O=b(c[45],L,m),v=ct(e,d,f0,[0,s,K,J,H]),P=ct(e,d,fZ,[0,M,v]),w=cA(e,d[1],0,P),Q=w[2];d[1]=a1(ac[23],0,0,0,0,e,w[1]);var
y=ct(e,d,f1,[0,s,v,Q,O]),z=o(ae[2],0,e,d[1],y),R=z[2];d[1]=z[1];var
A=t(aq),S=bq[9],T=eZ[1],U=j[18][1],V=u===A?aq[1]:q===A?a(r[2],aq):aq,W=a(j[62][6],V),B=t(ak),X=b(j[18][7],W,U),Y=u===B?ak[1]:q===B?a(r[2],ak):ak,Z=a(j[62][6],Y),_=b(j[18][7],Z,X);function
$(e,c){var
d=t(c),f=u===d?c[1]:q===d?a(r[2],c):c,g=a(aS[8],f);return b(j[18][7],g,e)}var
aa=g(f[17][15],$,_,[0,cR,[0,f0,[0,f1,[0,id,[0,ic,[0,ie,[0,ig,[0,ih,[0,ii,[0,ij,[0,ik,0]]]]]]]]]]]),C=b(bq[3][13],S,[0,T[1],aa]);function
D(b){var
c=g(ff[1],C,b,d[1]);return a(ff[2],c)}var
ab=a(D(e),R),p=b(c[3],d[1],ab);if(6===p[0]){var
ad=p[2];b(c[h][5],c[16],p[3]);var
af=a(D(e),y),ag=a(k[10][6],m),E=o(N[68],e,d[1],ag,ad),i=E[1],ah=E[2],ai=d[1],aj=b(c[x],i,e),al=g(N[29],aj,ai,ah),l=b(c[3],d[1],al);if(6===l[0]){var
am=l[3],an=l[2],ao=l[1],ap=d[1],ar=b(c[x],i,e),F=g(N[70],ar,ap,an),as=F[2],at=F[1],au=d[1],av=b(c[x],i,e),aw=g(ff[1],C,av,au),ax=a(ff[2],aw),G=a(ax,b(c[44],as,at)),ay=a(c[20],[0,ao,G,am]);return[0,G,b(c[44],ay,i),af]}throw[0,I,yN]}throw[0,I,yM]}function
kH(j,i,X,e,J,I,v,s){var
p=b(c[x],e,j),w=y(a8[14],0,p,i[1],0,v),z=w[2],m=w[1],K=y(T[2],0,0,p,m,z),A=g(N[22],p,m,K),L=a(f[17][1],e);if(o(c[h][14],m,1,L,A))var
M=-a(f[17][1],e)|0,n=b(c[h][1],M,A);else
var
W=a(d[3],yO),n=ad([0,a(bk[6],v),yP,W]);var
B=b(c[45],z,e),C=t(aw),O=u===C?aw[1]:q===C?a(r[2],aw):aw,D=o(l[hK],0,0,m,O),E=D[1],Q=a(c[14],D[2]),R=b(c[h][1],1,n),S=a(c[20],[0,k[9],R,Q]),F=a(c[20],[0,k[9],n,S]),G=s?a1(a8[15],0,j,E,0,s[1],F):cA(j,E,0,F),H=G[2];i[1]=G[1];var
U=g5(j,i,e,J,I,n,B,H),V=b(P[30],i[1],H);return[0,b(P[30],i[1],B),V,U]}function
g6(M,L,i,e,J,d){var
v=d[7];if(v){var
m=v[1];if(0===m[0]){var
w=m[1];if(typeof
w==="number")var
N=i[2],O=function(c){var
e=a(k[10][1][2],c),f=a(K[13][16],e);return 1-b(j[1][1],f,d[2])},x=b(f[17][61],O,N),y=a(f[17][1],x),P=aT(y,d[5]),A=y,z=b(f[18],P,x);else
var
D=a(f[17][1],i[2]),Z=i[2],$=aT(D,d[5]),A=D,z=b(f[18],$,Z);var
B=i[1],Q=d[2];if(B){var
t=B[1];if(t){var
u=t[1];if(0===u[0])var
H=u[1],I=function(a){var
c=a[1];if(typeof
a[2]==="number")if(b(j[1][1],c,Q))return 0;return[0,b(V[3],0,[0,c,0])]},n=b(f[17][65],I,H),l=1;else
var
l=0}else
var
l=0}else
var
l=0;if(!l)var
n=0;var
C=b(f[18],z,e),R=g4(e),S=b(f[18],R,n),T=[1,[0,w,a(f[17][1],n)]],U=a(f[17][1],d[5]),W=d[6],X=a(f[17][1],d[5])+1|0,Y=g(c[h][2],A,X,W),o=[0,_(C),e,C,Y,U,T];return[0,d,o[1],o[4],S,[0,o]]}var
E=m[1],p=kH(M,L,J,d[5],d[6],d[4],E[1],E[2]),F=p[3],aa=F[3],ab=F[1],ac=p[2],ad=p[1],ae=g4(e),af=a(f[17][1],d[5]),ag=ar(a(k[8],d[2]),0,ab),q=b(f[18],d[5],e),G=[0,ag,q],ah=[0,G,[0,yQ,bD(1,gC(q))],G],r=[0,ah,e,q,b(c[h][1],1,d[6]),af,[0,[0,aa,0,ad,ac]]],ai=d[9],aj=d[8],ak=d[7],al=d[6],am=b(f[18],d[5],e);return[0,[0,d[1],d[2],d[3],d[4],am,al,ak,aj,ai],r[1],r[4],ae,[0,r]]}var
an=d[9],ao=d[8],ap=d[7],aq=d[6],as=b(f[18],d[5],e),s=[0,d[1],d[2],d[3],d[4],as,aq,ap,ao,an],at=g4(e),au=s[6];return[0,s,_(s[5]),au,at,0]}var
kI=[cN,yR,cK(0)];function
fg(i,e,n,N,bk,bj,aA,m,E,w,o){var
F=bk,y=bj;for(;;){var
bm=m[3],bn=m[2];if(X[1]){var
bo=bC(i,E),bq=a(d[3],yS),bs=cF(n,i,e[1],m),bt=a(d[3],yT),bu=function(a){return a[1]},bv=b(f[17][68],bu,y),bw=a(dA(i,e[1]),bv),bx=a(d[3],yU),by=b(d[12],bx,bw),bz=b(d[12],by,bt),bA=b(d[12],bz,bs),bB=b(d[12],bA,bq),bE=b(d[12],bB,bo);b(L[9],0,bE)}if(y){var
ac=y[2],ae=y[1],aB=ae[2],U=aB[2],af=aB[1],ag=ae[1],Y=ag[3],B=ag[2],C=ag[1];if(X[1]){var
bG=cF(n,i,e[1],m),bH=a(d[3],yV),bI=bC(i,b(f[18],E,B)),bJ=a(d[3],yW),bK=b(d[12],bJ,bI),bL=b(d[12],bK,bH),bM=b(d[12],bL,bG);b(L[9],0,bM)}var
ah=kr(b(f[18],E,B),m);if(typeof
ah==="number"){if(0===ah){if(X[1]){var
bN=a(d[3],yX);b(L[9],0,bN)}var
F=[0,ae,F],y=ac;continue}if(X[1]){var
bO=a(d[3],yY);b(L[9],0,bO)}var
aC=kz(b(f[18],E,B),m);aM(function(n){var
e=a(f[7],m),h=b(c[x],e,i);function
j(a){return b_(h,a)}var
k=g(d[39],d[13],j,aC),l=a(d[3],yZ);return b(d[12],l,k)});var
aD=function(A,z){var
q=A,h=z;for(;;){if(h){var
j=h[2],k=h[1];aM(function(j){return function(k){var
e=a(f[7],m),g=b_(b(c[x],e,i),j),h=a(d[3],y0);return b(d[12],h,g)}}(k));var
l=fc([0,i,e],k,a(f[7],m));if(l){var
r=l[1];if(0===r[0]){var
p=r[1],s=p[1],B=p[3],C=p[2];aM(function(j){return function(k){var
e=a(f[7],m),g=b_(b(c[x],e,i),j),h=a(d[3],y1);return b(d[12],h,g)}}(s));var
t=[0,C,bn,bm];try{var
D=function(s){return function(h,g){if(g){var
b=g[1],k=a(f[8],b),l=bp(e[1],k,o),m=a(f[8],b),p=dH(e[1],m,w),c=fg(i,e,n,N,0,h,aA,ao(0,i,[0,e[1]],b,s),E,p,l);if(c){var
j=c[1],q=j[2],r=j[1];aM(function(b){return a(d[3],y4)});return[0,r,[0,q]]}throw O}return[0,h,0]}}(t),G=a(f[17][9],F),H=b(f[18],G,y),u=g(f[19][64],D,H,B),I=[0,[0,[0,u[1],[1,t,s,o,u[2]]]]];return I}catch(b){b=v(b);if(b===O){aM(function(b){return a(d[3],y2)});var
h=j;continue}if(b[1]===kI){aM(function(b){return a(d[3],y3)});var
h=j;continue}throw b}}aM(function(j){return function(k){var
e=a(f[7],m),g=b_(b(c[x],e,i),j),h=a(d[3],y5);return b(d[12],h,g)}}(k));var
J=q||l,q=J,h=j;continue}var
h=j;continue}return 0}}(0,aC);if(aD){var
P=aD[1];if(0===P[0]){var
aE=P[1];return[0,[0,aE[1],aE[2]]]}var
bR=P[3],bS=P[2],bT=P[1],bU=a(d[3],y6),bV=a(d[5],0),bW=a(d[3],y7),bX=e[1],bY=b(c[x],bS,i),bZ=g(z[11],bY,bX,bR),b0=a(d[3],y8),b1=a(K[13][8],bT),b2=a(d[3],y9),b3=b(d[12],b2,b1),b4=b(d[12],b3,b0),b5=b(d[12],b4,bZ),b6=b(d[12],b5,bW),b7=b(d[12],b6,bV);return ad([0,C,y_,b(d[12],b7,bU)])}return 0}var
Z=ah[1],aG=Z[4],b9=Z[3],b$=Z[2],ca=Z[1];if(X[1]){var
cb=a(d[3],y$);b(L[9],0,cb)}var
cc=function(a){return[0,a[1][1],a[2]]},G=b(f[17][68],cc,ca);if(0===U)var
aH=za;else
var
cy=a(J[22],U),aH=b(J[17],zn,cy);var
cd=a(J[22],af),ce=b(J[17],cd,aH),cf=b(J[17],zb,ce),cg=a(j[1][6],cf);if(aG){var
aJ=aG[1],ai=aJ[2],aj=aJ[1];if(Y)return ad([0,C,zd,a(d[3],zc)]);if(0===ai[0]){var
ch=ai[1],aK=g2([0,i,e],a(f[7],m),ch);if(aK){var
aL=aK[1],ci=[0,m,0,o,[1,aL[1],aL[3]]],cj=a(f[17][9],F);return[0,[0,b(f[18],cj,[0,[0,[0,aj,B,Y],[0,af,U+1|0]],ac]),ci]]}var
ck=cF(n,i,e[1],m),cl=a(d[5],0),cm=a(d[3],ze),cn=b(d[12],cm,cl);return ad([0,aj,zf,b(d[12],cn,ck)])}var
co=dG(i,e[1],ai),cp=a(d[5],0),cq=a(d[3],zg),cr=b(d[12],cq,cp);return ad([0,aj,zh,b(d[12],cr,co)])}if(Y){var
p=Y[1],ak=[0,cg,aA],s=m[1],cJ=m[2],Q=kD(s,i,e),cM=function(j){var
c=j[2],f=j[1],h=g1(i,s,e,N,0,G,w,[1,f])[1];if(2===c[0]){var
k=c[1];try{var
E=at(br[10],0,0,Q,e[1],0,h,k)}catch(c){c=v(c);if(c[1]===cT[1]){var
A=c[4],B=c[3],C=c[2],D=function(c,E){var
f=g(bP[2],C,B,A),i=a(d[3],zu),j=a(d[14],0),l=g(z[11],Q,e[1],k),m=a(d[3],zv),n=a(d[13],0),o=a(d[14],0),p=g(z[11],Q,e[1],h),q=a(d[3],zw),r=b(d[12],q,p),s=b(d[12],r,o),t=b(d[12],s,n),u=b(d[12],t,m),v=b(d[12],u,l),w=b(d[12],v,j),x=b(d[12],w,i),y=b(d[12],x,f),D=b(d[26],0,y);return g($[6],c,zx,D)};return b(V[10],D,f)}throw c}e[1]=E;return 0}var
l=b8(c),m=g(z[11],Q,e[1],l),n=a(d[3],zs),o=a(d[13],0),p=g(z[11],Q,e[1],h),q=a(d[3],zt),r=b(d[12],q,p),t=b(d[12],r,o),u=b(d[12],t,n),x=b(d[12],u,m);function
y(a,b){throw[0,kI,[0,a,x]]}return b(V[10],y,f)},cN=function(f){var
l=f[2],j=f[1];function
k(j,f){if(a(M[3],j))return 0;if(typeof
f!=="number"&&0===f[0])return 0;var
k=fb(e,s,i,G,w),m=k[1],n=g(c[h][3],k[4],0,l),o=e[1],p=b(c[x],m,i),q=g(z[11],p,o,n),r=a(d[3],zy),t=b(d[12],r,q);return g($[6],j,zz,t)}return b(V[10],k,j)};b(f[17][11],cM,b$);b(f[17][11],cN,b9);switch(p[0]){case
0:var
aR=p[2],cO=p[1],_=fb(e,s,i,G,w),ay=_[4],bh=_[2],az=_[1],T=aR[2],dS=_[3],dT=function(n,r){var
A=r[1],B=A[1],m=B[2],o=n[5],C=n[3],v=n[2],d=n[1],R=r[2],S=A[4],U=B[1],V=n[4],D=g3(o,e,0,ez(m,[0,[0,r,0],T]),1,T,r),W=b(f[18],d[6],T);function
X(a){return gs(o,W,D,a)}var
w=b(f[17][68],X,R),E=gX(o,e[1],D,w),x=E[2];e[1]=E[1];var
s=bQ(x),Y=[0,[0,a(k[8],m),s],0],Z=fe(d[1],[0,x,0]),p=[0,Z,Y,d[3],d[4],d[5],d[6]],q=g6(o,e,p,v,ay,x),F=q[5],y=q[4],G=q[3],t=q[2],j=q[1],H=at(a8[3],o,e[1],[0,d[5]],0,[0,m,0],[0,s,0],[0,j[8],0]),_=b(f[18],d[6],T),I=[0,p[1],p[2],p[3],p[4],H,_],$=b(f[18],d[6],T),z=[0,d[1],d[2],d[3],d[4],H,$],u=[0,m,ak],aa=aF(0,v),ab=b(c[h][3],ay,C),J=b(f[17][68],ab,aa);function
K(b){return[0,b,j,J,u,u,a(f[17][1],y),s]}if(S)var
ac=c9(0,i,e,j,I,w,u,t,y,G),L=c7(i,e,z[3],j,t,ac,F),ad=L[5],ae=K(L),N=a(du[4],ae),M=ad;else{var
ag=bQ(j),P=cA(i,e[1],[0,[0,[0,U],[3,[0,zQ,[0,m],0]]]],ag),Q=P[2];e[1]=P[1];var
ah=b(c[83],e[1],Q),ai=function(c){var
b=c9(0,i,e,j,I,w,u,t,y,G),a=c7(i,e,z[3],j,t,b,F);e[1]=g(l[31],ah[1],a[5],e[1]);return K(a)},N=a(du[3],ai),M=Q}var
af=[0,b(c[41],M,J)],O=ar(a(k[8],m),af,s);return[0,z,[0,O,v],C+1|0,[0,N,V],b(c[aP],O,bh)]},dU=aR[1],dV=[0,N,az,0,0,b(c[x],az,i)],ab=g(f[17][15],dT,dV,dU),bi=ab[3],dW=ab[4],dX=ab[2],dY=ab[1];b(c[x],az,i);var
aS=g0(i,e,dY,[0,dX,bh,dS,ay],bi,cO,[0,b(c[h][1],bi,o)]),cP=aS[2],cQ=aS[1],cR=function(b){var
c=t(b);return u===c?b[1]:q===c?a(r[2],b):b},H=[0,[0,m,b(f[17][68],cR,dW),cP,[0,cQ]]];break;case
1:var
aU=p[1],al=aU[2],aV=aU[1],aQ=b(f[17][31],al,G);if(0===aQ[0])var
aW=aQ[1];else
var
cK=a(j[1][9],al),cL=a(d[3],zq),aW=ad([0,[0,aV],zr,b(d[12],cL,cK)]);var
aX=g2([0,i,e],a(f[7],m),aW);if(aX)var
aY=aX[1],H=[0,[0,m,0,o,[1,aY[1],aY[3]]]];else
var
cS=a(d[3],zA),cU=a(j[1][9],al),cV=a(d[3],zB),cW=b(d[12],cV,cU),H=ad([0,[0,aV],zC,b(d[12],cW,cS)]);break;default:var
aZ=p[2],am=p[1];if(!am)throw[0,I,zP];var
cX=am[2],cY=am[1],a0=cX||0,a1=g1(i,s,e,N,0,G,w,[0,cY]),a2=a1[2],an=a1[1],ap=kB(cJ),a3=kC(i,e[1],s,ap),a4=a3[2],aa=a3[1],S=bl(0,i,e[1],[0,aa,a4,s]),cZ=a(A[76],aa),c0=a(j[1][10][35],cZ),c1=a(j[1][6],zD),aq=b(av[26],c1,c0),c2=R(e[1],S,a2),a5=[0,[0,a(k[8],aq),c2],aa],c3=R(e[1],S,an),as=b(c[h][1],1,c3),a6=gA(zF,zE,i,e[1],a5,1,as),au=a6[2],D=a6[1],c4=function(a){return 1===a[2]?1:0},a7=b(f[17][27],c4,au)[1],c5=a(f[7],D),c6=i1(a7,R(e[1],D,as),c5),c8=bD(1,a4),c_=a(f[8],D),c$=[0,c6,a(eE(e[1],c_),c8),aa],a9=ao(0,i,[0,e[1]],c$,S),aw=a(f[7],D),da=dI(aw),db=function(g){var
d=b(c[73],e[1],g),h=a(f[8],a9);function
i(a){return 3===a[0]?d===a[1]?1:0:0}return b(f[17][22],i,h)?[3,d]:[0,d]},ax=[0,aw,b(f[17][14],db,da),aw],a_=b(c[x],a5,i),dc=g(bc[9],a_,e[1],as),dd=R(e[1],S,o),de=b(c[h][1],1,dd),df=g(bc[9],a_,e[1],de),dg=g(A[50],e[1],dc,df),a$=R(e[1],D,dg),dh=function(b,a){return a[1]-b[1]|0},di=b(f[17][39],dh,au),dj=function(a){return a[2]},dk=b(f[17][14],dj,di);if(a0)var
dl=[0,b(V[3],C,[0,aq,1]),0],ba=[0,[0,C,b(f[18],B,dl),[0,[2,a0,aZ]]],0];else
var
ba=aZ;var
bb=function(c,k){var
h=[0,-1],l=a(j[1][6],zG);function
u(d){h[1]++;var
c=a(J[22],h[1]);return b(K[5],l,c)}function
n(h){var
j=h[3],k=h[2],p=h[1],w=a(f[17][1],k)-c|0,q=b(f[17][W],w,k),l=q[2],x=q[1];if(l){var
y=l[2],z=l[1],r=kt(m,b(f[18],E,x));if(typeof
r==="number"){var
A=bC(i,k),B=a(d[13],0),C=a(d[3],zH),D=a(d[5],0),F=aI(i,e[1],m),G=a(d[13],0),H=a(d[3],zI),J=a(d[16],c),K=a(d[5],0),L=a(d[3],zJ),M=b(d[12],L,K),N=b(d[12],M,J),P=b(d[12],N,H),Q=b(d[12],P,G),R=b(d[12],Q,F),S=b(d[12],R,D),T=b(d[12],S,C),U=b(d[12],T,B),X=b(d[12],U,A);return g($[6],p,zK,X)}var
Y=r[1][1],Z=function(a){if(1===a)return[0,z];function
c(b){var
c=b[1]===(a-1|0)?1:0,d=b[2],e=c?d:c;return e}if(b(f[17][22],c,ap))return 0;try{var
e=b(f[17][31],a-1|0,Y),g=[0,b(V[3],0,e)];return g}catch(a){a=v(a);if(a===O){var
d=[0,u(0),1];return[0,b(V[3],0,d)]}throw a}},_=b(f[17][65],Z,dk);if(j){var
n=j[1];if(2===n[0])var
t=n[1],ab=n[2],s=[0,[2,t,bb(a(f[17][1],t)+c|0,ab)]],o=1;else
var
o=0}else
var
o=0;if(!o)var
s=j;var
aa=a(f[17][9],_);return[0,[0,p,b(f[18],aa,y),s]]}throw[0,I,zL]}return b(f[17][65],n,k)},bd=bb(1,ba),dm=function(b,a){return a[1]-b[1]|0},dn=b(f[17][39],dm,au),dq=function(e){var
d=e[2];if(1===d)return an;var
g=b(f[17][7],ap,(d-1|0)-1|0)[1];return a(c[10],g)},dr=b(f[17][68],dq,dn),ds=function(d){if(b(c[51],e[1],d)){var
g=b(c[73],e[1],d)-1|0,h=a(f[7],m),i=b(f[17][7],h,g);return a(k[10][1][9],i)?0:[0,d]}return[0,d]},dt=b(f[17][65],ds,dr),dv=a(f[17][1],w),dw=gY(i,s,e,G)[2],dx=aT(1,w),dy=aT(dv+1|0,dw),dz=b(f[18],dy,dx),dB=a(f[8],D),dC=dH(e[1],dB,dz),dD=function(b,a){return[0,a,[0,b+1|0,0]]},be=fg(i,e,n,N,0,b(f[17][13],dD,bd),ak,ax,0,dC,a$);if(be){var
bf=be[1],bg=bf[2];kE(i,e[1],bf[1]);var
dE=bF(i,e,n[4],bg)[1],H=[0,[3,m,[0,[0,aq,an,a2],o,ku(a7,a(f[7],D)),ak,dE,dt,S,ax,a9,a$],bg]]}else
var
dF=a(dA(i,e[1]),bd),dJ=a(d[3],zM),dK=a(d[5],0),dL=cF(n,i,e[1],ax),dM=a(d[5],0),dN=a(d[3],zN),dO=b(d[12],dN,dM),dP=b(d[12],dO,dL),dQ=b(d[12],dP,dK),dR=b(d[12],dQ,dJ),H=cz(zO,b(d[12],dR,dF))}if(H){var
cs=H[1],ct=a(f[17][9],F);return[0,[0,b(f[18],ct,[0,[0,[0,C,B,[0,p]],[0,af,U+1|0]],ac]),cs]]}var
cu=a(d[3],zi),cv=eu(i,e[1],[0,C,B,[0,p]]),cw=a(d[3],zj),cx=b(d[12],cw,cv);return ad([0,dp,zk,b(d[12],cx,cu)])}return ad([0,C,zm,a(d[3],zl)])}var
aN=kA([0,i,e],a(f[7],m));if(aN){var
aO=aN[1],cB=[0,m,0,o,[1,aO[1],aO[3]]],cC=a(f[17][9],F);return[0,[0,b(f[18],cC,y),cB]]}var
cD=cF(n,i,e[1],m),cE=a(d[5],0),cG=a(d[3],zo),cH=b(d[12],cG,cE),cI=b(d[12],cH,cD);return ad([0,[0,n[1]],zp,cI])}}function
c9(i,e,c,h,p,o,n,g,m,l){var
q=i?i[1]:1;function
r(b,a){return[0,a,[0,b+1|0,0]]}var
j=fg(e,c,h,p,0,b(f[17][13],r,o),n,g,m,0,l);if(j){var
k=j[1],s=k[2],t=k[1];if(q)kE(e,c[1],t);return s}var
u=cF(h,e,c[1],g),v=a(d[5],0),w=a(d[3],zR),x=b(d[12],w,v);return cz(zS,b(d[12],x,u))}function
kJ(h,e,d,i,a){function
j(l,r){var
m=d[6],n=b(c[x],d[2],h);function
o(a){return gs(n,m,l,a)}var
i=b(f[17][68],o,r),j=gX(h,e[1],l,i),g=j[2];e[1]=j[1];var
a=g6(h,e,d,0,0,g),k=a[2],p=a[5],q=a[1];return[0,q,k,c9(0,h,e,g,d,i,[0,g[2],0],k,a[4],a[3]),p]}var
k=g(f[17][69],j,i,a);return e9(h,e,d[3],0,k)}aD(1227,[0,bf,aO,gW,dR,kn,ko,kp,e_,kq,e$,kr,ks,fa,kt,gY,kv,gZ,g0,g1,ky,kz,yn,yo,fc,kA,kB,yr,ys,fd,kC,kD,yu,cF,yx,yy,ku,fb,fg,c9,gX,fe,kF,kG,g5,kH,g6,g3,kJ],nV);function
zT(a){return a}function
kK(aD,i,y,p){var
H=p[2],L=p[1],E=a(w[31],L),aI=E[1],aJ=E[2][2],aL=b(c[2][2],i,H),X=b(aB[25],aL,aJ),Y=t(aw),aE=1,aM=u===Y?aw[1]:q===Y?a(r[2],aw):aw;switch(aM){case
0:var
F=a(J[3],zU);break;case
1:var
F=c[16];break;case
2:var
F=c[17];break;default:var
dg=[0,E,b(c[2][2],i,H)],di=b(bS[11],aD,dg),dj=a(bb[52],di)[2],F=a(c[14],dj)}var
aN=a(f[17][1],X),s=aI[6],n=aN-s|0,aO=b(f[17][68],c[bK],X),Z=b(f[17][W],n,aO),m=Z[2],d=Z[1],aP=U(0,m),aQ=[0,a(c[28],p),aP],N=a(c[23],aQ);function
_(a){var
d=b(c[91],i,a)[2];return b(f[17][W],s,d)[2]}var
aR=cq(i,p),aS=b(bS[19],aR,E);function
aU(k,q){var
r=a(c[9],q),e=b(c[99],i,r),d=e[1],t=e[2],l=a(f[17][1],d),n=l-s|0,o=b(f[17][W],n,d)[1];function
u(d,k){var
l=a(aG,k)[3],e=b(c[99],i,l),f=e[2],m=e[1],n=b(c[91],i,f)[1],g=b(c[3],i,n);if(11===g[0])if(b(j[37],g[1][1],L)){var
o=_(b(c[h][1],d+1|0,f));return[0,[0,m,d,a(c[10],d+1|0),o]]}return 0}var
v=b(D[66],u,o),w=U(0,d),x=[0,a(c[31],[0,p,k+1|0]),w],y=a(c[23],x),z=_(t),A=1;function
B(i,e){var
g=e[1],j=e[4],p=e[3],q=e[2],d=a(f[17][1],g),r=[0,b(c[h][1],d,y),0],s=U(0,g),t=[0,b(c[h][1],d,p),s],u=[0,a(c[23],t),r],v=a(c[h][1],d),w=b(f[17][68],v,z),x=b(f[18],w,u),A=b(f[18],j,x),B=aF(n+d|0,m),C=b(f[18],B,A),D=a(f[19][12],C),E=[0,a(c[10],(l+1|0)+d|0),D],F=a(c[23],E),G=aT(q+1|0,g),H=b(c[44],F,G);return[0,k,i,b(c[44],H,o)]}return g(f[17][71],B,A,v)}var
aW=b(f[19][16],aU,aS),aX=0;function
aY(c,a){return b(f[18],c,a)}var
$=g(f[19][18],aY,aW,aX),aa=aT(n,d),aZ=aT(n,aa);function
O(e){var
f=U(e+am.caml_mul(2-e|0,n)|0,d),g=[0,b(c[h][1],(3*n|0)+e|0,N),f];return a(c[23],g)}var
a0=O(0),a1=a(j[1][6],zV),a2=[0,[0,a(k[8],a1),0,a0],0],a3=O(1),a4=a(j[1][6],zW),a5=[0,[0,a(k[8],a4),0,a3],a2],a6=O(2),a7=a(j[1][6],zX),a8=[0,[0,a(k[8],a7),0,a6],a5],a9=b(f[18],aa,d),a_=b(f[18],aZ,a9),a$=iV(a8),v=3*(n+1|0)|0,ba=b(f[18],a$,a_),bd=[0,a(c[10],2),0],bf=[0,a(c[10],3),bd],bg=aF(n+3|0,d),bh=b(f[18],bg,bf),bi=aF((2*n|0)+3|0,d),bj=b(f[18],bi,bh),bk=aF(v,m),bl=b(f[18],bk,bj),bm=a(f[19][12],bl),bn=[0,a(c[10],(v+1|0)+s|0),bm],bo=a(c[23],bn),bp=[0,a(c[10],1),0],bq=[0,a(c[10],2),bp],br=aF(3,d),bs=b(f[18],br,bq),bt=aF(n+3|0,d),bu=b(f[18],bt,bs),bv=aF(v,m),bw=b(f[18],bv,bu),bx=a(f[19][12],bw),by=[0,a(c[10],(v+1|0)+s|0),bx],bz=a(c[23],by),bA=[0,a(c[10],1),0],bB=[0,a(c[10],3),bA],bC=aF(3,d),bD=b(f[18],bC,bB),bE=aF((2*n|0)+3|0,d),bF=b(f[18],bE,bD),bG=aF(v,m),bI=b(f[18],bG,bF),bL=a(f[19][12],bI),bM=[0,a(c[10],(v+1|0)+s|0),bL],bN=a(c[23],bM),bO=b(c[h][1],2,bN),bP=b(c[h][1],1,bz),bQ=[0,a(k[7],0),bP,bO],bR=a(c[20],bQ),bT=[0,a(k[7],0),bo,bR],bU=a(c[20],bT);b(c[44],bU,ba);var
cd=b(l[d0],y,i),bV=a(az[46],[2,p[1]]),ab=b(K[5],bV,zY),ce=0;function
bX(a){return g(c[5],0,i,a[3])}var
bY=b(f[17][68],bX,$);function
bZ(c){var
d=c[1],e=a(J[22],c[2]),f=b(J[17],zZ,e),g=a(J[22],d),h=b(J[17],g,f),i=b(J[17],z0,h);return b(K[5],ab,i)}var
b0=b(f[17][68],bZ,$),Q=a(f[17][1],d),b1=aT(Q,d),b2=b(f[18],b1,d),b3=U(2*Q|0,m),b4=[0,a(c[28],p),b3],ad=a(c[23],b4),b5=[0,ad,U(0,d)],b6=a(c[23],b5),b7=b(c[h][1],1,b6),b8=[0,a(k[7],0),b7,F],b9=a(c[20],b8),b_=[0,ad,U(Q,d)],b$=a(c[23],b_),ca=[0,a(k[7],0),b$,b9],cb=a(c[20],ca),cc=b(c[44],cb,b2),ae=[0,[0,ab,g(c[5],0,i,cc),0,b0,bY],ce],cf=0,ch=0;function
ci(a){var
d=b(k[10][1][16],zT,a);return b(c[d1],i,d)}var
cj=[0,0,0,b(f[17][68],ci,m),ae,cd,ch,cf],R=o(kM[2],0,cj,kL[3],0),S=a(w[2],0),ck=a(l[17],S),af=o(l[nH],0,S,ck,[0,R,0]),cl=af[1];gF(S,cl,y,dh(af[2]));var
ag=a(c[28],[0,[0,R,0],H]),cm=0;function
cn(b,a){var
c=a[5],d=1;function
e(a,c){return[0,en,y,1,0,[0,[3,[0,[0,R,b],a]]]]}return g(f[17][71],e,d,c)}var
co=g(f[17][71],cn,cm,ae),cp=[0,a(f[17][58],co)];g(aK[22],0,[0,f5,0],cp);var
cr=a(az[46],[2,L]),ah=b(K[5],cr,z1),ai=b(K[6],z2,ah),z=a(w[2],0),aj=b(l[d2],i,z),e=[0,aj],ak=dq(aj,ap(fZ,e));if(a(f[17][48],d))var
cs=[0,ag,U(0,m)],B=m,A=N,al=a(c[23],cs);else
var
C=gE(0,z,e,m,N),V=C[8],av=C[6],ax=C[5],ay=C[3],cS=C[4],aA=b(c[x],ay,z),cT=b(c[h][2],2,2),aC=b(f[17][68],cT,cS),cU=[0,ax,a(c[10],1)],cV=a(c[26],cU),cW=a(c[h][5],cV),cX=b(f[17][68],cW,aC),cY=[0,ax,a(c[10],2)],cZ=a(c[26],cY),c0=a(c[h][5],cZ),c1=b(f[17][68],c0,aC),c2=[0,av,a(c[10],1)],c3=[0,a(c[26],c2),0],c4=[0,av,a(c[10],2)],c5=[0,a(c[26],c4),c3],c6=b(f[18],cX,c5),c7=b(f[18],c1,c6),c8=aF(2,m),c9=i7(ag,b(f[18],c8,c7)),c_=b(c[h][1],1,V),c$=a(j[1][6],z7),da=[0,a(k[8],c$),c_,c9],db=a(c[21],da),dc=a(j[1][6],z8),dd=[0,a(k[8],dc),V,db],de=a(c[21],dd),df=g(bc[9],aA,e[1],V),B=ay,A=df,al=g(bc[9],aA,e[1],de);var
ct=[0,ap(ib,e),[0,A,al]],cu=a(c[23],ct),cv=b(c[45],cu,B),cw=[0,ap(ia,e),[0,A]],cx=a(c[23],cw),cy=b(c[44],cx,m),an=aV(ah,cv,[0,cy],y,e[1],z3),ao=an[2],cz=ao[2],cA=an[1];e[1]=ao[1];g(aK[22],0,[0,f5,0],[3,[0,[1,cA],0]]);var
cB=[0,cz,U(0,m)],aq=a(c[23],cB),cC=b(c[x],B,z),cD=[0,ap(h$,e),[0,A,aq]],cE=a(c[23],cD),cF=[0,A,[0,aq,[0,aH(hy(P[4],0,0,0,0,0,0,0,0,cC),e,cE),0]]],ar=ge(e[1],ak,cF),cG=ar[1],as=b(c[44],ar[2],B),cH=a(M[7],cG),au=b(c[45],cH,B);function
cI(f,e,d,b){if(1===b[0]){var
c=o(ac[5],ak[1],en,aE,[1,b[1]]);return a(ac[6],c)}throw[0,I,z4]}cP(a(w[2],0),e,au);cP(a(w[2],0),e,as);var
G=a(l[bJ],e[1]),cJ=g(c[5],z5,G,as),cK=g(c[5],z6,G,au),T=at(be[5],z,ai,G,0,0,cK,cJ),cL=T[4],cM=T[3],cN=T[1],cO=a(l[bH],G),cQ=[0,a(bW[1],cI)],cR=[0,iH(0)];cg(be[7],ai,[0,cM],cL,cO,0,0,[0,[0,2,y,10]],cR,0,cQ,0,cN);return 0}b7([0,z9,function(a,b){return b6(kK,a,b)}]);function
kN(y,V,u,t){var
i=t[1],d=[0,V],X=t[2],z=a(w[31],i),r=z[2],v=z[1],q=v[6],B=r[6],m=r[7],C=b(f[17][68],c[bK],r[2]),Y=U(0,C),_=[0,a(c[28],t),Y],$=a(c[23],_),aa=a(j[1][6],z_),E=[0,ag([0,a(k[8],aa),0,$]),C],F=b(f[17][W],m+1|0,E),G=F[2],n=F[1],H=gg(a(P[8],[0,l[cm]]),d),I=b(c[44],H,n),ab=b(c[45],H,n),ac=b(c[h][1],m+1|0,ab),ad=aX(m+1|0,q),J=U(0,b(D[co],m+1|0,E)),e=a(j[1][6],z$),L=[0,a(k[8],e),I],ae=b(c[h][1],1,I),x=a(j[1][6],Aa),p=a(j[1][6],Ab),s=a(j[1][6],Ac),af=[0,a(c[11],e)],ah=b(f[19][5],ad,af),N=b(f[19][5],ah,J),ai=[0,a(c[11],s),N],O=a(c[23],ai),aj=b(c[44],O,n),ak=b(c[h][1],2,aj),al=b(c[45],O,n),am=b(c[h][1],m+1|0,al),an=r[9];function
ao(C,j){var
D=b(bb[23],j[2],j[1]),k=a(c[9],D),l=a(Z[49],[0,i,C+1|0]),n=a(c[11],p),E=b(c[2][2],d[1],X),F=g(bS[5],i[1],v,E),G=b(f[17][68],c[9],F),H=b(c[h][4],G,k),r=b(c[99],d[1],H)[1],I=a(f[17][1],r)-q|0,t=b(f[17][W],I,r)[1],J=v[4]-i[2]|0,K=aX(-q|0,q),L=[0,a(c[10],J),K],N=a(c[23],L),O=o(A[51],d[1],N,n,k),u=b(c[99],d[1],O)[1],P=a(f[17][1],u)-q|0,Q=b(f[17][W],P,u)[1];function
R(e,f){var
d=e[2],g=e[1],i=a(a$,f),j=b(c[h][1],d,i);return[0,[0,[0,a(c[10],d),j],g],d+1|0]}var
w=g(f[17][15],R,Ad,Q)[1];function
y(h,e){var
i=0;function
j(e,f){if(e){var
i=e[1],j=i[2],k=i[1],l=b(h,function(b){var
e=b[2],f=b[1],g=[0,ap(ed,d),[0,e,j]],h=a(c[23],g),i=[0,ap(fY,d),[0,e,j,f,k]];return[0,a(c[23],i),h]},f),m=function(a){return[0,a]};return g(M[22],m,e,l)}return b(h,function(a){return a},f)}var
k=g(f[17][15],j,i,e),l=ap(cr,d),m=[0,ap(cs,d),l];function
n(a){return a}return g(M[22],n,m,k)}function
z(p,o,j){var
q=j[1],k=b(c[99],d[1],j[2]),e=k[1],l=b(c[91],d[1],k[2]),r=l[2];if(g(c[aJ],d[1],l[1],n)){var
i=a(f[17][1],e),s=aX(0,i),t=[0,b(c[h][1],i,q),s],u=[0,a(c[23],t),0],v=b(f[18],r,u),m=b(p,a(f[19][12],v),i),w=m[2],x=b(c[45],m[1],e);return[0,a(o,[0,x,b(c[44],w,e)])]}return 0}var
B=ap(ed,d);function
S(b,j){var
d=[0,a(c[11],p),b],f=a(c[23],d),g=[0,a(c[11],e),b],h=[0,B,[0,a(c[23],g),f]],i=a(c[23],h);return[0,a(c[10],0),i]}var
T=y(function(a,b){return z(S,a,b)},w)[2];function
U(g,j){var
k=[0,a(c[11],p),g],h=a(c[23],k),m=[0,a(c[11],e)],n=b(f[19][5],m,g),o=aX(l+j|0,q),i=b(f[19][5],o,n),r=[0,a(c[11],x),g],t=[0,a(c[23],r),[0,h]],u=a(c[23],t),v=[0,a(c[11],s),i],w=a(c[23],v),y=[0,a(c[11],e),g],z=[0,a(c[23],y),w,u,h],A=[0,ap(fY,d),z],C=a(c[23],A),D=[0,a(c[11],s),i],E=a(c[23],D),F=[0,a(c[11],e),g],G=[0,B,[0,a(c[23],F),E]];return[0,C,a(c[23],G)]}var
V=y(function(a,b){return z(U,a,b)},w)[1],Y=b(c[45],T,t),_=b(c[h][1],m+1|0,Y),$=b(c[45],V,t);return[0,l,_,b(c[h][1],m+1|0,$)]}var
Q=b(f[19][16],ao,an),aq=b(f[19][15],f[8],Q),ar=a(c[10],1),as=[0,o(Z[75],y,i,0,4),ac,ar,aq],at=a(c[32],as),au=b(f[19][15],f[9],Q),av=a(c[10],1),aw=[0,o(Z[75],y,i,0,4),am,av,au],ax=a(c[32],aw),ay=b(c[45],ax,n),aA=b(c[h][1],3,ay),aB=b(c[45],at,n),aC=b(c[h][1],2,aB),aD=[0,b(c[h][11],[0,p,[0,e,0]],aC)],aE=[0,[0,[0,B],0],[0,[0,a(k[8],p)],[0,ae],aD]],aF=a(c[33],aE),aG=b(c[45],aF,[0,L,G]),aH=a(az[46],[2,i]),aI=b(K[6],Ae,aH),R=aV(aI,aG,0,u,d[1],Af)[2],S=R[2],aK=R[1],aL=[0,b(c[h][11],[0,p,[0,x,0]],aA)],aM=[0,[0,[0,B],0],[0,[0,a(k[8],p)],[0,ak],aL]],aN=a(c[33],aM),aO=a(c[h][1],1),aP=b(f[19][15],aO,J),aQ=[0,a(c[11],e),aP],aR=a(c[23],aQ),aS=a(c[23],[0,S,N]),aT=a(c[20],[0,k[9],aS,aR]),aU=b(c[44],aT,n),aW=b(c[h][1],1,aU),aY=[0,a(k[8],x),aW],aZ=b(c[43],aY,aN),a0=b(c[h][11],[0,e,0],aZ),a1=b(c[45],a0,[0,L,G]),a2=b(c[h][9],[0,[0,s,S],0],a1),a3=a(az[46],[2,i]),a4=b(K[6],Ag,a3);if(u)var
T=aK;else
var
a5=a(w[2],0),T=a(l[17],a5);aV(a4,a2,0,u,T,Ah);return 0}b7([0,Ai,function(a,b){return b6(kN,a,b)}]);aD(1230,[0,kK,kN],hG);var
kO=a(f[17][68],c[bK]);function
kP(d,l){var
m=l[2],n=l[1],e=n[1],p=a(w[31],n)[1],r=p[8],s=b(c[2][2],d,m),t=a(kO,b(aB[25],s,r)),i=dw(0,function(b){return a(j[1][6],Aj)},t),k=i[3],q=i[1],u=i[2],v=a(f[17][1],k),x=a(w[2],0),y=g(f[17][16],c[cm],k,x);function
z(i,j){var
k=[0,[0,e,i],m],l=cV(0,q,a(kO,b(f[17][W],j[6],j[2])[1])),n=a(az[46],[2,[0,e,i]]),p=[0,a(c[28],k),u],r=a(c[40],p),s=cq(d,k),t=b(Z[4],y,s);function
x(e){var
f=a(c[9],e),i=g(c[df],d,v,f)[2],j=b(c[h][4],q,i);return b(c[99],d,j)}var
z=b(f[19][15],x,t);return[0,n,r,l,z,function(f,d,b){var
g=a(w[2],0),h=[0,o(Z[75],g,[0,e,i],0,4),d,f,b];return a(c[32],h)}]}return[0,k,b(f[19][16],z,p[1])]}function
kQ(c){var
d=ap(il,c),e=b(ac[11],c[1],d);return a(M[7],e)}function
kR(a){return ap(im,a)}function
kS(d){function
e(b){var
d=b3(b);return a(c[11],d)}var
g=b(f[17][68],e,d);return a(f[19][12],g)}function
kT(z,e,r,q){var
m=kP(e,q),i=m[1],d=[0,e],n=kQ(d)[2][1],s=a(f[19][11],m[2]);function
t(e){var
o=U(0,e[3]),m=a(c[23],[0,e[2],o]),p=[0,kR(d),[0,m]],q=a(c[23],p),s=a(j[1][6],Ak),t=a(k[8],s),u=a(j[1][6],Al),v=a(k[8],u),x=a(c[10],1),y=[0,a(c[10],2),x],z=[0,b(c[h][1],2,q),y],B=a(c[23],z),C=[0,v,b(c[h][1],1,m),B],D=[0,t,m,a(c[20],C)],E=a(c[20],D),F=b(c[44],E,e[3]),G=b(A[16],F,i);return[0,e,[0,G,function(j){var
k=kS(i),p=b(f[19][5],k,o),q=a(du[4],j),s=[0,m,[0,ct(a(w[2],0),d,q,p),0]],h=b(ac[15],n,s),t=h[2],u=e[3],v=a(M[7],h[1]),x=b(c[45],v,u),y=b(A[18],x,i),z=b(l[d0],r,d[1]),B=b(c[44],t,e[3]),C=b(A[16],B,i),D=[0,g(c[5],0,d[1],C)],E=Am[6],F=ab[39][1],G=[0,[0,g(c[5],0,d[1],y),F],E];return[0,b(gS[6],0,G),0,0,D,z,0,0]}]]}var
p=b(f[17][68],t,s);function
u(h,g,e,d){function
c(c){var
e=c[1],f=[0,[0,a(c[2][2],d)],An],g=b(K[5],e[1],Ao),h=[1,y(bM[3],0,0,g,0,f)],i=o(ac[5],n[1],aK[4],1,h);return a(ac[6],i)}return b(f[17][11],c,p)}var
v=a(bW[1],u);function
x(e){var
f=e[2][1],h=b(K[5],e[1][1],Ap),i=[0,iF(0)],j=a(l[bH],d[1]),k=g(c[5],0,d[1],f);cg(be[7],h,0,k,j,0,0,0,i,0,[0,v],0,[0]);return 0}return b(f[17][11],x,p)}b7([0,Aq,function(a,b){return b6(kT,a,b)}]);aD(1232,[0,kP,kQ,kR,kS,kT],m3);function
Ar(k,i,d,h,c){if(a(j[1][10][2],c))return 0;var
e=[0,c,0];return g(eo,function(f,e){var
d=f[2],a=f[1],c=b3(e);if(b(j[1][10][3],c,h))return[0,a,d];if(b(j[1][10][3],c,a))return[0,a,[0,c,d]];var
l=g(A[99],k,i,e),m=j[1][10][1],n=b(j[1][10][9],l,a);return b(j[1][10][11],n,m)?[0,a,d]:[0,b(j[1][10][4],c,a),[0,c,d]]},e,d)[2]}var
g7=[cN,As,cK(0)];function
kU(e,d,c){var
a=[0,d];try{var
h=function(c){var
d=f$(e,At,j[1][10][1],c),f=a[1];function
h(c,a){if(b(j[1][10][3],c,a))throw g7;return b(j[1][10][4],c,a)}a[1]=g(j[1][10][15],h,d,f);return 0};b(f[19][13],h,c);var
i=1;return i}catch(a){a=v(a);if(a===g7)return 0;throw a}}function
kV(e,h){var
d=e[2];b(C[17],h,e);var
i=a(cU,b(C[15],e,h)),k=i[2],q=i[3];if(k)var
l=b(c[91],d,k[1]),m=l[1],g=l[2];else
var
p=b(c[91],d,q),m=p[1],g=p[2];if(0===g)return 0;var
n=ga(d,m,a(f[19][12],g)),o=n[2];if(kU(d,f$(d,Au,j[1][10][1],n[1]),o)){var
r=function(e){var
f=1-b(c[52],d,e);if(f)return f;var
g=b(c[75],d,e);return a(A[bw],g)};return b(f[19][22],r,o)}return 1}function
g8(m,e,d){var
t=m?m[1]:1,h=d[2],n=b(C[14],d,e),l=b(c[3],h,n);if(9===l[0])var
F=ga(h,l[1],l[2])[2],o=a(f[19][11],F);else
var
o=0;function
p(e){var
f=b(c[3],h,e);if(1===f[0])return f[1];var
i=a(C[2],d),k=a(C[5],d),l=g(av[9],k,i,e),m=a(j[1][6],l);return b(C[17],m,d)}var
u=a(C[5],d);function
v(f,b){var
h=b[3],i=b[2],j=b[1],l=f[1],m=a(C[2],d),e=y(kW[6],u,m,Av,j,l),n=e[2],o=e[1],p=a(k[7],i);return[0,g(c[46],p,h,o),n]}function
w(a){var
c=b(el,d,a);return[0,a,p(a),c]}var
q=b(f[17][14],w,o),r=t?[0,[0,e,p(e),n],q]:q,x=a(C[2],d),z=[0,a(C[4],d),x],A=g(f[17][15],v,z,r)[1],B=b(f[17][14],f[7],r),D=b(c[41],A,B),E=g(s[3],Aw,D,2);return b(i[72][7],E,d)}function
kX(D,d){var
E=d[1],F=a(az[46],[2,d]),u=a(w[31],d),m=u[2],v=u[1],G=v[1];function
H(b,d){return a(c[27],[0,E,b])}var
I=b(f[19][16],H,G),L=a(f[19][11],I),M=a(f[17][9],L),p=v[6],i=b(f[17][68],c[bK],m[2]),N=a(f[17][1],i)-p|0,x=b(f[17][W],N,i),z=x[2],n=x[1],q=a(f[17][1],n),O=U(0,i),Q=[0,a(c[27],d),O],r=a(c[23],Q),R=a(w[2],0),e=[0,a(l[17],R)],S=[0,[0,k[9],r],n],T=P[8],V=gg(function(a){return b(T,0,a)},e),X=b(c[44],V,S),s=m[9].length-1,Y=m[9],_=m[4];function
$(g,L,l){var
q=b(bb[23],l[2],l[1]),r=a(c[9],q),t=b(c[h][4],M,r),m=b(c[99],e[1],t),n=m[1],u=b(c[91],e[1],m[2])[2],v=b(f[17][W],p,u)[2],i=a(f[17][1],n)-p|0,o=aT(g+1|0,b(f[17][W],i,n)[1]),w=U(0,o),x=U((i+g|0)+1|0,z),y=b(f[19][5],x,w),A=[0,a(c[29],[0,d,g+1|0]),y],B=[0,a(c[23],A),0],C=b(f[18],v,B),D=a(c[10],(i+g|0)+1|0),E=b(c[41],D,C),F=a(c[10],(1+s|0)-g|0),G=b(c[44],E,o),H=a(J[22],g),I=b(J[17],Ax,H),K=a(j[1][6],I);return[0,[0,a(k[8],K),G],F]}var
t=g(f[19][59],$,_,Y),aa=a(w[2],0),ab=o(Z[75],aa,d,0,4);function
A(e){var
g=U(0,n),h=U((q+s|0)+e|0,z),i=b(f[19][5],h,g),j=[0,a(c[27],d),i];return a(c[23],j)}var
ac=A(2+q|0),B=[0,[0,k[9],ac],n],ad=U(0,B),ae=[0,a(c[10],(q+s|0)+3|0),ad],af=a(c[23],ae),ag=b(c[45],af,B);function
ah(a){return a[2]}var
ai=b(f[19][15],ah,t),aj=[0,ab,ag,a(c[10],1),ai],ak=a(c[32],aj),al=A(1),am=e[1],an=a(w[2],0),ao=o(av[11],an,am,al,0),aq=a(j[1][6],Ay),ap=1+(t.length-1)|0,ar=[0,[0,a(k[8],aq),X],i];function
as(a){return a[1]}var
au=b(f[19][15],as,t),aw=a(f[19][11],au),ax=a(f[17][9],aw),ay=b(f[18],ax,ar),aA=b(c[h][1],ap,r),aB=[0,[0,a(k[7],ao),aA],ay],aC=b(c[45],ak,aB),aD=b(l[d0],D,e[1]),aE=g(c[5],0,e[1],aC),aF=at(bM[2],0,0,0,0,[0,aD],0,aE),aG=b(K[5],F,Az),aH=[1,y(bM[3],0,0,aG,0,[0,[0,aF],AA])],C=a(w[2],0);return[0,C,a(l[17],C),i,r,aH]}function
kY(w,l,f,k){var
g=k[1],d=kX(f,g),h=d[3],m=d[5],n=d[4],o=d[2],p=d[1],q=a(az[46],[2,g]),e=[0,o],r=b(K[6],AB,q),s=it(e),i=bh(e,m),t=y(T[2],0,0,p,e[1],i),j=U(0,h),u=[0,a(c[23],[0,i,j]),0],v=[0,n,[0,gf(l,t,j),u]];return di(r,f,e[1],h,s,v)}function
AC(d,c,b,a){kY(d,c,b,a);return 0}b7([0,AD,function(a,b){return b6(AC,a,b)}]);function
kZ(l,e,d){var
r=l?l[1]:1,m=a(C[5],d),h=a(C[2],d),t=b(el,d,e),u=a(C[6],d),v=a(A[77],u),w=a(j[1][10][35],v),n=b(c[3],h,e),x=9===n[0]?a(f[19][11],n[2]):0;function
o(d){var
e=b(c[3],h,d);if(1===e[0])return e[1];var
f=g(av[9],m,h,d),i=a(j[1][6],f);return b(av[26],i,w)}function
z(e,b){var
f=b[3],h=b[2],i=b[1],j=a(C[2],d),l=y(kW[6],m,j,AE,i,e)[1],n=a(k[7],h);return g(c[46],n,f,l)}function
B(a){var
c=b(el,d,a);return[0,a,o(a),c]}var
p=b(f[17][14],B,x),q=r?[0,[0,e,o(e),t],p]:p,D=a(C[4],d),E=g(f[17][15],z,D,q),F=b(f[17][14],f[7],q),G=b(c[41],E,F),H=g(s[3],AF,G,2);return b(i[72][7],H,d)}function
dS(d,h,f){if(!b(c[52],d,f))if(!b(c[51],d,f)){var
i=b(c[3],d,h),j=b(c[3],d,f);if(9===i[0])if(9===j[0]){var
k=j[2],l=i[2],m=i[1];if(g(c[fJ],d,m,j[1]))if(b(c[63],d,m)){var
p=b(c[85],d,m)[1],e=a(Z[49],p);if(e<=l.length-1)if(e<=k.length-1){var
q=g(bd[7],l,l.length-1-e|0,e),r=g(bd[7],k,k.length-1-e|0,e),s=function(a,b){return dS(d,a,b)};return g(bd[37],s,q,r)}var
t=function(a,b){return dS(d,a,b)};return o(c[co],d,t,h,f)}}var
n=function(a,b){return dS(d,a,b)};return o(c[co],d,n,h,f)}return 1}function
AH(Z,E,A){var
M=a(C[5],A),ai=b(C[16],A,E),e=[0,a(C[2],A)];function
aj(e,b,a,d,c){try{var
f=dv(c,b),g=dv(d,b),h=at(br[10],0,0,e,a[1],0,g,f)}catch(a){a=v(a);if(a[1]===br[3])return 0;throw a}a[1]=h;return 1}var
aF=a(c[11],E),aI=0,aJ=0,aK=0,aL=Z?0:1,y=aL,p=aK,k=aJ,i=aI,m=aF,l=ai;for(;;){var
w=b(c[3],e[1],l);switch(w[0]){case
6:var
N=w[3],G=w[2],_=w[1];if(!y){var
aB=[0,a(c[10],1)],aC=[0,b(c[h][1],1,m),aB],aD=a(c[23],aC),y=0,k=[0,ar(_,0,G),k],m=aD,l=N;continue}var
O=b(c[3],e[1],G);if(9===O[0]){var
H=O[2];if(3===H.length-1){var
$=O[1],I=H[2],Q=H[3],aa=t(a4),aq=H[1],as=u===aa?a4[1]:q===aa?a(r[2],a4):a4;if(g(c[a2],e[1],as,$)){var
au=a(f[17][1],i);if(o(c[h][14],e[1],1,au,I))var
V=1;else{var
aA=a(f[17][1],i);if(o(c[h][14],e[1],1,aA,Q))var
V=1;else
var
U=1,V=0}if(V){var
D=b(c[3],e[1],$);switch(D[0]){case
10:var
W=D[1],R=[0,[1,W[1]],W[2]];break;case
11:var
X=D[1],R=[0,[2,X[1]],X[2]];break;case
12:var
Y=D[1],R=[0,[3,Y[1]],Y[2]];break;default:throw[0,bm,AG]}var
av=R[2],aw=a(f[17][1],i);if(o(c[h][14],e[1],1,aw,I))var
J=I,S=Q;else
var
J=Q,S=I;var
ab=t(bi),ax=u===ab?bi[1]:q===ab?a(r[2],bi):bi,ay=[0,er(e[1],[0,ax,av]),[0,aq,J]],ac=a(c[23],ay);if(dS(e[1],J,S))if(aj(b(c[x],k,M),i,e,S,J)){var
az=b(c[h][5],ac,N),p=1,m=a(c[23],[0,m,[0,ac]]),l=az;continue}var
K=[0,m,p,k,i,l],L=1,U=0}}else
var
U=1;if(U)var
L=0}else
var
L=0}else
var
L=0;if(!L){if(!p){var
ak=dv(G,i),al=b(c[x],k,M),am=aH(hy(P[4],0,0,0,0,0,0,0,0,al),e,ak),an=[0,a(c[10],1)],ao=[0,b(c[h][1],1,m),an],ap=a(c[23],ao),p=0,i=[0,ar(_,[0,am],G),i],m=ap,l=N;continue}var
K=[0,m,p,k,i,l]}break;case
8:var
B=w[4],ad=w[3],T=w[2],ae=w[1],af=t(aW),aE=u===af?aW[1]:q===af?a(r[2],aW):aW;if(!g(c[a2],e[1],aE,T)){if(y){var
i=[0,ar(ae,[0,T],ad),i],l=B;continue}var
k=[0,ar(ae,[0,T],ad),k],l=B;continue}if(!Z){var
y=1,l=b(c[h][5],c[16],B);continue}if(!y){var
y=1,l=b(c[h][5],c[16],B);continue}var
K=[0,m,p,k,i,b(c[h][5],c[16],B)];break;default:var
K=[0,m,p,k,i,l]}var
aM=K[5],aN=b(P[36],e[1],i),aO=function(f){var
d=a(aG,f),g=d[2],h=d[3],i=d[1];if(g)if(b(c[54],e[1],g[1]))return[0,i,h];return f},ag=b(f[17][68],aO,aN),aP=b(c[44],aM,ag),aQ=b(c[45],m,ag),aR=b(c[44],aP,k),aS=b(c[45],aQ,k),ah=b(P[30],e[1],aR),aT=b(P[30],e[1],aS);if(p){var
aU=F(a(s[43],aT)),aV=F(b(s[d5],E,ah));return g(n[8],aV,aU,A)}var
aX=g(z[11],M,e[1],ah),aY=a(j[1][9],E),aZ=a(d[3],AI),a0=b(d[12],aZ,aY),a1=b(d[12],a0,aX);return g(n[23],0,a1,A)}}function
g9(f,c,b){try{a(F(a(s[76],[0,c,0])),b);var
i=0,e=i}catch(b){b=v(b);if(!a($[18],b))throw b;var
e=1}if(e){var
h=a(d[3],AJ);return g(n[23],0,h,b)}return AH(f,c,b)}function
dT(s,r){function
e(e){var
t=a(i[68][4],e),u=a(i[68][2],e),p=a(i[68][5],e),C=o(T[3],0,t,p,u),w=a(aE[17],C),E=a(ax[48],t),F=a(i[68][3],e),m=r[2],x=r[1];function
G(b){var
c=a(k[11][1][2],b);return a(A[bw],c)}var
y=b(D[bw],G,F),q=y[1],l=b(c[bX],y[2],E);function
H(D){var
t=em(q),e=t[1],E=t[2],F=dw(AL,function(a){throw[0,I,AK]},e)[2],o=b(c[h][11],E,u),v=[0,[0,b(af[1],0,AM)],AN];function
G(i){if(X[1]){var
m=a(dA(l,p),i),n=a(d[5],0),q=a(d[3],AO),r=b(d[12],q,n),s=b(d[12],r,m);b(L[6],0,s)}var
t=[0,AQ,0,AP,0,a8[1],0],u=b(c[44],o,e),v=[0,x,a(j[1][6],AR),u,w,e,o,0,0,0],y=_(e),A=g(k[10][14],c[10],0,e);function
B(k){var
e=[0,k],m=[0,bF(l,e,w,c9(0,l,e,v,t,i,0,y,0,o))[1],A],n=b(N[57],e[1],m),p=a(f[17][9],F),j=b(c[h][4],p,n);if(X[1]){var
q=g(z[11],l,e[1],j),r=a(d[3],AS),s=b(d[12],r,q);b(L[9],0,s)}return[0,e[1],j]}return b(cD[1],1,B)}if(s)var
H=s[1],J=function(c,e){function
d(f){var
d=a(k[11][1][2],f);return b(j[1][1],d,m)?b(V[3],c,e):b(V[3],0,[0,d,0])}return[0,c,b(f[17][14],d,q),[0,v]]},K=a(V[10],J),O=b(f[17][68],K,H),y=a(i[16],O);else{var
A=fc([0,l,[0,p]],D,e);if(A){var
B=A[1];if(0===B[0])var
P=a(f[19][11],B[1][3]),Q=a(M[29][2],P),R=function(a){return jq(0,0,a)},S=b(f[17][68],R,Q),T=function(a){return[0,[0,x],a,[0,v]]},U=b(f[17][68],T,S),C=a(i[16],U),r=1;else
var
r=0}else
var
r=0;if(!r)var
W=a(j[1][9],m),Y=a(d[3],AT),Z=b(d[12],Y,W),C=b(n[65][5],0,Z);var
y=C}return b(i[73][1],y,G)}try{var
Q=function(f,e){var
d=f,c=e;for(;;){if(c){var
g=c[2],h=a(k[11][1][2],c[1]);if(b(j[1][1],m,h))return d;var
d=d+1|0,c=g;continue}throw O}}(1,q),R=a(i[16],Q),B=R}catch(c){c=v(c);if(c!==O)throw c;var
J=a(j[1][9],m),K=a(d[3],AU),P=b(d[12],K,J),B=b(n[65][5],0,P)}return b(i[73][1],B,H)}return a(i[68][8],e)}aD(1234,[0,Ar,g7,kU,kV,g8,kX,kY,kZ,g9,dS,dT,function(c,g){function
d(h){var
j=a(i[68][4],h);if(c)var
d=c[1],k=[0,ey(0,d)],l=function(b){var
c=gr(j,0,[0,k],0,b);return a(f[17][5],c)},e=[0,b(f[17][68],l,d)];else
var
e=0;return dT(e,g)}return a(i[68][8],d)}],mY);function
k0(e,c){try{var
g=e[5],h=function(d){var
e=d[1],f=a(aS[16],c);return b(j[63][1],[1,e],f)},i=b(f[17][27],h,g);return i}catch(b){b=v(b);if(b===O)return bB(0,a(d[3],AV));throw b}}function
k1(c){var
b=a(aK[15],AW);return a(aK[14][14],b)}function
AX(b){return F(a(s[63],[0,b,0]))}var
AY=a(n[52],AX),AZ=F(s[62]),A0=b(n[5],AZ,AY);function
fh(c,a){var
d=b(f[18],a,A1),e=[0,k1(0)];return F(y(g_[8],0,e,0,c,d))}function
g$(a){return b(J[17],a[3],A2)}function
A3(b){var
c=fh(0,b),d=[0,a(n[20],c),0],e=g(cG[2],0,n[65][2],b),f=[0,a(i[72][7],e),d],h=a(n[6],f);return a(n[16],h)}function
ha(c,b){var
d=fh(0,b),e=[0,a(n[20],d),0],f=g(cG[6],0,b,c),h=[0,a(i[72][7],f),e],j=a(n[6],h);return a(n[16],j)}function
k2(b){var
c=g(cG[2],0,n[65][2],[0,b,0]),d=a(i[72][7],c);return a(n[16],d)}function
fi(c){var
f=a(cG[4],c);function
e(c){if(c){var
f=c[1],l=c[2],h=a(aS[16],f[1]),m=f[5]?c_[3]:c_[4],o=function(a){return b(m,0,a)},p=a(n[65][61],h),j=b(i[17],p,o),q=function(f){if(X[1]){var
c=a(d[3],A4);b(L[9],0,c)}return e(l)};if(X[1])var
r=function(c){var
e=a(i[68][2],c),f=a(i[68][5],c),k=a(i[68][4],c),l=g(z[11],k,f,e),m=a(d[3],A5),n=a(z[39],h),o=a(d[3],A6),p=b(d[12],o,n),q=b(d[12],p,m),r=b(d[12],q,l);b(L[9],0,r);return j},k=a(i[68][8],r);else
var
k=j;return b(i[22],k,q)}var
s=a(d[3],A7);return b(n[65][4],0,s)}var
h=e(f);return a(i[72][7],h)}function
A8(b){var
c=[0,b3(a(C[35][17],b)),0];return a(s[84],c)}var
hb=a(i[68][8],A8);function
k3(c,b,a){if(a){var
f=a[2],d=hx(P[4],0,0,0,0,0,0,0,0,c,b,a[1]),g=d[2],e=k3(c,d[1],f);return[0,e[1],[0,g,e[2]]]}return[0,b,0]}function
k4(o,h,n,m){var
f=o,j=n,i=m;for(;;){var
p=b(A[60],h,i),e=b(c[3],h,p);switch(e[0]){case
6:var
k=e[2],t=e[3],u=e[1];if(1===j)try{var
l=g(Z[71],f,h,k)[1],w=[0,l[1][1],l[2]];return w}catch(a){a=v(a);if(a===O)return ba(A_);throw a}var
f=b(c[aP],[0,u,k],f),j=j-1|0,i=t;continue;case
8:var
x=e[4],f=b(c[aP],[1,e[1],e[2],e[3]],f),i=x;continue;default:var
q=g(z[11],f,h,i),r=a(d[3],A9),s=b(d[12],r,q);return g($[6],0,0,s)}}}function
fj(x,r){function
e(F){function
e(e){function
m(av){var
s=b(f[17][68],i[10],av);function
H(c){var
d=b(l[23],e,c);return a(l[4],d)}var
n=b(f[17][68],H,s);function
K(d){var
f=b(l[23],e,d),g=a(l[5],f);return a(c[au][5],g)}var
L=b(f[17][68],K,s),y=a(f[17][aJ],L),z=y[1],M=y[2];function
N(a){return g(k[11][6],G[80],z,a)}var
p=b(f[17][21],N,M)?b(ax[38],z,F):F;if(x)var
m=b(f[17][68],j[1][6],x);else
var
at=function(f,d){var
c=b(l[61],d,e);if(c)return c[1];var
g=a(J[22],f),h=b(J[17],Bm,g);return a(j[1][6],h)},m=b(f[17][13],at,s);var
q=a(f[17][1],m),t=a(f[17][1],r),u=a(f[17][1],n),A=q===t?1:0,P=A?q===u?1:0:A;if(1-P){var
Q=b(f[15][47],u,A$),R=a(d[3],Q),S=a(d[16],u),T=a(d[3],Ba),U=1===t?Bb:Bl,V=a(d[3],U),W=a(d[16],t),X=a(d[3],Bc),Y=b(f[15][47],q,Bd),Z=a(d[3],Y),_=a(d[16],q),aa=a(d[3],Be),ab=b(d[12],aa,_),ac=b(d[12],ab,Z),ad=b(d[12],ac,X),ae=b(d[12],ad,W),af=b(d[12],ae,V),ag=b(d[12],af,T),ah=b(d[12],ag,S),ai=b(d[12],ah,R);g($[6],0,Bf,ai)}function
aj(c,b,a){return[0,c,b,a]}var
B=o(D[73],aj,m,r,n),C=a(f[17][5],B),ak=k4(p,e,C[2],C[3])[1];function
al(q,o){var
h=q,f=o;for(;;){if(f){var
i=f[1],m=i[3],l=i[1],r=f[2],s=k4(p,e,i[2],m)[1];if(1-b(j[23][12],ak,s))ba(Bg);try{b(k[11][5],l,h);var
A=1,n=A}catch(a){a=v(a);if(a!==O)throw a;var
n=0}if(n){var
t=a(d[3],Bh),u=a(a7[6],l),w=a(d[3],Bi),x=b(d[12],w,u),y=b(d[12],x,t);g($[6],0,Bj,y)}var
z=g(c[5],0,e,m),h=[0,[0,a(k[7],l),z],h],f=r;continue}return h}}var
am=al(a(ax[10],p),B);function
an(a){return a-1|0}var
E=b(f[19][57],an,r),ao=b(f[19][57],k[8],m),w=[0,function(a){throw[0,I,Bk]}];function
ap(e){var
g=a(ax[33],am),d=k3(b(ax[49],g,p),e,n),i=d[2],j=d[1],k=a(f[17][9],m),l=a(c[h][11],k),o=b(f[19][57],l,i),q=[0,ao,a(f[19][12],n),o];w[1]=function(b){return a(c[33],[0,[0,E,b],q])};return[0,j,a(w[1],0)]}var
aq=b(cD[1],0,ap);function
ar(c){function
d(b){return[0,b,a(w[1],c+1|0)]}return b(cD[1],0,d)}var
as=[0,aq,b(f[17][56],E.length-1-1|0,ar)];return a(i[36],as)}return b(i[73][1],i[66][6],m)}return b(i[73][1],i[54],e)}return b(i[73][1],i[55],e)}function
Bn(j,c){var
k=a(f[17][5],j),m=a(i[10],k);try{var
d=b(l[23],c,m),e=d[3];if(e){var
n=e[1],o=a(l[12],d);g(Z[79],o,c,n);var
h=1}else
var
h=1;return h}catch(a){a=v(a);if(a[1]===cH[1])return 0;throw a}}function
fk(f,e,d){var
a=k0(f,e),b=a[2],c=b[2],g=a[1],h=Y(d,c)[c+1];return[0,g,b[2],h]}function
k5(d,h,i,g){function
e(h,g){var
j=a(f[17][1],g);if(a(f[17][1],h)===j){var
k=0,l=function(g,a,j){if(g)return g;var
f=b(c[91],d,j);switch(a[0]){case
0:var
h=f[1];if(a[1]===i)return[0,b(c[75],d,h)];break;case
1:return e(a[2],f[2])}return 0};return o(f[17][19],l,k,h,g)}throw[0,I,Bo]}var
j=e(a(f[17][9],h),g);return a(M[7],j)}function
dU(d){var
e=a(C[4],d),f=a(C[2],d);switch(b(c[3],f,e)[0]){case
6:var
h=F(s[16]);return g(n[5],h,dU,d);case
8:var
i=F(s[59]);return g(n[5],i,dU,d);default:return a(n[1],d)}}function
hc(d){var
c=[0,F(b(s[110],0,0)),0];return a(n[6],c)}function
k6(a){return 1===a[0]?[0,a[4]]:0}function
k7(a){return 3===a[0]?[0,a[3]]:0}function
k8(a){return 0===a[0]?[0,[0,a[1],a[2]]]:0}function
fl(c,b){return b?a(c,b[1]):0}function
fm(a){var
b=[0,g$(a),0];return aL(Bq,ah(fh(Bp,[0,a[3],b])))}function
k9(h,g,b,e){var
d=a(f[19][8],g);Y(d,b)[b+1]=e;return a(c[23],[0,h,d])}function
k_(a){function
c(d){function
c(a){return b(w[55],[0,a[1]],1)}return b(f[17][11],c,a)}return[0,c,function(d){function
c(a){return b(w[55],[0,a[1]],a[2])}return b(f[17][11],c,a)}]}function
k$(g,j,f,d,a){function
e(k,a,f){if(0===f)return 0;var
d=b(c[3],j,k);switch(d[0]){case
6:if(a){var
g=a[1],l=a[2];return[0,g,e(b(c[h][5],g,d[3]),l,f-1|0)]}break;case
8:var
i=d[2];return[0,i,e(b(c[h][5],i,d[4]),a,f-1|0)]}throw[0,I,Br]}return e(f,d,a)}function
la(d){var
a=d[1];if(typeof
a==="number")return 0;else{if(0===a[0]){var
b=a[1];if(b)return[0,b[1][1]+1|0];throw[0,I,Bs]}var
c=a[1];return c?[0,c[1][1]+1|0]:Bt}}function
fn(e,E,R,r,p,m){function
H(J,t,H,r,p,i){function
L(a){return a[4]}var
u=b(M[16],L,H),v=i[3];if(v){var
j=v[1],O=i[4],P=j[2],Q=function(k){var
e=a(C[5],k),E=a(C[2],k),r=j[6];if(0===r[0]){var
u=r[1],G=a(C[4],k),v=g(c[df],E,j[5],G),t=v[2],l=v[1],H=function(d){var
i=[0,d],v=o(T[3],0,e,d,t),w=a(aE[17],v),j=b(c[91],d,t),z=j[2],A=j[1],B=a(f[17][1],P),C=k$(e,d,y(T[2],0,0,e,d,A),z,B),D=u[3],E=a(f[17][9],C),k=b(c[h][4],E,D),F=aF(0,l),G=b(c[41],k,F),m=b(c[x],l,e),n=o(ae[2],0,m,d,G),p=n[1],q=g(N[22],m,p,n[2]),H=a(f[17][1],l);if(o(c[h][14],p,1,H,q)){var
J=-a(f[17][1],l)|0,K=b(c[h][1],J,q),r=g5(e,i,l,t,w,K,k,u[4]),L=r[3],s=cA(e,i[1],0,r[2]),M=s[1];return[0,M,a(c[23],[0,L,[0,s[2]]])]}throw[0,I,Bv]};return a(F(b(cD[1],0,H)),k)}var
m=r[1][1];if(typeof
m==="number")var
p=0,q=1;else
if(0===m[0]){var
A=m[1];if(!A)throw[0,I,BB];var
B=A[1][1],q=0}else{var
D=m[1];if(D)var
B=D[1][1],q=0;else
var
p=BC,q=1}if(!q)var
p=[0,B];if(p){var
w=p[1],L=b(K[5],i[1][2],Bw);aM(function(q){var
c=a(f[17][1],J),e=a(d[16],c),g=a(d[3],Bx),h=a(d[16],j[5]),i=a(d[3],By),k=a(d[16],w),l=a(d[3],Bz),m=b(d[12],l,k),n=b(d[12],m,i),o=b(d[12],n,h),p=b(d[12],o,g);return b(d[12],p,e)});var
M=[0,s[29],0],O=[0,b(s[8],L,w+1|0),M],z=aL(BA,a(n[65][22],O))}else
var
z=s[29];return a(F(z),k)},R=q(t,u,r,O),S=F(s[29]),U=b(n[5],S,R),V=[0,aA(BD,b(n[5],Q,U)),0],W=F(hb),X=[0,b(n[25],j[5],W),V],Y=[0,F(s[29]),X];return a(n[6],Y)}if(p){var
w=p[1][7];if(w){var
z=w[1];if(0===z[0]){var
e=z[1];if(typeof
e==="number")var
k=0,m=1;else
if(0===e[0]){var
D=e[1];if(!D)throw[0,I,BG];var
E=D[1][1],m=0}else{var
G=e[1];if(G)var
E=G[1][1],m=0;else
var
k=BH,m=1}if(!m)var
k=[0,E];if(k)var
Z=k[1],_=b(K[5],i[1][2],BE),$=[0,s[29],0],aa=[0,b(s[8],_,Z+1|0),$],A=aL(BF,a(n[65][22],aa));else
var
A=s[29];var
B=A,l=1}else
var
l=0}else
var
l=0}else
var
l=0;if(!l)var
B=s[29];var
ab=q(t,u,r,i[4]),ac=F(B);return b(n[5],ac,ab)}function
q(p,t,r,T){var
m=T;for(;;)switch(m[0]){case
0:var
u=m[2],U=m[4],Z=m[1][1],J=fl(k8,t);if(J)var
K=J[1],V=K[2],$=K[1],aa=function(a){return[0,a]},ab=b(f[17][68],aa,V),N=a(f[7],$),x=ab;else
var
aB=function(a){return 0},N=0,x=b(f[17][68],aB,u);if(a(f[17][48],u))var
B=n[1];else{var
ar=function(k,o,m,y,C){var
q=C[2],Y=C[1],$=m[1];if(y){var
t=y[1];try{var
D=b(a9[23],t[4],e[3])}catch(a){a=v(a);if(a===O)throw[0,I,BO];throw a}var
aa=D[2],ab=D[1];if(X[1]){var
ac=g(z[11],k,o,ab),ad=a(d[3],BP),ae=g(z[11],k,o,t[7]),af=a(d[3],BQ),ag=aU(t),ai=g(z[11],k,o,ag),aj=a(d[3],BR),ak=a(d[3],BS),al=b(d[12],ak,aj),am=b(d[12],al,ai),an=b(d[12],am,af),ao=b(d[12],an,ae),ap=b(d[12],ao,ad),aq=b(d[12],ap,ac);b(L[9],0,aq)}var
E=t[1],ar=a(f[17][1],N),as=a(f[17][1],E[1][5])-ar|0,F=b(f[17][W],as,E[1][5]),at=F[1],au=a(f[17][1],F[2]),A=au<=a(f[17][1],q)?q:bB(0,a(d[3],B5)),av=aU(t),G=b(c[h][4],A,av),J=cV(0,A,at);if(X[1]){var
aw=b9(k,l[16],J),ax=a(d[3],BT),aA=g(z[11],k,o,G),aB=a(d[3],BU),aC=b(z[11],k,o),aD=g(d[39],d[13],aC,A),aE=a(d[3],BV),aG=b(d[12],aE,aD),aH=b(d[12],aG,aB),aJ=b(d[12],aH,aA),aK=b(d[12],aJ,ax),aM=b(d[12],aK,aw);b(L[9],0,aM)}var
Q=0,x=J,u=G,P=-1,K=[0,aa,r]}else{var
bn=aU(m),B=$[1][5],bo=a(f[17][1],q),bp=a(f[17][1],B)-bo|0,bq=b(f[17][W],bp,B)[1],V=b(c[h][4],q,bn),br=cV(0,q,bq);if(X[1]){var
bs=b9(k,o,B),bt=a(d[3],B6),bu=g(z[11],k,o,V),bv=a(d[3],B7),bw=b(z[11],k,o),bx=g(d[39],d[13],bw,q),by=a(d[3],B8),bz=aU(m),bA=g(z[11],k,o,bz),bC=a(d[3],B9),bD=a(d[3],B_),bF=b(d[12],bD,bC),bG=b(d[12],bF,bA),bH=b(d[12],bG,by),bI=b(d[12],bH,bx),bJ=b(d[12],bI,bv),bK=b(d[12],bJ,bu),bL=b(d[12],bK,bt),bM=b(d[12],bL,bs);b(L[9],0,bM)}var
Q=0,x=br,u=V,P=p[1],K=r}var
aN=[0,P,p[2]],aO=0,aP=m[1],aQ=[0,m[2]];function
aR(a){return a[1]}var
aS=[0,ah(H(Z,aN,b(M[16],aR,y),K,aQ,aP)),aO],aT=b(s[82],f4,1),aV=[0,aL(BW,a(n[65][24],aT)),aS],aW=[0,b(n[65][31],Q,hb),aV],aX=aL(BX,a(n[65][22],aW));try{var
bm=b(a9[23],m[4],e[2]),R=bm}catch(a){a=v(a);if(a!==O)throw a;var
R=ba(BY)}var
S=R[1];if(X[1]){var
T=a(w[2],0),aY=_(x),aZ=aI(T,l[16],aY),a0=a(d[3],BZ),a1=g(z[11],T,l[16],u),a2=a(d[3],B0),a3=bE(m),a4=a(a7[6],a3),a5=a(d[3],B1),a6=a(j[1][8],S),a8=a(d[3],a6),a_=a(d[3],B2),a$=b(d[12],a_,a8),bb=b(d[12],a$,a5),bc=b(d[12],bb,a4),bd=b(d[12],bc,a2),be=b(d[12],bd,a1),bf=b(d[12],be,a0),bg=b(d[12],bf,aZ);b(L[9],0,bg)}var
bh=b(ay[32],0,S),bi=a(az[13],bh);function
U(d){var
e=b(c[91],l[16],u)[2];function
g(a){return b(c[52],l[16],a)}var
h=b(f[17][61],g,e),a=aF(0,x),i=b(f[17][57],h,a),j=[0,b(c[41],u,a),0],k=b(f[17][57],i,j),m=b(c[41],d,k);return b(c[44],m,x)}function
bj(c){if(X[1]){var
e=a(w[2],0),f=U(c),h=g(z[11],e,l[16],f),i=a(d[3],B3),k=bE(m),n=a(j[1][8],k),o=a(d[3],n),p=a(d[3],B4),q=b(d[12],p,o),r=b(d[12],q,i),t=b(d[12],r,h);b(L[9],0,t)}var
u=U(c),v=[0,bE(m)];return g(s[d1],v,u,aX)}var
bk=a(n[65][61],bi),bl=b(i[17],bk,bj);return[0,b(n[65][3],Y,bl),[0,u,q]]},as=a(f[17][1],x);if(a(f[17][1],u)!==as)throw[0,I,B$];var
at=function(e){var
j=a(i[68][4],e),d=a(i[68][5],e),k=a(i[68][2],e),l=b(c[91],d,k)[2],m=a(f[17][fJ],l);function
h(a,k){var
e=b(c[91],d,k),l=e[2],i=b(c[3],d,e[1]);switch(i[0]){case
1:var
j=i[1];return b(f[17][25],j,a)?a:[0,j,a];case
12:return g(f[17][15],h,a,l);default:return a}}var
p=g(f[17][15],h,0,m);function
q(b){return 1-a(A[bw],b)}var
r=b(f[17][61],q,p),s=b(f[17][68],c[11],r),t=[0,n[65][2],s];function
v(a,b,c){return ar(j,d,a,b,c)}return o(f[17][20],v,u,x,t)[1]},au=a(i[68][8],at),av=fi(e[1][3]),aw=[0,a(n[20],av),0],ax=[0,F(au),aw],B=a(n[6],ax)}if(0===U[0]){var
ac=0,S=function(m){var
h=a(i[68][5],m),y=a(i[68][2],m),o=b(c[3],h,y);if(9===o[0]){var
S=a(f[19][44],o[2]),T=b(c[91],h,S)[1];try{var
U=b(c[82],h,T)[1],V=a(j[17][8],U),W=a(j[6][6],V),X=function(a){return b(j[1][1],a[1],W)},Y=[0,b(D[27],X,R)],x=Y}catch(a){a=v(a);if(a!==G[59])if(a!==O)throw a;var
x=0}var
k=x}else
var
k=0;if(k){var
p=k[1],d=p[3],r=d[3],z=p[2];if(r){var
t=r[1],u=t[6],A=t[5];if(0===u[0])var
l=0;else
var
K=u[1],L=[0,b(n[65][31],A,s[16]),0],N=la(K),P=b(M[23],1,N),Q=[0,b(s[8],d[1][2],P),L],w=a(n[65][22],Q),l=1}else
var
l=0;if(!l)var
w=a(i[16],0);var
B=ah(q(E,0,0,d[4])),C=b(n[65][3],w,B),H=ah(aA(Bu,F(fm(e[1])))),I=[0,bV(d)],J=g(s[d1],I,z,C);return b(n[65][3],J,H)}return a(i[16],0)},ad=aA(BI,F(a(i[68][8],S))),ae=aA(BJ,F(fm(e[1]))),af=a(n[21],ae),ag=[0,b(n[4],af,ad),ac],ai=function(c){var
d=c_[3];function
e(a){return b(d,0,a)}var
f=fV(c),g=a(n[65][61],f),h=F(b(i[17],g,e));return a(n[20],h)},aj=b(n[29],ai,r),ak=F(s[29]),al=[0,b(n[5],ak,aj),ag],am=[0,aA(BK,hc(e[1])),al],an=[0,aA(BL,B),am],ao=fi(e[1][3]),ap=[0,dU,[0,a(n[20],ao),an]];return aA(BM,a(n[6],ap))}var
aq=[0,dU,[0,B,[0,F(iL(0)),0]]];return aA(BN,a(n[6],aq));case
1:var
aC=m[2],aD=m[1],aE=a(f[19][11],m[4]),aG=function(a){return a},aH=b(f[17][65],aG,aE),P=fl(k6,t);if(P)var
aJ=a(f[19][11],P[1]),aK=function(a){return a},Q=[0,b(f[17][65],aK,aJ)];else
var
Q=0;var
aM=function(a){var
c=b(f[17][7],aH,a-1|0);function
d(c){return b(f[17][7],c,a-1|0)}return q(p,b(M[16],d,Q),r,c)},aN=function(e){var
o=a(C[4],e),q=a(C[2],e),j=b(c[3],q,o);if(9===j[0]){var
s=a(f[19][11],j[2]),k=a(f[17][fJ],s),u=0<=p[1]?b(f[17][W],p[1],k)[2]:k;if(t){var
h=t[1];if(1===h[0])var
x=h[2],m=eG(h[1]),l=x,i=1;else
var
i=0}else
var
i=0;if(!i)var
v=eG(aD),w=function(a){return 1-e_(a)},m=b(f[17][61],w,v),l=aC;return a(F(f8(k5(a(C[2],e),m,l,u))),e)}var
r=a(d[3],Ca);return g(n[23],0,r,e)};return aA(Cb,b(n[7],aN,aM));case
2:var
m=m[2];continue;default:var
aO=m[3],aP=m[2],aQ=fl(k7,t),aR=a(f[7],aP[1]),aS=function(h){var
l=a(i[68][5],h),F=a(i[68][2],h),o=b(c[3],l,F);if(9===o[0]){var
t=o[2],H=o[1],u=b(bd[58],t.length-1-1|0,t),I=u[1],J=Y(u[2],0)[1],v=b(c[81],l,J),w=v[2],x=v[1],K=g(c[5],0,l,x),z=fk(e[1],K,w),A=z[2],L=z[3],m=b(C[35][11],aR,h),M=a(i[68][3],h),B=j[1][10][1],D=function(d,c){var
e=a(k[11][1][2],c);return b(j[1][10][4],e,d)},E=g(f[17][15],D,B,M),N=a(j[1][10][21],E),O=function(a){return[0,[0,0,a],0]},P=[0,[0,b(f[17][68],O,N)],2],Q=k9(x,w,A,a(c[11],m)),R=a(c[11],m),S=[0,k9(H,I,A-p[2]|0,R),[0,Q]],T=a(c[23],S),U=[0,ah(q(p,aQ,r,aO)),0],V=[0,aL(Cd,a(s[77],[0,m,0])),U],W=[0,aL(Cf,g(s[3],Ce,T,2)),V],X=[0,aL(Cg,y(s[147],1,0,[0,m],[0,l,L],P)),W];return a(n[65][22],X)}var
G=a(d[3],Cc);return b(n[65][4],0,G)},aT=[0,fm(e[1]),0],aV=[0,a(i[68][8],aS),0],aW=a(n[65][35],aV),aX=ah(hc(e[1])),aY=ah(fi(e[1][3])),aZ=a(n[65][24],aY),a0=b(n[65][3],aZ,aX),a1=[0,b(n[65][19],a0,aW),aT];return F(aL(Ch,a(n[65][22],[0,s[29],a1])))}}return H(0,E,r,p,0,m)}function
fo(e,c){if(X[1]){var
h=function(j){function
h(h){function
j(k){var
j=b(f[17][68],i[10],k),l=hw(z[66],0,0,0,0,h,0,0,0,0,j),m=a(d[3],Ci),n=a(d[3],e),o=a(d[3],Cj),p=b(d[12],o,n),s=b(d[12],p,m),v=b(d[12],s,l);b(L[9],0,v);function
w(g){var
f=g[1];if(f[1]===bO[26])var
c=f[3],m=f[2],n=hw(z[66],0,0,0,0,h,0,0,0,0,j),k=t(c),o=a(d[3],Ck),p=u===k?c[1]:q===k?a(r[2],c):c,s=a(d[13],0),v=a(d[3],e),w=a(d[3],Cl),x=a(d[16],m),y=a(d[3],Cm),A=b(d[12],y,x),B=b(d[12],A,w),C=b(d[12],B,v),D=b(d[12],C,s),E=b(d[12],D,p),F=b(d[12],E,o),l=b(d[12],F,n);else
var
l=a($[15],g);var
G=a(d[3],Cn),H=b(d[12],G,l);b(L[9],0,H);return a(i[16],0)}function
x(c){if(0===c){var
f=a(d[3],Co),h=a(d[3],e),j=b(d[12],h,f);b(L[9],0,j);return a(i[16],0)}return ah(function(c){var
e=g(z[65],0,0,c),f=a(d[3],Cp),h=b(d[12],f,e);b(L[9],0,h);return[0,[0,c[1],0],c[2]]})}var
y=b(i[73][1],i[53],x),A=b(i[18],c,y);return b(i[23],A,w)}return b(i[73][1],i[66][6],j)}return b(i[73][1],i[54],h)};return b(i[73][1],i[55],h)}return c}var
c$=[cN,Cq,cK(0)];function
hd(c){function
d(d){function
e(e){function
c(c){return Bn(d,c)?a(i[16],0):b(i[21],0,c$)}return b(i[73][1],i[54],c)}return b(i[73][1],c,e)}return b(i[73][1],i[66][6],d)}function
lb(J,ax,e,az,q,h){function
ay(d){var
c=d[1];if(c[1]===cT[1]){var
e=g(bP[2],c[2],c[3],c[4]);b(L[8],0,e);return a(f[33],d)}return a(f[33],d)}if(J){var
t=J[1];if(t){var
u=t[1];if(0===u[0])var
v=u[1],M=function(b){var
a=b[2];if(typeof
a!=="number"&&0===a[0])return 1;return 0},w=b(f[17][30],M,v),x=w[2],z=w[1],N=function(c){var
a=c[2];if(typeof
a!=="number"&&0===a[0]){var
b=a[1];if(b)return b[1][1]+1|0}return-1},j=b(f[17][68],N,z),O=function(d){var
a=d[1][1][7];if(a){var
b=a[1];if(0===b[0]){var
c=b[1];if(typeof
c!=="number"&&1!==c[0])return 1}}return 0},A=b(f[17][30],O,h),B=A[2],m=A[1],P=g_[8],Q=[0,Cr,[0,e[1][3],0]],p=function(c){if(c){var
d=c[2];if(d){var
e=[0,p(d),0],f=[0,a(i[16],0),e],g=a(i[36],f),h=a(s[114],0);return b(i[73][2],h,g)}}return a(i[16],0)},C=function(c){function
d(g){var
d=g[1],c=e[1],h=e[3],i=e[2],j=c[7],k=c[6],l=b(f[18],e[1][5],g[3][2][5]),m=[0,[0,c[1],c[2],c[3],c[4],l,k,j],i,h],n=[0,d[1],d[2],0,d[4],d[5]];return ah(fn(m,[0,0,a(f[17][1],v)],q,0,0,n))}var
g=b(f[17][68],d,c),h=a(i[36],g);return b(i[73][2],s[29],h)},R=C(B),S=function(d){var
c=d[2],e=d[1];if(typeof
c!=="number"&&1===c[0]){var
f=c[1];return f?b(s[8],e,f[1][1]+1|0):b(s[8],e,1)}return a(i[16],0)},T=b(f[17][68],S,x),U=a(i[36],T),V=b(i[73][2],U,R),W=C(m),Y=f7(0),Z=fj(0,j),_=b(i[73][2],Z,Y),E=b(i[73][2],_,W),$=function(v){var
w=v[1],I=v[2];if(w===c$){var
J=function(c){var
e=c[1],f=c[2];if(e===c$){var
g=a(d[3],Cw),h=a(d[3],Cx),j=b(d[12],h,g);b(L[6],0,j);return n[65][2]}return b(i[21],[0,f],e)};if(j)if(j[2])var
g=0;else{var
x=j[1];if(X[1]){var
y=a(d[3],Cs);b(L[9],0,y)}if(h)if(h[2])var
o=0;else{var
r=h[1][1],t=r[4];if(1===t[0])var
G=a(f[19][11],t[4]),H=function(a){return a},u=[0,[0,r,b(D[65],H,G)]];else
var
u=0;var
l=u,o=1}else
var
o=0;if(!o)var
l=0;if(l)var
p=l[1],c=p[1],z=p[2],A=0,B=function(d){function
g(a){return ah(fn(e,Ct,q,0,0,[0,c[1],c[2],c[3],a,c[5]]))}var
h=b(f[17][68],g,z),j=a(i[36],h),l=f7(0),m=s[29],n=iK(a(k[11][1][2],d)),o=b(i[73][2],n,m),p=b(i[73][2],o,l);return b(i[73][2],p,j)},C=aL(Cu,a(n[65][47],B)),E=b(n[65][31],x,s[16]),F=[0,b(i[73][2],E,C),A],m=aL(Cv,a(i[36],F)),g=1;else
var
m=b(i[21],0,c$),g=1}else
var
g=0;if(!g)var
m=b(i[21],0,c$);var
K=hd(m);return b(i[23],K,J)}return b(i[21],[0,I],w)},aa=0<a(f[17][1],x)?E:hd(E),ab=b(i[23],aa,$),ac=a(f[17][1],m),ad=function(n){function
g(h,d){var
m=a(i[68][5],n),e=b(c[3],m,h);if(9===e[0]){var
f=e[2];if(2===f.length-1){var
j=f[1],k=f[2],o=e[1];if(1===d)return[0,j,[0,k]];var
l=g(k,d-1|0),p=l[2];return[0,a(c[23],[0,o,[0,j,l[1]]]),p]}}if(1===d)return[0,h,0];throw[0,I,Cy]}var
d=g(a(i[68][2],n),ac),e=d[2],h=d[1],l=fo(Cz,y(P,0,0,0,0,Q)),q=[0,a(i[16],0),0],r=a(f[17][1],z),t=o(i[31],0,1,r,ab),u=p(m),v=[0,fo(CA,b(i[73][2],u,t)),q],w=a(i[36],v),x=b(s[mI],0,h);if(e)var
A=e[1],C=[0,a(i[16],0),0],D=fo(CB,p(B)),E=b(i[73][2],s[16],D),F=[0,fo(CC,b(i[73][2],E,V)),C],G=a(i[36],F),H=a(c[20],[0,k[9],h,A]),J=b(s[mI],0,H),j=b(i[73][2],J,G);else
var
j=a(i[16],0);var
K=ei(0),L=b(i[73][2],K,j),M=b(i[73][2],L,x),N=b(i[73][2],M,w);return b(i[73][2],N,l)},K=a(i[68][8],ad),l=1;else
var
l=0}else
var
l=0}else
var
l=0;if(!l){var
ae=e[1][5],af=function(a){return a[1]},ag=b(f[17][68],af,ae),ai=[0,a(G[71],ax)[1],ag],aj=function(a){return[0,a,0]},F=k_(b(f[17][68],aj,ai)),ak=F[2],al=F[1];if(h)if(h[2])var
r=0;else{var
H=h[1],am=H[2],an=H[1];a(al,0);var
ao=function(b){a(ak,0);return a(i[16],b)},ap=[0,ah(fn(e,CE,q,am,0,an)),0],aq=[0,s[29],ap],ar=[0,ei(0),aq],as=a(n[65][22],ar),at=a(n[65][34],as),au=b(i[17],at,ao),av=function(c){var
e=c[1],f=c[2];if(e===c$){var
g=a(d[3],CF),h=a(d[3],CG),j=b(d[12],h,g);b(L[6],0,j);return a(i[16],0)}return b(i[21],[0,f],e)},aw=hd(au),K=b(i[23],aw,av),r=1}else
var
r=0;if(!r)throw[0,I,CD]}return b(i[23],K,ay)}function
lc(a,e){var
d=b(c[91],a,e)[1];if(b(c[62],a,d))return b(c[82],a,d)[1];throw[0,I,CI]}function
ld(z,ay,Y,V,S,R,m){if(X[1]){var
l=L[9],Z=a(C[5],m),_=a(C[2],m);b(l,0,a(d[3],C8));b(l,0,ce(Z,_,C9,S[4]));var
aB=a(d[5],0),aC=a(d[3],C_),aD=a(d[5],0),aE=b(d[12],aD,aC);b(l,0,b(d[12],aE,aB));b(l,0,ce(Z,_,C$,R[4]))}try{var
B=function(b){return dT(0,[0,a(dB[4],CJ),b])},$=z[5],aa=function(a){return a[1]},ab=[0,Y,[0,V,b(f[17][68],aa,$)]],ac=function(a){return[0,a,0]},ad=b(f[17][68],ac,ab),D=t(ds),af=dV[3],ag=u===D?ds[1]:q===D?a(r[2],ds):ds,E=k_([0,[0,a(aS[8],ag),af],ad]),e=E[2],G=E[1],H=function(c,b){a(G,0);var
d=a(c,b);a(e,0);return d},p=function(a){return H(F(iG(0)),a)},ai=F(s[62]),aj=function(a){return H(ai,a)},ak=[0,a(N[16],bq[10]),2],al=F(b(s[51],CK,ak)),am=0,an=[0,b(J[17],z[3],CL),0],ao=function(a){return f6(an,am,a)},ap=b(n[5],ao,al),aq=0,ar=[0,z[3],0],as=function(a){return f6(ar,aq,a)},A=b(n[5],as,ap),at=function(k,d){var
l=a(C[4],d),m=a(C[2],d),i=b(c[3],m,l);if(9===i[0]){var
h=i[2];if(3===h.length-1){var
o=h[2],q=h[3],e=a(C[2],d),r=b(c[91],e,o)[1],t=b(c[91],e,q)[1];try{var
w=function(a){var
d=a[2],b=g(c[a2],e,[1,a[1]],r);return b?g(c[a2],e,[1,d],t):b},j=b(f[17][27],w,k),x=a(s[69],[0,[0,CO,[1,j[1]]],[0,[0,CN,[1,j[2]]],0]]),y=[0,p,[0,F(iC(0)),0]],z=[0,F(x),y],A=b(n[6],z,d);return A}catch(c){c=v(c);if(c===O){var
u=b(CM[4],10,0);return a(F(b(n[65][12],s[cp],u)),d)}throw c}}}return a(F(s[cp]),d)},P=function(c){function
d(a){return at(c,a)}var
f=F(s[cp]);function
g(c){a(e,0);var
b=a(f,c);a(G,0);return b}return aA(CP,b(n[4],g,d))},Q=function(m,c,l){function
d(z){var
o=a(i[68][5],z),f=lc(o,c[5]),g=lc(o,l[5]),A=[0,F(a(s[69],[0,[0,CR,[1,f]],[0,[0,CQ,[1,g]],0]])),[0,aj,0]],d=a(n[6],A);function
p(a){b(w[55],[0,f],1);return b(w[55],[0,g],1)}var
q=c[3];if(q){var
h=q[1],r=h[6];if(0===r[0])if(d7[1])var
B=[0,iJ(0),0],C=[0,ah(d),B],e=[0,a(n[65][22],C),0];else
var
K=[0,iI(0),0],L=[0,ah(d),K],e=[0,a(n[65][22],L),1];else{var
v=la(r[1]);if(v)var
M=v[1],N=[0,ah(d),0],O=[0,b(n[65][31],h[5],s[16]),N],P=[0,aL(CW,fj(0,[0,M,0])),O],Q=[0,b(n[65][31],h[5],hb),P],y=[0,a(n[65][22],Q),0];else
var
y=[0,a(i[16],0),0];var
e=y}var
k=[0,[0,f,g],m],j=e[1],t=e[2]}else
var
k=m,j=ah(d),t=0;var
D=0,E=[0,function(b){p(0);return a(aA(CS,x(k,c[4],l[4])),b)},D];if(t)var
G=function(b){p(0);return a(aA(CT,x(k,c[4],c[4])),b)},H=F(j),u=b(n[8],H,G);else
var
u=F(j);var
I=[0,aA(CU,u),E],J=[0,aA(CV,F(s[29])),I];return ah(a(n[6],J))}return a(i[68][8],d)},x=function(m,q,J){var
e=J;for(;;){switch(q[0]){case
0:var
t=q[2];if(0===q[4][0])switch(e[0]){case
0:var
u=e[2],L=e[1][1];if(0===e[4][0]){var
N=function(q,p,k){try{var
d=b(a9[23],k[4],ay)}catch(a){a=v(a);if(a===O)throw[0,I,CX];throw a}var
i=d[2],r=d[1];return function(j){var
t=a(C[5],j),l=[0,a(C[2],j)],d=k[1],e=d[1][5],u=p[1],v=a(f[17][1],L),o=a(f[17][1],e)-v|0,w=U(0,b(f[17][W],o,e)[1]),x=[0,b(c[h][1],o,r),w],y=a(c[23],x),z=U(0,e),A=a(c[23],[0,d[5],z]),B=b0(t,l,d[1][6],y,A),D=b(c[44],B,e),E=Q(m,u,d),G=F(g(CY[2],0,[0,i],E)),H=F(a(s[79],0)),I=ah(b(n[5],H,G)),J=g(s[d1],[0,i],D,I),K=a(c[11],i),M=[0,F(b(c_[3],0,K)),[0,q,0]],N=[0,F(J),M],O=[0,a(bO[8],l[1]),N];return b(n[6],O,j)}},R=a(f[17][1],u);if(a(f[17][1],t)===R){var
S=o(f[17][19],N,n[1],t,u),V=[0,p,[0,P(m),0]],X=[0,S,[0,aA(CZ,a(n[20],A)),V]],Y=[0,F(s[29]),X];return aA(C0,a(n[6],Y))}throw[0,I,C1]}var
r=1;break;case
2:var
l=0,r=0;break;default:var
l=1,r=0}else
var
r=1;if(r)switch(e[0]){case
0:var
w=e[4],Z=e[1][1];if(0!==w[0]){var
_=a(bA,b(f[17][7],Z,w[1]-1|0));return F(B(a(K[13][16],_)))}var
l=1;break;case
2:var
l=0;break;default:var
l=1}break;case
1:var
D=q[4];switch(e[0]){case
1:var
E=e[4],$=e[2],aa=e[1][1];return aA(C4,function(e){var
s=a(C[2],e),i=a(C[5],e),o=b(f[17][7],aa,$-1|0),q=cY(dz(i,s,a(k[10][1][4],o))[1])[1][1],r=b(bS[4],i,q);if(a(bS[15],r)){var
t=a(f[19][42],E),u=a(M[7],t),v=a(f[19][42],D);return a(x(m,a(M[7],v),u),e)}var
w=a(C[4],e),y=a(C[2],e),j=b(c[3],y,w);if(9===j[0]){var
l=j[2];if(3===l.length-1){var
A=l[3],h=a(C[2],e),G=b(c[91],h,A)[1],H=b(c[86],h,G)[3],I=n[1],J=b(c[91],h,H)[1],K=b(c[75],h,J),L=a(f[19][11],D),N=function(a){return a},O=b(f[17][65],N,L),P=a(f[19][11],E),Q=function(a){return a},R=b(f[17][65],Q,P),S=function(c){var
d=b(f[17][7],O,c-1|0),e=[0,I,[0,p,[0,x(m,d,b(f[17][7],R,c-1|0)),0]]];return a(n[6],e)},T=F(B(K));return a(F(ah(b(n[7],T,S))),e)}}var
z=a(d[3],C3);return g(n[23],0,z,e)});case
2:var
l=0;break;default:var
l=1}break;case
3:var
ab=q[3];switch(e[0]){case
2:var
l=0;break;case
3:var
G=e[2],ac=e[3],ad=a(f[7],G[1]),H=function(e){var
B=a(C[4],e),D=a(C[2],e),q=b(c[3],D,B);if(9===q[0]){var
h=q[2];if(3===h.length-1){var
I=h[2],J=h[3],f=a(C[2],e),K=b(c[91],f,G[5])[1],L=b(c[82],f,K)[1],r=b(c[81],f,I),M=r[2],N=r[1],t=b(c[81],f,J),O=t[2],Q=t[1],k=fk(z,g(c[5],0,f,N),M)[3],u=fk(z,g(c[5],0,f,Q),O),l=u[3],R=u[1],v=b(C[17],ad,e);if(b(j[17][12],R,L)){var
S=[0,A,[0,x(m,ab,ac),0]],U=a(s[77],[0,v,0]),V=[0,a(i[72][7],U),S],W=[0,aA(C6,F(y(s[bY],0,[0,v],l,0,dK[5]))),V],X=[0,P(m),0],Y=ah(a(n[6],X)),w=function(d){var
h=a(i[68][4],d),e=a(i[68][5],d);if(g(c[aJ],e,k,l))return a(i[16],0);var
p=y(T[2],0,0,h,e,k),m=aR(e,a4),q=m[1],n=a(c[23],[0,m[2],[0,p,k,l]]),r=o(ae[2],0,h,q,n)[1],t=a(j[1][6],CH),f=b(C[35][11],t,d),u=a(s[76],[0,f,0]),v=a(c[11],f),w=b(c_[3],0,v),x=g(s[d1],[0,f],n,Y),z=a(i[66][1],r),A=b(i[73][2],z,x),B=b(i[73][2],A,w);return b(i[73][2],B,u)},Z=[0,F(a(i[68][8],w)),W];return b(n[6],Z,e)}return b(n[6],[0,A,[0,p,[0,H,0]]],e)}}var
E=a(d[3],C5);return g(n[23],0,E,e)},af=[0,p,[0,aA(C7,H),0]],ag=[0,F(s[29]),af];return F(ah(a(n[6],ag)));default:var
l=1}break;default:var
l=0}if(!l)if(2===e[0]){var
e=e[2];continue}throw[0,I,C2]}};try{var
au=[0,F(Q([0,[0,Y,V],0],S,R)),0],av=[0,F(s[29]),au],aw=[0,F(ei(0)),av],ax=b(n[6],aw,m);a(e,0);return ax}catch(b){b=v(b);a(e,0);throw b}}catch(a){a=v(a);if(a[1]===az[4])throw a;throw a}}function
le(A,l,z,k,x){var
m=g_[8],p=[0,Da,[0,k[3],0]];function
e(a){return y(m,0,0,0,a,p)}function
j(l,k){function
d(m){var
r=a(i[68][4],m),t=a(i[68][5],m),B=a(i[68][2],m),p=b(c[3],t,B);if(0===l){var
C=a(f[17][9],k),q=b(c[41],A,C),u=o(ae[2],0,r,t,q),d=u[1],D=u[2];if(1===z){var
v=g(N[18],r,d,q),E=0,y=function(b){var
c=a(i[68][5],b),d=a(i[68][4],b),f=o(ae[2],0,d,c,v)[1],g=[0,aL(Db,e(0)),0],h=[0,s[62],g],j=[0,aL(Dc,a(s[87],v)),h],k=[0,a(i[66][1],f),j];return aL(Dd,a(n[65][22],k))},F=[0,a(i[68][8],y),E],G=[0,s[62],[0,s[29],F]],H=[0,a(i[66][1],d),G];return a(n[65][22],H)}var
J=b(c[99],d,D)[2],K=e(0),L=s[62],M=a(s[87],q),O=b(i[73][2],M,L),P=b(i[73][2],O,K),Q=[0,a(n[65][8],P),0],R=e(0),S=a(s[142],0),T=a(n[65][61],x),U=b(i[73][1],T,S),V=b(i[73][2],U,R),W=b(i[73][2],s[16],V),X=[0,a(n[65][8],W),Q],Y=a(i[36],X),Z=a(s[144],J),_=s[29],$=s[62],aa=a(i[66][1],d),ab=b(i[73][2],aa,$),ac=b(i[73][2],ab,_),ad=b(i[73][2],ac,Z);return b(i[73][2],ad,Y)}switch(p[0]){case
6:var
af=0,ag=function(b){return j(l-1|0,[0,a(c[11],b),k])},ah=[0,a(n[65][45],ag),af];return a(n[65][22],[0,s[16],ah]);case
8:var
w=p[2],ai=p[4],aj=[0,j(l-1|0,[0,w,k]),0],ak=b(c[h][5],w,ai),al=[0,g(s[3],Df,ak,2),aj];return a(n[65][22],al);default:throw[0,I,De]}}return a(i[68][8],d)}try{var
r=aL(Dh,j(l,0));return r}catch(c){var
q=a(d[3],Dg);return b(n[65][4],0,q)}}aD(1242,[0,k0,k1,A0,fh,g$,A3,ha,k2,fi,fj,fk,k5,dU,hc,k6,k7,k8,fl,fm,k$,fn,lb,ld,le],"Principles_proofs");function
lf(d){var
a=d[7];if(a){var
b=a[1];if(0===b[0]){var
c=b[1];if(typeof
c==="number")return Di;else
if(0!==c[0])return Dj}}return 0}function
lg(a){return typeof
a==="number"?0===a?1:0:1}function
lh(a){return a[1]}function
Dk(a){return a[2]}function
Dl(a){var
c=a[2],d=c[1];return[0,d,b(aS[14],a[1],c[2])]}function
Dm(a){return[0,a[2]]}var
Dn=[0,Dl];function
Do(i){var
c=i[2],d=c[2],e=c[1],f=a(w[2],0),g=[0,o(li[16],0,0,f,d),1,0],h=[0,b(af[1],0,g),0];return b(cG[1],e,h)}var
Dq=o(fp[17],Dp,Do,Dn,Dm),Dr=a(fp[4],Dq);function
Ds(a){return b(Dt[40],a[1],a[2])}function
Du(a){return[0,a[2]]}var
Dv=[0,Ds];function
Dw(a){return b(w[55],[0,a[2]],1)}var
Dy=o(fp[17],Dx,Dw,Dv,Du),lj=a(fp[4],Dy);function
lk(f,d,b){function
e(h){var
a=h;for(;;){if(a<b.length-1){if(a<d.length-1){var
i=Y(b,a)[a+1],j=Y(d,a)[a+1];if(g(c[aJ],f,j,i))return[0,a,e(a+1|0)];var
a=a+1|0;continue}var
a=a+1|0;continue}return[0,a,0]}}return e(0)}function
fq(b,a){function
d(h,c,g){var
b=h,a=g;for(;;){if(c)if(a){var
e=a[2],f=c[1],i=a[1],j=c[2];if(b<f){var
b=b+1|0,a=e;continue}if(b===f)return[0,i,d(b+1|0,j,e)];throw[0,I,Dz]}return a}}return d(0,b,a)}var
aZ=a(DA[1],[0,G[86]]);function
ll(l,k,i){var
a=k;for(;;){if(a){var
d=a[1];if(d){var
e=d[1];if(0===e[0]){var
m=a[2],n=e[1];try{var
o=function(a){var
c=a[2];return b(j[1][1],l,a[1])?[0,c]:0},f=b(D[99],o,n);if(typeof
f==="number")var
c=0;else{var
h=f[1];if(h)var
g=[0,h[1][1]<i?1:0],c=1;else
var
c=0}if(!c)var
g=DD;return g}catch(b){b=v(b);if(b===O){var
a=m;continue}throw b}}}var
a=a[2];continue}return 0}}function
lm(c,b){var
d=aZ[1];function
e(e,d,b){var
f=a(c,e);return g(aZ[4],f,d,b)}return g(aZ[13],e,b,d)}function
he(c,a){function
d(e,c,a){if(c){var
d=c[1];return a?[0,b(J[5],d,a[1])]:c}return a?a:0}return g(aZ[8],d,c,a)}function
ln(d,c){function
e(a,e){var
c=a[1],f=a[2],g=b(aB[12],[0,d,0],c);return[0,c+1|0,[0,b(k[10][1][16],g,e),f]]}var
f=g(m[20],e,DE,c)[2];return a(m[9],f)}function
lo(N,M,d,n,e){function
f(f){var
p=f[6],q=f[5],r=f[4],s=f[3],t=f[2][2],O=a(c[au][1],f[1]);if(b(G[80],O,n)){var
P=a(G[71],n)[1],Q=a(m[1],e),R=a(j[17][8],P),u=ll(a(j[6][6],R),N,Q);if(u)if(0===u[1])return 0;var
v=a(m[1],q),l=fq(t,e);if(v<=a(m[1],l))var
w=b(D[W],v,l),x=w[2],S=w[1],T=a(m[1],x),K=a(m[9],e),L=b(D[bI],T,K),z=0,y=[0,a(m[9],L),S,x];else{var
U=b(m[17],c[au][3],q),d=a(m[9],U),h=l;for(;;){if(h){if(d){var
o=d[1],F=h[2],H=h[1];if(0===o[0]){var
d=ln(H,d[2]),h=F;continue}var
d=ln(o[2],d[2]);continue}throw[0,I,DF]}var
i=a(m[9],d),B=a(m[1],i),V=g(k[10][14],G[1],0,i),X=a(G[89],B),Y=b(m[17],X,l),Z=b(J[26],Y,V),_=g(k[10][14],G[1],0,i),$=a(G[89],B),aa=b(m[17],$,e),z=i,y=[0,b(J[26],aa,_),Z,0];break}}return[0,[0,r,p,t,z,y]]}if(s){var
C=s[1],ab=C[2],ac=b(A[69],M,C[1])[1],ad=a(c[au][1],ac),E=a(G[69],ad)[1];return b(G[80],E,n)?[0,[0,r,p,ab,0,[0,e,e,0]]]:0}return 0}try{var
h=[0,b(D[99],f,d)];return h}catch(a){a=v(a);if(a===O)return 0;throw a}}function
hf(x,V,l,U,s,w,I){var
W=l?l[1]:1;function
J(a){return a[2][1]}var
y=b(m[17],J,w),z=[0,0];function
f(e,i,l,n){var
d=a(G[29],n);switch(d[0]){case
6:var
H=d[3],at=d[2],av=d[1];if(b(aB[3],1,H)){var
I=f(e,i,l,at),aw=I[2],ax=I[1],J=f(e,i,ax,b(aB[14],G[8],H)),ay=J[1],az=[0,av,aw,b(G[89],1,J[2])];return[0,ay,a(G[12],az)]}break;case
7:var
K=d[2],L=d[1],aA=f(e+1|0,[0,[0,L,0,K],i],aZ[1],d[3])[1];return[0,he(l,lm(function(b){return a(G[12],[0,L,K,b])},aA)),n];case
8:var
M=d[3],u=d[2],N=d[1],aC=d[4],aD=f(e,i,l,u)[1],aE=f(e+1|0,[0,[0,N,[0,u],M],i],aZ[1],aC)[1];return[0,he(aD,lm(function(b){return a(G[14],[0,N,u,M,b])},aE)),n];case
13:var
O=d[4],aF=d[2],aG=d[1],P=f(e,i,l,d[3]),aH=P[2],aI=P[1],aJ=function(b,a){return f(e,i,b,a)[1]},aK=g(aY[17],aJ,aI,O),aL=a(G[26],[0,aG,aF,aH,O]),aM=a(c[9],aL),aN=g(c[h][3],y,s+1|0,aM);return[0,aK,a(c[au][1],aN)];case
16:var
aO=d[1],Q=f(e,i,l,d[2]),aP=Q[1];return[0,aP,a(G[19],[0,aO,Q[2]])]}var
B=a(G[70],n),p=B[2],q=B[1],X=a(c[9],q),v=b(c[3],x,X);if(10===v[0])var
R=a(j[17][8],v[1][1]),S=a(j[6][6],R),C=b(j[1][10][3],S,V);else
var
C=0;if(C){if(W)var
Y=a(c[9],n),Z=g(c[h][3],y,s+e|0,Y),D=a(c[au][1],Z);else
var
D=n;return[0,l,D]}var
E=lo(U,x,w,q,a(aY[11],p));if(E){var
r=E[1],t=r[5],o=r[4],_=t[3],$=t[2],aa=t[1],ab=r[3],ac=r[1],ad=function(g,d,j){var
a=ab;for(;;){if(a){var
c=a[1],h=a[2];if(mD(g,c))var
b=1;else{if(!mE(g,c)){var
a=h;continue}var
b=0}}else
var
b=0;return b?d:f(e,i,d,j)[1]}},ae=g(bd[48],ad,l,p),af=[0,q,a(aY[12],aa)],ag=a(G[15],af),F=b(A[15],ag,o),ah=g(k[10][14],G[1],0,o),ai=a(m[1],o),aj=b(G[89],ai,F),ak=[0,b(bb[13],aj,ah)],al=a(aY[12],$),am=(((ac+1|0)+s|0)+e|0)+a(m[1],o)|0,an=[0,a(G[1],am),al],ao=[0,a(G[15],an),ak],ap=a(G[15],ao),aq=b(bb[23],ap,o),T=he(b(aZ[6],aq,z[1]),ae);z[1]++;return[0,T,a(bb[12],[0,F,_])]}function
ar(b,a){return f(e,i,b,a)[1]}var
as=g(aY[17],ar,l,p);return[0,as,a(G[15],[0,q,p])]}var
K=a(c[au][1],I),n=f(0,0,aZ[1],K),o=n[2],p=n[1];function
q(b,d){var
c=a(G[46],b);return c?c:a(G[45],b)}var
d=b(aZ[17],q,p),r=d[2],t=d[1];function
u(d,e,c){var
f=a(bb[36],d),h=f[2],i=a(m[1],f[1]);if(g(aB[4],1,i,h)){var
j=b(G[89],-i|0,h);return b(aZ[3],j,c)?c:g(aZ[4],d,e,c)}return g(aZ[4],d,e,c)}var
v=g(aZ[13],u,t,r),B=a(aZ[19],v);function
C(b,a){return am.caml_int_compare(b[2],a[2])}var
D=b(m[48],C,B);function
E(d,f){var
e=d[1],g=d[2],i=a(c[9],f[1]),l=b(c[h][1],e,i),m=a(j[1][6],DC);return[0,e+1|0,[0,[0,a(k[8],m),l],g]]}var
e=g(m[20],E,DB,D),i=e[1],F=e[2],H=a(c[9],o);return[0,F,i,b(c[h][1],i,H)]}function
lp(d,h,j,e){function
k(f,e,b){var
d=0<b.length-1?g(aY[7],b,0,b.length-1-1|0):b;return a(c[23],[0,h,d])}function
f(e,a){var
h=b(c[3],d,a);switch(h[0]){case
1:if(g(c[aJ],d,j,a))return k(e,a,[0]);break;case
9:var
i=h[1],m=h[2];if(g(c[aJ],d,j,i)){var
n=function(a){return a+1|0},p=o(c[dg],d,n,f,e);return k(e,i,b(aY[15],p,m))}break}function
l(a){return a+1|0}return y(c[dg],d,l,f,e,a)}return f(0,e)}function
DG(d,c,b,a){return gO(function(a){return lp(d,c,b,a)},a)}function
lq(e,q,d){function
f(r){var
i=r;for(;;){var
d=b(c[3],e,i);switch(d[0]){case
6:var
k=d[3],m=d[2],s=d[1],o=b(c[99],e,m)[2],l=b(c[91],e,o)[1];if(b(c[53],e,l))var
p=b(c[84],e,l)[1][1],n=b(j[23][12],p,q);else
var
n=0;if(n){var
t=a(c[10],1);if(g(A[38],e,t,k))throw[0,I,DH];var
i=b(c[h][5],c[16],k);continue}var
u=[0,s,m,f(k)];return a(c[20],u);case
8:var
v=d[3],w=d[2],x=d[1],y=[0,x,w,v,f(d[4])];return a(c[22],y);default:return i}}}return b(cy,f,d)}function
lr(q,e,ad,ac,ab,S,w,p,R,v,Q,P){var
x=b(c[99],e[1],P),y=x[2],z=x[1];function
T(a){return lg(a[2][8][1])}var
V=b(m[35],T,p),B=a(m[1],V);if(1===B)var
X=a(m[1],v)+2|0,s=b(D[bI],X,z);else
var
s=z;if(1===B)var
Y=b(c[h][4],[0,c[16],[0,Q,0]],y),t=b(c[44],Y,v);else
var
L=function(i,g,f){var
d=b(c[99],e[1],i),j=d[2],k=b(D[bI],2,d[1]),l=[0,f,U(0,g)],m=[0,a(c[23],l),0],n=b(c[h][4],[0,c[16],m],j);return b(c[44],n,k)},O=function(m,l){var
f=m,d=l;for(;;){var
g=b(c[3],e[1],f);if(d){var
i=d[1][2][8][1];if(typeof
i==="number")if(0!==i){var
d=d[2];continue}if(9===g[0]){var
h=g[2];if(2===h.length-1){var
k=d[1][2],o=g[1],p=h[1],q=k[4],r=k[1][1],s=O(h[2],d[2]),t=[0,o,[0,L(p,q,r),s]];return a(c[23],t)}}var
j=d[1][2],n=d[2],f=L(f,j[4],j[1][1]),d=n;continue}return f}},t=O(y,p);var
u=lq(e[1],S,s);if(1===w){var
Z=b(c[44],t,u);return[0,a(m[1],u),Z]}var
ae=f3(e,3),_=a(m[1],s)-w|0,C=b(D[W],_,u),$=C[1],E=a(D[aJ],C[2]),aa=E[2],af=E[1];function
ah(af,D,C){var
f=C[2],r=f[7],E=f[6],F=f[5],s=f[4],G=f[3],ah=C[1];if(1===f[8][1]){var
ai=a(aG,D)[1],t=a(m[1],s),H=[0,ag([0,k[9],0,F]),s];if(r)var
J=r[1],u=(t-J[2][1]|0)+1|0,aj=J[1],ak=a(a$,b(m[7],s,(u-1|0)-1|0)),al=b(c[h][1],u,ak),am=a(c[10],u),i=[0,[0,u,al,b(c[h][1],1,aj),am]];else
var
i=0;var
an=ap(fX,e),K=function(f,d,m,l,i,g){var
n=b(c[h][1],1,g),p=a(c[10],1),q=b(c[h][1],1,d),r=o(A[51],e[1],q,p,n),s=a(j[1][6],DI),t=[0,a(k[8],s),f,r],u=[0,an,[0,f,a(c[21],t),d,m,l,i]];return a(c[23],u)};if(i)var
x=i[1],v=x[3],L=x[2],ao=x[4],l=1,aq=function(d,k){var
n=k[2],p=k[1],f=b(c[h][1],l,ao);function
q(i){var
a=b(c[h][1],2,d),g=b(c[h][1],l,v);return[0,[0,o(A[51],e[1],g,f,a),p],n]}var
r=b(c[3],e[1],d);if(0===r[0]){var
i=r[1],w=a(a$,b(m[7],s,i-1|0)),x=b(c[h][1],i,w),j=b(c[h][1],2,x);if(g(A[38],e[1],f,j)){if(b(c[51],e[1],v))var
t=b(c[h][1],2,d);else
var
E=b(c[h][1],2,d),F=a(c[10],1),G=b(c[h][1],l,v),t=K(b(c[h][1],l,L),f,G,F,E,j);if(b(c[51],e[1],v))var
u=b(c[h][1],4,d);else
var
y=b(c[h][1],2,j),z=b(c[h][1],4,d),B=a(c[10],1),C=a(c[10],2),D=b(c[h][1],2,f),u=K(b(c[h][1],3,L),D,C,B,z,y);return[0,[0,t,p],[0,[0,i,u],n]]}return q(0)}return q(0)},O=g(m[21],aq,E,DJ),d=l,Q=O[1],P=O[2];else
var
bc=a(c[h][1],1),d=0,Q=b(m[17],bc,E),P=0;if(i){var
w=i[1],y=w[4],R=w[3],n=w[2],S=w[1],T=b(c[h][1],1,F),U=function(c,b,a){return o(A[51],e[1],c,b,a)},ar=a(c[10],S);if(g(A[38],e[1],ar,T)){var
V=a(c[10],2),as=b(c[h][1],3,T),at=b(c[h][1],2,y),au=a(c[10],1),av=b0(q,e,b(c[h][1],2,n),au,at),aw=a(c[10],2),ax=U(a(c[10],S+3|0),aw,as),ay=function(d,b){var
e=b[2];return U(a(c[10],b[1]+4|0),e,d)},z=g(m[20],ay,ax,P);if(g(c[h][13],e[1],1,z))var
az=ap(fX,e),aA=a(c[10],1),aB=b(c[h][1],d,R),aC=b(c[h][1],d,y),aD=b(c[h][5],c[16],z),aE=b(c[h][1],d,n),aF=a(j[1][6],DK),aH=[0,a(k[8],aF),aE,aD],aI=a(c[21],aH),aJ=[0,az,[0,b(c[h][1],d,n),aI,aC,aB,aA,V]],W=a(c[23],aJ);else
var
a1=ap(h7,e),a2=a(c[10],1),a3=b(c[h][1],d,R),a4=a(j[1][6],DP),a5=[0,a(k[8],a4),av,z],a6=a(c[21],a5),a7=b(c[h][1],d,n),a8=a(j[1][6],DQ),a9=[0,a(k[8],a8),a7,a6],a_=a(c[21],a9),ba=b(c[h][1],d,y),bb=[0,a1,[0,b(c[h][1],d,n),ba,a_,V,a3,a2]],W=a(c[23],bb);var
X=W}else
var
X=a(c[10],2);var
Y=X}else
var
Y=a(c[10],1);if(G){var
aK=G[2],aL=1,Z=b(h3(function(b,a){return ka(a[2][3],aK)?[0,(ah+1|0)-b|0]:0}),aL,p);if(Z){var
aM=a(c[10],Z[1]),aN=b(c[h][1],(t+1|0)+d|0,aM),aO=b(c[41],aN,Q),aP=b(c[41],aO,[0,Y,0]),aQ=function(a){return b0(q,e,a[2],a[3],a[4])},_=b(M[16],aQ,i);if(r)var
aV=b(c[h][1],1,r[1][1]),aW=g(N[18],q,e[1],aV),B=eg(t+2|0,-(af-1|0)|0,hf(e[1],ad,DM,ac,t,ab,aW)[1]);else
var
B=0;var
aX=aT(d,B),aY=a(m[1],B),aZ=b(c[h][1],aY,aP),$=f9(q,e[1],aZ,aX);if(_)var
aR=_[1],aS=a(j[1][6],DL),aU=[0,a(k[8],aS),aR,$],aa=a(c[20],aU);else
var
aa=$;var
a0=b(c[45],aa,H);return ag([0,ai,[0,a0],b(c[44],ae,H)])}throw[0,I,DN]}throw[0,I,DO]}return D}var
ai=a(m[6],p),aj=a(m[9],ai),F=o(D[72],ah,1,aa,aj),i=R,f=a(m[9],$),n=0,l=0;for(;;){if(i){var
G=i[1],H=G[1];if(typeof
H==="number")if(1===H)if(f){var
ak=i[2],i=ak,f=dx(c[16],f[2]),n=n+1|0;continue}if(!G[4]){var
i=i[2];continue}if(f){var
i=i[2],al=[0,f[1],l],f=f[2],l=al;continue}var
r=bB(0,a(d[3],DR))}else
if(f)var
am=a(m[9],f),r=[0,n,b(J[26],am,l)];else
var
r=[0,n,l];var
K=r[2],an=r[1],ao=b(J[26],F,[0,af,0]),aq=b(J[26],K,ao),ar=b(c[h][1],-an|0,t),as=b(c[44],ar,aq),at=function(b){var
c=a(gb,b);return a(M[3],c)},au=b(m[35],at,F),av=a(m[1],au);return[0,(a(m[1],K)+av|0)+1|0,as]}}function
DS(e,a){function
d(f,a){var
d=a[1],g=a[2];return[0,d+1|0,[0,b(bj,b(c[h][10],d,e),f),g]]}return g(m[21],d,a,DT)}function
DU(f,e,i,c){var
k=c[7],h=b(ax[25],i,f),l=ce(f,e,0,c[1][4]),m=a(d[5],0),n=aI(f,e,c[1][2]),o=a(d[5],0),p=a(d[3],DV),q=g(z[11],h,e,k),r=a(d[3],DW),s=bE(c),t=a(j[1][9],s),u=a(d[3],DX),v=a(d[5],0),w=aU(c),x=g(z[11],h,e,w),y=b(d[12],x,v),A=b(d[12],y,u),B=b(d[12],A,t),C=b(d[12],B,r),D=b(d[12],C,q),E=b(d[12],D,p),F=b(d[12],E,o),G=b(d[12],F,n),H=b(d[12],G,m);return b(d[12],H,l)}function
DY(a){function
c(a){return aU(a)}return b(m[17],c,a)}function
hg(c,a){return b(A[69],c,a)[2]}function
ls(e,d){var
f=[0,[0,DZ,[1,b(c[82],e,d)[1]]],0];return F(a(s[69],f))}function
hh(o,f,e,n){if(f){var
g=f[1],d=b(c[99],o,n)[1],p=a(m[1],d),i=b(A[8],0,p);if(-1===g)var
k=a(D[fJ],i),j=0;else
var
l=b(D[W],g-1|0,i),u=l[1],k=u,j=a(m[6],l[2]);var
q=b(J[26],k,j),r=a(m[1],d),s=b(c[h][1],r,e),t=b(c[41],s,q);return b(c[45],t,d)}return e}function
lt(r,e,d){function
i(s,d){var
e=s;for(;;){var
j=d[3],t=d[2],u=d[1];if(e){var
k=e[2],l=e[1],n=l[2],w=n[2],x=n[1],y=l[1];try{var
o=b(A[6],y,j),f=o[1],p=hh(r,x,w,b(c[h][1],f,o[3])),z=dy(f,p,j),q=b(D[W],f-1|0,t),B=q[1],C=a(m[6],q[2]),E=function(f,i){return function(a){var
b=a[2],d=b[1],e=a[1];return[0,e,[0,d,g(c[h][3],[0,i,0],f,b[2])]]}}(f,p),F=b(m[17],E,k),G=i(F,[0,u,b(m[11],B,C),z]);return G}catch(a){a=v(a);if(a===O){var
e=k;continue}throw a}}return d}}return i(e,_(d))}function
lu(d,a,j,i,e){var
k=_(e[1]);function
l(f,g){var
i=g[2],j=f[1],m=i[2],n=i[1],o=g[1];try{var
k=b(A[6],o,j),l=k[1],p=b(c[h][1],l,k[3]),q=ao(0,d,[0,a],c0(0,d,a,l,[2,hh(a,n,R(a,e,m),p)],j),f);return q}catch(a){a=v(a);if(a===O)return f;throw a}}var
f=g(m[20],l,k,i);return[0,f,ao(0,d,[0,a],ao(0,d,[0,a],f,e),j)]}function
lv(E,i){var
q=[0,0],e=a(w[2],0),x=a(l[17],e),n=a1(c[d5],0,0,0,e,x,i),r=n[2],p=n[1],A=y(T[2],0,0,e,p,r);function
k(i,f,l,F){var
e=b(c[3],f,F);switch(e[0]){case
6:var
s=e[3],n=e[2],o=e[1];try{var
u=o[1];if(u){var
L=u[1],M=function(c){var
d=a(j[17][8],c),e=a(j[6][6],d);return b(j[1][1],e,L)},N=b(m[33],M,E),w=b(c[99],f,n)[1],P=a(m[6],w),x=a1(c[d5],0,0,0,i,f,[1,N]),y=x[1],Q=x[2],R=[0,Q,U(1,P)],S=a(c[23],R),p=b(c[45],S,w);aM(function(f){var
c=g(z[11],i,y,p),e=a(d[3],D0);return b(d[12],e,c)});q[1]=1;var
T=k(i,y,[0,p,l],b(c[h][5],p,s));return T}throw O}catch(d){d=v(d);if(d===O){var
H=a(c[h][1],1),I=b(m[17],H,l),J=[0,a(c[10],1),I],t=k(b(c[aP],[0,o,n],i),f,J,s),K=t[1];return[0,K,a(c[21],[0,o,n,t[2]])]}throw d}case
8:var
A=e[3],B=e[2],C=e[1],V=e[4],W=a(c[h][1],1),X=b(m[17],W,l),D=k(b(c[aP],[1,C,B,A],i),f,X,V),Y=D[1];return[0,Y,a(c[22],[0,C,B,A,D[2]])];default:var
G=[0,r,a(bd[70],l)];return[0,f,a(c[23],G)]}}var
s=k(e,p,0,A),f=s[2],t=s[1];if(q[1]){aM(function(i){var
c=g(z[11],e,t,f),h=a(d[3],D1);return b(d[12],h,c)});var
B=o(ae[2],0,e,t,f)[1],u=a(l[bJ],B),C=a(l[nG],u);return[1,b(P[30],u,f),C]}return[0,i]}function
hi(d,c,a){function
e(a){var
b=a[2],e=b[1],f=a[1];return[0,f,[0,e,R(d,c,b[2])]]}return b(m[17],e,a)}function
lw(n,f,e){var
w=[0,a9[1]],d=[0,f];function
r(b,a){return lt(d[1],b,a)}function
l(c,b,a){return lu(n,d[1],c,b,a)}function
F(p,e,o,i,f){function
q(d,f){var
e=d[1][7];if(e){var
g=0===e[1][0]?0:D4,i=a(m[1],d[2][1])-o|0,j=[0,g,b(c[h][1],i,f)];return[0,[0,d[1][2],j]]}return 0}var
s=g(m[23],q,i,f),u=a(m[9],s);function
v(a){return a}var
j=b(D[65],v,u);function
w(d){var
e=d[2],f=e[2],g=e[1],i=d[1],k=a(m[1],j);return[0,i,[0,g,b(c[h][1],k,f)]]}var
x=b(m[17],w,e),k=b(J[26],j,x);function
y(b,j){var
c=b[3],m=c?c[1][1]:b[2],a=b[1],f=r(e,a[5]),g=l(f,e,_(a[5]))[1],o=a[9],q=a[8],s=R(d[1],g,a[6]),h=[0,a[1],a[2],a[3],a[4],g[1],s,0,q,o],u=[0,h,b[2],b[3],b[4],b[5]],v=[0,b[1][2],p],w=r(k,m[1]),i=t(w,k,u,j,v,b[4]),x=bF(n,d,a[4],i)[1];return[0,h,_(f[3]),0,i,x]}return g(m[23],y,i,f)}function
t(p,e,u,y,x,f){switch(f[0]){case
0:var
G=f[2],s=f[1],H=s[1],al=f[4],am=f[3],L=l(p,e,s),z=L[2],O=L[1],an=hi(d[1],s,e),P=e5(G),ah=s[3],ai=s[2],aj=s[1],ak=bD(a(m[1],P),ai),Q=l(p,e,[0,b(J[26],P,aj),ak,ah])[1],ao=function(b){return a(M[2],b[2][1])},ap=b(m[28],ao,e),aq=function(f,v){var
y=v[1],p=f[4],A=f[3],i=f[1],M=v[2],N=f[7],P=f[5],B=e5(y),Q=r(e,O[3]),q=d[1],J=[0,O,Q];function
L(c,f){var
e=f[2],d=f[1],g=d[3],h=d[2],i=d[1],j=b(bj,function(a){return R(q,e,a)},c),l=a(k[10][1][4],c),o=gD(n,q,e,[0,[0,a(k[10][1][1],c),l],0]),p=[0,j,g],r=1;function
s(a){return cC(r,a)}return[0,[0,[0,c,i],[0,D3,b(m[17],s,h)],p],o]}var
o=bl(0,n,q,g(m[21],L,B,J)[1]),S=a(m[1],H),T=a(m[1],B)+S|0,U=R(d[1],o,N);function
V(d){var
e=d[2],f=e[2],g=e[1],j=d[1],k=a(m[1],H),l=a(m[1],i[2][1])-k|0;return[0,j,[0,g,b(c[h][1],l,f)]]}var
W=b(m[17],V,an),s=F(x,W,T,[0,i,0],[0,aU(f),0]);if(s)if(!s[2]){var
l=s[1];if(ap)var
t=0;else{var
E=i[3];if(E)if(0===E[1][6][0])var
G=1,u=1;else
var
u=0;else
var
u=0;if(!u)var
G=0;if(G)var
t=0;else
var
ag=R(d[1],o,i[5]),ah=d[1],ai=function(a){return R(ah,o,a)},aj=b(m[17],ai,A),D=[0,l[1],l[2],l[3],l[4],ag],C=aj,t=1}if(!t){var
X=bu(0,p),Y=b(K[5],X,D6),Z=b(av[28],Y,j[1][10][1]),_=R(d[1],o,i[5]),$=d[1],aa=function(a){return R($,o,a)},ab=b(m[17],aa,A),ac=w[1],ad=l[4],ae=[0,b(c[41],_,ab),Z,ad];w[1]=g(a9[4],p,ae,ac);var
D=l,C=aF(0,z[1])}var
af=a(m[1],z[1]);return[0,[0,[0,D,i[1],C,p,P,af,U],y],[0,f,M]]}throw[0,I,D5]},ar=g(m[21],aq,G,D7)[1],as=km(d[1],Q,al),at=function(a){return a},au=gV(b(N[18],n,d[1]),at,as);return[0,z,ar,R(d[1],Q,am),au];case
1:var
aw=f[4],ax=f[3],ay=f[2],S=l(p,e,f[1]),T=S[1],az=S[2],aA=a(c[10],ay),aB=R(d[1],T,aA),aC=b(c[73],d[1],aB),aD=function(a){return t(p,e,u,y,x,a)},aE=a(M[16],aD),aG=b(aY[15],aE,aw);return[1,az,aC,R(d[1],T,ax),aG];case
2:var
aH=f[2],aI=l(p,e,f[1])[2];return[2,aI,t(p,e,u,y,x,aH)];default:var
i=f[2],A=f[1],U=i[8],V=i[7],X=i[6],B=i[3],C=i[1],aJ=f[3],aK=i[10],aL=i[5],aM=i[2],aN=C[3],aO=C[2],aP=C[1],v=hi(d[1],A,e),E=hi(d[1],i[9],v),Y=l(p,e,A),q=Y[1],aQ=Y[2],aR=l(r(e,V[3]),v,V)[2],Z=r(E,U[3]),_=l(Z,E,U),$=_[2],aS=_[1],aT=i[9],aV=l(r(v,i[9][3]),v,aT)[2],aW=function(b){return a(M[2],b[2][1])},aX=b(m[28],aW,e),aa=i[4],ab=t(Z,E,u,y,aa,aJ);if(aX)var
ac=[0,D8],aZ=0,a0=0,a1=function(k,g,f){if(k===B[2]){var
i=a(m[1],g),j=$[1],h=function(a,b){return 0===b?0:a?0===a[1][0]?h(a[2],b-1|0)+1|0:h(a[2],b)+1|0:0};ac[1]=[0,h(a(m[9],j),i),i]}if(b(c[51],d[1],f)){var
l=b(c[73],d[1],f)-1|0,n=a(bA,b(m[7],A[1],l)),o=a(K[13][16],n);return b(m[42],o,e)?g:[0,R(d[1],q,f),g]}return[0,R(d[1],q,f),g]},a2=o(D[85],a1,a0,aZ,X),a3=bF(n,d,u[1][4],ab)[1],a4=ac[1],a5=b(N[18],n,d[1]),a6=b(m[17],a5,a2),af=a3,ae=a(m[9],a6),ad=a4;else
var
ba=d[1],bb=function(a){return R(ba,q,a)},bc=b(m[17],bb,X),bd=a(m[1],e),ag=b(D[W],bd,bc),be=ag[2],bf=ag[1],bg=R(d[1],q,aL),bh=a(m[1],e),bi=B[2]-bh|0,bk=a(m[1],e),bm=[0,B[1]-bk|0,bi],af=b(c[41],bg,bf),ae=be,ad=bm;var
a7=R(d[1],q,aO),a8=g(N[18],n,d[1],a7),a_=R(d[1],aS,aK),a$=R(d[1],q,aM);return[3,aQ,[0,[0,aP,a8,R(d[1],q,aN)],a$,ad,aa,af,ae,aR,$,aV,a_],ab]}}function
i(a){return a[5]}var
p=F(0,0,0,e,b(m[17],i,e));return[0,w[1],p]}function
lx(f,d,i,l,e){function
n(a){return a[1]}var
o=b(m[17],n,e),j=lw(f,d[1],o),k=j[2],h=j[1];if(a(a9[2],h))if(!go(l)){var
q=function(b,c){var
a=b[1],d=b[2],e=_(e4(a));return[0,[0,a[1],a[2],a[3],c[4],a[5]],0,d,[0,a[1][2],h,a[5],e]]};return g(m[23],q,e,k)}function
p(g,o){var
j=g[1],a=j[1],k=a[2],l=a[5],p=g[2],q=a[6],m=_(l),r=b(K[5],k,D9),n=kl(f,d,D$,0,i,D_,c7(f,d,i,[0,a[1],r,a[3],a[4],l,q,a[7],a[8],a[9]],m,o[4],0))[1],e=n[1],s=n[2],t=[0,k,h,e[5],m];return[0,j,[0,[0,e,[0,b(c[82],d[1],e[5])[1],s]]],p,t]}return g(m[23],p,e,k)}function
ly(a,j,i,d){function
f(e,d){var
h=b(c[3],a,d);switch(h[0]){case
1:if(g(c[aJ],a,j,d))return g(i,e,d,[0]);break;case
9:var
k=h[1],m=h[2];if(g(c[aJ],a,j,k)){var
n=function(a){return a+1|0},p=o(c[dg],a,n,f,e);return g(i,e,k,b(aY[15],p,m))}break}function
l(a){return a+1|0}return y(c[dg],a,l,f,e,d)}return f(0,d)}function
lz(a){return[0,[0,a[1],0],a[2],a[3]]}function
lA(l,j,e){var
f=e[3];function
i(f,e){var
g=e[3],i=e[2],d=e[1],j=a(k[10][1][3],f);if(j){var
l=b(c[h][4],d,j[1]),n=1,o=function(a){return cC(n,a)};return[0,[0,l,d],b(m[17],o,i),g]}var
p=a(c[h][4],d),q=[0,b(k[10][1][16],p,f),g],r=1;function
s(a){return cC(r,a)}var
t=[0,Eb,b(m[17],s,i)],u=a(c[h][1],1),v=b(m[17],u,d);return[0,[0,a(c[10],1),v],t,q]}var
d=g(m[21],i,f,Ea),n=d[1];return[0,ao(0,l,[0,j],e,[0,f,d[2],d[3]]),n]}function
fr(a){var
c=eG(a);return b(m[19],b8,c)}function
lB(l,e,k,j,i,f){var
r=f[2],n=f[4],p=f[3];function
o(j,n,l,p,k,t,B){var
i=B;for(;;)switch(i[0]){case
0:var
C=i[4],D=i[3],E=i[2],F=i[1],G=function(d,n){var
o=n[1],B=n[2],C=aU(d),g=b(c[h][4],o,C),p=b(c[91],e,g),q=p[1],D=p[2];try{var
m=b(a9[23],d[4],r),L=m[3],M=m[2],x=b4(e,m[1]),z=x[1],N=x[2],A=lk(e,hg(e,aU(d)),N),P=[0,[0,[0,z,A],q],k],Q=[0,[0,[0,z,A],M,L]],u=Q,t=P}catch(a){a=v(a);if(a!==O)throw a;var
u=0,t=k}var
E=y(T[2],0,0,j,e,q);function
i(p,j,d){var
f=b(c[3],e,p);if(6===f[0])if(d){var
k=d[2],l=d[1],m=f[3],q=f[2],r=f[1];if(b(c[51],e,l)){var
n=i(m,j+1|0,k),s=[0,j,n[2]];return[0,a(c[21],[0,r,q,n[1]]),s]}var
o=i(b(c[h][5],l,m),j+1|0,k);return[0,o[1],o[2]]}if(d)throw[0,I,Ec];return[0,g,0]}var
w=i(E,0,D),f=w[1],F=w[2],l=lA(j,e,_(d[1][1][5]))[1],G=s(j,l,f,0,t,Ed,d[1]),H=d[1][1][6],J=a(a9[2],r)?[0,f,F]:[0,f,Ee],K=fr(l);return[0,[0,g,o],[0,[0,J,u,d[5],l[1],H,K,0,G],B]]},u=g(m[21],G,E,Ef),q=u[1],H=u[2],w=ao(0,j,[0,e],F,n);if(X[1]){var
K=b(z[11],j,e),M=g(d[39],d[13],K,q),P=a(d[3],Eg),Q=b(d[12],P,M);b(L[9],0,Q)}var
S=function(a){return a},U=gV(function(l){var
f=b(c[h][4],q,l),i=g(N[18],j,e,f);function
d(d,i){var
b=d[1],f=d[2],g=b[2],h=b[1];return ly(e,h,function(e,d,b){if(0===e){var
h=[0,f,fq(g,a(aY[11],b))];return a(c[40],h)}return a(c[23],[0,d,b])},i)}return g(m[21],d,k,i)},S,C),V=fr(w),W=b(c[h][4],q,D);return[0,[0,w[1],l,p,V,W,l,[0,2,t[2]],U,[0,H]],0];case
1:var
Y=i[4],Z=0,$=function(c,a){if(a){var
d=o(j,n,l,p,k,t,a[1]);return b(J[26],c,d)}return c};return g(aY[17],$,Z,Y);case
2:var
aa=i[2];ao(0,j,[0,e],n,i[1]);var
i=aa;continue;default:var
f=i[2],x=i[1],ab=i[3],ac=f[1][2],A=ao(0,j,[0,e],x,n),ad=fr(A),ae=fr(ao(0,j,[0,e],f[9],A)),af=[0,hg(e,f[5]).length-1,0],ag=o(j,f[8],f[5],0,k,Eh,ab),ah=f[3],ai=[0,[0,R(e,f[9],ac),ah]],aj=[0,[0,[0,[0,f[5],af],0,f[4],f[8][1],f[10],ae,ai,ag],0]],ak=[0,b(c[41],f[5],f[6])];return[0,[0,x[1],l,p,ad,f[2],l,Ei,ak,aj],0]}}function
s(g,f,e,d,c,b,a){return o(g,f,e,d,c,[0,b[1],0],a[4])}return s(l,n,p,k,0,j,i)}function
Ej(b,d){switch(b[0]){case
0:return a(c[11],b[1]);case
1:return a(c[25],[0,b[1],d]);case
2:return a(c[28],[0,b[1],d]);default:return a(c[30],[0,b[1],d])}}function
Ep(p,k,H,e,O,am,u,q,al,N,ak,aj,t,aC,G,aB,aA){var
x=c8(p[1]),r=a(j[1][6],p[1][3]),f=[0,0],Q=b(K[5],r,Eq);function
h(q){var
d=q[2],g=d[8][1],k=d[4],h=d[3],l=d[2],r=d[1][1];if(typeof
g==="number")if(0===g)var
i=0;else
var
n=0,i=1;else
var
i=0;if(!i)var
n=1;if(n){var
s=l?l[1][1][1]:r,o=aF(0,k),t=a(c[40],[0,s,o]),v=bu(0,h),w=bh(e,fV(b(K[5],v,Er))),x=[0,w,b(J[26],o,[0,t,0])],y=a(c[40],x),p=b2(H,e[1],y,k),z=function(a){var
c=a[1],d=bu(0,h);return b(j[1][1],c[1][2],d)},A=b(m[33],z,u)[1],B=typeof
g==="number"?0:1;if(B){var
C=f[1];f[1]=[0,[0,bu(0,h),p,A],C]}return[0,p]}return 0}if(q){var
R=q[1];if(q[2])var
B=function(f){var
b=f;for(;;){var
c=a(D[aJ],b),d=c[2],e=h(c[1]);if(e)return[0,e[1],d];var
b=d;continue}}(q),S=B[2],U=B[1],V=function(g,b){var
d=h(g);if(d){var
i=d[1],f=[0,ap(ed,e),[0,i,b]];return a(c[23],f)}return b},s=g(m[21],V,S,U);else
var
ax=h(R),s=a(M[7],ax);var
W=a(m[1],N),X=b(A[8],0,W),C=k?k[1][1][1]:G,an=a(c[40],[0,C,X]),Y=function(ao,aS,aR,A){var
i=a(w[2],0);g(aK[22],0,[0,p[1][3],0],[1,[0,[0,0,x,[0,A]],0]]);try{var
h=p[1],o=a(j[1][6],h[3]),B=a(m[1],ak),R=a(w[2],0),S=b(jV[26],R,t)[1],U=a(w[2],0);e[1]=a(l[17],U);if(c8(h)){e[1]=b(l[fC],e[1],h[2]);e[1]=b(l[fC],e[1],ao);var
C=b(P[9],e[1],t),D=C[2],E=C[1],V=y(T[2],0,0,i,E,D);e[1]=E;var
G=D,F=V}else
var
ai=Ej(t,c[2][3]),G=ai,F=a(c[9],S);var
H=lr(i,e,h[7],O,am,aj,B,q,al,N,an,F),s=H[2],W=H[1],X=function(z,x,v,m){var
c=a(w[2],0),n=a(l[17],c),p=b(ay[32],0,o),e=a_(n,a(az[13],p)),f=e[2],g=a_(e[1],m),i=g[2],j=is(g[1]),q=j[2],k=fW(j[1],W),d=k[1],r=[0,k[2],[0,i,0]],s=[0,f,[0,y(T[2],0,0,c,d,i),r]],t=[0,y(T[2],0,0,c,d,f),s],u=b(K[6],Ek,o);di(u,c8(h),d,0,q,t);return 0},Y=le(G,B,a(m[1],u),h,A);try{aM(function(k){var
c=g(z[11],i,e[1],s),f=a(d[5],0),h=a(d[3],En),j=b(d[12],h,f);return b(d[12],j,c)});cP(a(w[2],0),e,s);aM(function(b){return a(d[3],Eo)})}catch(f){f=v(f);if(f[1]!==cH[1])throw f;var
Z=f[2],_=[17,b(cH[25],c[9],f[3])],aa=g(bP[2],Z,e[1],_),ab=a(d[3],El),ac=b(d[12],ab,aa);g($[6],0,0,ac)}var
ad=[0,a(bW[1],X)],ae=[0,h[4]],af=a(l[bH],e[1]),ag=g(c[5],0,e[1],s),ah=b(K[5],o,Em);cg(be[7],ah,0,ag,af,0,0,ae,[0,Y],0,ad,0,[0])}catch(f){f=v(f);if(f[1]===cH[1]){var
ap=f[2],aq=[17,b(cH[25],c[9],f[3])],ar=g(bP[2],ap,e[1],aq),as=a(d[3],Es),at=b(d[12],as,ar);g($[6],0,0,at)}else
if(f[1]===cT[1]){var
aH=g(bP[2],f[2],f[3],f[4]),aI=a(d[3],Eu),aJ=b(d[12],aI,aH);g($[6],0,0,aJ)}else{var
aL=b($[14],0,f),aN=a(d[5],0),aO=a(d[3],Ev),aP=b(d[12],aO,aN),aQ=b(d[12],aP,aL);b(L[8],0,aQ)}}var
au=a(l[17],i),av=b(ay[32],0,r),I=a_(au,a(az[13],av)),n=I[2],J=a_(I[1],A),M=J[2],Q=ir(J[1]),f=Q[1],aw=Q[2],ax=[0,n,[0,y(T[2],0,0,i,f,M),[0,M,0]]],aA=[0,y(T[2],0,0,i,f,n),ax];di(b(K[6],Et,r),x,f,0,aw,aA);if(d8[1]){var
aB=dV[3],aC=[0,b(c[82],f,n)[1]];b(w[55],aC,aB);if(k){var
aD=dV[3],aE=[0,b(c[82],f,k[1][1][1])[1]];return b(w[55],aE,aD)}return 0}var
aF=a(lj,b(c[82],f,n)[1]);b(gq[8],0,aF);if(k){var
aG=a(lj,b(c[82],f,k[1][1][1])[1]);return b(gq[8],0,aG)}return 0},Z=e[1],_=a(w[2],0);e[1]=o(ae[2],0,_,Z,s)[1];var
aa=g(c[5],0,e[1],s),ab=g(c[5],0,e[1],C);if(x)var
E=e[1];else
var
aw=a(w[2],0),E=a(l[17],aw);var
ac=a(l[bH],E),F=function(b){var
c=[0,a(bW[1],Y)],d=[0,a(n[65][24],b)];cg(be[7],Q,0,aa,ac,0,0,[0,p[1][4]],d,0,c,0,[0]);return 0},ad=lb(O,ab,p,r,f[1],u);try{var
av=F(ad);return av}catch(f){f=v(f);if(f[1]===cH[1]){var
af=f[2],ag=[17,b(cH[25],c[9],f[3])],ah=g(bP[2],af,e[1],ag),ai=a(d[3],Ew),ao=b(d[12],ai,ah);return g($[6],0,0,ao)}var
aq=b($[14],0,f),ar=a(d[5],0),as=a(d[3],Ex),at=b(d[12],as,ar),au=b(d[12],at,aq);b(L[8],0,au);return F(a(i[16],0))}}throw[0,I,Ey]}function
lC(i,h,d,a){function
c(a){var
e=a[4],f=a[1],c=b(M[23],f,a[2]);return[0,f,e,lB(i,h,d,[0,lf(c[1]),0],c,e)]}var
f=b(m[17],c,a);function
e(a){function
c(a,g){var
c=a[9],d=a[7],q=g[2],r=g[1],h=a[8],i=a[6],j=a[5],k=a[4],l=a[3],m=a[2],n=a[1];if(c)var
o=c[1],p=function(a){var
c=a[7],f=a[6],g=a[5],h=a[4],i=a[3],j=a[2],k=a[1],b=e(a[8]);return[0,[0,[0,k,j,i,h,g,f,c,d],b[1]],b[2]]},f=b(D[76],p,o);else
var
f=0;return[0,[0,[0,n,m,l,k,j,i,d,h],r],b(J[26],f,q)]}return g(m[21],c,a,Ez)}function
j(c,h){var
f=c[2],i=c[1],g=e(c[3]),a=i[1],j=g[2],k=g[1],l=[0,lf(a),0],n=b(m[19],b8,f[4][2]),o=[0,[0,[0,f[3],0],d,[0,a[2],0],a[5],a[6],n,0,l],k];return[0,o,b(J[26],j,h)]}return g(m[21],j,f,0)}function
EA(f){var
d=a(i[68][5],f),o=a(i[68][2],f),g=b(c[3],d,o);if(9===g[0]){var
h=g[2];if(3===h.length-1){var
e=b(c[3],d,h[2]);if(9===e[0]){var
p=e[2],j=b(c[3],d,e[1]);if(14===j[0]){var
k=j[1][1],l=k[2],m=Y(k[1],l)[l+1],q=Y(p,m)[m+1],n=b(c[3],d,q);return 1===n[0]?f8(n[1]):a(i[16],0)}return a(i[16],0)}return a(i[16],0)}}return a(i[16],0)}var
EB=a(i[68][8],EA);function
hj(P,O,f,I,H,q){if(X[1]){var
aa=L[9],ad=function(c){var
e=c[2],h=c[1];if(e)var
i=ce(O,f,0,e[1][4]),j=a(d[3],EC),g=b(d[12],j,i);else
var
g=a(d[7],0);var
k=a(d[5],0),l=ce(O,f,0,h[4]),m=b(d[12],l,k);return b(d[12],m,g)},ai=g(d[39],d[5],ad,q),aj=a(d[3],ED);b(aa,0,b(d[12],aj,ai))}var
h=a(w[2],0),u=a(m[5],q),Q=u[4],R=u[3],S=u[1],ak=j[1][10][1];function
al(c,a){return b(j[1][10][7],a[3][2][7],c)}var
am=g(m[20],al,ak,q),B=Q[3],U=Q[2],p=R[2],an=e4(S),C=R[1],V=lC(h,f,I,q);function
ao(a){return a[1]}var
E=b(m[17],ao,V),W=a(m[1],E);function
ap(e){var
i=e[2],j=e[1][1];if(i){var
k=i[1][1][1];aM(function(o){var
c=g(z[11],h,f,k),e=a(d[3],EE),i=g(z[11],h,f,j),l=a(d[3],EF),m=b(d[12],l,i),n=b(d[12],m,e);return b(d[12],n,c)});var
l=b(c[91],f,k)[1];return[0,b(c[82],f,l)[1]]}aM(function(l){var
c=a(d[3],EG),e=g(z[11],h,f,j),i=a(d[3],EH),k=b(d[12],i,e);return b(d[12],k,c)});return 0}var
aq=b(D[65],ap,E);function
ar(i){var
c=i[3][2];function
e(e){aM(function(g){var
c=a(z[39],e),f=a(d[3],D2);return b(d[12],f,c)});var
f=lv(aq,e),g=c8(c);return[0,aK[4],g,1,0,f]}var
f=c[6];function
h(a){var
d=e([1,a]);try{var
f=[0,g$(c),0],h=g(aK[22],0,f,[0,[0,d,0]]);return h}catch(a){a=v(a);if(a[1]===$[5])return b(L[8],0,a[3]);throw a}}return b(m[15],h,f)}b(m[15],ar,q);var
as=1;function
at(i,a){var
d=a[2],e=a[1],j=a[5],k=a[4],l=e[2],h=b(A[60],f,e[1]),m=b(c[93],f,h)[2],n=b(c[91],f,m)[1],o=d?[0,d[1][1]]:0;return[0,n,[0,h,l],o,W-i|0,k,g(c[5],0,f,j)]}var
Z=g(D[71],at,as,E),e=[0,f],t=c8(p);function
au(aD,j){var
f=j[1],k=f[2],p=j[2],q=f[8],r=f[7],t=f[6],u=f[5],v=f[4],w=f[3],y=f[1];if(k)var
l=k[1][1],o=[0,l,0,w,v,u,t,r,q],Q=l[2];else
var
o=f,Q=y[2];function
C(f){var
j=f[8],t=f[7],u=f[5],v=f[4],w=f[3],l=f[2],k=f[1],R=t[2],S=t[1];if(w)var
y=w[1],T=y[2],U=y[1][1],V=c_[3],Y=function(a){return b(V,0,a)},_=b(ay[32],0,T),$=a(az[13],_),aa=a(n[65][61],$),D=U,C=b(i[17],aa,Y);else{if(g(c[aJ],e[1],l,B))var
aB=ah(ls(e[1],B)),aC=b(n[65][3],aB,EB),P=b(n[65][12],s[cp],aC);else
var
P=n[65][2];var
D=l,C=P}var
E=b(c[41],D,v),ab=e[1],ac=b(c[x],k,h),o=b(N[18],ac,ab);if(0===j[0])var
ad=a(o,j[1]),F=b0(h,e,u,a(o,E),ad);else
var
ax=[0,u,a(o,E)],aA=[0,iw(e),ax],F=a(c[23],aA);var
p=b(c[44],F,k);if(X[1]){var
af=g(z[11],h,e[1],p),ag=a(d[3],EI),ai=b(d[12],ag,af);b(L[9],0,ai)}aH(b(ae[2],0,h),e,p);if(0===j[0]){var
aj=j[1],G=a(m[1],k),ak=g(N[18],h,e[1],aj),q=hf(e[1],am,0,H,G,Z,ak),r=q[2],al=q[3],an=q[1],I=a(c[10],(G+(W-aD|0)|0)+r|0);if(R)var
K=I;else
var
av=b(A[60],e[1],l),aw=fq(Q,f_(r,b(c[91],e[1],av)[2])),K=b(c[41],I,aw);var
ao=f_(r,v),ap=b(J[26],ao,[0,al,0]),aq=b(c[41],K,ap),ar=f9(h,e[1],aq,an),M=iP(e[1],ar,k);if(X[1]){var
as=g(z[11],h,e[1],M),at=a(d[3],EJ),au=b(d[12],at,as);b(L[9],0,au)}var
O=[0,M]}else
var
O=0;return[0,S,C,p,O]}return[0,o,b(m[17],C,p)]}var
_=g(D[71],au,0,V),av=0;function
aw(b,a){var
c=a[2],d=a[1],e=1;function
f(b,a){return[0,b,a]}return[0,b,d,g(D[71],f,e,c)]}var
r=g(D[71],aw,av,_);function
ax(a){return a[2]}var
aA=b(m[17],ax,_),aB=a(m[13],aA),F=[0,a9[1]];function
aC(i,p){var
q=p[3],j=p[2],f=j[5],d=j[4],r=j[3],s=i[3],w=i[2],x=i[1],z=bu(0,r),l=b(K[5],z,EK);function
A(b){var
c=a(bA,b),d=a(K[13][16],c);return a(G[2],d)}var
B=b(m[19],A,d);F[1]=g(a9[4],r,[0,l,B],F[1]);function
C(a){var
d=a[2][4],f=b(c[5],0,e[1]);return b(M[16],f,d)}var
t=b(D[65],C,q);function
E(c){var
d=c[2],e=d[4],f=d[1],g=c[1];function
h(h){var
c=a(J[22],g),d=1===f?EL:EM,e=b(J[17],d,c);return b(K[5],l,e)}return b(M[16],h,e)}var
H=b(D[65],E,q);function
I(f,d){var
g=a(c[9],d),h=b(c[hO],e[1],g);return b(ab[2][7],h,f)}var
L=g(m[20],I,w,t),N=b(c[44],f,d);if(1===y(T[4],0,0,h,e[1],N))var
n=ab[5];else
var
U=[0,ag([0,k[9],0,f]),d],V=e[1],u=[0,h,s],v=function(e,d){var
f=d[1],g=d[2],h=a(a$,e),i=o(T[3],0,f,V,h),j=a(aE[17],i),k=b(ab[12],j,g);return[0,b(c[aP],e,f),k]},n=g(m[21],v,U,u)[2];var
O=a(aE[18],n),P=a(c[14],O),Q=a(c[20],[0,k[9],f,P]),R=b(c[44],Q,d),S=[0,l,g(c[5],0,e[1],R),0,H,t];return[0,[0,[0,S,d,f],x],L,b(ab[12],n,s)]}e[1]=a(l[bJ],e[1]);if(!t){var
aF=a(l[nG],e[1]);b(bM[14],0,aF);var
aG=a(w[2],0);e[1]=a(l[17],aG)}function
aD(d){var
f=d[3],h=d[2],G=h[2],i=h[3],az=d[1],L=cf(a(m[1],f),0),u=bu(0,i);function
v(f){var
d=f[2],M=f[1],aA=d[4],i=d[3],v=d[2],x=a(J[22],M),y=b(J[17],EW,x),z=b(K[5],u,y);function
A(aJ,aI,aH,N){if(0===aA)o(ac[35],0,0,1,N);else{var
aG=a(Dr,[0,p[3],N]);b(gq[8],0,aG)}var
O=M-1|0;Y(L,O)[O+1]=1;function
aD(a){return a}var
Q=b(bd[21],aD,L);if(Q){g(ac[26],[1,C],0,0);if(G){var
aF=[0,b(c[82],e[1],G[1][1][1])[1]];b(w[55],aF,1)}b(w[55],[0,C],1);var
R=P?(az+1|0)===a(m[1],r)?1:0:P;if(R){var
i=g(m[20],aC,[0,0,ab[2][1],ab[5]],r),V=i[3],W=i[1],X=b(l[na],e[1],i[2]),n=a(l[bJ],X),_=function(e){var
d=e[1],f=e[3],h=e[2],i=b(m[17],c[9],d[5]),j=b(c[5],0,n),l=b(m[17],j,i),o=d[4],p=d[3],q=a(aE[18],V),r=a(c[14],q),s=a(c[20],[0,k[9],f,r]),t=b(c[44],s,h),u=g(c[5],0,n,t);return[0,d[1],u,p,o,l]},d=b(m[19],_,W),s=b(l[d0],t,n);g(by[12],EO,EN,0);var
f=o(kM[2],0,[0,0,0,0,d,s,0,0],kL[3],0);g(by[12],EQ,EP,1);var
$=a(w[31],[0,f,0])[2][8],aa=b(D[39],aE[14],$),h=a(D[105],aa),v=a(ER[8],h);if(d)if(d[2])var
u=0;else{var
E=b(K[5],d[1][1],v),au=0,av=function(a,c){return[0,b(af[1],0,E),0,[0,f,a],h]},aw=g(D[71],av,au,d);b(hk[5],EV,aw);var
ax=b(ay[32],0,E),z=b(ea[3],0,ax),u=1}else
var
u=0;if(!u){var
ad=0,ae=function(c,a){var
d=b(K[5],a[1],ES);return[0,b(af[1],0,d),0,[0,f,c],h]},x=g(D[71],ae,ad,d);b(hk[5],ET,x);var
ag=b(J[17],EU,v),ah=a(j[1][6],p[3]),y=b(K[5],ah,ag),ai=function(b,a){var
c=b[1];return[0,c,lg(a[2][8][1])]},aj=g(m[23],ai,x,r),ak=function(a){var
b=a[1];return a[2]?[0,b]:0},al=b(D[65],ak,aj),am=b(af[1],0,y);b(hk[8],am,al);var
ao=b(ay[32],0,y),z=b(ea[3],0,ao)}if(0===s[0])var
A=a(c[27],[0,f,0]);else
var
as=a(ab[36][4],s[2]),at=[0,[0,f,0],a(c[2][1],as)],A=a(c[28],at);var
ap=function(b,a){var
c=a[5],d=1;function
e(a,c){return[0,aK[4],t,1,0,[0,[3,[0,[0,f,b],a]]]]}var
h=[0,g(D[71],e,d,c)];return g(aK[22],0,[0,p[3],0],h)};b(m[16],ap,d);var
aq=[0,p,F[1],U],ar=S[4];return Ep(aq,I,a(w[2],0),e,H,Z,q,r,aB,an,d,f,z,h,B,ar,A)}var
T=R}else
var
T=Q;return T}var
E=[0,s[cp],0];if(a(a9[2],U))var
h=n[65][2];else
var
X=ah(k2(b(J[17],p[3],EX))),h=a(n[65][24],X);var
N=[0,v,[0,iM([1,C]),[0,h,E]]],O=a(n[65][22],[0,s[29],N]);if(!t){var
W=a(w[2],0);e[1]=a(l[17],W)}var
Q=[0,a(bW[1],A)],R=[0,p[4]],T=a(l[bH],e[1]),V=g(c[5],0,e[1],i);cg(be[7],z,0,V,T,0,0,R,[0,O],0,Q,0,[0]);return 0}return b(m[15],v,f)}return b(m[15],aD,r)}aD(nI,[0,lh,Dk,lk,fq,ll,lA,lv,lo,hf,ly,lp,DG,lq,lr,DS,DU,DY,hg,ls,lt,hh,lu,lw,lx,hj,lC,lB,lz],"Principles");function
lD(a){var
c=a[5];function
d(a){return g(az[48],0,j[1][10][1],[1,a[1]])}var
e=b(f[17][68],d,c);return b(gG[88],1,e)}function
lE(n,y,as,E){var
q=a(w[2],0),h=[0,a(l[17],q)];if(n[1]){var
ap=a(f[17][5],E)[2][2][2];h[1]=b(l[fC],h[1],ap)}var
r=lx(q,h,n,y,E);if(r){var
s=r[1],F=s[2];if(F)if(!r[2]){var
t=s[4],p=s[3],G=F[1],k=G[1],m=s[1],i=G[2][2],H=b(j[1][10][7],p[2][7],i[7]),L=i[6],M=b(f[18],p[2][5],i[5]),e=[0,i[1],i[2],p[2][3],i[4],M,L,H];lD(e);var
z=i[1];if(1===z[0]){var
u=z[1];if(n[1])h[1]=a(l[18],i[2]);var
A=bh(h,i[1]),N=bV(k),B=b(K[5],N,EZ),P=function(X,W,V,U){b(w[55],[0,u],dV[3]);function
g(t,h){var
f=h[2];try{var
r=b(ay[32],0,f),s=a(az[15],r),g=s}catch(c){c=v(c);if(c!==O)throw c;var
i=a(j[1][9],f),k=a(d[3],E0),g=bB(0,b(d[12],k,i))}var
l=a(w[2],0),c=o(li[16],0,0,l,[1,g]),m=[0,b(af[1],0,[0,c,1,0]),0],n=b(J[17],e[3],E1);b(cG[1],n,m);var
p=[0,b(af[1],0,[0,c,0,0]),0],q=b(J[17],e[3],E2);return b(cG[1],q,p)}b(a9[11],g,t[2]);var
i=a(w[2],0);if(1-n[1])h[1]=a(l[17],i);var
c=k[1],r=k[5],s=k[4],x=k[3],z=k[2],C=c[9],D=c[8],E=c[7],F=c[6],G=c[5],H=c[4],I=c[3],K=bV(m),L=[0,[0,c[1],K,I,H,G,F,E,D,C],z,x,s,r],M=t[4],N=t[2],P=[0,bV(m),N,A,M],Q=e[7],R=b(f[18],e[6],p[2][6]),S=[0,[0,m,[0,L],[0,u,[0,e[1],e[2],e[3],e[4],e[5],R,Q]],P],0],T=[0,lz([0,m[5],B,m[4]])];return hj(n[4],q,h[1],T,y,S)};if(1-n[1]){var
Q=a(w[2],0);h[1]=a(l[17],Q)}var
x=e4(k),R=kc(k),S=[0,A,U(0,x)],T=a(c[23],S),V=U(0,x),W=a(c[23],[0,m[5],V]),X=b0(a(w[2],0),h,R,W,T),Y=b(c[44],X,x),Z=h[1],_=a(w[2],0),C=g(ae[6],_,Z,Y),D=C[1],$=C[2],aa=p[1],ab=t[2],ac=function(a){return ld(e,ab,aa,u,m,k,a)},ad=[0],ag=0,ai=[0,a(bW[1],P)],aj=[0,function(a){return a}],ak=[0,ah(ac)],al=[0,e[4]],am=[0,kb(m)],an=a(l[bH],D),ao=g(c[5],0,D,$);cg(be[7],B,0,ao,an,0,am,al,ak,aj,ai,ag,ad);return 0}throw[0,I,EY]}}function
aq(a){var
b=a[2],c=a[4],d=a[3],e=a[1],f=b?[0,b[1][1]]:0;return[0,e,f,d,c]}var
ar=b(f[17][68],aq,r);return hj(n[4],q,h[1],0,y,ar)}function
lF(p,G,n,F,g,e){function
s(a,c){try{var
d=b(f[17][31],a,F);return d}catch(a){a=v(a);if(a===O)return c;throw a}}var
x=s(1,d9[1]);if(x)var
z=x,y=s(0,d_[1]);else
var
z=0,y=0;var
i=a(w[2],0),d=[0,p,n,z,y],c=[0,a(l[17],i)];function
H(a){return g3(i,c,p,ez(a[1][1][2],[0,g,e]),n,e,a)}var
h=b(f[17][68],H,g),A=fe(0,h);kF(i,c[1],h);var
B=a(w[2],0),k=kG(B,c,0,h),J=k[3],K=k[1],C=b(P[36],c[1],k[2]),L=[0,A,C,d,G,K,e];function
N(a){return a[2]}var
D=kJ(B,c,L,h,b(f[17][68],N,g)),E=t(bz),Q=a(w[2],0),R=u===E?bz[1]:q===E?a(r[2],bz):bz,S=a(aS[8],R),T=a(f[17][5],D)[1][2],U=a(j[1][8],T),V=eZ[2],W=a(j[18][6],S),X=a(j[18][12],W);o(aK[17],0,U,[0,V[1],X],1);var
m=cf(a(f[17][1],g),0);return gU(Q,c,A,C,d,0,D,function(h,p,g){lD(g);var
i=g[1];if(1===i[0]){var
q=i[1];c[1]=a(l[18],g[2]);Y(m,h)[h+1]=[0,[0,p,[0,q,g]]];var
r=function(b){return 1-a(M[3],b)},j=b(bd[21],r,m);if(j){var
s=a(P[30],c[1]),t=b(f[17][68],s,J),u=function(b){return a(M[7],b)},k=b(f[19][56],u,m),v=function(a){return a[1][1]},x=fe(0,b(f[17][68],v,k)),y=a(w[2],0),z=a(dD[9],y);b(f[17][11],z,e);var
A=d[3],n=A||d[4];if(n)return lE(d,x,t,k);var
o=n}else
var
o=j;return o}throw[0,I,E3]})}function
hl(i,h,e,d,a,c){function
j(c){var
a=c[1][1],d=b(af[1],[0,a[1]],a[2]);return g(et[14],d,0,E4)}b(f[17][11],j,a);return lF(i,h,e,d,a,c)}function
lG(A,z,d){var
B=a(C[4],d);function
k(e,i){var
c=a(G[29],e);switch(c[0]){case
6:var
l=c[1][1];if(l){var
q=c[3],r=l[1],t=a(C[5],d),m=ec(j[1][10][1],r,t),u=a(G[2],m),g=k(b(aB[14],u,q),[0,m]),v=g[3],w=g[2],x=g[1],y=F(s[16]);return[0,b(n[5],y,x),w,v]}break;case
8:var
o=c[1][1];if(o){var
p=o[1],z=c[4],A=c[2],B=a(j[1][8],p);if(b(f[15][34],B,E5))return[0,n[1],i,e];var
D=a(C[5],d),E=[0,ec(j[1][10][1],p,D)],h=k(b(aB[14],A,z),E),H=h[3],I=h[2],J=h[1],K=F(s[16]);return[0,b(n[5],K,J),I,H]}break}return[0,n[1],i,e]}var
D=a(C[2],d),l=k(g(c[5],0,D,B),0),p=l[2],E=l[3],H=l[1];if(p)var
I=p[1],q=function(a){return F(b(s[82],a,[1,I]))};else
var
q=function(a){return n[1]};var
J=a(c[9],E),K=a(C[2],d),h=b(c[3],K,J);if(8===h[0]){var
v=h[1][1];if(v){var
Y=h[4],Z=h[2],_=v[1],$=a(C[2],d),i=b(c[3],$,Y);if(8===i[0]){var
x=i[1][1];if(x)var
aa=i[4],ab=i[2],ac=x[1],ad=a(C[2],d),ae=eb(g(c[5],0,ad,ab)),af=a(C[2],d),w=[0,_,ac,eb(g(c[5],0,af,Z)),ae,aa],o=1;else
var
o=0}else
var
o=0;if(!o)var
w=ba(E8);var
e=w,m=1}else
var
m=0}else
var
m=0;if(!m)var
e=ba(E6);var
L=e[5],M=e[4],N=e[3],O=e[2],P=e[1];function
r(g,f){if(0===g)return[0,0,f];var
j=a(C[2],d),e=b(c[3],j,f);if(8===e[0]){var
h=e[1][1];if(h){var
k=e[3],l=e[2],m=h[1],i=r(g-1|0,e[4]);return[0,[0,[0,m,l,k],i[1]],i[2]]}}return ba(E7)}var
t=r(M,L)[1],u=[0,P,[0,O,b(f[17][68],lh,t)]],Q=F(a(s[76],u)),R=F(a(s[25],u)),S=b(n[5],R,Q),T=F(s[16]),U=b(n[25],N+1|0,T);function
V(a){var
c=a[1],d=a[3],e=a[2],f=q(c),g=b(n[5],f,z),h=F(y(s[bY],0,[0,c],e,[0,d],cw));return b(n[5],h,g)}var
W=b(f[17][68],V,t),X=[0,H,[0,S,[0,U,[0,b(n[10],A,W),0]]]];return b(n[6],X,d)}aD(1250,[0,lF,lE,hl,lG,function(c,f,e,d){var
a=b(ax[98],c,e),h=g(eo,function(a,d){var
e=b3(d),h=g(A[99],c,f,d);return b(j[1][10][3],e,a)?b(j[1][10][7],h,a):a},a,d);return[0,a,b(j[1][10][9],h,a)]}],a3);function
hm(m,D,X,C,B,k,W,V){var
E=a(w[31],C[1]),Y=E[2],Z=E[1],_=b(c[2][2],D,C[2]),$=b(aB[25],_,Y[2]),aa=cX(D,b(f[17][68],c[bK],$)),F=am.caml_string_equal(k,E9)?Z[6]:a(f[17][1],aa),ab=aX(0,F),ad=b(K[6],E_,B),af=b(K[6],k,ad),ag=b(K[6],E$,af),ah=b(K[6],Fa,B),ai=b(K[6],k,ah),G=t(cS),aj=b(K[6],Fb,ai),ak=u===G?cS[1]:q===G?a(r[2],cS):cS,n=a(ac[8],ak),al=a(l[17],m),H=a1(l[fO],0,[0,l[cm]],0,m,al,[1,V]),J=H[2],L=a_(H[1],n[2]),d=L[1],an=b(c[84],d,L[2])[2],ao=a(c[23],[0,J,ab]),ap=y(T[2],0,0,m,d,J),N=g(c[df],d,F,ap),p=N[1],O=b(c[3],d,N[2]);if(6===O[0]){var
Q=ge(d,[0,n,an],[0,O[2],[0,ao,0]])[1],aq=a(w[2],0),e=b(c[x],p,aq),av=a(M[7],Q),aw=y(T[2],0,0,e,d,av),i=d,v=a(M[7],Q),s=aw;for(;;){var
z=b(c[3],i,s);if(6===z[0]){var
ar=z[3],R=hx(P[4],0,0,0,0,0,0,0,0,e,i,z[2]),S=R[2],as=R[1],au=b(c[h][5],S,ar),i=as,v=a(c[23],[0,v,[0,S]]),s=au;continue}var
U=b(c[45],v,p),ax=b(c[44],s,p),j=o(ae[2],0,e,i,U)[1],ay=function(f,e,d,b){var
c=o(ac[5],n,en,1,b);return a(ac[6],c)},az=a(bW[1],ay),aA=g(c[5],0,j,ax),aC=g(c[5],Fd,j,U),A=at(be[5],e,ag,j,0,0,aC,aA),aD=A[4],aE=A[3],aF=A[1],aG=a(l[bH],j);cg(be[7],aj,[0,aE],aD,aG,0,0,[0,[0,2,X,0]],[0,W],0,[0,az],0,aF);return 0}}throw[0,I,Fc]}function
lH(d,s,F,p){var
v=p[1],G=a(w[31],v),H=G[2],ap=G[1],aq=b(c[2][2],s,p[2]),z=[0,p[1],aq],as=b(Z[1],d,z),au=a(c[9],as),ax=b(c[69],s,au)[2],ay=b(aB[25],z[2],H[2]),J=cX(s,b(f[17][68],c[bK],ay)),aA=a(f[17][1],J),A=ap[6],aC=H[6],L=aX(0,aA);b(f[19][58],A,L);a(c[10],1);var
aF=[0,a(c[28],p),L],M=a(c[23],aF),N=aR(s,dl),aH=N[2],O=aR(N[1],bZ),m=O[1],aD=0,aI=O[2],an=[0,j[1][10][1],0];function
ao(r,i){var
e=i[2],f=i[1],g=a(aG,r),h=g[3],l=g[2],n=g[1][1];if(n){var
p=b(av[26],n[1],f),s=b(j[1][10][4],p,f);return[0,s,[0,ar(a(k[8],p),l,h),e]]}var
t=b(c[x],e,d),q=o(av[10],t,m,h,0),u=b(j[1][10][4],q,f);return[0,u,[0,ar(a(k[8],q),l,h),e]]}var
n=g(f[17][16],ao,J,an)[2],aJ=a(j[1][6],Fe),aK=a(j[1][6],Ff),aL=[0,ag([0,a(k[8],aJ),0,M]),n],aM=b(c[h][1],1,M),y=[0,ag([0,a(k[8],aK),0,aM]),aL],P=t(aw),Q=u===P?aw[1]:q===P?a(r[2],aw):aw;if(2<=Q){var
R=b(c[1][2],m,ax),S=a(c[14],R),aN=a(aE[17],R);if(a(ab[3][7],aN))var
B=m,i=S;else
var
al=at(cu[6],[0,l[bX]],Fx,0,Fw,d,m,S),B=al[1],i=al[2]}else
var
am=o(l[hK],0,0,m,Q),be=am[1],B=be,i=a(c[14],am[2]);b(c[44],i,y);g(k[10][15],c[10],0,n);a(f[17][1],aD);var
U=_(y),aO=b(Z[4],d,z),X=aR(B,ai),aP=X[2],Y=aR(X[1],aj),$=Y[2],aa=aR(Y[1],a4),e=aa[1],aQ=aa[2];function
aS(c){var
d=a(bA,c),e=[0,a(K[13][16],d),1];return b(V[3],0,e)}var
ac=b(f[17][14],aS,n);function
aT(z,y){var
B=a(c[9],y),C=g(c[df],e,A,B)[2],D=b(f[17][W],aC,n)[2];function
E(b){var
d=a(bA,b),e=a(K[13][16],d);return a(c[11],e)}var
F=b(f[17][68],E,D),G=g(c[h][3],F,0,C),m=b(c[99],e,G),p=m[1],H=m[2];function
u(i,a,h){function
d(g){var
a=b(c[3],e,g);switch(a[0]){case
0:return a[1]===i?1:0;case
9:var
h=a[2];return b(c[63],e,a[1])?b(f[19][22],d,h):0;default:return 0}}var
g=b4(e,H)[2];return b(f[19][22],d,g)?[0,1,a]:[0,0,a]}var
w=o(f[17][85],u,1,0,p),x=a(f[17][9],w),I=0;function
J(l,i,t){var
m=l[2],n=l[1],p=a(k[10][1][2],i),q=p?p[1]:a(j[1][6],Fi),u=b(K[5],q,Fg),e=b(av[26],u,n),r=b(j[1][10][4],e,n),v=b(K[5],q,Fh),d=b(av[26],v,r),w=b(j[1][10][4],d,r);if(t)var
x=0,y=0,z=function(f,e,b){var
i=b[3],j=b[2],k=b[1],l=[0,a(c[11],d),0];return[0,[0,k,j,g(c[h][3],l,f,i)],e]},A=o(f[17][85],z,y,x,m),s=a(f[17][9],A);else
var
s=[0,[0,e,d,a(a$,i)],m];return[0,[0,w,s],[0,[0,e,1],[0,d,1]]]}var
q=o(f[17][91],J,[0,j[1][10][1],0],p,x),L=q[1][2],r=a(f[17][hO],q[2]),M=r[2],N=r[1];function
s(a){function
c(a){return b(V[3],0,a)}return[1,[0,v,z+1|0],A,b(f[17][14],c,a)]}var
O=s(M),P=[0,b(V[3],0,O),0],Q=s(N),R=[0,b(V[3],0,Q),P],S=b(f[18],ac,R),d=a(f[17][9],L);if(d)var
i=d[1],T=d[2],U=i[3],X=i[2],Y=i[1],Z=function(f,e){var
d=e[3],j=e[2],g=e[1],l=f[3],m=f[2],n=f[1],o=[0,a(k[8],g),d,n],i=a(c[21],o),p=a(c[11],j),q=b(c[h][5],p,l),r=[0,$,[0,d,i,a(c[11],j),q]],s=a(c[23],r),t=a(c[11],g),u=b(c[h][5],t,m),v=[0,$,[0,d,i,a(c[11],g),u]],w=a(c[23],v);return[0,a(c[23],[0,aP,[0,d,i]]),w,s]},_=a(c[11],X),aa=[0,U,a(c[11],Y),_],l=g(f[17][15],Z,aa,T),t=a(c[23],[0,aQ,[0,l[1],l[2],l[3]]]);else
var
t=aH;return[0,I,S,[0,[0,[2,t],Fj]]]}var
aU=b(f[19][16],aT,aO),aV=a(f[19][11],aU);function
ad(b){return[0,a(j[1][6],b),1]}var
aW=ad(Fk),aY=[0,b(V[3],0,aW),0],aZ=ad(Fl),a0=[0,b(V[3],0,aZ),aY],a2=[0,[0,0,b(f[18],ac,a0),[0,[0,[2,aI],Fm]]],0],a3=b(f[18],aV,a2),ae=a(az[46],[2,v]),a5=b(K[6],Fn,ae),af=b(c[44],i,y),a6=o(T[3],0,d,e,af),a7=a(c[14],a6),ah=at(cu[6],[0,l[bX]],Fp,0,Fo,d,e,a7),C=ah[1],a9=b(c[76],C,ah[2]),a_=b(c[1][2],C,a9),D=[0,C],ba=a(aE[17],a_),E=[0,Fq,0,[0,F,0,0,0],0,a8[1],0],ak=[0,a(dB[4],Fr),a5,af,ba,y,i,0,0,0],bb=c9(Fs,d,D,ak,E,a3,0,U,0,i);function
bc(o,n,i){var
d=i[1];if(1===d[0]){var
e=d[1];b(w[55],[0,e],dV[3]);var
f=a(w[2],0),j=a(l[17],f),g=a1(l[fO],0,[0,l[cm]],0,f,j,[2,v]),h=g[1],k=b(c[84],h,g[2]),m=iE(0);return hm(a(w[2],0),h,F,k,ae,Fu,m,e)}throw[0,I,Ft]}var
bd=[0,c7(d,D,E[3],ak,U,bb,0),0];return gU(d,D,Fv,0,E[3],0,bd,bc)}function
Fy(d,c,b,a){lH(d,c,b,a);return 0}b7([0,Fz,function(a,b){return b6(Fy,a,b)}]);aD(1251,[0,hm,lH],"Noconf_hom");function
hn(i,d,k,t,s){var
l=dz(i,d,y(T[2],0,0,i,d,k))[1],m=cY(l),e=m[1],u=m[2],v=e[1][1],n=a(w[31],e[1]),j=n[2],p=n[1],x=p[1];function
z(b,d){return a(c[28],[0,[0,v,b],e[2]])}var
A=b(f[19][16],z,x),B=a(f[19][11],A),C=a(f[17][9],B),D=j[2],q=b(c[2][2],d,e[2]),E=b(aB[25],q,D);a(f[17][1],E);var
r=p[6],F=o(Z[75],i,e[1],0,4),G=j[9],H=j[4];function
I(n,m,g){var
o=b(bb[23],g[2],g[1]),p=b(aB[24],q,o),t=a(c[9],p),v=b(c[h][4],C,t),i=b(c[99],d,v),j=i[1],w=i[2],x=a(f[17][1],j)-r|0,y=b(f[17][W],x,j)[1],z=b(c[44],w,y),A=a(f[17][9],u),B=b(c[h][4],A,z),k=b(c[99],d,B),l=k[1],D=a1(s,e,n,m,r,l,k[2]);return b(c[45],D,l)}var
J=g(f[19][59],I,H,G);return at(Z[76],i,d,l,F,t,k,J)}function
lI(n,aa,E,e){var
s=e[1],d=[0,aa],ab=e[2],F=a(w[31],s),G=F[2],ac=F[1],ad=b(c[2][2],d[1],e[2]),ae=b(Z[1],n,[0,e[1],ad]),af=a(c[9],ae),ah=b(c[69],d[1],af)[2],aj=G[2],al=b(c[2][2],d[1],ab),am=b(aB[25],al,aj),an=b(f[17][68],c[bK],am),H=cX(d[1],an),ao=a(f[17][1],H),aq=ac[6],ar=G[6],I=aX(0,ao),J=b(f[19][58],aq,I)[2];if(0===J.length-1)var
as=a(c[10],1),au=[0,a(c[28],e),I],p=a(c[23],au),z=as,v=H,o=0;else{var
m=dJ(n,d[1],e),X=m[3],aZ=m[8],a0=m[7],a2=m[6],a3=m[2];d[1]=m[1];var
Y=t(ai),a4=u===Y?ai[1]:q===Y?a(r[2],ai):ai,_=b(P[9],d[1],a4),a5=_[2];d[1]=_[1];var
a6=g(c[5],0,d[1],a3),a7=a(f[17][1],X),a8=b(bb[35],a7,a6)[2],a9=[0,a5,[0,aZ,a(c[9],a8)]],a_=a(c[23],a9),a$=b(f[17][co],a0,a2),$=t(ak),ba=a(c[10],1),bc=u===$?ak[1]:q===$?a(r[2],ak):ak,bd=a(c[26],[0,bc,ba]),p=g(N[20],n,d[1],a_),z=bd,v=X,o=a$}var
av=ap(dl,d),ax=ap(bZ,d),L=a(j[1][6],FA),A=a(j[1][6],FB),B=[0,ag([0,a(k[8],L),0,p]),v],ay=b(c[h][1],1,p),M=t(aw),aA=[0,ag([0,a(k[8],A),0,ay]),B],aC=u===M?aw[1]:q===M?a(r[2],aw):aw;switch(aC){case
0:var
i=c[15];break;case
1:var
i=c[16];break;case
2:var
i=c[17];break;default:var
aV=b(c[1][2],d[1],ah),aW=a(c[14],aV),W=at(cu[6],[0,l[bX]],FG,0,FF,n,d[1],aW),aY=W[2];d[1]=W[1];var
i=aY}var
aD=b(c[44],i,aA),C=b(c[x],B,n),aE=g(k[10][15],c[10],0,v);function
O(a){return b(c[h][1],a,p)}function
Q(d){var
g=a(c[h][1],d),i=b(f[19][15],g,aE),j=b(f[19][5],i,J),k=[0,a(c[28],e),j];return a(c[23],k)}var
R=a(f[17][1],o),aF=O(ar+2|0),aG=aT(1,o),aH=Q(R+1|0),aI=[0,ag([0,a(k[8],L),0,aH]),aG],aJ=ag([0,k[9],0,aF]),aK=b(c[42],aJ,i),aL=b(c[45],aK,aI);function
aM(F,p,E,D,e,B){var
l=O(a(f[17][1],e)+1|0),j=[0,a(k[8],A),0,l],m=[0,ag(j),e],g=b(c[x],m,C),n=aT(a(f[17][1],e)+2|0,o),q=Q((a(f[17][1],e)+R|0)+2|0),r=[0,a(k[8],A),0,q];function
s(t,o,s,r,k,q){if(p===o){if(0===a(f[17][1],e))return av;var
l=c2(C,d,e)[3],m=c2(g,d,k)[3],n=a(f[17][1],e)+1|0,i=b(c[h][1],n,l),j=b(c[x],k,g);return b0(j,d,y(T[2],0,0,j,d[1],i),i,m)}return ax}var
t=[0,ag(r),n],u=b(c[45],i,t),v=hn(g,d[1],z,u,s),w=ag(j);return b(c[43],w,v)}var
aN=hn(C,d[1],z,aL,aM),aO=b(c[45],aN,B),aP=h6(0,[0,E],d[1],[0,aD],aO)[2],S=a(az[46],[2,s]),aQ=b(K[6],FC,S),aR=y(bM[3],0,0,aQ,0,[0,[0,aP],FD]),D=a(w[2],0),aS=a(l[17],D),U=a1(l[fO],0,[0,l[cm]],0,D,aS,[2,s]),V=U[1],aU=b(c[84],V,U[2]);return hm(D,V,E,aU,S,FE,iD(0),aR)}b7([0,FH,function(a,b){return b6(lI,a,b)}]);aD(1252,[0,hn,lI],nj);function
lJ(l,h,g){function
d(d){var
m=a(i[68][5],d),e=b(c[91],m,g),f=e[1],n=e[2],o=b(C[35][21],d,f),p=a(aY[12],n),q=[0,a(c[10],1),p],r=a(c[23],q),t=a(j[1][6],FI),u=[0,a(k[8],t),o,r],v=a(c[21],u),w=y(s[bY],0,[0,h],v,0,dK[6]),x=y(s[bY],0,[0,l],f,0,dK[6]);return b(i[18],x,w)}return a(i[68][8],d)}function
lK(c){if(1===c[0]){var
d=a(j[17][8],c[1]),e=a(j[6][7],d);return b(FL[7],[0,FK,[0,e,0]],dK[7])}throw[0,I,FJ]}function
lL(l){function
d(d){var
f=a(i[68][4],d),e=a(i[68][5],d),j=a(i[68][2],d),k=T[2];function
p(a){return g(k,0,0,a)}var
q=g(C[35][1],p,d,l),m=eZ[2],n=b(br[1],0,m),h=[0,e];return function(z,x,w){var
f=z,j=x,p=w;for(;;){var
g=b(c[3],e,j),d=b(c[3],e,p);if(6===g[0]){var
u=g[2],M=g[3],N=g[1];switch(d[0]){case
6:var
O=d[3],P=d[2];try{var
Q=y(br[4],[0,n],f,h[1],u,P)}catch(a){a=v(a);if(a[1]===br[3])return ba(FP);throw a}h[1]=Q;var
R=ag([0,N,0,u]),f=b(c[aP],R,f),j=M,p=O;continue;case
9:var
k=0;break;default:var
k=1}}else
var
k=0;if(!k)if(9===d[0]){var
q=d[1],A=d[2];if(b(c[54],e,q)){var
B=b(c[83],e,q),C=h[1],r=o(i6,f,C,B,a(aY[11],A)),s=r[2],E=r[1],F=b(br[15],ki[7][1],m),G=function(a){return FN},H=[0,F,b(D[56],s[2].length-1,G)],t=a1(br[17],n,f,E,s,H,j),I=t[1];if(t[2]){var
J=function(a){return[0,a,l]},K=b(cD[1],0,J),L=a(i[66][1],I);return b(i[73][2],L,K)}return ba(FO)}}return ba(FM)}}(f,j,q)}return a(i[68][8],d)}aD(1254,[0,lJ,lK,lL],mK);a(a0[9],as);var
fs=i[72][1],dW=aa[8],FQ=0;function
FR(c,b,a,d){return lJ(c,b,a)}var
FS=[1,[5,a(E[16],aa[11])],0],FT=[1,[5,a(E[16],aa[7])],FS],FV=[0,[0,[0,FU,[1,[5,a(E[16],aa[7])],FT]],FR],FQ];y(an[8],as,FW,0,0,FV);var
FX=0;function
FY(a,b){return lK(a)}var
F0=[0,[0,[0,FZ,[1,[5,a(E[16],aa[17])],0]],FY],FX];y(an[8],as,F1,0,0,F0);var
F2=0;function
F3(c,a,d){return b(c3[5],c,a)}var
F4=[1,[5,a(E[16],aa[7])],0],F6=[0,[0,[0,F5,[1,[5,a(E[16],dW)],F4]],F3],F2];y(an[8],as,F7,0,0,F6);var
F8=0;function
F9(b,c){return a(c3[4],b)}var
Ga=[0,[0,[0,F$,[0,F_,[1,[5,a(E[16],dW)],0]]],F9],F8];y(an[8],as,Gb,0,0,Ga);var
Gc=0,Ge=[0,[0,Gd,function(a){return c3[2]}],Gc];function
Gf(b,c){return a(c3[1],b)}var
Gh=[0,[0,[0,Gg,[1,[5,a(E[16],dW)],0]],Gf],Ge];y(an[8],as,Gi,0,0,Gh);var
Gj=0;function
Gk(a,b){return jN(a)}var
Gm=[0,[0,[0,Gl,[1,[5,a(E[16],aa[7])],0]],Gk],Gj];y(an[8],as,Gn,0,0,Gm);var
Go=0;function
Gp(d,c,b,a,e){return o(c3[3],d,c,b,a)}var
Gq=[1,[5,a(E[16],aa[7])],0],Gr=[1,[5,a(E[16],aa[7])],Gq],Gs=[1,[5,a(E[16],aa[11])],Gr],Gu=[0,[0,[0,Gt,[1,[5,a(E[16],aa[11])],Gs]],Gp],Go];y(an[8],as,Gv,0,0,Gu);var
Gw=0;function
Gx(a,e){var
c=0;function
d(b){return g8(c,a,b)}return b(i[72][1],0,d)}var
GA=[0,[0,[0,Gz,[0,Gy,[1,[5,a(E[16],aa[11])],0]]],Gx],Gw];y(an[8],as,GB,0,0,GA);var
GC=0;function
GD(a,d){function
c(b){return g8(GE,a,b)}return b(i[72][1],0,c)}var
GI=[0,[0,[0,GH,[0,GG,[0,GF,[1,[5,a(E[16],aa[11])],0]]]],GD],GC];y(an[8],as,GJ,0,0,GI);var
GK=0;function
GL(a,e){var
c=0;function
d(b){return kZ(c,a,b)}return b(i[72][1],0,d)}var
GN=[0,[0,[0,GM,[1,[5,a(E[16],aa[11])],0]],GL],GK];y(an[8],as,GO,0,0,GN);var
GP=0;function
GQ(c,f){function
e(b){if(kV(b,c))return a(bO[6],b);var
e=a(d[3],GR);return g(bO[38],0,e,b)}return b(i[72][1],0,e)}var
GT=[0,[0,[0,GS,[1,[5,a(E[16],dW)],0]],GQ],GP];y(an[8],as,GU,0,0,GT);var
GV=0;function
GW(d,c,a){var
e=F(b(ef[24],a,c)),f=F(b(ef[24],a,d));return b(fs,0,function(a){return lG(f,e,a)})}var
GX=[1,[5,a(E[16],eh[8])],0],GZ=[0,[0,[0,GY,[1,[5,a(E[16],eh[8])],GX]],GW],GV];y(an[8],as,G0,0,0,GZ);var
G1=0;function
G2(e,d,f){return b(fs,0,ha(d,a(iz,b(m[17],c[au][1],e))))}var
G3=[1,[5,a(E[16],aa[19])],0],G5=[0,[0,[0,G4,[1,[2,[5,a(E[16],aa[11])]],G3]],G2],G1];function
G6(c,a,d){return b(fs,0,ha(a,c))}var
G7=[1,[5,a(E[16],aa[19])],0],G9=[0,[0,[0,G8,[1,[0,[5,a(E[16],aa[16])]],G7]],G6],G5];y(an[8],as,G_,0,0,G9);function
G$(b,a){return ew}function
Ha(b,a){return ew}var
Hb=[0,function(b,a){return ew},Ha,G$],Hc=0,Hd=[0,function(b,a){return a}],He=[0,function(b,a){return[0,b,a]}],Hf=0,Hg=0;function
Hh(b,a){return Hi}var
Hk=[0,[0,[0,0,[0,a(cI[10],Hj)]],Hh],Hg];function
Hl(b,a){return Hm}var
Ho=[0,[0,[0,0,[0,a(cI[10],Hn)]],Hl],Hk];function
Hp(b,a){return Hq}var
Hs=[0,[0,[0,0,[0,a(cI[10],Hr)]],Hp],Ho];function
Ht(b,a){return Hu}var
Hw=[0,[1,[0,[0,[0,0,[0,a(cI[10],Hv)]],Ht],Hs]],Hf,He,Hd,Hc,Hb],lM=b(an[9],Hx,Hw),lN=lM[2],Hy=lM[1];function
Hz(b,a){return ex}function
HA(b,a){return ex}var
HB=[0,function(b,a){return ex},HA,Hz],HC=0,HD=[0,function(b,a){return a}],HE=[0,function(b,a){return[0,b,a]}],HF=0,HG=0;function
HH(d,a,c,b){return a}var
HJ=[0,a(cI[10],HI)],HL=[0,[0,[0,[0,[0,0,[0,a(cI[10],HK)]],[1,[6,lN]]],HJ],HH],HG],HM=[0,[1,[0,[0,0,function(a){return 0}],HL]],HF,HE,HD,HC,HB],lO=b(an[9],HN,HM),ho=lO[1],HO=lO[2];function
ft(e,d,c,b){return a(j[1][9],b[2])}function
HP(b,a){return ft}function
HQ(b,a){return ft}var
HR=[0,function(b,a){return ft},HQ,HP],HS=0,HT=[0,function(b,a){return a}],HU=[0,function(b,a){return[0,b,a]}],HV=0,HW=0;function
HX(b,a){return[0,a,b]}var
lP=b(an[9],HY,[0,[1,[0,[0,[0,0,[6,B[15][2]]],HX],HW]],HV,HU,HT,HS,HR]),lQ=lP[2],HZ=lP[1],H0=0;function
lR(h,g,f,e,c,b){return a(d[7],0)}function
lS(h,g,f,e,c,b){return a(d[7],0)}function
lT(h,g,f,e,c,b){return a(d[7],0)}var
fu=a(E[3],H1),H2=a(E[4],fu),hp=g(B[14],B[10],H3,H2),H4=b(a6[4],fu,0);o(dX[1],fu,lR,lS,lT);var
fv=a(E[3],H5),H6=b(a6[4],fv,0);function
lU(h,g,f,e,c,b){return a(d[7],0)}function
lV(h,g,f,e,c,b){return a(d[7],0)}function
lW(h,g,f,e,c,b){return a(d[7],0)}var
H7=a(E[4],fv),fw=g(B[14],lX[1],H8,H7);o(dX[1],fv,lU,lV,lW);var
fx=a(E[3],H9),H_=b(a6[4],fx,0);function
lY(h,g,f,e,c,b){return a(d[7],0)}function
lZ(h,g,f,e,c,b){return a(d[7],0)}function
l0(h,g,f,e,c,b){return a(d[7],0)}var
H$=a(E[4],fx),hq=g(B[14],B[11],Ia,H$);o(dX[1],fx,lY,lZ,l0);var
da=a(E[3],Ib),Ic=b(a6[4],da,0);function
l1(h,g,f,e,c,b){return a(d[7],0)}function
l2(h,g,f,e,c,b){return a(d[7],0)}function
l3(h,g,f,e,c,b){return a(d[7],0)}var
Id=a(E[4],da),l4=g(B[14],lX[1],Ie,Id);o(dX[1],da,l1,l2,l3);function
If(b,a){return a}function
l5(e,d){var
c=a(E[2],d);b(a6[4],c,e);return c}var
Ih=a(E[6],aa[4]),fy=l5([0,a(a6[3],Ih)],Ig);function
l6(b,a){return[0,b,a]}function
l7(b,a){return a}function
l8(c,b){return a(hr[1],b)}function
l9(c,d){function
e(f,e){function
g(d){var
e=a(E[6],c),f=a(a6[3],e),g=b(a6[1][8],f,d);return a(hr[1],g)}var
h=b(d,f,e);return b(hr[2],h,g)}return b(a6[7],c,e)}function
l_(a){b(l$[9],a,l6);b(l$[10],a,l7);return l9(a,l8)}l_(fy);var
Ii=a(E[4],fy),ma=g(B[14],B[11],Ij,Ii);b(cI[1],0,Ik);var
hs=a(B[2][1],Il),ht=a(B[2][1],Im),mb=a(B[2][1],In),mc=a(B[2][1],Io),md=a(B[2][1],Ip),cJ=a(B[2][1],Iq),me=a(B[2][1],Ir),mf=a(B[2][1],Is),mg=a(B[2][1],It),mh=a(B[2][1],Iu),mi=a(B[2][1],Iv),mj=a(B[2][1],Iw),hu=a(B[2][1],Ix),hv=a(B[2][1],Iy),Iz=0,IA=0,IC=[0,0,[0,[0,0,0,[0,[0,IB,function(a,b){return a}],IA]],Iz]];g(B[19],ma,0,IC);var
ID=0,IE=0;function
IF(a,b){return a}g(B[19],hp,0,[0,0,[0,[0,0,0,[0,[0,[0,0,[6,B[16][16]]],IF],IE]],ID]]);var
IG=0,IH=0,IJ=[0,0,[0,[0,0,0,[0,[0,[0,0,[4,[6,ht],II]],function(a,b){return a}],IH]],IG]];g(B[19],fw,0,IJ);var
IK=0,IL=0;function
IM(d,a,c,b){return a}g(B[19],hq,0,[0,0,[0,[0,0,0,[0,[0,[0,[0,IP,[4,[6,B[16][3]],IO]],IN],IM],IL]],IK]]);var
IQ=0,IR=0,IW=[0,0,[0,[0,IV,0,[0,[0,[0,[0,IU,[4,[6,ht],IT]],IS],function(i,d,h,g,c){var
e=a(E[4],ev),f=[12,0,0,[0,b(E[7],e,d)]];return b(af[1],[0,c],f)}],IR]],IQ]];g(B[19],B[16][5],0,IW);var
IX=0,IY=0;function
IZ(b,a){return[0,a,b]}g(B[19],hs,0,[0,0,[0,[0,0,0,[0,[0,[0,0,[6,B[16][6]]],IZ],IY]],IX]]);var
I0=0,I1=0;function
I2(b,a,d,c){return[0,[1,a],b]}var
I5=[0,[0,[0,[0,I4,[2,[6,B[16][3]],I3]],[6,hu]],I2],I1],I6=[0,0,[0,[0,0,0,[0,[0,[0,[0,0,[6,mb]],[6,hu]],function(b,a,c){return[0,[0,a],b]}],I5]],I0]];g(B[19],ht,0,I6);var
I7=0,I8=0;function
I9(a,b){return a}g(B[19],mb,0,[0,0,[0,[0,0,0,[0,[0,[0,0,[6,B[16][3]]],I9],I8]],I7]]);var
I_=0,I$=0;function
Ja(a,b){return a}g(B[19],mc,0,[0,0,[0,[0,0,0,[0,[0,[0,0,[2,[6,B[16][3]],Jb]],Ja],I$]],I_]]);var
Jc=0,Jd=0;function
Je(b,a,e,d,c){return[0,[1,[0,a,b]]]}var
Jg=[0,[0,[0,[0,Jf,[6,B[16][1]]],[5,[6,B[16][1]]]],Je],Jd],Ji=[0,[0,[0,Jh,[5,[6,hs]]],function(a,d,c,b){return[0,[0,a]]}],Jg],Jj=[0,0,[0,[0,0,0,[0,[0,0,function(a){return 0}],Ji]],Jc]];g(B[19],md,0,Jj);var
Jk=0,Jl=0;function
Jm(f,i,e,d,h,c,b,g,a){return[0,[0,b,a,c,[0,d],e],f]}g(B[19],cJ,0,[0,0,[0,[0,0,0,[0,[0,[0,[0,[0,[0,[0,[0,[0,0,[6,lQ]],[6,hp]],Jo],[6,B[16][3]]],[6,md]],Jn],[6,hv]],Jm],Jl]],Jk]]);var
Jp=0,Jq=0;function
Jr(c,b,e,a,d){return[1,[0,a,b,c]]}var
Js=0,Ju=[5,[8,[0,[0,Jt,function(a,c,b){return a}],Js]]],Jw=[0,[0,[0,[0,[0,[0,0,[6,B[15][22]]],Jv],[6,B[16][1]]],Ju],Jr],Jq],Jy=[0,0,[0,[0,0,0,[0,[0,[0,0,[6,cJ]],function(b,c){return[0,a(b,Jx)]}],Jw]],Jp]];g(B[19],me,0,Jy);var
Jz=0,JA=0,JC=[0,[0,[0,JB,[6,me]],function(a,c,b){return a}],JA],JF=[0,[0,[0,JE,[6,cJ]],function(b,d,c){return[0,a(b,JD)]}],JC],JG=[0,0,[0,[0,0,0,[0,[0,[0,0,[6,cJ]],function(b,c){return[0,a(b,0)]}],JF]],Jz]];g(B[19],mf,0,JG);var
JH=0,JI=0,JK=[0,0,[0,[0,0,0,[0,[0,[0,0,[3,[6,mf]]],function(a,c){function
b(a){if(a){var
c=a[1];if(0===c[0]){var
f=c[1],d=b(a[2]);return[0,[0,f,d[1]],d[2]]}var
g=c[1],e=b(a[2]);return[0,e[1],[0,g,e[2]]]}return JJ}return b(a)}],JI]],JH]];g(B[19],mg,0,JK);var
JL=0,JM=0;function
JN(c,b,e,a,d){return[1,[0,a,b,c]]}var
JO=0,JQ=[5,[8,[0,[0,JP,function(a,c,b){return a}],JO]]],JS=[0,[0,[0,[0,[0,[0,0,[6,B[15][22]]],JR],[6,B[16][1]]],JQ],JN],JM],JU=[0,0,[0,[0,0,0,[0,[0,[0,0,[6,cJ]],function(b,c){return[0,a(b,JT)]}],JS]],JL]];g(B[19],mh,0,JU);var
JV=0,JW=0,JY=[0,[0,[0,JX,[6,mh]],function(a,c,b){return a}],JW],J1=[0,0,[0,[0,0,0,[0,[0,[0,J0,[6,cJ]],function(b,d,c){return[0,a(b,JZ)]}],JY]],JV]];g(B[19],mi,0,J1);var
J2=0,J3=0,J5=[0,0,[0,[0,0,0,[0,[0,[0,0,[3,[6,mi]]],function(a,c){function
b(a){if(a){var
c=a[1];if(0===c[0]){var
f=c[1],d=b(a[2]);return[0,[0,f,d[1]],d[2]]}var
g=c[1],e=b(a[2]);return[0,e[1],[0,g,e[2]]]}return J4}return b(a)}],J3]],J2]];g(B[19],mj,0,J5);var
J6=0,J7=0,J9=[0,[0,[0,J8,[6,hs]],function(a,c,b){return[0,[1,a]]}],J7];function
J_(b,a,d,c){return[0,[0,[0,a],b]]}var
J$=[6,mj],Ka=[6,B[16][3]],Kb=0,Kd=[0,[0,Kc,function(b,a){return 0}],Kb],Kf=[0,[0,[0,[0,[0,0,[8,[0,[0,Ke,function(b,a){return 0}],Kd]]],Ka],J$],J_],J9];function
Kg(b,e,a,d,c){return[0,[2,a,b]]}var
Kh=[6,hv],Ki=0,Kk=[0,[0,Kj,function(b,a){return 0}],Ki],Km=[8,[0,[0,Kl,function(b,a){return 0}],Kk]],Kn=[6,mc],Ko=0,Kq=[0,[0,[0,[0,[0,[0,0,[8,[0,[0,Kp,function(b,a){return 0}],Ko]]],Kn],Km],Kh],Kg],Kf],Kr=[0,0,[0,[0,0,0,[0,[0,0,function(a){return 0}],Kq]],J6]];g(B[19],hu,0,Kr);var
Ks=0,Kt=0,Kw=[0,[0,[0,[0,Kv,[6,fw]],Ku],function(d,a,c,b){return a}],Kt],Kx=[0,0,[0,[0,0,0,[0,[0,[0,0,[6,fw]],function(a,b){return a}],Kw]],Ks]];g(B[19],hv,0,Kx);var
Ky=0,Kz=0,KA=[0,0,[0,[0,0,0,[0,[0,[0,[0,0,[6,cJ]],[6,mg]],function(b,c,f){var
d=b[2],e=b[1];return[0,[0,a(c,0),e],d]}],Kz]],Ky]];g(B[19],l4,0,KA);function
mk(a){return KB}var
KC=0,KD=0;function
KE(g,c,f,a){var
h=b(bG[3][5],bG[5],bG[6]),d=b(bG[1],h,f),e=hl(d[1],d[2],1,g,c[1],c[2]);return[0,a[1],a[2],e,a[4]]}var
KF=[1,[5,a(E[16],da)],0],KI=[0,[0,0,[0,KH,[0,KG,[1,[5,a(E[16],ho)],KF]]],KE,KD],KC];o(dY[2],KJ,[0,mk],0,KI);var
KK=0,KL=0;function
KM(g,c,f,a){var
h=b(bG[3][5],bG[5],bG[6]),d=b(bG[1],h,f),e=hl(d[1],d[2],0,g,c[1],c[2]);return[0,a[1],a[2],e,a[4]]}var
KN=[1,[5,a(E[16],da)],0],KP=[0,[0,0,[0,KO,[1,[5,a(E[16],ho)],KN]],KM,KL],KK],KQ=0,KR=[0,function(a){return dY[6]}];o(dY[2],KS,KR,KQ,KP);function
ml(c,b,a){return dC(c,b,0,a[1])}function
mm(g,c,e){var
d=a(bO[2],c),h=b(KT[3][1],d,c[1]),i=[0,a(j[1][11][30],g[1])];function
k(a){return ml(h,i,a)}return[0,d,b(f[17][68],k,e)]}function
mn(d,c){var
e=a(iN[6],d);return b(f[17][68],e,c)}function
mo(b,a){return a}function
mp(e,d,c,b){return bC(a(w[2],0),b)}function
mq(h,f,e,l,k,c){var
i=b(e,h,f);function
j(b){return a(d[3],KU)}return g(d[39],j,i,c)}function
mr(f,e,c,k,j,b){function
h(a){return g(c,f,e,a)}function
i(b){return a(d[3],KV)}return g(d[39],i,h,b)}function
KW(b,a){return mp}function
KX(b,a){return function(c,d,e,f){return mr(b,a,c,d,e,f)}}var
KY=[0,function(b,a){return function(c,d,e,f){return mq(b,a,c,d,e,f)}},KX,KW],KZ=[2,mm],K0=[0,mo],K1=[0,[0,hq],0,[0,function(a,b){return[0,a,mn(a,b)]}],K0,KZ,KY],ms=b(an[9],K2,K1),mt=ms[1],K3=ms[2],K4=0;function
K5(c,b,d){return dT([0,b],[0,a(dB[4],K6),c])}var
K8=[0,K7,[1,[5,a(E[16],mt)],0]],K$=[0,[0,[0,K_,[0,K9,[1,[5,a(E[16],aa[7])],K8]]],K5],K4];function
La(b,c){return dT(0,[0,a(dB[4],Lb),b])}var
Le=[0,[0,[0,Ld,[0,Lc,[1,[5,a(E[16],aa[7])],0]]],La],K$];y(an[8],as,Lf,0,0,Le);var
Lg=0;function
Lh(f,g){function
e(g){var
h=a(i[68][5],g),e=b(c[3],h,f);if(1===e[0])if(a(A[bw],e[1]))return a(i[16],0);var
j=a(d[3],Li);return b(n[65][4],0,j)}return a(i[68][8],e)}var
Lk=[0,[0,[0,Lj,[1,[5,a(E[16],aa[11])],0]],Lh],Lg];y(an[8],as,Ll,0,0,Lk);var
Lm=0;function
Ln(a,b){return lL(a)}var
Lp=[0,[0,[0,Lo,[1,[5,a(E[16],aa[13])],0]],Ln],Lm];y(an[8],as,Lq,0,0,Lp);var
Lr=0;function
Ls(a,e){var
c=1;function
d(b){return g9(c,a,b)}return b(i[72][1],0,d)}var
Lu=[0,[0,[0,Lt,[1,[5,a(E[16],aa[7])],0]],Ls],Lr];function
Lv(a,e){var
c=0;function
d(b){return g9(c,a,b)}return b(i[72][1],0,d)}var
Lx=[0,[0,[0,Lw,[1,[5,a(E[16],aa[7])],0]],Lv],Lu];y(an[8],as,Ly,0,0,Lx);var
Lz=0;function
LA(b,a,c){return iU(b,a)}var
LB=[1,[5,a(E[16],aa[11])],0],LD=[0,[0,[0,LC,[1,[5,a(E[16],aa[7])],LB]],LA],Lz];y(an[8],as,LE,0,0,LD);var
LF=0,LG=0;function
LH(h,g,e,d){var
i=b(bG[1],bG[5],e);function
a(a){var
c=b(ea[3],0,a);return[0,a[2],c]}var
c=b(f[17][68],a,g);i_(i,b(f[17][68],j[1][8],h),c);return d}var
LJ=[0,LI,[1,[2,[5,a(E[16],aa[18])]],0]],LL=[0,[0,0,[0,LK,[1,[0,[5,a(E[16],aa[7])]],LJ]],LH,LG],LF],LM=0,LN=[0,function(a){return dY[6]}];o(dY[2],LO,LN,LM,LL);var
fz=a(E[3],LP),LQ=b(a6[4],fz,0);function
mu(e,d,c,b,a){return dO}function
mv(e,d,c,b,a){return dO}function
mw(e,d,c,b,a){return dO}var
LR=a(E[4],fz),fA=g(B[14],B[11],LS,LR);o(dX[1],fz,mu,mv,mw);var
mx=a(B[2][1],LT),my=a(B[2][1],LU),mz=a(B[2][1],LV),mA=a(B[2][1],LW),LX=0,LY=0,LZ=[0,0,[0,[0,0,0,[0,[0,[0,0,[1,[6,mx]]],function(a,b){return a}],LY]],LX]];g(B[19],fA,0,LZ);var
L0=0,L1=0,L2=[0,0,[0,[0,0,0,[0,[0,[0,0,[6,my]],function(b,a){return[0,[0,a],b]}],L1]],L0]];g(B[19],mx,0,L2);var
L3=0,L4=0,L5=[0,[0,[0,0,[6,mz]],function(a,b){return[0,a]}],L4],L7=[0,[0,L6,function(b,a){return 0}],L5],L9=[0,[0,L8,function(b,a){return 1}],L7],L$=[0,0,[0,[0,0,0,[0,[0,L_,function(b,a){return 2}],L9]],L3]];g(B[19],my,0,L$);var
Ma=0,Mb=0,Me=[0,[0,Md,function(b,a){return Mc}],Mb],Mh=[0,[0,Mg,function(b,a){return Mf}],Me],Mj=[0,[0,Mi,function(b,a){return 1}],Mh],Mm=[0,[0,Ml,function(b,a){return Mk}],Mj],Mp=[0,[0,[0,[0,Mo,[6,fA]],Mn],function(e,a,d,c,b){return[2,a]}],Mm],Mq=[0,0,[0,[0,0,0,[0,[0,[0,0,[6,mA]],function(a,b){return[1,a]}],Mp]],Ma]];g(B[19],mz,0,Mq);var
Mr=0,Ms=0,Mu=[0,[0,Mt,function(b,a){return 0}],Ms],Mw=[0,0,[0,[0,0,0,[0,[0,Mv,function(b,a){return 1}],Mu]],Mr]];g(B[19],mA,0,Mw);function
fB(c,b,a){return dO}function
Mx(b,a){return fB}function
My(b,a){return fB}var
Mz=[0,function(b,a){return fB},My,Mx],MA=0,MB=[0,function(b,a){return a}],MC=[0,[0,fA],0,[0,function(b,a){return[0,b,a]}],MB,MA,Mz],mB=b(an[9],MD,MC),mC=mB[1],ME=mB[2],MF=0,MH=[0,[0,MG,function(a){return gM(0)}],MF];function
MI(a,b){return gM(a)}var
MK=[0,[0,[0,MJ,[1,[5,a(E[16],mC)],0]],MI],MH];y(an[8],as,ML,0,0,MK);var
MM=0;function
MN(b,a,c){return fj(b,a)}var
MO=[1,[2,[5,a(E[16],aa[3])]],0],MQ=[0,[0,[0,MP,[1,[2,[5,a(E[16],fy)]],MO]],MN],MM];y(an[8],as,MR,0,0,MQ);aD(1266,[0,as,fs,dW,Hy,lN,ho,HO,ft,HZ,lQ,H0,lR,lS,lT,fu,hp,H4,fv,H6,lU,lV,lW,fw,fx,H_,lY,lZ,l0,hq,da,Ic,l1,l2,l3,l4,If,l5,fy,l6,l7,l8,l9,l_,ma,mk,ml,mm,mn,mo,mp,mq,mr,mt,K3,fz,LQ,mu,mv,mw,fA,fB,mC,ME],"G_equations");a(a0[9],MS);a(a0[9],MT);a(a0[9],MU);a(a0[9],MV);a(a0[9],MW);a(a0[9],MX);a(a0[9],MY);a(a0[9],MZ);a(a0[9],M0);a(a0[9],M1);a(a0[9],M2);a(a0[9],M3);a(a0[9],M4);aD(1267,[0],"Equations_plugin_mod");return}
