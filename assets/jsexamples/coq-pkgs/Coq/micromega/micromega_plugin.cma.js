function(Iv){"use strict";var
mb="QMicromega",mz="*",hI="param.csdp",mu="__varmap",my="diagonalize: not PSD",l7="csdp: error ",mW="monoid",m4="__p",hR='"',mK="__p%i",mL=",",m3=" 1 ",mJ="1\n",m2="__ff",ma="=",mt="find_pivot",mI="%s*%a",mV="Require Import ZArith Lia. Open Scope Z_scope.\n",hD='"\n',mi="buggy certificate",mx="lia",al="ZMicromega",mH=" * ",J="micromega",fu='command "',ms=")^2",l6="compare_num",hU="real_nonlinear_prover",l$=" [*] ",mG="__wit",mU=143,l_="Zero",hT="Lia",hH="; csdp ",mh="ERROR: no compatible proof",aK="",bY="RingMicromega",mF='Unfortunately Coq isn\'t aware of the presence of any "csdp" executable in the path. \n\n',m1="parse_zop",hP="real nonlinear prover",hO="0",hN="> /dev/null",mr="%a * %a",l5="__arith",dL="Reals",m0=", False\n",hG=438,aS=248,l3="<=",l4="QArith",hM="cd ",mw=") * (",cQ=" + ",y="Coq",mT="psatz_R",l9=148,mS=".",mf="Csdp packages are provided by some OS distributions; binaries and source code can be downloaded from https://projects.coin-or.org/Csdp",mg=" : ",mR="Bad logical fragment",i=246,me="-%a",mv="(%a) * (%a)",mZ="x%i",mE=118,$="Tauto",hL="%a + %a",mD=119,mC="csdp: Problem is infeasible",hQ=" Cannot find witness",mQ="Z",mq="the use of a specialized external tool called csdp. \n\n",ar=" ",mY="e",ad=103,ft=120,mP="EnvRing",l2="t",hF=".dat-s",l8="PsatzZ",mp="-",hS="_vendor+v8.10+64bit/coq/plugins/micromega/mfourier.ml",mX="Rdefinitions",mo="Timeout",mB="D",mN="linear prover",mO="Depth",md="(%a)^2",mA=" Skipping what remains of this tactic: the complexity of the goal requires ",mm="psatz_Q",mn='" exited ',fw="_vendor+v8.10+64bit/coq/plugins/micromega/certificate.ml",fv="%s",hK=".out",mk="psatz_Z",ml="Rpow_def",mj="nat",l1="%i",hJ="sos",aJ="\n",hE="pure_sos",mM=0.693147180559945286,aB="VarMap",mc=250,C=Iv.jsoo_runtime,w=C.caml_check_bound,fs=C.caml_compare,W=C.caml_equal,aR=C.caml_fresh_oo_id,a$=C.caml_int_compare,lY=C.caml_int_of_string,bX=C.caml_lessthan,Is=C.caml_list_of_js_array,cn=C.caml_ml_string_length,fq=C.caml_mul,c=C.caml_new_string,lZ=C.caml_obj_tag,aA=C.caml_register_global,lX=C.caml_string_equal,bK=C.caml_string_get,cP=C.caml_sys_remove,hC=C.caml_sys_system_command,n=C.caml_wrap_exception;function
b(a,b){return a.length==1?a(b):C.caml_call_gen(a,[b])}function
a(a,b,c){return a.length==2?a(b,c):C.caml_call_gen(a,[b,c])}function
g(a,b,c,d){return a.length==3?a(b,c,d):C.caml_call_gen(a,[b,c,d])}function
D(a,b,c,d,e){return a.length==4?a(b,c,d,e):C.caml_call_gen(a,[b,c,d,e])}function
S(a,b,c,d,e,f){return a.length==5?a(b,c,d,e,f):C.caml_call_gen(a,[b,c,d,e,f])}function
V(a,b,c,d,e,f,g){return a.length==6?a(b,c,d,e,f,g):C.caml_call_gen(a,[b,c,d,e,f,g])}function
fr(a,b,c,d,e,f,g,h){return a.length==7?a(b,c,d,e,f,g,h):C.caml_call_gen(a,[b,c,d,e,f,g,h])}function
l0(a,b,c,d,e,f,g,h,i){return a.length==8?a(b,c,d,e,f,g,h,i):C.caml_call_gen(a,[b,c,d,e,f,g,h,i])}function
Iu(a,b,c,d,e,f,g,h,i,j){return a.length==9?a(b,c,d,e,f,g,h,i,j):C.caml_call_gen(a,[b,c,d,e,f,g,h,i,j])}function
It(a,b,c,d,e,f,g,h,i,j,k,l){return a.length==11?a(b,c,d,e,f,g,h,i,j,k,l):C.caml_call_gen(a,[b,c,d,e,f,g,h,i,j,k,l])}var
p=C.caml_get_global_data(),b5=[0,0,0],f$=[0,0],kc=Is([[0,c(y),[0,c("Lists"),[0,c("List"),0]]],[0,c(y),[0,c(J),[0,c(al),0]]],[0,c(y),[0,c(J),[0,c($),0]]],[0,c(y),[0,c(J),[0,c("DeclConstant"),0]]],[0,c(y),[0,c(J),[0,c(bY),0]]],[0,c(y),[0,c(J),[0,c(mP),0]]],[0,c(y),[0,c(J),[0,c(al),0]]],[0,c(y),[0,c(J),[0,c("RMicromega"),0]]],[0,c(y),[0,c(J),[0,c($),0]]],[0,c(y),[0,c(J),[0,c(bY),0]]],[0,c(y),[0,c(J),[0,c(mP),0]]],[0,c(y),[0,c(l4),[0,c("QArith_base"),0]]],[0,c(y),[0,c(dL),[0,c(mX),0]]],[0,c(y),[0,c(dL),[0,c(ml),0]]],[0,c("LRing_normalise"),0]]),ax=c("micromega_plugin"),he=[0,0],bj=[0,1],lo=c(" \t\n\r"),lp=c(",;"),lq=c("()[]{}"),lr=c("\\!@#$%^&*-+|\\<=>/?~.:"),ls=c("'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"),lt=c("0123456789"),lM=[0,1],hv=c("axtol=1.0e-8\natytol=1.0e-8\nobjtol=1.0e-8\npinftol=1.0e8\ndinftol=1.0e8\nmaxiter=100\nminstepfrac=0.9\nmaxstepfrac=0.97\nminstepp=1.0e-8\nminstepd=1.0e-8\nusexzgap=1\ntweakgap=0\naffine=0\nprintlevel=1\n"),d=p.Num,k=p.Stdlib__printf,e=p.Stdlib,N=p.Unix,d9=p.Stdlib__marshal,d4=p.Stdlib__printexc,f=p.Stdlib__list,l=p.Big_int,aV=p.Assert_failure,dd=p.Ratio,f6=p.Stdlib__set,b6=p.Stdlib__map,bb=p.Stdlib__hashtbl,L=p.Not_found,m=p.Util,cb=p.CErrors,aY=p.Option,jJ=p.Invalid_argument,bC=p.Stdlib__filename,gL=p.CList,j9=p.CamlinternalLazy,j8=p.End_of_file,bS=p.Names,j=p.EConstr,aZ=p.Tacmach,M=p.Tacticals,bh=p.Pp,cJ=p.Proofview,k0=p.CAst,aF=p.Tactics,e6=p.Failure,kQ=p.Context,kC=p.Retyping,kK=p.Evd,dt=p.Coqlib,ds=p.Goptions,ay=p.Ltac_plugin__Tacinterp,aG=p.Ltac_plugin__Tacentries,e9=p.Stdarg,aa=p.Genarg,az=p.Ltac_plugin__Tacarg,a9=p.Stdlib__string,tD=p.CMap,B$=p.Coq_config,Cd=p.Envars,A2=p.Stdlib__array,A1=p.Sorts,AI=p.Redexpr,At=p.UnivProblem,Au=p.Univ,Al=p.Reductionops,z7=p.Typeclasses,wz=p.UnivGen,B9=p.System,CX=p.Mltop,EI=p.Sys_error;aA(976,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],"Micromega_plugin");var
m_=[0,1],m5=[0,[12,91,[2,0,0]],c("[%s")],m9=c("]-oo"),m6=c(mL),m7=[0,[2,0,[12,93,0]],c("%s]")],m8=c("+oo["),oB=[0,0],oO=[0,0,0],oP=[0,[0,0],0],oU=[0,[0,0],0],oV=[0,0,0],oS=[0,[0,0],0],oT=[0,0,0],oH=[0,[0,0],0],oI=[0,0,0],oF=[0,[0,0],0],oG=[0,0,0],oz=[0,1],oA=[0,0],oy=[0,0],ow=[0,0,1,0],oq=[0,0],op=[0,0],oo=[0,0],og=[0,[0,0]],oh=[0,[0,0]],oi=[0,[0,0]],oj=[0,[0,0]],oc=[0,[0,0]],od=[0,[0,0]],oe=[0,[0,0]],of=[0,[0,0]],nV=[0,[0,0],0],nU=[0,0,0],nO=[0,1],nP=[0,2],nQ=[0,3],nJ=[0,0],nL=[0,0],nK=[0,1],nN=[0,3],nM=[0,0],nI=[0,0,0],no=[0,[1,0]],np=[0,0,[0,0]],nq=[0,[0,0],0],nr=[0,0],ns=[0,[1,0]],nt=[0,[1,0]],nu=[0,0],nv=[0,[1,0]],nw=[0,[1,0]],nx=[0,[1,0]],ny=[0,0],nz=[0,[1,0]],nA=[0,0,0],nB=[0,0,0],nC=[0,0],nD=[0,0,0],nE=[0,0],nj=[1,0],ni=[0,0],nb=[1,0],nc=[1,0],nd=[0,0],nf=[0,0],ne=[0,0],n0=[0,0],oa=[0,0],ou=[0,0],oD=[0,[0,0],0],oE=[0,0,0],oJ=[0,0,0],oK=[0,0,0],oL=[0,[0,0],0],oM=[0,0,0],oQ=[0,[0,0],0],oR=[0,0,0],oW=[0,0,0],oX=[0,0,0],qv=[0,[11,c(fu),[2,0,[11,c(mn),[4,3,0,0,0]]]],c('command "%s" exited %i')],qu=[0,[11,c(fu),[2,0,[11,c(mn),[2,0,0]]]],c('command "%s" exited %s')],qw=[0,[11,c(fu),[2,0,[11,c('" killed '),[4,3,0,0,0]]]],c('command "%s" killed %i')],qx=[0,[11,c(fu),[2,0,[11,c('" stopped '),[4,3,0,0,0]]]],c('command "%s" stopped %i')],qi=[0,c("_vendor+v8.10+64bit/coq/plugins/micromega/mutils.ml"),262,7],qe=[0,0,0],qd=[0,0,0],qb=[0,0,0],pz=[0,[4,3,0,0,[12,32,0]],c("%i ")],qG=[0,[15,[11,c(cQ),[15,0]]],c(hL)],qH=c(hO),qO=c(l6),qP=c(l6),qS=[0,0],qT=[0,0],q1=[0,0],q2=[0,0],q_=[0,1],q7=[0,0],q6=[0,c("_vendor+v8.10+64bit/coq/plugins/micromega/vect.ml"),285,16],q3=[0,[0,0,[0,0]],0],qZ=[0,0],qY=[0,0],qX=[0,0],qU=[0,1],qV=[0,1],qR=[0,1],qQ=[0,0],qN=[0,0],qM=[0,0],qK=[0,[15,[12,32,0]],c("%a ")],qL=[0,[11,c("(+ "),[15,[12,41,0]]],c("(+ %a)")],qI=[0,[12,ft,[4,3,0,0,0]],c(mZ)],qC=[0,0],qD=[0,[2,0,0],c(fv)],qF=[0,[11,c("(- "),[15,[12,41,0]]],c("(- %a)")],qE=[0,[11,c("(* "),[2,0,[12,32,[15,[12,41,0]]]]],c("(* %s %a)")],qy=[0,0],qz=[0,[2,0,0],c(fv)],qB=[0,[12,45,[15,0]],c(me)],qA=[0,[2,0,[12,42,[15,0]]],c(mI)],td=c("pivot: equality as second argument"),te=[0,1],tf=[0,-1],tc=[0,1,0,0],s_=[0,0],s$=[0,-1],ta=c("cutting_plane ignore strict constraints"),s8=[0,0],s3=[0,[15,[12,10,0]],c("%a\n")],s1=[0,[15,[12,32,[2,0,[11,c(" 0 by "),[15,[12,10,0]]]]]],c("%a %s 0 by %a\n")],so=[0,[11,c(l_),0],c(l_)],sp=[0,[12,40,[15,[12,41,[12,64,[2,0,0]]]]],c("(%a)@%s")],sq=[0,[11,c("Hyp "),[4,3,0,0,0]],c("Hyp %i")],sr=[0,[11,c("Def "),[4,3,0,0,0]],c("Def %i")],ss=[0,[11,c("Cst "),[2,0,0]],c("Cst %s")],st=[0,[12,40,[15,[11,c(ms),0]]],c(md)],su=[0,[12,40,[15,[11,c(mw),[15,[12,41,0]]]]],c(mv)],sv=[0,[12,40,[15,[11,c(")/"),[2,0,0]]]],c("(%a)/%s")],sw=[0,[12,40,[15,[11,c(mw),[15,[12,41,0]]]]],c(mv)],sx=[0,[15,[11,c(cQ),[15,0]]],c(hL)],sy=[0,[12,91,[15,[12,93,0]]],c("[%a]")],sz=[0,[12,46,0],c(mS)],sA=[0,[4,3,0,0,[11,c(":= "),[15,[11,c(" ; "),[15,0]]]]],c("%i:= %a ; %a")],sB=c(";"),sC=[0,[4,3,0,0,[12,123,[15,[11,c(l3),[15,[11,c(l3),[15,[12,125,[15,0]]]]]]]]],c("%i{%a<=%a<=%a}%a")],sE=[0,1],sF=[0,1],sD=[0,0],sG=[0,c("_vendor+v8.10+64bit/coq/plugins/micromega/polynomial.ml"),695,14],sH=[0,1],sK=[0,1],sJ=[0,1],sI=[0,1],sR=[0,0],sS=c("eval_prf_rule : negative constant"),sT=[0,[11,c("MulC("),[15,[12,44,[15,[11,c(") invalid 2d arg "),[15,[12,32,[2,0,0]]]]]]]],c("MulC(%a,%a) invalid 2d arg %a %s")],sU=c("eval_prf_rule : not an equality"),sX=c("Proof is not finished"),sY=[0,[11,c("Last inference "),[15,[12,32,[2,0,[12,10,0]]]]],c("Last inference %a %s\n")],sZ=c("Not implemented"),sV=[0,0],sP=c("Cuts should already be compiled"),sM=[0,[4,3,0,0,[12,44,[2,0,0]]],c("%i,%s")],sN=c(aK),sO=[0,[11,c("id_of_hyp "),[4,3,0,0,[12,32,[2,0,0]]]],c("id_of_hyp %i %s")],sl=[0,[11,c("(H"),[4,3,0,0,[11,c(mg),[15,[12,32,[2,0,[11,c(" 0)\n"),0]]]]]]],c("(H%i : %a %s 0)\n")],sj=[0,[11,c("(x"),[4,3,0,0,[11,c(mg),[2,0,[11,c(") "),0]]]]],c("(x%i : %s) ")],sk=[0,[11,c("forall "),[15,[12,10,0]]],c("forall %a\n")],sm=[0,[11,c(m0),0],c(m0)],sg=[0,0],sd=[0,[12,mE,[4,3,0,0,0]],c("v%i")],sb=[0,1],sc=[0,0],sa=[0,0],r$=[0,1],r9=[0,1],r7=[0,[15,[12,32,[2,0,[12,32,[2,0,0]]]]],c("%a %s %s")],r3=c(ma),r4=c(">="),r5=c(">"),r0=[0,0],r1=[0,0],rY=[0,0],rX=[0,1],rV=[0,0],rU=[0,[15,[11,c(cQ),0]],c("%a + ")],rQ=[0,0],rR=[0,[2,0,0],c(fv)],rT=[0,[12,45,[15,0]],c(me)],rS=[0,[2,0,[12,42,[15,0]]],c(mI)],re=[0,[15,[12,42,[15,0]]],c("%a*%a")],rc=[0,[12,ft,[4,3,0,0,0]],c(mZ)],rd=[0,[12,ft,[4,3,0,0,[12,94,[4,3,0,0,0]]]],c("x%i^%i")],r2=c("Micromega_plugin.Polynomial.Strict"),s4=c("Micromega_plugin.Polynomial.WithProof.InvalidProof"),tj=[0,[12,72,[4,3,0,0,0]],c("H%i")],tk=[0,[11,c("E("),[4,3,0,0,[12,44,[15,[12,44,[15,[12,41,0]]]]]]],c("E(%i,%a,%a)")],tl=[0,[11,c("A("),[15,[12,44,[15,[12,41,0]]]]],c("A(%a,%a)")],t9=[0,1],t_=[0,[0,0,0]],t6=c("merge_proof : pivot is not possible"),t7=[0,1],t8=[0,1],t5=[0,0],tZ=[0,1],t0=[0,1],t1=[0,1],t2=[0,1],t3=[0,1],t4=[0,1],tV=[0,0],tW=[0,-1],tX=[0,[11,c("optimise Exception : "),[2,0,0]],c("optimise Exception : %s")],tL=[0,0],tM=[0,0],tN=[0,0],tO=[0,0],tP=[0,0],tQ=[0,0],tR=[0,0],tS=[0,0],tI=[0,[11,c("bound_of_variable: eval_vecr "),[15,[11,c(" = "),[2,0,[12,44,[15,[12,10,0]]]]]]],c("bound_of_variable: eval_vecr %a = %s,%a\n")],tJ=[0,[11,c("current interval:  "),[15,[12,10,0]]],c("current interval:  %a\n")],tK=c("bound_of_variable: impossible"),tH=[0,0,0],tF=[0,0,0],tG=c("SystemContradiction"),tE=[0,0],tB=[0,0],tA=[0,0,0,0],tu=[0,0],tv=[0,0],ty=[0,c(hS),200,4],tw=[0,1],tx=[0,1],ts=[0,c(hS),151,6],tr=[0,0,0],tq=[0,0],tn=[0,c(hS),95,4],ti=c("Micromega_plugin.Mfourier.SystemContradiction"),tp=c("Micromega_plugin.Mfourier.TimeOut"),ud=[0,0],ue=c("find_pivot_column"),uP=[0,1],uQ=[0,0],uM=[0,1],uN=[0,1],uO=[0,1],uH=[0,0],uI=[0,2],uJ=[0,1],uK=[0,1],uL=[0,1],uR=[0,1],uG=[0,0],uF=[0,0],uE=[0,1],uB=[0,1],uA=[0,-1],uv=[0,0],uw=c("push_real"),ux=[0,-1],uy=[0,0],uz=[0,1],uu=[0,0],ut=c(mt),uq=[0,0],up=c("pivot"),um=[0,0],un=[0,0],uo=[0,1],uh=[0,0],ui=c("Cannot solve column"),uj=[0,-1],uk=[0,0],ul=[0,-1],ug=c(mt),uf=[0,0],ub=[0,0],t$=[0,[11,c("Cannot restrict "),[4,3,0,0,0]],c("Cannot restrict %i")],uC=c("Micromega_plugin.Simplex.FoundVar"),uS=c(hO),uT=[0,[12,mE,[2,0,0]],c("v%s")],uU=[0,[11,c("- ("),[15,[12,41,0]]],c("- (%a)")],uV=[0,[12,40,[15,[11,c(")+("),[15,[12,41,0]]]]],c("(%a)+(%a)")],uW=[0,[12,40,[15,[11,c(")-("),[15,[12,41,0]]]]],c("(%a)-(%a)")],uX=[0,[12,40,[15,[11,c(")*("),[15,[12,41,0]]]]],c("(%a)*(%a)")],uY=[0,[12,40,[15,[11,c(")^("),[4,3,0,0,[12,41,0]]]]],c("(%a)^(%i)")],uZ=[0,[11,c("Aeq("),[4,3,0,0,[12,41,0]]],c("Aeq(%i)")],u0=[0,[11,c("Ale("),[4,3,0,0,[12,41,0]]],c("Ale(%i)")],u1=[0,[11,c("Alt("),[4,3,0,0,[12,41,0]]],c("Alt(%i)")],u2=[0,[11,c("eq("),[2,0,[12,41,0]]],c("eq(%s)")],u3=[0,[11,c("le("),[2,0,[12,41,0]]],c("le(%s)")],u4=[0,[11,c("lt("),[2,0,[12,41,0]]],c("lt(%s)")],u5=[0,[12,40,[15,[11,c(ms),0]]],c(md)],u6=[0,[11,c(mW),0],c(mW)],u7=[0,[15,[11,c(mH),[15,0]]],c(mr)],u8=[0,[15,[11,c(cQ),[15,0]]],c(hL)],u9=[0,[15,[11,c(mH),[15,0]]],c(mr)],vy=c("scale term: not implemented"),vz=[0,0],vD=[0,0],v4=c("nia"),v3=c(mx),vV=c(".v"),vW=[0,[11,c(mV),0],c(mV)],vX=c(mQ),vY=[0,[11,c("Goal "),[15,[11,c(".\n"),0]]],c("Goal %a.\n")],v0=[0,[11,c("Proof.\n intros. "),[2,0,[11,c(".\nQed.\n"),0]]],c("Proof.\n intros. %s.\nQed.\n")],vZ=[0,[11,c("Proof.\n intros. Fail "),[2,0,[11,c(".\nAbort.\n"),0]]],c("Proof.\n intros. Fail %s.\nAbort.\n")],vQ=[0,c(fw),922,4],vR=[0,0],vS=[0,1],vT=[0,c(fw),951,4],vM=[0,1],vN=[0,0,0],vO=c("Interval without proof"),vJ=[0,1],vK=[0,-1],vE=[0,0],vF=[0,1],vC=[0,0],vA=[0,1],vB=[0,0],vx=c("P"),vw=[0,1],vt=[0,1],vu=[0,-1],vp=[0,1],vq=[0,c(fw),339,11],vr=c("check_sat : Unexpected operator"),vs=[0,0],vn=[0,c(fw),302,14],vk=[0,0],vl=c("dual_raw_certificate: empty_certificate"),vh=[0,1],vg=[0,0],va=[0,0],vd=[0,[0,0],0],ve=[0,0,0],vo=c("Micromega_plugin.Certificate.FoundProof"),v$=[0,0,0],v9=[0,0,0],v7=[0,0,[0,5,0]],v_=[0,1,[0,4,[0,5,0]]],v8=[0,1,[0,6,[0,5,0]]],v5=c("Micromega_plugin.Persistent_cache.PHashtable(Key).InvalidTableFormat"),v6=c("Micromega_plugin.Persistent_cache.PHashtable(Key).UnboundTable"),Bn=[0,[12,68,0],c(mB)],Bo=[0,[11,c("R["),[15,[12,44,[15,[12,93,0]]]]],c("R[%a,%a]")],Bp=[0,[11,c("C["),[15,[12,44,[15,[12,93,0]]]]],c("C[%a,%a]")],Bq=c("]"),Br=c("["),Bs=[0,[11,c("EP["),[15,[12,44,[15,[12,44,[15,[12,93,0]]]]]]],c("EP[%a,%a,%a]")],BD=c("abstract_wrt_formula"),CW=c("Not ground"),CM=c(hU),CL=c(hU),CK=c(hU),CE=c(hP),CD=c(hP),CC=c(hP),Ch=c(mi),Cg=c(mi),Ca=c("csdpcert"),Cb=c(J),Cc=c("plugins"),B4=c(l5),B5=[0,0],B3=c(hQ),BX=c(mR),BY=c(mo),BZ=c(mf),B0=c(mF),B1=c(mq),B2=c(mA),BR=c(mG),BS=c(l2),BT=[0,[0,c(y),[0,c(J),[0,c(aB),0]]],[0,[0,c(aB),0],0]],BU=c(aB),BV=c(mu),BW=c(m2),BM=c(hQ),BN=c(l5),BO=[0,0],BP=c(hQ),BG=c(mR),BH=c(mo),BI=c(mf),BJ=c(mF),BK=c(mq),BL=c(mA),BB=[0,[11,c(mh),0],c(mh)],BC=c("Cannot find compatible proof"),Bz=c("bad old index"),BA=c("proof compaction error"),By=[0,0],Bv=c(mG),Bw=c(mu),Bx=c(m2),Bm=[0,[15,[12,47,[15,0]]],c("%a/%a")],Bi=c(l2),Bj=[0,[0,c(y),[0,c(J),[0,c(aB),0]]],[0,[0,c(aB),0],0]],Bk=c(aB),Be=c("Empty"),Bf=[0,[0,c(y),[0,c(J),[0,c(aB),0]]],[0,[0,c(aB),0],0]],Bg=c(aB),Ba=c("Elt"),Bb=[0,[0,c(y),[0,c(J),[0,c(aB),0]]],[0,[0,c(aB),0],0]],Bc=c(aB),A8=c("Branch"),A9=[0,[0,c(y),[0,c(J),[0,c(aB),0]]],[0,[0,c(aB),0],0]],A_=c(aB),A7=[0,[11,c(m4),[4,3,0,0,0]],c(mK)],A6=[0,[11,c(m4),[4,3,0,0,0]],c(mK)],A5=[0,[11,c("__x"),[4,3,0,0,0]],c("__x%i")],A4=[0,c("_vendor+v8.10+64bit/coq/plugins/micromega/coq_micromega.ml"),1187,11],AV=c("error : parse_arith(2)"),AT=c("parse_qexpr parse error"),AR=[0,0],AO=[0,0,0],Av=c("get_rank"),Ar=[1,c("Oups")],Ap=c(m1),An=c(m1),Ae=[0,[12,48,0],c(hO)],Af=[0,[11,c("(In "),[15,[12,41,[12,37,[11,c(mj),0]]]]],c("(In %a)%%nat")],Ag=[0,[12,40,[15,[11,c("^2)"),0]]],c("(%a^2)")],Ah=[0,[11,c("( "),[15,[11,c(l$),[15,[12,41,0]]]]],c("( %a [*] %a)")],Ai=[0,[12,40,[15,[11,c(l$),[15,[12,41,0]]]]],c("(%a [*] %a)")],Aj=[0,[12,40,[15,[11,c(" [+] "),[15,[12,41,0]]]]],c("(%a [+] %a)")],Ak=[0,[12,40,[15,[12,41,[12,37,[11,c("positive"),0]]]]],c("(%a)%%positive")],Ab=[0,[11,c("Pc "),[15,0]],c("Pc %a")],Ac=[0,[11,c("Pinj("),[15,[12,44,[15,[12,41,0]]]]],c("Pinj(%a,%a)")],Ad=[0,[11,c("PX("),[15,[12,44,[15,[12,44,[15,[12,41,0]]]]]]],c("PX(%a,%a,%a)")],z_=[0,[15,[11,c(" ,"),[15,0]]],c("%a ,%a")],z$=[0,[15,0],c("%a")],Aa=[0,[2,0,[15,[2,0,0]]],c("%s%a%s")],z8=[0,[2,0,0],c(fv)],z6=[0,[4,3,0,0,0],c(l1)],z5=[0,[4,3,0,0,0],c(l1)],z0=c("Formula"),z1=[0,[0,c(y),[0,c(J),[0,c(bY),0]]],[0,[0,c(bY),0],0]],z2=c(bY),zW=c("Build_Formula"),zX=[0,[0,c(y),[0,c(J),[0,c(bY),0]]],[0,[0,c(bY),0],0]],zY=c(bY),zT=c("QWitness"),zU=[0,[0,c(y),[0,c(J),[0,c(mb),0]]],0],zV=c(mb),zQ=c("BFormula"),zR=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zS=c(al),zM=c("I"),zN=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zO=c(al),zI=c("X"),zJ=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zK=c(al),zE=c("A"),zF=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zG=c(al),zA=c("N"),zB=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zC=c(al),zw=c(mB),zx=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zy=c(al),zs=c("Cj"),zt=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zu=c(al),zo=c("FF"),zp=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zq=c(al),zk=c("TT"),zl=[0,[0,c(y),[0,c(J),[0,c($),0]]],[0,[0,c($),0],0]],zm=c(al),zi=c("GT"),zg=c(l8),ze=c("PsatzC"),zc=c("PsatzAdd"),za=c("PsatzMulC"),y_=c("PsatzMulE"),y8=c("PsatzSquare"),y6=c("PsatzIn"),y4=c("OpGt"),y2=c("OpGe"),y0=c("OpLt"),yY=c("OpLe"),yW=c("OpNEq"),yU=c("OpEq"),yS=c("Pinj"),yQ=c("Pc"),yO=c("PX"),yM=c("PEpow"),yK=c("PEsub"),yI=c("PEmul"),yG=c("PEopp"),yE=c("PEadd"),yC=c("PEc"),yA=c("PEX"),yz=c("Q2R"),yy=c("IZR"),yw=c("powerRZ"),yv=c("pow"),yu=c("Rinv"),yt=c("Rmult"),ys=c("Ropp"),yr=c("Rminus"),yq=c("Rplus"),yo=c("Rlt"),ym=c("Rle"),yk=c("Rge"),yi=c("Rgt"),yh=c("Qpower"),yg=c("Qmult"),yf=c("Qopp"),ye=c("Qminus"),yd=c("Qplus"),yb=c("Qeq"),x$=c("Qlt"),x9=c("Qle"),x8=c("Z.pow"),x7=c("Z.mul"),x6=c("Z.opp"),x5=c("Z.sub"),x4=c("Z.add"),x3=c("eq"),x1=c("Z.lt"),xZ=c("Z.le"),xX=c("Z.ge"),xV=c("Z.gt"),xT=c("EnumProof"),xR=c("CutProof"),xP=c("RatProof"),xN=c("DoneProof"),xM=c("ZArithProof"),xL=c("R1"),xK=c("R0"),xI=c("COpp"),xG=c("CInv"),xE=c("CPow"),xC=c("CMult"),xA=c("CMinus"),xy=c("CPlus"),xw=c("CZ"),xu=c("CQ"),xs=c("C1"),xq=c("C0"),xp=c("Rcst"),xo=c("Qmake"),xn=c("R"),xm=c("Q"),xk=c("Zneg"),xi=c("Zpos"),xg=c("Z0"),xf=c(mQ),xd=c("xI"),xb=c("xO"),w$=c("xH"),w9=c("Npos"),w7=c("N0"),w5=c("inr"),w3=c("inl"),w1=c("tt"),wZ=c("None"),wY=c("unit"),wX=c(mj),wV=c("S"),wT=c("O"),wS=c("list"),wQ=c("nil"),wO=c("cons"),wN=c("False"),wM=c("True"),wK=c("iff"),wJ=c("not"),wI=c("or"),wH=c("and"),wa=c(aK),wc=[0,c(hT),[0,c("Enum"),0]],wd=c("Lia Enum"),wg=[0,c("Simplex"),0],wh=c("Use the Simplex instead of Fourier elimination"),wk=[0,c("Dump"),[0,c("Arith"),0]],wl=c("Generate Coq goals in file from calls to 'lia' 'nia'"),wn=[0,c("Lra"),[0,c(mO),0]],wp=[0,c(hT),[0,c(mO),0]],wr=[0,c(y),[0,c("Logic"),[0,c("Decidable"),0]]],ww=[0,[0,c(y),[0,c("Numbers"),[0,c("BinNums"),0]]],0],wx=[0,[0,c(y),[0,c(dL),[0,c(mX),0]]],[0,[0,c(y),[0,c(dL),[0,c(ml),0]]],[0,[0,c(y),[0,c(dL),[0,c("Raxioms"),0]]],[0,[0,c(y),[0,c(l4),[0,c("Qreals"),0]]],0]]]],wy=[0,[0,c(y),[0,c("ZArith"),[0,c("BinInt"),0]]],0],wB=c(al),wC=c(al),wD=c(al),wE=c(al),wF=c(al),wG=c(al),z3=c("Micromega_plugin.Coq_micromega.M.ParseError"),BE=c("Micromega_plugin.Coq_micromega.CsdpNotFound"),B7=c(".csdp.cache"),B8=c("csdp"),Ck=c(".lia.cache"),Cn=c(".nia.cache"),Cq=c(".nra.cache"),Cu=c(mN),Cy=c(mN),CB=c("nra"),CF=c(mx),CH=c("nlia"),CN=c(hE),CQ=c(hE),CT=c(hE),CZ=[0,c("myred"),0],C1=c("RED"),C4=c("is_ground"),C6=c("ISGROUND"),C9=c(mk),Db=c(mk),Dd=c(l8),Dg=c("xlia"),Di=c(hT),Dl=c("xnlia"),Dn=c("Nia"),Dq=c("xnra"),Ds=c("NRA"),Dv=c("xnqa"),Dx=c("NQA"),DA=c("sos_Z"),DC=c("Sos_Z"),DF=c("sos_Q"),DH=c("Sos_Q"),DK=c("sos_R"),DM=c("Sos_R"),DP=c("lra_Q"),DR=c("LRA_Q"),DU=c("lra_R"),DW=c("LRA_R"),DZ=c(mT),D3=c(mT),D5=c("PsatzR"),D8=c(mm),Ea=c(mm),Ec=c("PsatzQ"),Ei=c("end_itlist"),Ek=c("tryfind"),Em=c("choose: completely undefined function"),EK=c(aJ),EJ=c("strings_of_file: can't open "),EF=c(" expected"),En=c("apply"),Ej=c(aK),Ee=[0,2],Ef=[0,10],Eo=c("Micromega_plugin.Sos_lib.Noparse"),EM=c("Micromega_plugin.Sos_lib.TooDeep"),Ff=[0,1],HU=[0,0,0],Ir=[0,0],Ip=[0,0],Iq=[0,0],In=[0,1],Ik=[0,1],Il=[0,2],Ij=[0,0,0],Ih=[0,1],Ii=[0,-1],Im=[0,0,0],Io=[0,0,0],If=c(mC),Ig=c(l7),H8=c(hF),H9=c(hJ),H_=c(hK),H$=c(hI),Ia=c(aK),Ie=c(hN),Ib=c(ar),Ic=c(hH),Id=c(hM),H2=c(aK),H3=c(aJ),H4=c(mJ),H5=c(aJ),H6=c(hD),H7=c(hR),HZ=c(aJ),H0=c(ar),H1=c(ar),HX=c(m3),HY=c(aK),HV=c(aJ),HW=c(ar),HO=[0,0],HM=[0,0],HN=[0,0],HL=[0,1],HH=[0,1],HI=[0,2],HG=[0,1],HJ=[0,0,0,0],HK=[0,0,0,0],HP=[0,-1],HQ=[0,0,0,0],HD=[0,0],HB=[0,0],Hy=c(mC),Hz=c(l7),Hp=c(hF),Hq=c(hJ),Hr=c(hK),Hs=c(hI),Ht=c(aK),Hx=c(hN),Hu=c(ar),Hv=c(hH),Hw=c(hM),Hi=c(aK),Hj=c(aJ),Hk=c(ar),Hl=c(aJ),Hm=c(aJ),Hn=c(hD),Ho=c(hR),He=c(aJ),Hf=c(ar),Hg=c(ar),Hh=c(ar),Hc=c(ar),Hd=c(aK),Hb=[0,0,0,0],G8=[0,0],G9=[0,1],G7=[0,0],G_=[0,0],G$=[0,1],Ha=[0,1],G3=[0,0],G4=c(my),G5=[0,0],G6=c(my),G2=c("diagonalize: non-square matrix"),G1=[0,0,0],GZ=[0,0],G0=[0,0],GY=[0,-1],GX=c("choose_variable"),GW=[0,0],GV=[0,0],GU=[0,0],GS=[0,c("_vendor+v8.10+64bit/coq/plugins/micromega/sos.ml"),533,12],GR=[0,1],GQ=c("linear_program: An error occurred in the SDP solver"),GM=[0,1],GN=[0,1],GO=[0,0],GP=[0,0],GD=c(hF),GE=c(hJ),GF=c(hK),GG=c(hI),GH=c(aK),GL=c(hN),GI=c(ar),GJ=c(hH),GK=c(hM),Gi=[0,0,0],Gd=c("mkparser: unparsed input"),F$=[0,10],FZ=c("+"),F0=c(mp),FC=c(aK),FD=c(aJ),FE=c(mJ),FF=c(aJ),FG=c(hD),FH=c(hR),Fz=c(aJ),FA=c(ar),FB=c(ar),Fx=c(m3),Fy=c(aK),Fv=c(aJ),Fw=c(ar),Fo=[0,0],Fp=c(" - "),Fq=c(cQ),Fm=c("<<0>>"),Fn=c(aK),Fr=c(">>"),Fs=c(cQ),Fu=c(mp),Ft=c("<<"),Fj=[0,1],Fk=c(mz),Fh=c("1"),Fi=c(mz),Fg=c("^"),Fe=[0,0],Fd=[0,0],Fc=[0,0],Fb=[0,0],Fa=[0,1],E8=[0,0],E7=c("matrix_add: incompatible dimensions"),E6=[0,0],E4=[0,0],E3=[0,0],E2=[0,0],E1=[0,0],EO=[0,10],EP=[0,1],EQ=[0,10],ER=[0,1],ES=[0,10],ET=[0,0],EU=c("0.0"),EV=[0,1],EW=c(aK),E0=c(mY),EX=[0,0],EY=c("-0."),EZ=c("0."),EN=c("Micromega_plugin.Sos.Sanity"),FS=c(mS),F3=c("E"),F5=c(mY),Ge=c("}"),Gf=c(mL),Gg=c("{"),Gj=c(ma),Gk=c("xVec"),Gn=c(aJ),Gp=c(ar),Gv=c(ar),HE=[0,-1];function
hV(c,f){var
h=f[2],i=f[1];if(i){var
j=b(d[40],i[1]);g(k[1],c,m5,j)}else
a(e[55],c,m9);a(e[55],c,m6);if(h){var
l=b(d[40],h[1]);return g(k[1],c,m7,l)}return a(e[55],c,m8)}function
fx(b){var
c=b[1];if(c){var
e=b[2];if(e)return a(d[29],c[1],e[1])?[0,b]:0}return[0,b]}function
fy(c,b){var
f=b[2],g=b[1],h=c[2],i=c[1];function
e(d,c,b){if(c){var
e=c[1];return b?[0,a(d,e,b[1])]:c}return b?b:0}var
j=e(d[39],h,f);return fx([0,e(d[38],i,g),j])}function
dM(c){var
e=c[1];if(e){var
f=c[2];if(f){var
g=f[1],h=b(d[24],e[1]),i=b(d[22],g),j=a(d[4],i,h);return[0,a(d[1],j,m_)]}}return 0}function
hW(f,e){var
b=dM(f),c=dM(e);return b?c?a(d[29],b[1],c[1]):1:0}function
fz(e,b){var
c=e[2],f=e[1];if(f){var
g=f[1];if(c){var
i=c[1],h=a(d[29],g,b);return h?a(d[29],b,i):h}return a(d[29],g,b)}return c?a(d[29],b,c[1]):1}aA(980,[0,hV,fy,dM,hW,fz,fx],"Micromega_plugin__Itv");function
bn(a){return 0===a?1:0}function
bL(a){return a[1]}function
m$(a){return a[2]}function
O(a,b){if(a){var
c=a[1];return[0,c,O(a[2],b)]}return b}function
hX(a){switch(a){case
0:return 0;case
1:return 2;default:return 1}}function
fA(b,a){return b?[0,fA(b[1],a)]:a}function
hY(e,d,c){var
b=e,a=d;for(;;){if(b){var
f=b[1];if(a){var
b=f,a=a[2];continue}return c}return a?a[1]:c}}function
ba(c,a){if(a){var
d=a[1],e=ba(c,a[2]);return[0,b(c,d),e]}return 0}function
dN(d,c,b){if(b){var
e=b[1];return a(d,e,dN(d,c,b[2]))}return c}var
na=[0];function
bo(a){return typeof
a==="number"?nb:0===a[0]?[1,bo(a[1])]:[0,a[1]]}function
co(b,a){if(typeof
b==="number")return typeof
a==="number"?nc:0===a[0]?[1,bo(a[1])]:[0,a[1]];else{if(0===b[0]){var
c=b[1];return typeof
a==="number"?[1,bo(c)]:0===a[0]?[1,cR(c,a[1])]:[0,co(c,a[1])]}var
d=b[1];return typeof
a==="number"?[0,d]:0===a[0]?[0,co(d,a[1])]:[1,co(d,a[1])]}}function
cR(b,a){if(typeof
b==="number")return typeof
a==="number"?nd:0===a[0]?[0,bo(a[1])]:[1,bo(a[1])];else{if(0===b[0]){var
c=b[1];return typeof
a==="number"?[0,bo(c)]:0===a[0]?[0,cR(c,a[1])]:[1,cR(c,a[1])]}var
d=b[1];return typeof
a==="number"?[1,bo(d)]:0===a[0]?[1,cR(d,a[1])]:[0,co(d,a[1])]}}function
cS(a){return typeof
a==="number"?0:0===a[0]?[0,[1,a[1]]]:[0,cS(a[1])]}function
cT(a){return typeof
a==="number"?0===a?ne:1:[0,[0,a[1]]]}function
cU(a){return typeof
a==="number"?a:[0,[1,a[1]]]}function
hZ(a){return typeof
a==="number"?0:0===a[0]?[0,[1,[1,a[1]]]]:[0,[1,cS(a[1])]]}function
cp(b,a){if(typeof
b==="number")return typeof
a==="number"?0:1;else{if(0===b[0]){var
c=b[1];return typeof
a==="number"?[0,[1,c]]:0===a[0]?cU(cp(c,a[1])):cT(cp(c,a[1]))}var
d=b[1];return typeof
a==="number"?[0,cS(d)]:0===a[0]?cT(cV(d,a[1])):cU(cp(d,a[1]))}}function
cV(b,a){if(typeof
b==="number")return 1;else{if(0===b[0]){var
c=b[1];return typeof
a==="number"?[0,cS(c)]:0===a[0]?cT(cV(c,a[1])):cU(cp(c,a[1]))}var
d=b[1];return typeof
a==="number"?hZ(d):0===a[0]?cU(cV(d,a[1])):cT(cV(d,a[1]))}}function
fB(c,b){var
a=cp(c,b);return typeof
a==="number"?0:a[1]}function
fC(b,a){return typeof
b==="number"?a:0===b[0]?co(a,[1,fC(b[1],a)]):[1,fC(b[1],a)]}function
cW(a){return typeof
a==="number"?nf:0===a[0]?[0,cW(a[1])]:[0,cW(a[1])]}function
h0(h,g,f){var
c=h,b=g,a=f;for(;;)if(typeof
b==="number")return typeof
a==="number"?c:1;else{if(0===b[0]){var
d=b[1];if(typeof
a==="number")return 2;else{if(0===a[0]){var
b=d,a=a[1];continue}var
c=2,b=d,a=a[1];continue}}var
e=b[1];if(typeof
a==="number")return 2;else{if(0===a[0]){var
c=1,b=e,a=a[1];continue}var
b=e,a=a[1];continue}}}var
ng=0;function
h1(a,b){return h0(ng,a,b)}function
fD(j,i,h){var
c=j,b=i,a=h;for(;;){if(c){var
d=c[1];if(typeof
b==="number")return 0;else{if(0===b[0]){var
e=b[1];if(typeof
a==="number")return 0;else{if(0===a[0]){var
f=a[1];switch(h1(e,f)){case
0:return b;case
1:var
c=d,a=b,b=fB(f,e);continue;default:var
c=d,b=fB(e,f);continue}}var
c=d,a=a[1];continue}}var
g=b[1];if(typeof
a==="number")return 0;else{if(0===a[0]){var
c=d,b=g;continue}return[1,fD(d,g,a[1])]}}}return 0}}function
nh(b,a){var
c=cW(a);return fD(fA(cW(b),c),b,a)}function
h2(a){return a?bo(h2(a[1])):0}var
u=[0,bo,co,cR,cS,cT,cU,hZ,cp,cV,fB,fC,cW,h0,h1,fD,nh,h2],h3=[0,function(a){return a?[0,b(u[17],a[1])]:0}];function
dO(b,d,c){if(typeof
c==="number")return d;else{if(0===c[0]){var
e=dO(b,d,c[1]);return a(b,d,a(b,e,e))}var
f=dO(b,d,c[1]);return a(b,f,f)}}function
fE(a){return typeof
a==="number"?0:0===a[0]?[0,[1,a[1]]]:[1,[1,a[1]]]}function
h4(a){return typeof
a==="number"?ni:0===a[0]?[0,[0,a[1]]]:[1,b(u[4],a[1])]}function
h5(a){return typeof
a==="number"?nj:0===a[0]?[0,b(u[4],a[1])]:[1,[0,a[1]]]}function
bZ(c,a){if(typeof
c==="number")return typeof
a==="number"?0:0===a[0]?[1,[1,a[1]]]:[1,b(u[4],a[1])];else{if(0===c[0]){var
d=c[1];return typeof
a==="number"?[0,[1,d]]:0===a[0]?fE(bZ(d,a[1])):h4(bZ(d,a[1]))}var
e=c[1];return typeof
a==="number"?[0,b(u[4],e)]:0===a[0]?h5(bZ(e,a[1])):fE(bZ(e,a[1]))}}function
bM(c,b){if(typeof
c==="number")return b;else{if(0===c[0]){var
d=c[1];return typeof
b==="number"?c:0===b[0]?[0,a(u[2],d,b[1])]:bZ(d,b[1])}var
e=c[1];return typeof
b==="number"?c:0===b[0]?bZ(b[1],e):[1,a(u[2],e,b[1])]}}function
b0(a){return typeof
a==="number"?0:0===a[0]?[1,a[1]]:[0,a[1]]}function
dP(b,a){return bM(b,b0(a))}function
b1(c,b){if(typeof
c==="number")return 0;else{if(0===c[0]){var
d=c[1];return typeof
b==="number"?0:0===b[0]?[0,a(u[11],d,b[1])]:[1,a(u[11],d,b[1])]}var
e=c[1];return typeof
b==="number"?0:0===b[0]?[1,a(u[11],e,b[1])]:[0,a(u[11],e,b[1])]}}function
cX(c,b){if(typeof
c==="number")return typeof
b==="number"?0:0===b[0]?1:2;else{if(0===c[0]){var
d=c[1];if(typeof
b!=="number"&&0===b[0])return a(u[14],d,b[1]);return 2}var
e=c[1];if(typeof
b!=="number"&&1===b[0])return hX(a(u[14],e,b[1]));return 1}}function
h6(b,a){return 2<=cX(b,a)?0:1}function
fF(b,a){return 1===cX(b,a)?1:0}function
nk(b,a){return 2<=cX(b,a)?1:0}function
nl(b,a){return 1===cX(b,a)?a:b}function
dQ(a){if(typeof
a!=="number"&&1===a[0])return[0,a[1]];return a}function
nm(a){if(typeof
a!=="number"&&0===a[0])return[0,a[1]];return 0}function
nn(a){return a?[0,b(u[17],a[1])]:0}function
b2(b,a){if(typeof
b==="number")return h6(no,a)?np:nq;else{if(0===b[0]){var
e=b2(b[1],a),f=e[1],c=bM(b1(ns,e[2]),nr);if(fF(c,a))return[0,b1(nt,f),c];var
i=dP(c,a);return[0,bM(b1(nv,f),nu),i]}var
g=b2(b[1],a),h=g[1],d=b1(nw,g[2]);if(fF(d,a))return[0,b1(nx,h),d];var
j=dP(d,a);return[0,bM(b1(nz,h),ny),j]}}function
h7(b,a){if(typeof
b==="number")return nA;else{if(0===b[0]){var
c=b[1];if(typeof
a==="number")return nB;else{if(0===a[0])return b2(c,a);var
d=b2(c,[0,a[1]]),e=d[2],f=d[1];if(typeof
e==="number")return[0,b0(f),0];var
l=bM(a,e);return[0,b0(bM(f,nC)),l]}}var
g=b[1];if(typeof
a==="number")return nD;else{if(0===a[0]){var
h=b2(g,a),i=h[2],j=h[1];if(typeof
i==="number")return[0,b0(j),0];var
m=dP(a,i);return[0,b0(bM(j,nE)),m]}var
k=b2(g,[0,a[1]]),n=k[1];return[0,n,b0(k[2])]}}}function
nF(b,a){return h7(b,a)[1]}var
o=[0,fE,h4,h5,bZ,bM,b0,dP,b1,cX,h6,fF,nk,nl,dQ,nm,nn,b2,h7,nF,function(c,b){if(typeof
c==="number")return dQ(b);else{if(0===c[0]){var
d=c[1];return typeof
b==="number"?dQ(c):0===b[0]?[0,a(u[16],d,b[1])]:[0,a(u[16],d,b[1])]}var
e=c[1];return typeof
b==="number"?dQ(c):0===b[0]?[0,a(u[16],e,b[1])]:[0,a(u[16],e,b[1])]}}];function
aL(c,b){return 0===a(o[9],c,b)?1:0}function
nG(a){return[0,a]}function
nH(a){return[0,a]}function
fG(d,f,e){var
c=f,b=e;for(;;)switch(c[0]){case
0:var
g=c[1];return 0===b[0]?a(d,g,b[1]):0;case
1:var
h=c[2],i=c[1];if(1===b[0]){var
j=b[2];if(0===a(u[14],i,b[1])){var
c=h,b=j;continue}return 0}return 0;default:var
k=c[3],l=c[2],m=c[1];if(2===b[0]){var
n=b[3],o=b[1];if(0===a(u[14],l,b[2])){if(fG(d,m,o)){var
c=k,b=n;continue}return 0}return 0}return 0}}function
ae(c,b){switch(b[0]){case
0:return b;case
1:var
d=b[2];return[1,a(u[2],c,b[1]),d];default:return[1,c,b]}}function
h8(a,c){return typeof
a==="number"?c:0===a[0]?[1,[1,a[1]],c]:[1,b(u[4],a[1]),c]}function
T(f,e,b,d,c){switch(b[0]){case
0:return a(e,b[1],f)?ae(0,c):[2,b,d,c];case
1:return[2,b,d,c];default:var
g=b[2],h=b[1];return fG(e,b[3],[0,f])?[2,h,a(u[2],g,d),c]:[2,b,d,c]}}function
h9(c,b,a){return[2,[0,b],a,[0,c]]}function
h_(b,a){return h9(b,a,0)}function
as(c,a){switch(a[0]){case
0:return[0,b(c,a[1])];case
1:var
d=a[1];return[1,d,as(c,a[2])];default:var
e=a[2],f=a[1],g=as(c,a[3]);return[2,as(c,f),e,g]}}function
bN(d,b,c){switch(b[0]){case
0:return[0,a(d,b[1],c)];case
1:var
e=b[1];return[1,e,bN(d,b[2],c)];default:var
f=b[2],g=b[1];return[2,g,f,bN(d,b[3],c)]}}function
cq(d,b,c){switch(b[0]){case
0:return[0,a(d,b[1],c)];case
1:var
e=b[1];return[1,e,cq(d,b[2],c)];default:var
f=b[2],g=b[1];return[2,g,f,cq(d,b[3],c)]}}function
cY(g,f,e,c,d){switch(d[0]){case
0:return ae(c,bN(g,e,d[1]));case
1:var
i=d[2],m=d[1],h=a(o[4],m,c);return typeof
h==="number"?ae(c,a(f,i,e)):0===h[0]?ae(c,a(f,[1,h[1],i],e)):ae(m,cY(g,f,e,h[1],i));default:var
j=d[3],k=d[2],l=d[1];return typeof
c==="number"?[2,l,k,a(f,j,e)]:0===c[0]?[2,l,k,cY(g,f,e,[1,c[1]],j)]:[2,l,k,cY(g,f,e,b(u[4],c[1]),j)]}}function
cZ(h,g,f,e,c,d){switch(d[0]){case
0:var
p=d[1];return ae(c,bN(h,as(g,e),p));case
1:var
j=d[2],n=d[1],i=a(o[4],n,c);return typeof
i==="number"?ae(c,a(f,j,e)):0===i[0]?ae(c,a(f,[1,i[1],j],e)):ae(n,cZ(h,g,f,e,i[1],j));default:var
k=d[3],l=d[2],m=d[1];return typeof
c==="number"?[2,m,l,a(f,k,e)]:0===c[0]?[2,m,l,cZ(h,g,f,e,[1,c[1]],k)]:[2,m,l,cZ(h,g,f,e,b(u[4],c[1]),k)]}}function
fH(f,g,j,d,e,c){switch(c[0]){case
0:return[2,d,e,c];case
1:var
k=c[2],h=c[1];return typeof
h==="number"?[2,d,e,k]:0===h[0]?[2,d,e,[1,[1,h[1]],k]]:[2,d,e,[1,b(u[4],h[1]),k]];default:var
l=c[3],m=c[2],n=c[1],i=a(o[4],m,e);return typeof
i==="number"?T(f,g,a(j,n,d),m,l):0===i[0]?T(f,g,a(j,[2,n,i[1],[0,f]],d),e,l):T(f,g,fH(f,g,j,d,i[1],n),m,l)}}function
fI(g,f,h,k,d,e,c){switch(c[0]){case
0:return[2,as(f,d),e,c];case
1:var
l=c[2],i=c[1];if(typeof
i==="number")return[2,as(f,d),e,l];else{if(0===i[0]){var
q=[1,[1,i[1]],l];return[2,as(f,d),e,q]}var
r=[1,b(u[4],i[1]),l];return[2,as(f,d),e,r]}default:var
m=c[3],n=c[2],p=c[1],j=a(o[4],n,e);return typeof
j==="number"?T(g,h,a(k,p,d),n,m):0===j[0]?T(g,h,a(k,[2,p,j[1],[0,g]],d),e,m):T(g,h,fI(g,f,h,k,d,j[1],p),n,m)}}function
ab(c,e,d,f,g){switch(g[0]){case
0:return bN(e,f,g[1]);case
1:var
r=g[2],s=g[1];return cY(e,function(a,b){return ab(c,e,d,a,b)},r,s,f);default:var
h=g[3],j=g[2],i=g[1];switch(f[0]){case
0:return[2,i,j,bN(e,h,f[1])];case
1:var
m=f[2],k=f[1];return typeof
k==="number"?[2,i,j,ab(c,e,d,m,h)]:0===k[0]?[2,i,j,ab(c,e,d,[1,[1,k[1]],m],h)]:[2,i,j,ab(c,e,d,[1,b(u[4],k[1]),m],h)];default:var
n=f[3],p=f[2],q=f[1],l=a(o[4],p,j);if(typeof
l==="number"){var
t=ab(c,e,d,n,h);return T(c,d,ab(c,e,d,q,i),p,t)}else{if(0===l[0]){var
v=l[1],w=ab(c,e,d,n,h);return T(c,d,ab(c,e,d,[2,q,v,[0,c]],i),j,w)}var
x=l[1],y=ab(c,e,d,n,h);return T(c,d,fH(c,d,function(a,b){return ab(c,e,d,a,b)},i,x,q),p,y)}}}}function
I(d,f,g,c,e,h,i){switch(i[0]){case
0:return cq(g,h,i[1]);case
1:var
t=i[2],v=i[1];return cZ(f,c,function(a,b){return I(d,f,g,c,e,a,b)},t,v,h);default:var
j=i[3],l=i[2],k=i[1];switch(h[0]){case
0:var
w=h[1],x=bN(f,as(c,j),w);return[2,as(c,k),l,x];case
1:var
p=h[2],m=h[1];if(typeof
m==="number"){var
y=I(d,f,g,c,e,p,j);return[2,as(c,k),l,y]}else{if(0===m[0]){var
z=I(d,f,g,c,e,[1,[1,m[1]],p],j);return[2,as(c,k),l,z]}var
A=I(d,f,g,c,e,[1,b(u[4],m[1]),p],j);return[2,as(c,k),l,A]}default:var
q=h[3],r=h[2],s=h[1],n=a(o[4],r,l);if(typeof
n==="number"){var
B=I(d,f,g,c,e,q,j);return T(d,e,I(d,f,g,c,e,s,k),r,B)}else{if(0===n[0]){var
C=n[1],D=I(d,f,g,c,e,q,j);return T(d,e,I(d,f,g,c,e,[2,s,C,[0,d]],k),l,D)}var
E=n[1],F=I(d,f,g,c,e,q,j);return T(d,e,fI(d,c,e,function(a,b){return I(d,f,g,c,e,a,b)},k,E,s),r,F)}}}}function
c0(f,e,d,b,c){switch(b[0]){case
0:return[0,a(e,b[1],c)];case
1:var
g=b[1];return ae(g,c0(f,e,d,b[2],c));default:var
h=b[2],i=b[1],j=c0(f,e,d,b[3],c);return T(f,d,c0(f,e,d,i,c),h,j)}}function
c1(d,g,f,c,e,b){return a(c,b,d)?[0,d]:a(c,b,g)?e:c0(d,f,c,e,b)}function
bp(f,j,i,e,g,d,c,h){switch(h[0]){case
0:return ae(c,c1(f,j,i,e,d,h[1]));case
1:var
l=h[2],q=h[1],k=a(o[4],q,c);return typeof
k==="number"?ae(c,a(g,l,d)):0===k[0]?ae(c,a(g,[1,k[1],l],d)):ae(q,bp(f,j,i,e,g,d,k[1],l));default:var
m=h[3],n=h[2],p=h[1];if(typeof
c==="number"){var
r=a(g,m,d);return T(f,e,bp(f,j,i,e,g,d,0,p),n,r)}else{if(0===c[0]){var
s=bp(f,j,i,e,g,d,[1,c[1]],m);return T(f,e,bp(f,j,i,e,g,d,c,p),n,s)}var
t=bp(f,j,i,e,g,d,b(u[4],c[1]),m);return T(f,e,bp(f,j,i,e,g,d,c,p),n,t)}}}function
am(a,e,f,d,c,g,h){switch(h[0]){case
0:return c1(a,e,d,c,g,h[1]);case
1:var
q=h[2],r=h[1];return bp(a,e,d,c,function(b,g){return am(a,e,f,d,c,b,g)},q,r,g);default:var
i=h[3],m=h[2],k=h[1];switch(g[0]){case
0:return c1(a,e,d,c,h,g[1]);case
1:var
l=g[2],j=g[1],s=typeof
j==="number"?am(a,e,f,d,c,l,i):0===j[0]?am(a,e,f,d,c,[1,[1,j[1]],l],i):am(a,e,f,d,c,[1,b(u[4],j[1]),l],i);return T(a,c,am(a,e,f,d,c,g,k),m,s);default:var
n=g[3],o=g[2],p=g[1],t=am(a,e,f,d,c,n,i),v=0,w=bp(a,e,d,c,function(b,g){return am(a,e,f,d,c,b,g)},i,v,p),x=am(a,e,f,d,c,ae(0,n),k),y=am(a,e,f,d,c,p,k),z=T(a,c,w,o,t);return ab(a,f,c,T(a,c,ab(a,f,c,T(a,c,y,o,[0,a]),x),m,[0,a]),z)}}}function
c2(b,e,g,f,c,d){switch(d[0]){case
0:var
h=d[1];return[0,a(f,h,h)];case
1:var
l=d[1];return[1,l,c2(b,e,g,f,c,d[2])];default:var
i=d[3],j=d[2],k=d[1],m=am(b,e,g,f,c,k,ae(0,c1(b,e,f,c,i,a(g,e,e)))),n=c2(b,e,g,f,c,i);return T(b,c,ab(b,g,c,T(b,c,c2(b,e,g,f,c,k),j,[0,b]),m),j,n)}}function
h$(c,b,a){return h8(a,h_(c,b))}function
c3(h,g,f,e,d,c,n,a,m){var
j=n,i=m;for(;;)if(typeof
i==="number")return b(c,am(h,g,f,e,d,j,a));else{if(0===i[0]){var
k=i[1];return b(c,am(h,g,f,e,d,c3(h,g,f,e,d,c,c3(h,g,f,e,d,c,j,a,k),a,k),a))}var
l=i[1],j=c3(h,g,f,e,d,c,j,a,l),i=l;continue}}function
ia(h,a,g,f,e,d,c,b){return b?c3(h,a,g,f,e,d,[0,a],c,b[1]):[0,a]}function
X(a,f,c,g,e,d,b,h){switch(h[0]){case
0:return[0,h[1]];case
1:return h$(a,f,h[1]);case
2:var
i=h[2],j=h[1];if(5===j[0]){var
m=X(a,f,c,g,e,d,b,j[1]);return I(a,c,e,d,b,X(a,f,c,g,e,d,b,i),m)}if(5===i[0]){var
l=X(a,f,c,g,e,d,b,i[1]);return I(a,c,e,d,b,X(a,f,c,g,e,d,b,j),l)}var
k=X(a,f,c,g,e,d,b,i);return ab(a,c,b,X(a,f,c,g,e,d,b,j),k);case
3:var
n=h[1],o=X(a,f,c,g,e,d,b,h[2]);return I(a,c,e,d,b,X(a,f,c,g,e,d,b,n),o);case
4:var
p=h[1],q=X(a,f,c,g,e,d,b,h[2]);return am(a,f,c,g,b,X(a,f,c,g,e,d,b,p),q);case
5:return as(d,X(a,f,c,g,e,d,b,h[1]));default:var
r=h[2],s=X(a,f,c,g,e,d,b,h[1]);return ia(a,f,c,g,b,function(a){return a},s,r)}}function
bq(c,a){if(typeof
a!=="number")switch(a[0]){case
0:return[0,b(c,a[1])];case
2:var
d=a[1],e=bq(c,a[2]);return[2,bq(c,d),e];case
3:var
f=a[1],g=bq(c,a[2]);return[3,bq(c,f),g];case
4:return[4,bq(c,a[1])];case
5:var
h=a[2],i=a[1],j=bq(c,a[3]);return[5,bq(c,i),h,j]}return a}function
c4(d,f,e){var
b=f,c=e;for(;;){if(typeof
b!=="number")switch(b[0]){case
1:return a(d,c,b[2]);case
2:var
g=b[1],h=c4(d,b[2],c),b=g,c=h;continue;case
3:var
i=b[1],j=c4(d,b[2],c),b=i,c=j;continue;case
4:var
b=b[1];continue;case
5:var
k=b[1],l=c4(d,b[3],c),b=k,c=l;continue}return c}}function
ib(b,a){return b?[0,b[1],a]:a}function
fJ(a){if(typeof
a!=="number"&&5===a[0]){var
b=a[2];return ib(b,fJ(a[3]))}return 0}function
b3(b){var
a=b;for(;;){if(typeof
a!=="number")switch(a[0]){case
1:return[0,a[2],0];case
2:var
c=a[1],d=b3(a[2]);return O(b3(c),d);case
3:var
e=a[1],f=b3(a[2]);return O(b3(e),f);case
4:var
a=a[1];continue;case
5:var
g=a[1],h=b3(a[3]);return O(b3(g),h)}return 0}}function
a1(c,a){if(typeof
a==="number")return 0===a?0:1;else
switch(a[0]){case
0:return[0,a[1]];case
1:var
d=a[2];return[1,b(c,a[1]),d];case
2:var
e=a[1],f=a1(c,a[2]);return[2,a1(c,e),f];case
3:var
g=a[1],h=a1(c,a[2]);return[3,a1(c,g),h];case
4:return[4,a1(c,a[1])];default:var
i=a[2],j=a[1],k=a1(c,a[3]);return[5,a1(c,j),i,k]}}var
b4=0;function
dR(e,d,c,f){if(f){var
h=f[2],g=f[1],i=a(d,c[1],g[1]);if(i){if(b(e,i[1]))return 0;var
j=dR(e,d,c,h);return j?[0,[0,g,j[1]]]:0}var
k=dR(e,d,c,h);return k?[0,[0,g,k[1]]]:0}var
l=a(d,c[1],c[1]);return l?b(e,l[1])?0:[0,[0,c,0]]:[0,[0,c,0]]}function
ic(g,f,e,d){var
a=e,b=d;for(;;){if(a){var
h=a[2],c=dR(g,f,a[1],b);if(c){var
a=h,b=c[1];continue}return 0}return[0,b]}}function
id(e,d,c,a){var
b=0;return dN(function(f,a){var
b=ic(e,d,c,f);return b?[0,b[1],a]:a},b,a)}function
c5(d,c,a,b){if(a){var
e=a[2],f=id(d,c,a[1],b);return O(c5(d,c,e,b),f)}return b4}function
aC(d,c,f,e,q,p){var
b=q,g=p;for(;;)if(typeof
g==="number")return 0===g?b?b4:b5:b?b5:b4;else
switch(g[0]){case
0:return b5;case
1:var
h=g[2],i=g[1];return b?a(f,i,h):a(e,i,h);case
2:var
j=g[2],k=g[1];if(b){var
r=aC(d,c,f,e,b,j);return O(aC(d,c,f,e,b,k),r)}var
s=aC(d,c,f,e,b,j);return c5(d,c,aC(d,c,f,e,b,k),s);case
3:var
l=g[2],m=g[1];if(b){var
t=aC(d,c,f,e,b,l);return c5(d,c,aC(d,c,f,e,b,m),t)}var
u=aC(d,c,f,e,b,l);return O(aC(d,c,f,e,b,m),u);case
4:var
v=g[1],b=bn(b),g=v;continue;default:var
n=g[3],o=g[1];if(b){var
w=aC(d,c,f,e,b,n);return c5(d,c,aC(d,c,f,e,bn(b),o),w)}var
x=aC(d,c,f,e,b,n);return O(aC(d,c,f,e,bn(b),o),x)}}function
dS(e,d,c,g){if(g){var
j=g[2],f=g[1],k=a(d,c[1],f[1]);if(k){if(b(e,k[1]))return[1,[0,c[2],[0,f[2],0]]];var
h=dS(e,d,c,j);return 0===h[0]?[0,[0,f,h[1]]]:[1,h[1]]}var
i=dS(e,d,c,j);return 0===i[0]?[0,[0,f,i[1]]]:[1,i[1]]}var
l=a(d,c[1],c[1]);return l?b(e,l[1])?[1,[0,c[2],0]]:[0,[0,c,0]]:[0,[0,c,0]]}function
ie(g,f,e,d){var
a=e,b=d;for(;;){if(a){var
h=a[2],c=dS(g,f,a[1],b);if(0===c[0]){var
a=h,b=c[1];continue}return[1,c[1]]}return[0,b]}}function
ig(g,f,e,a){return dN(function(h,b){var
c=b[2],d=b[1],a=ie(g,f,e,h);return 0===a[0]?[0,[0,a[1],d],c]:[0,d,O(c,a[1])]},nI,a)}function
c6(d,c,a,b){if(a){var
g=a[1],e=c6(d,c,a[2],b),h=e[2],i=e[1],f=ig(d,c,g,b),j=f[1],k=O(h,f[2]);return[0,O(i,j),k]}return[0,b4,0]}function
br(e,d,g,f,F,E){var
b=F,c=E;for(;;)if(typeof
c==="number")return 0===c?b?[0,b4,0]:[0,b5,0]:b?[0,b5,0]:[0,b4,0];else
switch(c[0]){case
0:return[0,b5,0];case
1:var
h=c[2],i=c[1],G=0,H=b?a(g,i,h):a(f,i,h);return[0,H,G];case
2:var
I=c[2],j=br(e,d,g,f,b,c[1]),k=j[2],l=j[1],m=br(e,d,g,f,b,I),n=m[2],o=m[1];if(b){var
J=O(k,n);return[0,O(l,o),J]}var
p=c6(e,d,l,o),K=p[1];return[0,K,O(k,O(n,p[2]))];case
3:var
L=c[2],q=br(e,d,g,f,b,c[1]),r=q[2],s=q[1],t=br(e,d,g,f,b,L),u=t[2],v=t[1];if(b){var
w=c6(e,d,s,v),M=w[1];return[0,M,O(r,O(u,w[2]))]}var
N=O(r,u);return[0,O(s,v),N];case
4:var
P=c[1],b=bn(b),c=P;continue;default:var
Q=c[3],R=c[1],x=br(e,d,g,f,bn(b),R),y=x[2],z=x[1],A=br(e,d,g,f,b,Q),B=A[2],C=A[1];if(b){var
D=c6(e,d,z,C),S=D[1];return[0,S,O(y,O(B,D[2]))]}var
T=O(y,B);return[0,O(z,C),T]}}function
ih(f,e,d){var
c=e,b=d;for(;;){if(c){var
g=c[2],h=c[1];if(b){var
i=b[2];if(a(f,h,b[1])){var
c=g,b=i;continue}return 0}return 0}return 1}}function
dT(g,f,e,d,c,b,a){return ih(c,aC(g,f,e,d,1,b),a)}function
fK(d,c,b){return bn(a(d,c,b))}function
fL(f,e,c,b){var
d=a(e,c,b);return d?fK(f,c,b):d}function
ii(b,a){switch(b){case
0:return nJ;case
1:return 1===a?nK:0===a?nL:0;case
2:return 1===a?0:[0,a];default:return 1===a?0:0===a?nM:nN}}function
ij(b,a){switch(b){case
0:return[0,a];case
1:return 0===a?nO:0;case
2:return 1===a?0:nP;default:return 1===a?0:0===a?nQ:[0,a]}}function
dU(c,a){return a?b(c,a[1]):0}function
fM(d,c,b){if(c){var
e=c[1];return b?a(d,e,b[1]):0}return 0}function
ik(g,f,e,d,c,b,a){var
h=a[1];return 0===a[2]?[0,[0,am(g,f,e,d,c,b,h),0]]:0}function
il(g,f,e,d,c,b,a){var
h=b[1],i=a[1],j=ii(b[2],a[2]);return dU(function(a){return[0,[0,am(g,f,e,d,c,h,i),a]]},j)}function
c7(e,d,c,b,a){var
f=b[1],g=a[1],h=ij(b[2],a[2]);return dU(function(a){return[0,[0,ab(e,d,c,f,g),a]]},h)}function
bO(a,f,d,e,c,h,g,b){if(typeof
b==="number")return[0,[0,[0,a],0]];else
switch(b[0]){case
0:return[0,hY(b[1],g,[0,[0,a],0])];case
1:return[0,[0,c2(a,f,d,e,c,b[1]),3]];case
2:var
j=b[1],k=bO(a,f,d,e,c,h,g,b[2]);return dU(function(b){return ik(a,f,d,e,c,j,b)},k);case
3:var
l=b[1],m=bO(a,f,d,e,c,h,g,b[2]),n=bO(a,f,d,e,c,h,g,l);return fM(function(b,g){return il(a,f,d,e,c,b,g)},n,m);case
4:var
o=b[1],p=bO(a,f,d,e,c,h,g,b[2]),q=bO(a,f,d,e,c,h,g,o);return fM(function(b,e){return c7(a,d,c,b,e)},q,p);default:var
i=b[1];return fL(c,h,a,i)?[0,[0,[0,i],2]]:0}}function
c8(b,d,f,e){var
g=e[1],h=e[2];if(0===g[0]){var
c=g[1];switch(h){case
0:return fK(d,c,b);case
1:return a(d,c,b);case
2:return a(f,c,b);default:return fL(d,f,c,b)}}return 0}function
dV(c,i,h,g,b,a,f,e){var
d=bO(c,i,h,g,b,a,f,e);return d?c8(c,b,a,d[1]):0}function
im(e,j,d,i,c,b,a,h){var
k=h[3],l=h[2],f=X(e,j,d,i,c,b,a,h[1]),g=X(e,j,d,i,c,b,a,k);switch(l){case
0:var
m=[0,[0,I(e,d,c,b,a,g,f),2],0];return[0,[0,I(e,d,c,b,a,f,g),2],m];case
1:return[0,[0,I(e,d,c,b,a,f,g),0],0];case
2:return[0,[0,I(e,d,c,b,a,f,g),2],0];case
3:return[0,[0,I(e,d,c,b,a,g,f),2],0];case
4:return[0,[0,I(e,d,c,b,a,f,g),3],0];default:return[0,[0,I(e,d,c,b,a,g,f),3],0]}}function
fN(i,h,g,f,e,d,c,b,a){var
j=im(i,h,g,f,e,d,c,b);return ba(function(b){return[0,[0,b,a],0]},j)}function
io(e,j,d,i,c,b,a,h){var
k=h[3],l=h[2],f=X(e,j,d,i,c,b,a,h[1]),g=X(e,j,d,i,c,b,a,k);switch(l){case
0:return[0,[0,I(e,d,c,b,a,f,g),0],0];case
1:var
m=[0,[0,I(e,d,c,b,a,g,f),2],0];return[0,[0,I(e,d,c,b,a,f,g),2],m];case
2:return[0,[0,I(e,d,c,b,a,g,f),3],0];case
3:return[0,[0,I(e,d,c,b,a,f,g),3],0];case
4:return[0,[0,I(e,d,c,b,a,g,f),2],0];default:return[0,[0,I(e,d,c,b,a,f,g),2],0]}}function
fO(i,h,g,f,e,d,c,b,a){var
j=io(i,h,g,f,e,d,c,b);return ba(function(b){return[0,[0,b,a],0]},j)}function
dW(f,e){var
d=f,c=e;for(;;)switch(c[0]){case
0:return[0,c[1]];case
1:var
g=c[2],d=a(u[2],c[1],d),c=g;continue;default:var
h=c[3],i=c[2],j=c[1],k=dW(b(u[1],d),h);return[2,[4,dW(d,j),[6,[1,d],[0,i]]],k]}}function
ip(a){return dW(0,a)}function
a2(c,a){switch(a[0]){case
0:return[0,b(c,a[1])];case
1:return[1,a[1]];case
2:var
d=a[1],e=a2(c,a[2]);return[2,a2(c,d),e];case
3:var
f=a[1],g=a2(c,a[2]);return[3,a2(c,f),g];case
4:var
h=a[1],i=a2(c,a[2]);return[4,a2(c,h),i];case
5:return[5,a2(c,a[1])];default:var
j=a[2];return[6,a2(c,a[1]),j]}}function
dX(b,a){var
c=a[2],d=a[1],e=a2(b,a[3]);return[0,a2(b,d),c,e]}function
iq(q,h,f,g,c){if(typeof
c!=="number")switch(c[0]){case
1:var
m=c[1];if(0===m[0]){var
n=m[1];return a(g,q,n)?0:[5,a(f,n,n)]}return[1,m];case
3:var
b=c[2],d=c[1];if(typeof
d==="number")return 0;else
switch(d[0]){case
3:var
i=d[2],j=d[1];if(typeof
j!=="number"&&5===j[0]){var
s=j[1];return typeof
b==="number"?0:5===b[0]?[3,[5,a(f,b[1],s)],i]:c}if(typeof
i!=="number"&&5===i[0]){var
r=i[1];return typeof
b==="number"?0:5===b[0]?[3,[5,a(f,b[1],r)],j]:c}return typeof
b==="number"?0:5===b[0]?a(g,h,b[1])?d:[3,d,b]:c;case
5:var
e=d[1];if(typeof
b==="number")return 0;else
switch(b[0]){case
3:var
k=b[2],l=b[1];if(typeof
l!=="number"&&5===l[0])return[3,[5,a(f,e,l[1])],k];if(typeof
k!=="number"&&5===k[0])return[3,[5,a(f,e,k[1])],l];return a(g,h,e)?b:[3,d,b];case
4:return[4,[3,[5,e],b[1]],[3,[5,e],b[2]]];case
5:return[5,a(f,e,b[1])];default:return a(g,h,e)?b:[3,d,b]}default:return typeof
b==="number"?0:5===b[0]?a(g,h,b[1])?d:[3,d,b]:c}case
4:var
o=c[2],p=c[1];return typeof
p==="number"?o:typeof
o==="number"?p:[4,p,o]}return c}var
nR=[0];function
nS(a){return a[1]}function
nT(a){return a[2]}function
at(c,b){var
d=a(o[8],b[1],[0,c[2]]);return aL(a(o[8],c[1],[0,b[2]]),d)}function
c9(c,b){var
d=a(o[8],b[1],[0,c[2]]),e=a(o[8],c[1],[0,b[2]]);return a(o[10],e,d)}function
aM(c,b){var
d=a(u[11],c[2],b[2]),e=a(o[8],b[1],[0,c[2]]),f=a(o[8],c[1],[0,b[2]]);return[0,a(o[5],f,e),d]}function
aT(c,b){var
d=a(u[11],c[2],b[2]);return[0,a(o[8],c[1],b[1]),d]}function
bs(a){var
c=a[2];return[0,b(o[6],a[1]),c]}function
bP(b,a){return aM(b,bs(a))}function
fP(b){var
a=b[1];return typeof
a==="number"?nU:0===a[0]?[0,[0,b[2]],a[1]]:[0,[1,b[2]],a[1]]}function
fQ(a,b){return dO(aT,a,b)}function
fR(b,a){return typeof
a==="number"?nV:0===a[0]?fQ(b,a[1]):fP(fQ(b,a[1]))}function
nW(e,d,c){var
a=d,b=c;for(;;)if(typeof
a==="number")return e;else{if(0===a[0])return a[1];var
f=a[3],g=a[2],h=a[1];if(typeof
b==="number")return g;else{if(0===b[0]){var
a=f,b=b[1];continue}var
a=h,b=b[1];continue}}}function
cr(b,a,c){return typeof
a==="number"?[0,c]:0===a[0]?[1,0,b,cr(b,a[1],c)]:[1,cr(b,a[1],c),b,0]}function
dY(d,a,b,c){if(typeof
c==="number")return cr(d,a,b);else{if(0===c[0]){var
g=c[1];return typeof
a==="number"?[0,b]:0===a[0]?[1,0,g,cr(d,a[1],b)]:[1,cr(d,a[1],b),g,0]}var
e=c[3],h=c[2],f=c[1];return typeof
a==="number"?[1,f,b,e]:0===a[0]?[1,f,h,dY(d,a[1],b,e)]:[1,dY(d,a[1],b,f),h,e]}}var
nX=o[10],nY=o[8],nZ=o[5],n1=0;function
ir(a,b){return dV(n1,n0,nZ,nY,aL,nX,a,b)}var
n2=o[6],n3=o[7],n4=o[5],n5=0;function
an(a,b){return I(n5,n4,n3,n2,aL,a,b)}var
n6=o[5],n7=0;function
a3(a,b){return ab(n7,n6,aL,a,b)}var
n8=o[6],n9=o[7],n_=o[8],n$=o[5],ob=0;function
cs(a){return X(ob,oa,n$,n_,n9,n8,aL,a)}function
is(c){var
d=c[3],e=c[2],a=cs(c[1]),b=cs(d);switch(e){case
0:var
f=[0,[0,an(b,a3(a,oc)),3],0];return[0,[0,an(a,a3(b,od)),3],f];case
1:return[0,[0,an(a,b),0],0];case
2:return[0,[0,an(a,a3(b,oe)),3],0];case
3:return[0,[0,an(b,a3(a,of)),3],0];case
4:return[0,[0,an(a,b),3],0];default:return[0,[0,an(b,a),3],0]}}function
fS(b,a){var
c=is(b);return ba(function(b){return[0,[0,b,a],0]},c)}function
it(c){var
d=c[3],e=c[2],a=cs(c[1]),b=cs(d);switch(e){case
0:return[0,[0,an(a,b),0],0];case
1:var
f=[0,[0,an(b,a3(a,og)),3],0];return[0,[0,an(a,a3(b,oh)),3],f];case
2:return[0,[0,an(b,a),3],0];case
3:return[0,[0,an(a,b),3],0];case
4:return[0,[0,an(b,a3(a,oi)),3],0];default:return[0,[0,an(a,a3(b,oj)),3],0]}}function
fT(b,a){var
c=it(b);return ba(function(b){return[0,[0,b,a],0]},c)}var
ok=o[10],ol=0;function
dZ(a){return c8(ol,aL,ok,a)}var
om=o[5],on=0;function
fU(a,b){return c7(on,om,aL,a,b)}function
c_(a){return br(dZ,fU,fS,fT,1,a)}function
iu(e,d){var
b=a(o[18],e,d),c=b[1];return typeof
b[2]==="number"?c:a(o[5],c,oo)}function
fV(c,b){var
d=a(o[20],c,b);return a(o[13],d,op)}function
c$(d){var
a=d;for(;;)switch(a[0]){case
0:return[0,0,a[1]];case
1:var
a=a[2];continue;default:var
e=a[3],b=c$(a[1]),f=b[2],g=b[1],c=c$(e),h=c[2],i=c[1];return[0,fV(fV(g,f),i),h]}}function
da(b,c){switch(b[0]){case
0:return[0,a(o[19],b[1],c)];case
1:var
d=b[1];return[1,d,da(b[2],c)];default:var
e=b[2],f=b[1],g=da(b[3],c);return[2,da(f,c),e,g]}}function
d0(c){var
e=c$(c),f=e[2],d=e[1];if(a(o[12],d,0)){var
g=iu(b(o[6],f),d),h=b(o[6],g);return[0,da(cq(o[7],c,f),d),h]}return[0,c,0]}function
d1(d){var
e=d[2],b=d[1];switch(e){case
0:var
f=c$(b),g=f[2],c=f[1];if(a(o[12],c,0))if(bn(aL(g,0)))if(bn(aL(a(o[20],c,g),c)))return 0;return[0,[0,d0(b),0]];case
1:return[0,[0,[0,b,0],e]];case
2:return[0,[0,d0(cq(o[7],b,oq)),3]];default:return[0,[0,d0(b),3]]}}function
iv(a){var
b=a[1],c=a[2];return[0,a3(b[1],[0,b[2]]),c]}function
iw(a){return 0===a[0]?typeof
a[1]==="number"?1:0:0}var
or=o[10],os=o[8],ot=o[5],ov=0;function
db(a,b){return bO(ov,ou,ot,os,aL,or,a,b)}function
fW(a){return 0===a?1:3<=a?1:0}var
ix=0;function
ct(a,b){if(b){var
c=b[3],e=b[2],d=b[1];return typeof
a==="number"?[0,d,1,c]:0===a[0]?[0,d,e,ct(a[1],c)]:[0,ct(a[1],d),e,c]}return typeof
a==="number"?ow:0===a[0]?[0,0,0,ct(a[1],0)]:[0,ct(a[1],0),0,0]}function
ox(a){return ct(a,ix)}function
fX(b,a){if(b){var
c=b[3],d=b[2],e=b[1];if(a){var
f=a[2],g=a[1],h=fX(c,a[3]),i=d?1:f;return[0,fX(e,g),i,h]}return b}return a}function
iy(d,c){var
a=d,b=c;for(;;)if(typeof
a==="number")return b;else{if(0===a[0]){var
a=a[1],b=[0,b];continue}var
a=a[1],b=[1,b];continue}}function
iz(a){return iy(a,0)}function
d2(e,j,i,h){var
c=j,d=i,b=h;for(;;){if(c){var
f=c[3],g=c[1];if(c[2]){var
k=d2(e,g,d,[1,b]),c=f,d=a(e,iz(b),k),b=[0,b];continue}var
c=f,d=d2(e,g,d,[1,b]),b=[0,b];continue}return d}}var
aU=[0,ix,ct,ox,fX,iy,iz,d2,function(c,b,a){return d2(c,b,a,0)}];function
bt(d){var
c=d;for(;;)switch(c[0]){case
0:return aU[1];case
1:return b(aU[3],c[1]);case
2:var
e=c[2],f=bt(c[1]),g=bt(e);return a(aU[4],f,g);case
3:var
h=c[2],i=bt(c[1]),j=bt(h);return a(aU[4],i,j);case
4:var
k=c[2],l=bt(c[1]),m=bt(k);return a(aU[4],l,m);case
5:var
c=c[1];continue;default:var
c=c[1];continue}}function
iA(b){var
c=b[3],d=bt(b[1]),e=bt(c);return a(aU[4],d,e)}function
bQ(c){var
b=c;for(;;){if(typeof
b!=="number")switch(b[0]){case
1:return iA(b[1]);case
2:var
d=b[2],e=bQ(b[1]),f=bQ(d);return a(aU[4],e,f);case
3:var
g=b[2],h=bQ(b[1]),i=bQ(g);return a(aU[4],h,i);case
4:var
b=b[1];continue;case
5:var
j=b[3],k=bQ(b[1]),l=bQ(j);return a(aU[4],k,l)}return aU[1]}}function
dc(a){return[0,[1,a],3,oy]}function
fY(c,b,a){return[0,[1,c],0,[3,[1,b],[1,a]]]}function
iB(d,c,b){var
e=0;function
f(b,h){var
e=[1,a(u[2],c,b)],f=[0,a(u[2],c,b)],i=g(d,c,b,oz),j=[1,dc(f),i],k=g(d,c,b,oA),l=[2,[1,dc(e),k],j],m=g(d,c,b,0);return[2,[2,[1,fY(b,e,f),m],l],h]}return g(aU[8],f,b,e)}function
iC(c,b,a){return[5,iB(c,b,bQ(a)),0,a]}function
fZ(w,v){var
d=w,c=v;for(;;)if(typeof
c==="number")return 0;else
switch(c[0]){case
0:var
x=c[2],g=db(d,c[1]);if(g){var
h=g[1];if(dZ(h))return 1;var
d=[0,h,d],c=x;continue}return 0;case
1:var
y=c[2],i=db(d,c[1]);if(i){var
j=d1(i[1]);if(j){var
d=[0,iv(j[1]),d],c=y;continue}return 1}return 0;default:var
z=c[3],A=c[2],k=db(d,c[1]);if(k){var
B=k[1],l=db(d,A);if(l){var
C=l[1],m=d1(B);if(m){var
n=m[1],p=n[1],q=p[1],D=n[2],E=p[2],r=d1(C);if(r){var
s=r[1],t=s[1],F=s[2],G=t[2],H=t[1];if(fW(D))if(fW(F))if(iw(a3(q,H))){var
f=z,e=b(o[6],E);for(;;){if(f){var
I=f[2],J=f[1],u=fZ([0,[0,an(q,[0,e]),0],d],J);if(u){var
f=I,e=a(o[5],e,oB);continue}return u}return a(o[12],e,G)}}return 0}return 1}return 1}return 0}return 0}}function
oC(b,a){return dT(dZ,fU,fS,fT,function(a){var
b=ba(bL,a);return function(a){return fZ(b,a)}},b,a)}function
f0(a,b){return dV(oE,oD,aM,aT,at,c9,a,b)}function
f1(b,a){return fN(oG,oF,aM,aT,bP,bs,at,b,a)}function
f2(b,a){return fO(oI,oH,aM,aT,bP,bs,at,b,a)}function
f3(a){return c8(oJ,at,c9,a)}function
f4(a,b){return c7(oK,aM,at,a,b)}function
f5(a){return X(oM,oL,aM,aT,bP,bs,at,a)}function
cu(a){return br(f3,f4,f1,f2,1,a)}function
oN(b,a){return dT(f3,f4,f1,f2,function(a){var
b=ba(bL,a);return function(a){return f0(b,a)}},b,a)}function
iD(a){return 0===a[0]?a[1]:b(o[16],a[1])}function
aD(a){if(typeof
a==="number")return 0===a?oO:oP;else
switch(a[0]){case
0:return a[1];case
1:return[0,a[1],0];case
2:var
b=a[1],c=aD(a[2]);return aM(aD(b),c);case
3:var
d=a[1],e=aD(a[2]);return bP(aD(d),e);case
4:var
f=a[1],g=aD(a[2]);return aT(aD(f),g);case
5:var
h=a[1],i=iD(a[2]);return fR(aD(h),i);case
6:return fP(aD(a[1]));default:return bs(aD(a[1]))}}function
iE(a,b){return dV(oR,oQ,aM,aT,at,c9,a,b)}function
iF(b,a){return fN(oT,oS,aM,aT,bP,bs,at,b,a)}function
iG(b,a){return fO(oV,oU,aM,aT,bP,bs,at,b,a)}function
iH(a){return c8(oW,at,c9,a)}function
iI(a,b){return c7(oX,aM,at,a,b)}aA(981,[0,bn,bL,m$,O,hX,fA,hY,ba,dN,na,u,h3,dO,o,aL,nG,nH,fG,ae,h8,T,h9,h_,as,bN,cq,cY,cZ,fH,fI,ab,I,c0,c1,bp,am,c2,h$,c3,ia,X,bq,c4,ib,fJ,b3,a1,b4,b5,dR,ic,id,c5,O,aC,dS,ie,ig,c6,br,ih,dT,fK,fL,ii,ij,dU,fM,ik,il,c7,bO,c8,dV,X,I,ab,im,fN,io,fO,dW,ip,a2,dX,iq,nR,nS,nT,at,c9,aM,aT,bs,bP,fP,fQ,fR,nW,cr,dY,ir,an,a3,cs,is,fS,it,fT,dZ,fU,c_,iu,fV,c$,da,d0,d1,iv,iw,db,fW,aU,bt,iA,bQ,dc,fY,iB,iC,fZ,oC,f0,f1,f2,f3,f4,f5,cu,oN,iD,aD,iE,iF,iG,iH,iI,function(b,a){var
c=a1(function(a){return dX(aD,a)},b);return dT(iH,iI,iF,iG,function(a){var
b=ba(bL,a);return function(a){return iE(b,a)}},c,a)}],"Micromega_plugin__Micromega");var
oY=a$,E=[0,oY,function(b,a){return b===a?1:0}],v=b(f6[1],[0,E[1]]),iJ=v[13],oZ=v[1],o0=v[2],o1=v[3],o2=v[4],o3=v[5],o4=v[6],o5=v[7],o6=v[8],o7=v[9],o8=v[10],o9=v[11],o_=v[12],o$=v[14],pa=v[15],pb=v[16],pc=v[17],pd=v[18],pe=v[19],pf=v[20],pg=v[21],ph=v[22],pi=v[23],pj=v[24],pk=v[25],pl=v[26],pm=v[27],pn=v[28],po=v[29],pp=v[30],pq=v[31],pr=v[32],ps=v[33],pt=v[34],pu=v[35],pv=v[36],pw=v[37],px=v[38],py=v[39],s=[0,oZ,o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o_,iJ,o$,pa,pb,pc,pd,pe,pf,pg,ph,pi,pj,pk,pl,pm,pn,po,pp,pq,pr,ps,pt,pu,pv,pw,px,py,function(c,b){return a(iJ,function(a){return g(k[1],c,pz,a)},b)}],x=b(b6[1],[0,E[1]]),iK=x[26],pA=x[1],pB=x[2],pC=x[3],pD=x[4],pE=x[5],pF=x[6],pG=x[7],pH=x[8],pI=x[9],pJ=x[10],pK=x[11],pL=x[12],pM=x[13],pN=x[14],pO=x[15],pP=x[16],pQ=x[17],pR=x[18],pS=x[19],pT=x[20],pU=x[21],pV=x[22],pW=x[23],pX=x[24],pY=x[25],pZ=x[27],p0=x[28],p1=x[29],p2=x[30],p3=x[31],p4=x[32],p5=x[33],p6=x[34],p7=x[35],p8=x[36],p9=x[37],p_=x[38],r=[0,pA,pB,pC,pD,pE,pF,pG,pH,pI,pJ,pK,pL,pM,pN,pO,pP,pQ,pR,pS,pT,pU,pV,pW,pX,pY,iK,pZ,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p_,function(c,b){return a(iK,c-1|0,b)[3]}];function
iL(i,d,c,h){var
b=h;for(;;){if(b){var
f=b[2],g=b[1];if(f){a(d,c,g);a(e[55],c,i);var
b=f;continue}return a(d,c,g)}return 0}}function
p$(a,c){try{var
d=b(a,0);b(c,0);return d}catch(a){a=n(a);try{b(c,0)}catch(b){throw a}throw a}}function
qa(e,d){var
a=e;for(;;){if(a){var
f=a[2],c=b(a[1][1],d);if(c)return c;var
a=f;continue}return 0}}function
iM(e,d){var
c=0,b=d;for(;;){if(b){var
i=b[2],j=b[1],h=function(d){return function(c,b){return[0,a(e,d,b),c]}}(j),c=g(f[20],h,c,b),b=i;continue}return c}}function
iN(g,f,e){var
c=f,b=e;for(;;){if(c){var
h=c[2],i=c[1];if(b){var
d=b[2];if(a(g,i,b[1])){var
c=h,b=d;continue}var
b=d;continue}return 0}return 1}}function
bu(h,a){function
c(e,a){var
c=e[2],d=e[1];if(d)return[0,d,[0,a,c]];var
f=b(h,a);return f?[0,[0,[0,f[1],a]],c]:[0,d,[0,a,c]]}return g(f[20],c,qb,a)}function
qc(j,p,i){var
m=bu(j,i),n=m[1];if(n){var
o=n[1],g=o[1],f=o[2],c=0,d=m[2];for(;;){if(d){var
h=d[2],e=d[1],k=b(j,e);if(k){var
l=k[1];if(a(p,l,g)){var
g=l,q=[0,f,c],f=e,c=q,d=h;continue}var
c=[0,e,c],d=h;continue}var
c=[0,e,c],d=h;continue}return[0,[0,[0,g,f]],c]}}return[0,0,i]}function
iO(e,d){var
a=d;for(;;){if(a){var
f=a[2],c=b(e,a[1]);if(c)return[0,c[1]];var
a=f;continue}return 0}}function
iP(h,a){function
c(c,a){var
d=c[2],e=c[1],f=b(h,a);return f?[0,[0,[0,f[1],a],e],d]:[0,e,[0,a,d]]}return g(f[20],c,qd,a)}function
d3(h,c){function
d(c,a){var
d=c[1],f=c[2],e=b(h,a);return e?[0,[0,e[1],d],1]:[0,[0,a,d],f]}var
a=g(f[20],d,qe,c),e=a[1];return a[2]?[0,e]:0}function
iQ(e,c){var
d=0;function
a(a,d){var
c=b(e,d);return c?[0,c[1],a]:a}return g(f[20],a,d,c)}function
iR(j,i,c){function
d(l,k){var
c=l,d=k;for(;;){var
f=bu(j,d),g=f[1];if(g){var
h=f[2],m=g[1],n=a(e[26],h,c),o=iQ(b(i,m),n),c=a(e[26],o,c),d=h;continue}return c}}try{var
f=d(0,c);return f}catch(a){a=n(a);b(d4[4],e[28]);throw a}}function
iS(d,c){var
b=a(l[17],d,c),e=a(l[15],d,b),f=a(l[15],c,b),g=a(l[10],e,f);return a(l[10],b,g)}function
a4(a){return 2===a[0]?b(dd[3],a[1]):l[2]}function
af(a){switch(a[0]){case
0:return b(l[36],a[1]);case
1:return a[1];default:return b(dd[2],a[1])}}function
d5(e,d){var
a=d;for(;;){var
c=b(e,a);if(c){var
a=c[1];continue}return a}}function
iT(e,d){var
a=e;for(;;){if(a){var
f=a[2],c=b(a[1],d);if(c)return[0,c[1]];var
a=f;continue}return 0}}function
iU(a){return a?iU(a[1])+1|0:0}function
d6(a){return typeof
a==="number"?1:0===a[0]?1+(2*d6(a[1])|0)|0:2*d6(a[1])|0}function
qf(a){return a?d6(a[1]):0}function
f7(a){return typeof
a==="number"?1:0===a[0]?1+(2*f7(a[1])|0)|0:2*f7(a[1])|0}function
d7(b){if(typeof
b==="number")return l[2];else{if(0===b[0]){var
c=d7(b[1]),d=a(l[11],2,c);return a(l[7],1,d)}var
e=d7(b[1]);return a(l[11],2,e)}}function
f8(a){if(typeof
a==="number")return l[1];else{if(0===a[0])return d7(a[1]);var
c=d7(a[1]);return b(l[3],c)}}function
qg(b){var
c=b[1],e=[1,f8([0,b[2]])],f=[1,f8(c)];return a(d[9],f,e)}function
iV(a){return 0===a?0:[0,iV(a-1|0)]}function
cv(b){return a(E[2],b,1)?0:a(E[2],b&1,1)?[0,cv(b>>>1|0)]:[1,cv(b>>>1|0)]}function
qh(b){if(0<=b)return a(E[2],b,0)?0:[0,cv(b)];throw[0,aV,qi]}function
f9(b){return a(E[2],b,1)?0:a(E[2],b&1,1)?[0,f9(b>>>1|0)]:[1,f9(b>>>1|0)]}function
qj(a){var
b=a$(a,0);return 0===b?0:1===b?[0,cv(a)]:[1,cv(-a|0)]}function
d8(d){var
f=b(l[36],2);function
c(b){if(a(l[24],b,l[2]))return 0;var
d=a(l[14],b,f),e=d[1];return a(l[24],l[2],d[2])?[0,c(e)]:[1,c(e)]}return c(d)}function
iW(a){var
c=b(l[22],a);return 0===c?0:1===c?[0,d8(a)]:[1,d8(b(l[3],a))]}function
qk(a){var
b=d8(a4(a));return[0,iW(af(a)),b]}function
ql(e){var
c=e;for(;;){if(c){var
f=c[2],d=b(c[1],0);if(a(E[2],d,0)){var
c=f;continue}return d}return 0}}function
qm(g,f,e){var
c=f,b=e;for(;;){if(c){if(b){var
h=b[2],i=c[2],d=a(g,c[1],b[1]);if(a(E[2],d,0)){var
c=i,b=h;continue}return d}return 1}return b?-1:0}}function
qn(a){return a}function
qo(a){return a+1|0}var
qp=e[1][5];function
qq(d,c){var
f=b(e[22],c);return a(e[55],d,f)}var
qr=E[1];function
qs(a){return a}var
Q=b(f6[1],[0,qr]);function
qt(c){for(;;)try{var
d=a(N[15],0,c)[2];return d}catch(a){a=n(a);if(a[1]===N[1]){var
b=a[2];if(typeof
b==="number")if(11===b)continue}throw a}}function
iX(c,t,s){var
h=a(N[67],0,0),i=h[2],j=h[1],l=a(N[67],0,0),m=l[2],o=l[1],p=a(N[67],0,0),q=p[2],u=p[1],v=S(N[69],c,t,j,m,q),r=b(N[31],i);a(e[61],r,s);b(e[52],r);var
d=qt(v);function
w(e){var
c=[0,j,[0,i,[0,o,[0,m,[0,u,[0,q,0]]]]]];function
d(a){try{var
c=b(N[24],a);return c}catch(a){return 0}}return a(f[15],d,c)}return p$(function(q){switch(d[0]){case
0:var
a=d[1];if(0===a){var
f=b(N[30],o);try{var
j=b(d9[3],f);return j}catch(a){a=n(a);var
h=b(d4[1],a),i=g(k[4],qu,c,h);return b(e[3],i)}}var
l=g(k[4],qv,c,a);return b(e[3],l);case
1:var
m=g(k[4],qw,c,d[1]);return b(e[3],m);default:var
p=g(k[4],qx,c,d[1]);return b(e[3],p)}},w)}var
ag=[0,f8,qg,d6,qf,iU,f7],z=[0,cv,iW,qh,iV,qk,f9,qj,d8],b7=[0,Q[1],Q[2],Q[3],Q[4],Q[5],Q[6],Q[7],Q[8],Q[9],Q[10],Q[11],Q[12],Q[13],Q[15],Q[16],Q[17],Q[18],Q[19],Q[20],Q[21],Q[22],Q[24],Q[26],Q[28]],bv=[0,qq,qo,qp,qn,qs],f_=[0,qm,ql];aA(991,[0,E,s,r,af,a4,f_,bv,b7,iL,z,ag,iS,iM,qa,iN,bu,iP,qc,iO,d5,d3,iR,iQ,iT,iX],"Micromega_plugin__Mutils");function
cw(k,j){var
c=k,b=j;for(;;){if(c){var
e=c[1],l=c[2],m=e[2],n=e[1];if(b){var
f=b[1],o=b[2],p=f[2],g=a(E[2],n,f[1]);if(g){var
h=a(d[26],m,p);if(h){var
c=l,b=o;continue}var
i=h}else
var
i=g;return i}return 0}return b?0:1}}function
iY(f){var
c=0,a=f;for(;;){if(a){var
e=a[1],g=a[2],h=e[1],i=[0,h,b(d[56],e[2])],c=c+b(bb[27],i)|0,a=g;continue}return b(bb[27],c)}}var
K=0;function
bw(a){if(a){var
b=a[1];if(0===b[1])var
c=b[2],d=0===c[0]?0===c[1]?a[2]?0:1:0:0;else
var
d=0;if(!d)return 0}return 1}function
iZ(h,e,i){var
c=i[2],f=i[1];if(a(E[2],f,0)){if(a(d[32],qy,c))return 0;var
l=b(d[40],c);return g(k[1],e,qz,l)}if(0===c[0]){var
j=c[1]+1|0;if(!(2<j>>>0))switch(j){case
0:return D(k[1],e,qB,h,f);case
1:return 0;default:return a(h,e,f)}}var
m=b(d[40],c);return S(k[1],e,qA,m,h,f)}function
d_(d,c,b){if(b){var
f=b[2],g=b[1];if(f){var
h=function(a,b){return d_(d,a,b)},i=function(a,b){return iZ(d,a,b)};return V(k[1],c,qG,i,g,h,f)}return iZ(d,c,g)}return a(e[55],c,qH)}function
d$(b,a){return g(k[1],b,qI,a)}function
b8(b,a){return d_(d$,b,a)}function
qJ(e,c){function
h(e,c){function
h(c){function
f(f,i){var
c=i[2],e=i[1];if(a(E[2],e,0)){if(a(d[32],qC,c))return 0;var
j=b(d[40],c);return g(k[1],f,qD,j)}if(0===c[0]){var
h=c[1]+1|0;if(!(2<h>>>0))switch(h){case
0:return D(k[1],f,qF,d$,e);case
1:return 0;default:return d$(f,e)}}var
l=b(d[40],c);return S(k[1],f,qE,l,d$,e)}return D(k[1],e,qK,f,c)}return a(f[15],h,c)}return D(k[1],e,qL,h,c)}function
b9(b){function
e(i,h){var
c=i,b=h;for(;;){if(b){var
f=b[2],g=b[1];if(a(d[31],g,qM))return[0,[0,c,g],e(c+1|0,f)];var
c=c+1|0,b=f;continue}return 0}}return e(0,b)}function
ga(a){function
b(c,a){if(a){var
d=a[1],e=a[2],f=d[2];return c===d[1]?[0,f,b(c+1|0,e)]:[0,f$,b(c+1|0,a)]}return 0}return b(0,a)}function
cx(e,c,b){return a(d[26],c,qN)?b:[0,[0,e,c],b]}function
gb(f,d,c){if(c){var
h=c[2],i=c[1],j=i[2],g=i[1],k=a(E[1],f,g)+1|0;if(2<k>>>0)return b(e[3],qO);switch(k){case
0:return cx(f,b(d,f$),c);case
1:return cx(g,b(d,j),h);default:return[0,[0,g,j],gb(f,d,h)]}}return cx(f,b(d,f$),0)}function
G(f,d,c){if(c){var
h=c[2],i=c[1],g=i[1],k=i[2],j=a(E[1],f,g)+1|0;if(2<j>>>0)return b(e[3],qP);switch(j){case
0:return cx(f,d,c);case
1:return cx(g,d,h);default:return[0,[0,g,k],G(f,d,h)]}}return cx(f,d,0)}function
gc(b){return a(d[26],b,qQ)?0:[0,[0,0,b],0]}function
ao(b,c){if(0===b[0]){var
e=b[1];if(0===e)return 0;if(1===e)return c}function
g(c){var
e=c[1];return[0,e,a(d[7],b,c[2])]}return a(f[17],g,c)}function
cy(c,b){if(a(d[31],c,qR)){var
e=function(b){var
e=b[1];return[0,e,a(d[9],b[2],c)]};return a(f[17],e,b)}return b}function
cz(c){function
e(a){var
c=a[1];return[0,c,b(d[3],a[2])]}return a(f[17],e,c)}function
aW(q,p){var
c=q,b=p;for(;;){if(c){if(b){var
e=b[2],h=b[1],i=h[2],j=h[1],f=c[2],k=c[1],l=k[2],g=k[1],m=a$(g,j);if(0===m){var
n=a(d[2],l,i);if(a(d[32],qS,n)){var
c=f,b=e;continue}return[0,[0,g,n],aW(f,e)]}return 0<=m?[0,[0,j,i],aW(e,c)]:[0,[0,g,l],aW(f,b)]}var
o=c}else
var
o=b;return o}}function
ea(c,r,b,q){var
f=r,e=q;for(;;){if(f){if(e){var
g=e[2],j=e[1],k=j[2],l=j[1],h=f[2],m=f[1],n=m[2],i=m[1],o=a$(i,l);if(0===o){var
s=a(d[6],b,k),t=a(d[6],c,n),p=a(d[1],t,s);if(a(d[32],qT,p)){var
f=h,e=g;continue}return[0,[0,i,p],ea(c,h,b,g)]}if(0<=o){var
u=ea(c,f,b,g);return[0,[0,l,a(d[6],b,k)],u]}var
v=ea(c,h,b,e);return[0,[0,i,a(d[6],c,n)],v]}return ao(c,f)}return ao(b,e)}}function
gd(f,e,c,b){if(a(d[26],f,qU))if(a(d[26],c,qV))return aW(e,b);return ea(f,e,c,b)}function
qW(e,c){var
f=0,g=[0,function(b){return a(d[37],e[2],c[2])},f],h=[0,function(b){return a(E[1],e[1],c[1])},g];return b(f_[2],h)}var
ge=b(f_[1],qW);function
au(i,h){var
b=h;for(;;){if(b){var
d=b[1],f=b[2],g=d[2],e=a(E[1],d[1],i);if(-1===e){var
b=f;continue}var
c=0===e?[0,[0,g,b]]:0}else
var
c=0;return c?c[1][1]:qX}}function
i0(a){if(a){var
b=0===a[1][1]?a[2]?0:1:0;if(!b)return 0}return 1}function
de(a){if(a){var
b=a[1];if(0===b[1])return b[2]}return qY}function
aX(a){if(a){var
b=a[1];return[0,[0,b[1],b[2],a[2]]]}return 0}function
i1(c){var
a=c;for(;;){if(a){var
b=a[2],d=a[1][1];if(b){var
a=b;continue}return d+1|0}return 1}}function
gf(b){var
c=s[1];function
d(c,b){return a(s[4],b[1],c)}return g(f[20],d,c,b)}function
bc(a){if(a){var
b=a[1];if(0===b[1])return[0,b[2],a[2]]}return[0,qZ,a]}function
q0(b,f){var
a=f;for(;;){if(a){var
c=a[2],d=a[1],e=d[1],g=d[2];if(W(b,e))return[0,g,c];if(bX(b,e))return[0,q1,a];var
a=c;continue}return[0,q2,K]}}function
i2(a){return a?[0,a[1],a[2]]:q3}function
Z(c,b,a){function
d(b,a){return g(c,b,a[1],a[2])}return g(f[20],d,b,a)}function
q4(h,f,e){var
b=f,a=e;for(;;){if(a){var
c=a[1],i=a[2],d=g(h,b,c[1],c[2]);if(d){var
b=d[1],a=i;continue}return 0}return[0,b]}}function
gg(f,e){var
b=e;for(;;){if(b){var
c=b[1],g=b[2],d=a(f,c[1],c[2]);if(d)return[0,d[1]];var
b=g;continue}return 0}}function
eb(c,b){function
d(b){return a(c,b[1],b[2])}return a(f[27],d,b)}function
i3(c,b){function
d(a){return[0,a[1]-c|0,a[2]]}return a(f[17],d,b)}function
q5(c,b){function
d(a){return[0,a[1]+c|0,a[2]]}return a(f[17],d,b)}function
gh(c){var
d=l[1],b=Z(function(c,h,b){var
d=l[2],e=a4(b),f=a(l[23],e,d);if(a(E[2],f,0)){var
g=af(b);return a(l[17],c,g)}throw[0,aV,q6]},d,c),e=a(l[23],b,l[1]);return a(E[2],e,0)?l[2]:b}function
cA(b){var
e=l[2],g=Z(function(b,c,a){return iS(b,a4(a))},e,b),h=l[1],c=Z(function(c,e,b){var
d=af(b);return a(l[17],c,d)},h,b),i=a(l[23],c,l[1]),j=a(E[2],i,0)?l[2]:c;function
k(b){var
c=b[1],e=a(d[6],b[2],[1,g]);return[0,c,a(d[9],e,[1,j])]}return a(f[17],k,b)}function
i4(n,m,l){var
c=m,b=l;for(;;){if(c)if(b){var
e=b[2],f=b[1],g=f[2],h=f[1],i=c[2],j=c[1],k=j[2],d=j[1];if(a(E[2],d,h)){if(a(n,k,g))return[0,[0,d,k,g]];var
c=i,b=e;continue}if(d<h){var
c=i;continue}var
b=e;continue}return 0}}function
ec(m,l){var
e=q7,c=m,b=l;for(;;){if(c)if(b){var
f=b[2],g=b[1],h=g[1],i=c[2],j=c[1],k=j[1],n=g[2],o=j[2];if(k===h){var
p=a(d[6],o,n),e=a(d[1],e,p),c=i,b=f;continue}if(bX(k,h)){var
c=i;continue}var
b=f;continue}return e}}function
q8(c,b){function
d(b){return a(c,b[1],b[2])}return a(f[17],d,b)}function
q9(c){if(c){var
e=c[1],h=c[2],i=[0,e[1],e[2]],j=function(e,c){var
f=c[2],g=e[2],h=c[1],i=e[1],j=b(d[15],f),k=b(d[15],g);return a(d[27],k,j)?[0,i,g]:[0,h,f]};return[0,g(f[20],j,i,h)]}return 0}function
i5(c){function
d(b){return a(c,b[1],b[2])}return b(f[37],d)}aA(993,[0,iY,cw,ge,d_,b8,qJ,gf,de,bc,q0,i2,gc,i0,K,bw,au,G,function(a){return G(a,q_,K)},gb,i1,aX,b9,ga,i3,q5,gh,cA,aW,ao,gd,cy,cz,Z,q4,gg,eb,i4,ec,q8,q9,i5],"Micromega_plugin__Vect");var
gi=[0,e[8]],ra=d[2],rb=d[7],Y=b(b6[1],[0,E[1]]),q$=0;function
i6(d){try{var
e=b(Y[24],d),f=e[1],i=e[2],g=a(Y[26],f,d),j=g[3];if(b(Y[2],g[1]))if(b(Y[2],j))var
h=[0,[0,f,i]],c=1;else
var
c=0;else
var
c=0;if(!c)var
h=0;return h}catch(a){a=n(a);if(a===L)return 0;throw a}}function
ed(e,a){function
c(b,a){var
c=a[2],d=a[1];return 1===c?g(k[1],b,rc,d):D(k[1],b,rd,d,c)}function
d(b,a){if(a){var
e=a[2],f=a[1];return e?V(k[1],b,re,c,f,d,e):c(b,f)}return 0}return d(e,b(Y[19],a))}var
df=Y[1];function
i7(a){var
b=0;function
c(c,b,a){return a+b|0}return g(Y[13],c,a,b)}function
ee(c,b){var
d=i7(c),e=i7(b);return a(E[2],d,e)?g(Y[10],E[1],c,b):a(E[1],d,e)}function
ef(a){return W(a,Y[1])}function
eg(a){return g(Y[4],a,1,Y[1])}function
i8(b){var
a=i6(b);return a?1===a[1][2]?1:0:0}function
gj(c){var
a=i6(c);if(a){var
b=a[1],d=b[1];return 1===b[2]?[0,d]:0}return 0}function
i9(a){if(ef(a))return 0;try{var
b=function(c,a,b){var
d=a/2|0;if(0===(a%2|0))return g(Y[4],c,d,b);throw L},c=[0,g(Y[13],b,a,df)];return c}catch(a){a=n(a);if(a===L)return 0;throw a}}function
gk(c,b){try{var
d=a(Y[27],c,b);return d}catch(a){a=n(a);if(a===L)return 0;throw a}}function
gl(b,a){function
c(b,c,a){var
d=gk(b,a)+c|0;return g(Y[4],b,d,a)}return g(Y[13],c,b,a)}function
i_(c,b){var
f=e[8];function
h(f,d,b){var
g=C.caml_div(gk(f,c),d);return a(e[5],b,g)}var
d=g(Y[13],h,b,f),i=Y[1];function
j(c,f,a){var
e=f-fq(gk(c,b),d)|0;return 0===e?a:g(Y[4],c,e,a)}return[0,g(Y[13],j,c,i),d]}function
i$(b){var
c=s[1];function
d(c,d,b){return a(s[4],c,b)}return g(Y[13],d,b,c)}var
ja=Y[13],A=b(b6[1],[0,ee]),jb=A[8],rf=A[1],rg=A[2],rh=A[3],ri=A[4],rj=A[5],rk=A[6],rl=A[7],rm=A[10],rn=A[11],ro=A[12],rp=A[13],rq=A[14],rr=A[15],rs=A[16],rt=A[17],ru=A[18],rv=A[19],rw=A[20],rx=A[21],ry=A[22],rz=A[23],rA=A[24],rB=A[25],rC=A[26],rD=A[27],rE=A[28],rF=A[29],rG=A[30],rH=A[31],rI=A[32],rJ=A[33],rK=A[34],rL=A[35],rM=A[36],rN=A[37],rO=A[38],cB=[0,rf,rg,rh,ri,rj,rk,rl,jb,rm,rn,ro,rp,rq,rr,rs,rt,ru,rv,rw,rx,ry,rz,rA,rB,rC,rD,rE,rF,rG,rH,rI,rJ,rK,rL,rM,rN,rO,function(e){return b(jb,function(f,b,a){if(b){var
c=b[1];if(a)return g(e,f,c,a[1]);var
d=c}else{if(!a)return 0;var
d=a[1]}return[0,d]})}];function
rP(e,h){var
c=h[2],f=h[1];if(ef(f)){if(a(d[32],rQ,c))return 0;var
j=b(d[40],c);return g(k[1],e,rR,j)}if(0===c[0]){var
i=c[1]+1|0;if(!(2<i>>>0))switch(i){case
0:return D(k[1],e,rT,ed,f);case
1:return 0;default:return ed(e,f)}}var
l=b(d[40],c);return S(k[1],e,rS,l,ed,f)}var
ah=b(b6[1],[0,ee]);function
jc(c,b){function
d(b,a){return D(k[1],c,rU,rP,[0,b,a])}return a(ah[12],d,b)}function
jd(c,b){try{var
d=a(ah[27],c,b);return d}catch(a){a=n(a);if(a===L)return rV;throw a}}function
rW(a){var
b=ah[1],c=eg(a);return g(ah[4],c,rX,b)}function
dg(a){return g(ah[4],df,a,ah[1])}function
dh(e,f,c){if(0===b(d[25],f))return c;var
h=a(ra,jd(e,c),f);return 0===b(d[25],h)?a(ah[7],e,c):g(ah[4],e,h,c)}function
je(b,a){function
c(c,b,a){return dh(c,b,a)}return g(ah[13],c,b,a)}function
jf(c,i){var
e=ah[1];function
f(k,c,j){if(0===b(d[25],c))var
e=dg(rY);else
var
f=ah[1],h=function(e,d,b){var
f=a(rb,c,d),h=gl(k,e);return g(ah[4],h,f,b)},e=g(ah[13],h,i,f);return je(e,j)}return g(ah[13],f,c,e)}function
rZ(c){function
e(a){return b(d[3],a)}return a(ah[33],e,c)}var
jg=ah[13],eh=[aS,r2,aR(0)];function
jh(a){return 2===a[2]?1:0}function
ei(a){switch(a){case
0:return d[26];case
1:return d[30];default:return d[28]}}function
di(a){switch(a){case
0:return r3;case
1:return r4;default:return r5}}function
r6(c,a){var
e=a[2],f=a[1],g=b(d[40],a[3]),h=di(e);return V(k[1],c,r7,b8,f,h,g)}function
gm(c,b){switch(c){case
2:if(2<=b)return 2;var
a=0;break;case
1:var
a=0;break;default:var
a=1}if(!a)if(0!==b)return 1;return 0}function
ej(c,a){switch(c){case
0:var
d=a,b=1;break;case
1:if(1===a)return 1;var
b=0;break;default:var
b=0}if(!b){if(0!==a)return 2;var
d=c}return d}var
ek=b(b6[1],[0,ee]),el=b(b6[1],[0,E[1]]),em=[0,ek[1]],en=[0,el[1]],gn=[0,0];function
r8(a){em[1]=ek[1];en[1]=el[1];gn[1]=0;return 0}function
dj(b){try{var
d=a(ek[27],b,em[1]);return d}catch(a){a=n(a);if(a===L){var
c=gn[1];em[1]=g(ek[4],b,c,em[1]);en[1]=g(el[4],c,b,en[1]);gn[1]++;return c}throw a}}function
bx(b){return a(el[27],b,en[1])}dj(df);function
ji(a){return G(dj(eg(a)),r9,K)}function
r_(a){return G(dj(a),r$,K)}function
eo(a){return g(jg,function(c,b,a){return G(dj(c),b,a)},a,K)}function
dk(a){var
b=dg(sa);return Z(function(c,b,a){return dh(bx(b),a,c)},b,a)}function
go(a,c){var
d=[0,b(a,sc)];return Z(function(h,f,e){var
i=bx(f),c=[0,b(a,sb)],d=g(ja,function(d,c,a){var
e=b(z[3],c);return[4,[6,[1,b(z[1],d)],e],a]},i,c);return[2,[4,[0,b(a,e)],d],h]},d,c)}function
jj(c,b){try{var
a=ed(c,bx(b));return a}catch(a){a=n(a);if(a===L)return g(k[1],c,sd,b);throw a}}function
ep(b,a){return d_(jj,b,a)}function
b_(a){return 0===b(d[25],a)?K:G(0,a,K)}function
se(a){return eb(function(c,d){var
a=bx(c),b=i8(a);return b?b:ef(a)},a)}function
sf(e){var
b=i2(e),c=b[1],f=c[2],g=c[1];if(bw(b[2]))if(a(d[28],f,sg))return gj(bx(g));return 0}function
eq(h,f){var
i=dk(f),c=eg(h),b=dg(r0),d=[0,dg(r1),b];function
e(f,e,d){var
g=d[2],h=d[1],i=i_(f,c),j=i[2],k=i[1];if(0===j)return[0,h,dh(f,e,g)];var
b=df,a=j-1|0;for(;;){if(0===a)return[0,dh(gl(k,b),e,h),g];var
b=gl(b,c),a=a-1|0;continue}}var
a=g(ah[13],e,i,d),j=a[1],k=eo(a[2]);return[0,eo(j),k]}function
jk(b,a){return i0(eq(b,a)[1])}function
jl(f,c){var
a=0;return Z(function(a,h,g){if(b(f,g)){var
d=gj(bx(h));if(d){var
e=d[1];return jk(e,c)?[0,e,a]:a}return a}return a},a,c)}function
jm(c,b){var
a=jl(c,b);return a?[0,g(f[20],e[1][4],a[1],a[2])]:0}function
by(b,a){var
c=dk(a);return eo(jf(dk(b),c))}function
gp(b,a){return aW(b,a)}function
sh(a){return Z(function(c,b,a){var
d=b_(a);return gp(by(ji(b),d),c)},K,a)}function
gq(b){var
c=s[1];return Z(function(c,b,e){var
d=i$(bx(b));return a(s[7],d,c)},c,b)}function
si(e,b,c){var
h=s[1];function
i(c,b){var
d=gq(b[1]);return a(s[7],c,d)}var
d=g(f[20],i,h,c);function
j(b,f){function
c(a){return D(k[1],b,sj,a,e)}return a(s[13],c,d)}D(k[1],b,sk,j,d);function
l(c,a){var
d=a[1],e=di(a[2]);return V(k[1],b,sl,c,ep,d,e)}a(f[16],l,c);return a(k[1],b,sm)}function
sn(a){var
b=cB[1];return Z(function(a,d,e){var
b=bx(d),c=i9(b);return c?g(cB[4],c[1],b,a):a},b,a)}function
aE(e,c){if(typeof
c==="number")return a(k[1],e,so);else
switch(c[0]){case
0:return S(k[1],e,sp,aE,c[2],c[1]);case
1:return g(k[1],e,sq,c[1]);case
2:return g(k[1],e,sr,c[1]);case
3:var
f=b(d[40],c[1]);return g(k[1],e,ss,f);case
4:var
h=dk(c[1]);return D(k[1],e,st,jc,h);case
5:var
i=c[2],j=dk(c[1]);return V(k[1],e,su,jc,j,aE,i);case
6:var
m=c[2],n=b(l[33],c[1]);return S(k[1],e,sv,aE,m,n);case
7:return V(k[1],e,sw,aE,c[1],aE,c[2]);case
8:return V(k[1],e,sx,aE,c[1],aE,c[2]);default:return D(k[1],e,sy,aE,c[1])}}function
gr(c,b){if(typeof
b==="number")return a(k[1],c,sz);else{if(0===b[0])return fr(k[1],c,sA,b[1],aE,b[2],gr,b[3]);var
d=b[5],e=b[4],f=b[3],g=b[2],h=b[1],i=function(a,b){return iL(sB,gr,a,b)};return It(k[1],c,sC,h,aE,g,b8,f,aE,e,i,d)}}function
er(c){var
b=c;for(;;){if(typeof
b!=="number")switch(b[0]){case
0:var
b=b[2];continue;case
1:return sE;case
2:return sF;case
3:return b[1];case
5:var
b=b[2];continue;case
6:var
e=[1,b[1]],f=er(b[2]);return a(d[9],f,e);case
9:var
b=b[1];continue;case
4:break;default:var
g=b[1],h=er(b[2]),i=er(g);return a(d[1],i,h)}return sD}}function
cC(f){var
b=f;for(;;){if(typeof
b==="number")var
c=0;else
switch(b[0]){case
0:var
b=b[2];continue;case
9:var
d=b[1],c=1;break;case
1:case
2:return b[1];case
5:case
6:var
d=b[2],c=1;break;case
7:case
8:var
g=b[1],h=cC(b[2]),i=cC(g);return a(e[6],i,h);default:var
c=0}if(c){var
b=d;continue}return-1}}function
es(b){if(typeof
b==="number")return-1;else{if(0===b[0]){var
c=b[2],d=b[1],h=es(b[3]),i=cC(c),j=a(e[6],i,h);return a(e[6],d,j)}var
k=b[5],l=b[2],m=b[1],n=cC(b[4]),o=cC(l),p=a(e[6],o,n),q=a(e[6],m,p),r=function(c,b){var
d=es(b);return a(e[6],c,d)};return g(f[20],r,q,k)}}function
bz(c,n){var
b=n;for(;;){if(typeof
b!=="number")switch(b[0]){case
0:var
b=b[2];continue;case
5:var
o=b[1],d=bz(c,b[2]);return[0,d[1],d[2],[5,o,d[3]]];case
6:var
f=bz(c,b[2]),g=f[2];return[0,[0,[0,g,f[3]],f[1]],g+1|0,[2,g]];case
7:var
p=b[2],h=bz(c,b[1]),q=h[3],r=h[1],i=bz(h[2],p),s=i[2],t=[7,q,i[3]];return[0,a(e[26],i[1],r),s,t];case
8:var
u=b[2],j=bz(c,b[1]),v=j[3],w=j[1],k=bz(j[2],u),x=k[2],y=[8,v,k[3]];return[0,a(e[26],k[1],w),x,y];case
9:var
l=bz(c,b[1]),m=l[2];return[0,[0,[0,m,l[3]],l[1]],m+1|0,[2,m]]}return[0,0,c,b]}}function
gs(c,a){if(typeof
a!=="number"&&9===a[0]){var
b=bz(c,a[1]);return[0,b[1],b[2],[9,b[3]]]}return bz(c,a)}function
jn(b){var
a=b;for(;;){if(typeof
a!=="number"&&9===a[0]){var
a=a[1];continue}return a}}function
cD(e){var
b=e;for(;;){if(typeof
b==="number")var
c=0;else
switch(b[0]){case
0:var
b=b[2];continue;case
9:var
d=b[1],c=1;break;case
1:case
2:return a(s[4],b[1],s[1]);case
5:case
6:var
d=b[2],c=1;break;case
7:case
8:var
f=b[1],g=cD(b[2]),h=cD(f);return a(s[7],h,g);default:var
c=0}if(c){var
b=d;continue}return s[1]}}function
gt(h,o){var
c=o;for(;;)if(typeof
c==="number")return[0,h,0];else{if(0===c[0]){var
d=c[2],l=c[1];if(typeof
d!=="number"&&6===d[0])if(typeof
c[3]==="number"){var
c=[0,l,d[2],0];continue}var
p=c[3],i=gs(h,d),q=i[3],r=i[1],m=gt(i[2],p),s=m[1],t=[0,l,q,m[2]],u=function(b,a){return[0,a[1],[9,a[2]],b]};return[0,s,g(f[20],u,t,r)]}var
v=c[5],w=c[4],x=c[3],y=c[1],j=gs(h,jn(c[2])),z=j[3],A=j[2],B=j[1],k=gs(A,jn(w)),C=k[3],D=k[2],E=k[1],F=function(a){return gt(D,a)},G=a(f[17],F,v),n=b(f[46],G),H=n[2],I=n[1],J=a(e[26],E,B),K=[1,y,z,x,C,H],L=function(b,a){return[0,a[1],[9,a[2]],b]},M=g(f[20],L,K,J);return[0,g(f[20],e[6],0,I),M]}}function
jo(d,c){function
e(c){if(typeof
c==="number")return[0,0,s[1]];else{if(0===c[0]){var
j=c[3],h=c[2],d=c[1];if(typeof
j==="number"){var
q=cD(h);return[0,c,a(s[4],d,q)]}var
k=e(j),i=k[2],l=k[1];if(a(s[3],d,i)){var
r=cD(h),t=a(s[7],r,i);return[0,[0,d,h,l],a(s[4],d,t)]}return[0,l,i]}var
m=c[4],n=c[2],o=c[1],u=c[3],v=a(f[17],e,c[5]),p=b(f[46],v),w=p[1],x=g(f[20],s[7],s[1],p[2]),y=cD(m),z=cD(n),A=a(s[7],z,y),B=a(s[7],A,x);return[0,[1,o,n,u,m,w],a(s[4],o,B)]}}return gt(d,e(c)[1])}function
jp(a){if(typeof
a==="number")return 4;else
switch(a[0]){case
0:return 0;case
1:return 1;case
2:return 2;case
3:return 3;case
4:return 5;case
5:return 6;case
6:return 7;case
7:return 8;case
8:return 9;default:return 10}}function
et(f,e,c,b){var
g=b[2],h=c[2],d=a(f,c[1],b[1]);return 0===d?a(e,h,g):d}function
b$(h,g){var
c=h,b=g;for(;;){if(typeof
c==="number"){if(typeof
b==="number")return 0}else
switch(c[0]){case
0:if(typeof
b!=="number"&&0===b[0]){var
e=b[1],f=c[1],j=b[2],k=c[2];if(lX(f,e)){var
c=k,b=j;continue}return C.caml_string_compare(f,e)}break;case
1:if(typeof
b!=="number"&&1===b[0])return a$(c[1],b[1]);break;case
2:if(typeof
b!=="number"&&2===b[0])return a$(c[1],b[1]);break;case
3:if(typeof
b!=="number"&&3===b[0])return a(d[37],c[1],b[1]);break;case
4:if(typeof
b!=="number"&&4===b[0])return a(ge,c[1],b[1]);break;case
5:if(typeof
b!=="number"&&5===b[0])return et(ge,b$,[0,c[1],c[2]],[0,b[1],b[2]]);break;case
6:if(typeof
b!=="number"&&6===b[0])return et(l[23],b$,[0,c[1],c[2]],[0,b[1],b[2]]);break;case
7:if(typeof
b!=="number"&&7===b[0])return et(b$,b$,[0,c[1],c[2]],[0,b[1],b[2]]);break;case
8:if(typeof
b!=="number"&&7===b[0])return et(b$,b$,[0,c[1],c[2]],[0,b[1],b[2]]);break;default:if(typeof
b!=="number"&&9===b[0]){var
c=c[1],b=b[1];continue}}var
i=jp(b);return a$(jp(c),i)}}function
eu(b,a){if(typeof
b==="number")var
c=a;else{if(typeof
a!=="number")return[8,b,a];var
c=b}return c}function
cE(e,c){if(typeof
c!=="number")switch(c[0]){case
0:var
g=c[1];return[0,g,cE(e,c[2])];case
5:var
h=c[2];return[5,ao(e,c[1]),h]}var
f=b(d[25],e)+1|0;if(2<f>>>0)throw[0,aV,sG];switch(f){case
0:return[5,b_(e),c];case
1:return 0;default:return a(d[32],sH,e)?c:[7,[3,e],c]}}function
jq(b,a){var
c=bc(b),d=c[1];return bw(c[2])?cE(d,a):[5,b,a]}function
jr(b,a){if(typeof
b!=="number")if(typeof
a!=="number"){if(typeof
b==="number")var
c=0;else
if(3===b[0])var
f=a,e=b[1],c=1;else
var
c=0;if(!c){if(typeof
a==="number")var
d=0;else
if(3===a[0])var
f=b,e=a[1],d=1;else
var
d=0;if(!d)return[7,b,a]}return cE(e,f)}return 0}var
ca=b(b6[1],[0,b$]);function
gu(a){var
b=0;function
c(c,b,a){return eu(jq(b,c),a)}return g(ca[13],c,a,b)}function
cF(e){var
b=e;for(;;){if(typeof
b!=="number")switch(b[0]){case
0:var
b=b[2];continue;case
5:var
h=b[1],i=cF(b[2]),j=function(a){return by(h,a)};return a(ca[33],j,i);case
7:var
l=b[2],m=cF(b[1]),d=cF(l),c=gu(m),n=gu(d);if(typeof
c!=="number"&&3===c[0]){var
p=c[1],q=function(a){return ao(p,a)};return a(ca[33],q,d)}var
o=b_(sK);return a(ca[6],[7,c,n],o);case
8:var
r=b[1],s=cF(b[2]),t=cF(r),u=function(e,b,a){if(b){var
c=b[1];if(a)return[0,gp(c,a[1])];var
d=c}else{if(!a)return 0;var
d=a[1]}return[0,d]};return g(ca[8],u,t,s);case
6:case
9:var
k=b_(sJ);return a(ca[6],b,k)}var
f=b_(sI);return a(ca[6],b,f)}}function
sL(c,b){var
d=0;return Z(function(e,d,b){return eu(cE(b,a(r[27],d,c)),e)},d,b)}function
js(a){if(a){var
b=a[1],c=js(a[2]);return g(k[4],sM,b,c)}return sN}function
jt(l,h,j,a){function
c(q){var
a=q;for(;;)if(typeof
a==="number")return 0;else
switch(a[0]){case
0:var
a=a[2];continue;case
3:return[5,b(h,a[1])];case
4:return[1,b(l,go(h,a[1]))];case
5:var
r=a[2],s=b(l,go(h,a[1]));return[2,s,c(r)];case
7:var
t=a[1],u=c(a[2]);return[3,c(t),u];case
8:var
v=a[1],w=c(a[2]);return[4,c(v),w];case
1:case
2:var
m=a[1],f=0,d=j;for(;;){if(d){var
n=d[2];if(m!==d[1]){var
f=f+1|0,d=n;continue}var
i=f}else
var
o=js(j),p=g(k[4],sO,m,o),i=b(e[3],p);return[0,b(z[4],i)]}default:return b(e[3],sP)}}return c(a)}function
ev(c,a){return jt(cs,function(a){var
c=af(a);return b(z[2],c)},c,a)}function
ew(c,b){if(typeof
b==="number")return 0;else{if(0===b[0]){var
e=b[3],d=b[2],g=b[1];if(typeof
d!=="number"&&9===d[0]){var
i=d[1],j=ew([0,g,c],e);return[1,ev(c,i),j]}var
h=ew([0,g,c],e);return[0,ev(c,d),h]}var
k=b[5],l=b[4],m=b[2],n=[0,b[1],c],o=function(a){return ew(n,a)},p=a(f[17],o,k),q=ev(c,l);return[2,ev(c,m),q,p]}}function
sQ(b,a){return ew(b,jo(1+es(a)|0,a)[2])}function
bd(f,u){var
c=u;for(;;)if(typeof
c==="number")return[0,K,1];else
switch(c[0]){case
0:var
c=c[2];continue;case
3:var
g=c[1],h=a(d[37],g,sR),v=0===h?1:1===h?2:b(e[3],sS);return[0,G(0,g,K),v];case
4:var
i=c[1];return[0,by(i,i),1];case
5:var
j=c[2],l=c[1],m=bd(f,j),n=m[2],o=m[1];if(0===n)return[0,by(l,o),0];var
w=di(n);Iu(k[1],e[28],sT,b8,l,aE,j,b8,o,w);return b(e[3],sU);case
6:var
x=c[1],p=bd(f,c[2]),y=p[2];return[0,cy([1,x],p[1]),y];case
7:var
z=c[2],q=bd(f,c[1]),A=q[2],B=q[1],r=bd(f,z),C=r[1],D=gm(A,r[2]);return[0,by(B,C),D];case
8:var
E=c[2],s=bd(f,c[1]),F=s[2],H=s[1],t=bd(f,E),I=t[1],J=ej(F,t[2]);return[0,gp(H,I),J];case
9:var
c=c[1];continue;default:return b(f,c[1])}}function
sW(o,n){var
d=o,c=n;for(;;)if(typeof
c==="number")return b(e[3],sX);else{if(0===c[0]){var
j=c[3],p=c[2],q=c[1],l=bd(function(c){return function(b){return a(r[27],b,c)}}(d),p),f=l[2],h=l[1],i=bc(h),m=i[1],s=bw(i[2])?1-a(ei(f),m,sV):0;if(s)return 1;if(0===j){var
t=di(f);S(k[1],e[28],sY,ep,h,t);return 0}var
d=g(r[4],q,[0,h,f],d),c=j;continue}var
u=c[4],v=c[2];bd(function(b){return a(r[27],b,d)},v);bd(function(b){return a(r[27],b,d)},u);return b(e[3],sZ)}}function
s0(b,a){return[0,a[1],[0,b,a[2]]]}function
ju(c,a){var
b=a[1],d=a[2],e=b[1],f=di(b[2]);return fr(k[1],c,s1,ep,e,f,aE,d)}function
s2(c,b){var
d=g(k[1],c,s3,ju);return a(f[15],d,b)}var
jv=[aS,s4,aR(0)],s5=[0,[0,K,0],0];function
s6(a){return[0,[0,b_(a),1],[3,a]]}function
s7(c){var
a=c[1],e=c[2],f=a[2],g=a[1];return[0,[0,G(0,b(d[3],a[3]),g),f],e]}function
ex(b,a){var
c=a[1],d=b[1],e=c[2],f=c[1],g=d[2],h=d[1],i=jr(b[2],a[2]),j=gm(g,e);return[0,[0,by(h,f),j],i]}function
ey(b,a){var
c=a[1],d=b[1],e=c[2],f=c[1],g=d[2],h=d[1],i=eu(b[2],a[2]),j=ej(g,e);return[0,[0,aW(h,f),j],i]}function
ez(b,e){var
f=e[2],g=e[1],c=g[2],h=g[1];if(0===c){var
k=jq(b,f);return[0,[0,by(b,h),c],k]}var
i=bc(b),j=i[1];if(bw(i[2]))if(a(d[28],j,s8)){var
l=cE(j,f);return[0,[0,by(b,h),c],l]}throw jv}function
s9(g){var
h=g[2],i=g[1],j=i[2],k=i[1],m=bc(k),f=m[1],c=gh(m[2]);if(!a(l[24],l[2],c))if(!a(d[26],f,s_)){var
p=l[2],q=a4(f);if(a(l[24],q,p)){var
n=a(d[9],f,[1,c]),o=b(d[22],n);if(a(d[26],n,o))return 0;switch(j){case
0:return[0,[0,[0,G(0,s$,K),0],[6,c,h]]];case
1:return[0,[0,[0,G(0,o,cy([1,c],k)),j],[6,c,h]]];default:return b(e[3],ta)}}}return 0}function
tb(f){var
c=bc(f),a=c[1];if(bw(c[2])){var
e=b(d[25],a),g=0===e?tc:1===e?[0,1,2,[3,a]]:[0,0,2,[3,b(d[3],a)]];return[0,g]}return 0}function
gv(d,c){var
b=tb(c);if(b)return[0,b[1]];try{var
k=function(a){return cw(c,a[1][1])},g=a(f[33],k,d),l=[0,[0,1,g[1][2],g[2]]];return l}catch(b){b=n(b);if(b===L){var
h=cz(c);try{var
i=function(a){return cw(h,a[1][1])},e=a(f[33],i,d),j=[0,[0,0,e[1][2],e[2]]];return j}catch(a){a=n(a);if(a===L)return 0;throw a}}throw b}}function
gw(f,a){var
b=a[2],c=a[1],d=c[2],e=c[1];return f?[0,[0,e,d],b]:[0,[0,cz(e),d],b]}function
eA(q,I,H,G){var
J=G[1],K=I[1],j=[0,[0,K[1],K[2]],I[2]],i=[0,[0,J[1],J[2]],G[2]];for(;;){var
m=i[2],s=i[1],d=s[2],k=s[1],f=j[2],t=j[1],a=t[2],c=t[1],l=eq(H,c)[1],g=eq(H,k)[1];if(bw(g))var
h=[0,[0,[0,k,d],m]];else
if(0===a){if(0===d){var
M=ez(cz(g),[0,[0,c,a],f]),u=ey(ez(l,[0,[0,k,d],m]),M),v=u[1],j=[0,[0,c,a],f],i=[0,[0,v[1],v[2]],u[2]];continue}var
w=gv(q,l);if(w){var
n=w[1],x=n[1],N=gw(x,[0,[0,l,n[2]],n[3]]),O=x?cz(g):g,P=ez(O,[0,[0,c,a],f]),y=ey(ex(N,[0,[0,k,d],m]),P),z=y[1],j=[0,[0,c,a],f],i=[0,[0,z[1],z[2]],y[2]];continue}var
h=0}else
if(0===d)var
h=b(e[3],td);else{var
A=gv(q,l),B=gv(q,g);if(A)if(B){var
o=B[1],C=o[1],p=A[1],D=p[1],Q=o[3],R=o[2],S=p[3],T=p[2];if(D!==C){var
U=ex(gw(C,[0,[0,g,R],Q]),[0,[0,c,a],f]),E=ey(ex(gw(D,[0,[0,l,T],S]),[0,[0,k,d],m]),U),F=E[1],j=[0,[0,c,a],f],i=[0,[0,F[1],F[2]],E[2]];continue}var
h=0,r=1}else
var
r=0;else
var
r=0;if(!r)var
h=0}if(h){var
L=h[1],V=L[1];return[0,[0,V,gu(cF(L[2]))]]}return 0}}function
eB(e,c){var
b=c[1],f=b[2],g=b[1];function
h(b){if(e){var
c=a(d[26],b,te);return c?c:a(d[26],b,tf)}return 1}return 0===f?jm(h,g):0}function
tg(a){var
f=1,b=bu(function(a){return eB(f,a)},a),c=b[1],g=b[2];if(c){var
d=c[1],h=d[2],i=d[1],e=d3(function(b){return eA(a,h,i,b)},g);return e?e[1]:a}return a}function
th(a){return d5(function(e){var
f=1,b=bu(function(a){return eB(f,a)},e),c=b[1],g=b[2];if(c){var
d=c[1],h=d[2],i=d[1];return d3(function(b){return eA(a,h,i,b)},g)}return 0},a)}var
av=[0,jv,s0,s7,ju,s2,s5,s6,ex,ey,ez,s9,eA,th,tg,function(c,b){function
d(a){return eB(c,a)}return iR(d,function(d,c){var
e=c[1],f=e[1],g=d[1],h=c[2],i=e[2],j=d[2],k=gq(f);return a(s[3],g,k)?eA(b,j,g,[0,[0,f,i],h]):0},b)},eB],R=[0,er,cC,es,jo,aE,gr,eu,cE,jr,sQ,jt,sL,bd,sW],ai=[0,[0,r8,bx,dj],eo,ji,go,r_,sh,gq,sf,se,jk,b_,jm,jl,by,eq,sn,jj,ep,si],be=[0,dg,rW,je,jf,rZ,jd,jg,dh],eC=[0,ja,df,ef,eg,i9,i8,gj,i_,ee,i$];aA(995,[0,q$,gi,eC,cB,be,ei,ej,jh,eh,ai,R,r6,gm,av],"Micromega_plugin__Polynomial");var
dl=b(m[20][1],[0,a$]),aN=b(bb[25],[0,cw,iY]),dm=[aS,ti,aR(0)];function
dn(b,a){switch(a[0]){case
0:return g(k[1],b,tj,a[1]);case
1:return fr(k[1],b,tk,a[1],dn,a[2],dn,a[3]);default:return V(k[1],b,tl,dn,a[1],dn,a[2])}}function
tm(b,a){var
c=b[4],d=b[3],f=a[4],g=a[2],h=a[1],i=b[2],j=b[1];if(d===a[3])if(c===f){var
e=fy(j,h);return e?[0,[0,e[1],[2,i,g],d,c]]:0}throw[0,aV,tn]}function
to(e,b,d){try{var
c=a(aN[7],d,e),f=tm(b,c[1]);if(f){c[1]=f[1];var
h=0;return h}throw[0,dm,[2,b[2],c[1][2]]]}catch(a){a=n(a);if(a===L)return g(aN[10],d,e,[0,b]);throw a}}var
eD=[aS,tp,aR(0)];function
gx(d,c,a){var
e=gi[1];if(b(aN[15],a)<e)return to(d,c,a);throw eD}function
gy(i,c){var
j=fx(c[1]);if(j){var
k=j[1],f=k[2],g=k[1],l=aX(i);if(l){var
h=l[1][2],e=function(b){return a(d[9],b,h)};if(1===b(d[25],h))var
n=c[4],o=c[3],p=c[2],q=a(aY[16],e,f),m=[0,[0,a(aY[16],e,g),q],p,o,n];else
var
r=c[3],s=c[4],t=c[2],u=a(aY[16],e,g),m=[0,[0,a(aY[16],e,f),u],t,s,r];return[0,cy(h,i),m]}return fz([0,g,f],tq)?1:0}return 0}function
jw(a){return Z(function(a,h,g){var
c=a[2],e=a[1],f=b(d[25],g);if(0===f)throw[0,aV,ts];return 1===f?[0,e,c+1|0]:[0,e+1|0,c]},tr,a)}function
jx(a,f){var
b=a[3],c=a[1],g=a[2],d=jw(c),h=d[2],i=d[1],j=[0,f];switch(g){case
0:var
e=[0,[0,b],[0,b]];break;case
1:var
e=[0,[0,b],0];break;default:throw eh}return gy(c,[0,e,j,h,i])}function
tt(d){var
c=b(aN[1],1000);function
e(b,a){return[0,a,b]}var
f=a(m[17][13],e,d),h=dl[1];function
i(e,d){var
f=d[2],g=d[1],b=jx(g,f);if(typeof
b==="number"){if(0===b)throw[0,dm,[0,f]];return e}gx(b[1],b[2],c);var
h=g[1];return Z(function(c,b,d){return a(dl[4],b,c)},e,h)}return[0,c,g(m[17][15],i,h,f)]}function
jy(a){var
b=a[1],c=0;function
d(c,b,a){return[0,[0,c,b[1]],a]}return g(aN[14],d,b,c)}function
gz(e,c){var
f=c[2],g=e[2],i=c[1],j=e[1];if(a(d[31],g,tu))if(a(d[31],f,tv)){var
h=a(d[9],tw,f),b=gd(a(d[9],tx,g),j,h,i);return[0,b,jw(b)]}throw[0,aV,ty]}function
tz(i,c){var
h=c[1];function
j(k,q,j){var
a=q[1],f=j[3],g=j[2],h=j[1],c=au(i,k);if(0===c[0])if(0===c[1])return[0,h,[0,[0,k,a],g],f];function
e(d,b){return b?[0,[0,c,k,[0,[0,[0,b[1]],0],a[2],a[3],a[4]]],d]:d}var
l=a[1],m=l[2],n=l[1];if(1===b(d[25],c)){var
o=e(f,m);return[0,e(h,n),g,o]}var
p=e(f,n);return[0,e(h,m),g,p]}var
e=g(aN[14],j,h,tA),k=e[3],l=e[2],n=e[1],o=b(aN[15],c[1]),f=b(aN[1],o);function
p(a){return g(aN[10],f,a[1],[0,a[2]])}a(m[17][11],p,l);function
q(e){function
c(g){var
h=g[3],j=g[1],k=e[3],l=e[1],p=g[2],q=e[2],r=h[1],s=b(aY[7],k[1][1]),t=b(aY[7],r[1]),u=b(d[3],j),v=a(d[9],t,u),w=a(d[9],s,l),x=a(d[1],w,v),m=gz([0,q,l],[0,p,b(d[3],j)]),n=m[2],o=[0,[0,[0,x],0],[1,i,k[2],h[2]],n[2],n[1]],c=gy(m[1],o);if(typeof
c==="number"){if(0===c)throw[0,dm,o[2]];return 0}return gx(c[1],c[2],f)}return a(m[17][11],c,k)}a(m[17][11],q,n);return[0,f,a(dl[6],i,c[2])]}function
tC(e,q,C,B,c){var
r=au(e,q),f=b(aN[15],c[1]),s=b(aN[1],f),g=c[1];function
h(g,D){var
h=D[1],c=au(e,g);if(0===c[0])if(0===c[1])var
i=[0,g,h],j=1;else
var
j=0;else
var
j=0;if(!j)var
k=a(d[30],c,tB)?b(d[3],r):r,l=b(d[15],c),m=gz([0,q,k],[0,g,l]),n=m[2],u=n[2],v=n[1],w=m[1],x=a(d[9],C,k),o=function(b){var
c=a(d[9],b,l);return a(d[1],x,c)},p=h[1],y=p[1],z=a(aY[16],o,p[2]),A=[0,a(aY[16],o,y),z],i=[0,w,[0,A,[1,e,B,h[2]],u,v]];var
t=i[2],f=gy(i[1],t);if(typeof
f==="number"){if(0===f)throw[0,dm,t[2]];return 0}return gx(f[1],f[2],s)}a(aN[12],h,g);return[0,s,a(dl[6],e,c[2])]}var
H=b(tD[1],[0,a$]);function
jz(x,w,c){function
f(p,o,y){var
t=[0,tE,K],i=Z(function(e,c,b){var
f=e[2],g=e[1];try{var
h=a(H[23],c,x),i=a(d[6],h,b),j=[0,a(d[1],g,i),f];return j}catch(a){a=n(a);if(a===L)return[0,g,G(c,b,f)];throw a}},t,p),q=i[2],f=i[1],r=au(w,q),g=o[1][1];function
c(b){var
c=a(d[4],b,f);return a(d[9],c,r)}var
j=g[2],l=g[1],m=b(d[25],r);if(0===m)var
h=fz(g,f)?tF:b(e[3],tG);else
if(1===m)var
u=a(aY[16],c,j),h=[0,a(aY[16],c,l),u];else
var
v=a(aY[16],c,l),h=[0,a(aY[16],c,j),v];var
s=fy(y,h);if(s)return s[1];var
z=b(d[40],f);fr(k[1],e[28],tI,b8,p,z,b8,q);D(k[1],e[28],tJ,hV,o[1][1]);return b(e[3],tK)}return g(aN[14],f,c,tH)}function
tT(g,k,j,d,c){function
e(c,f){var
l=b(k,c);try{var
r=function(a){return a[1][1]!==g?1:0},d=a(m[17][27],r,l)[1],i=d[1],s=e(tC(i,d[2],d[3],d[4],c),[0,[0,i,c],f]);return s}catch(d){d=n(d);if(d===L){var
o=b(j,c);try{var
p=function(a){return a[1]!==g?1:0},h=a(m[17][27],p,o)[1],q=e(tz(h,c),[0,[0,h,c],f]);return q}catch(a){a=n(a);if(a===L)return[0,[0,c,f]];throw a}}throw d}}return e(d,c)}function
jA(d,c,b,a){try{var
e=tT(d,c,b,tt(a),0);return e}catch(a){a=n(a);if(a[1]===dm)return[1,a[2]];throw a}}function
jB(c){var
e=c[2],f=[0,0,jy(c)];function
h(x,w){var
e=w[2],c=0,h=0,i=0,f=0,G=w[1];for(;;){if(e){var
j=e[2],n=e[1],a=n[2],o=n[1],p=aX(o);if(p){var
l=p[1],q=l[3],y=l[2];if(x===l[1]){var
k=function(b){return function(a,c){return c?[0,b[4]+b[3]|0,a]:a}}(a),r=a[1],s=r[2],t=r[1];if(1===b(d[25],y)){var
z=k(f,s),e=j,c=[0,[0,q,a],c],h=k(h,t),f=z;continue}var
A=k(f,t),e=j,c=[0,[0,q,a],c],h=k(h,s),f=A;continue}var
e=j,c=[0,[0,o,a],c],i=(a[4]+a[3]|0)+i|0;continue}var
e=j,c=[0,[0,K,a],c],i=(a[4]+a[3]|0)+i|0;continue}var
u=b(m[17][1],h),B=0,C=function(b,a){return b+a|0},D=g(m[17][15],C,B,h),v=b(m[17][1],f),E=0,F=function(b,a){return b+a|0};return[0,[0,[0,x,i+v*D+u*g(m[17][15],F,E,f)-v*u],G],c]}}var
i=g(dl[15],h,e,f)[1];function
j(b,a){return C.caml_float_compare(b[2],a[2])}return a(m[17][39],j,i)}function
jC(b){var
c=b[1];if(c){var
e=b[2];if(e)return a(d[26],c[1],e[1])}return 0}function
jD(b,g){var
a=g;for(;;){var
c=aX(a);if(c){var
d=c[1],e=d[3],f=d[1];if(f===b)return[0,1,e];if(f<b){var
a=e;continue}return[0,0,a]}return[0,0,K]}}function
jE(I){var
l=jy(I),J=0;function
K(c,e){var
b=e[2],f=b[1],g=f[1],j=e[1];if(g){var
h=f[2];if(h){var
i=g[1];return a(d[26],i,h[1])?[0,[0,j,i,b[2],b[4]+b[3]|0],c]:c}}return c}var
n=g(m[17][15],K,J,l),b=n;for(;;){if(b){var
o=b[2],c=b[1],p=c[1],x=c[4],y=c[3],z=c[2],q=aX(p);if(!q){var
b=o;continue}var
r=q[1],A=r[1];if(!bw(r[3])){var
b=o;continue}var
k=[0,[0,A,p,z,y,x]]}else
var
k=0;if(k)var
h=[0,k[1]];else{var
e=n;a:for(;;){if(e){var
f=e[1],w=f[1],s=w,E=e[2],F=f[4],G=f[3],H=f[2];for(;;){var
t=aX(s);if(t){var
u=t[1],v=u[1],D=u[3],B=0,C=function(d){return function(a,b){var
c=b[2];return jD(d,b[1])[1]?jC(c[1])?a+1|0:a:a}}(v);if(2!==g(m[17][15],C,B,l)){var
s=D;continue}var
j=[0,v]}else
var
j=0;if(!j){var
e=E;continue a}var
h=[0,[0,j[1],w,H,G,F]];break}}else
var
h=0;break}}if(h){var
i=h[1];return[0,[0,[0,i[1],i[2],i[3],i[4]],0],0]}var
L=0,M=function(u,e){var
r=e[1],n=r,m=l,i=u,v=e[4],w=e[3],x=e[2];b:for(;;){var
o=aX(n);if(o){var
p=o[1],q=p[1],c=m,b=0,a=0,s=p[3],t=v-1|0;for(;;){if(c){var
f=c[2],j=c[1],d=j[2],g=d[3]+d[4]|0,k=jD(q,j[1]),h=k[2];if(0===k[1]){var
c=f,b=b+g|0,a=[0,[0,h,d],a];continue}if(jC(d[1])){var
c=f,b=b+g|0,a=[0,[0,h,d],a];continue}var
c=f,b=(b+g|0)+t|0,a=[0,[0,h,d],a];continue}var
n=s,m=a,i=[0,[0,[0,q,r,x,w],b],i];continue b}}return i}},N=g(m[17][15],M,L,n),O=function(b,a){return a$(b[2],a[2])};return a(m[17][39],O,N)}}function
tU(h,d){var
i=0;function
j(c,b){var
d=i1(b[1]);return a(e[1][5],c,d)}var
c=g(m[17][15],j,i,d),f=jA(c,jE,jB,[0,[0,G(c,tW,h),0,tV],d]);if(0===f[0]){var
l=f[1][1];try{var
p=[0,jz(H[1],c,l[1])];return p}catch(c){c=n(c);if(b(cb[18],c)){var
o=b(d4[1],c);a(k[2],tX,o);return 0}throw c}}return 0}function
tY(w){var
j=jA(e[8],jE,jB,w);if(0===j[0]){var
i=j[1][2],h=H[1];for(;;){if(i){var
r=i[1],s=r[1],x=i[2],k=jz(h,s,r[2][1]),m=k[1];if(m){var
n=k[2],c=m[1];if(n){var
o=n[1];if(a(d[29],c,tL))if(a(d[29],tM,o))var
f=tN,l=1;else
var
l=0;else
var
l=0;if(!l)var
t=b(d[22],o),u=b(d[24],c),f=a(d[29],u,t)?b(d[24],c):c}else
var
f=a(d[29],c,tO)?tP:b(d[24],c)}else{var
p=k[2];if(p)var
q=p[1],v=b(d[22],q),f=a(d[29],tQ,v)?tR:b(d[22],q);else
var
f=tS}var
i=x,h=g(H[4],s,f,h);continue}var
y=function(c,b,a){return G(c,b,a)};return[0,g(H[12],y,h,K)]}}return[1,j[1]]}function
cc(b,a){return gz(b,a)[1]}function
eE(b,a){if(0===b)if(0===a)return 0;return 1}function
jF(r,q,p){var
j=p[2],k=p[1],l=q[2],m=q[1],n=j[3],f=j[2],g=j[1],o=l[3],h=l[2],i=l[1],c=au(r,i),e=au(r,g),U=0===c[0]?0===c[1]?1:0:0;if(!U){var
V=0===e[0]?0===e[1]?1:0:0;if(!V){var
s=b(d[25],e);if(-1===fq(b(d[25],c),s)){var
t=b(d[15],e),u=a(d[9],n,t),v=b(d[15],c),w=a(d[9],o,v),x=a(d[1],w,u),y=eE(h,f),z=[0,g,b(d[15],e)],A=[0,cc([0,i,b(d[15],c)],z),y,x],B=[0,k,b(d[15],e)];return[0,[0,cc([0,m,b(d[15],c)],B),A]]}if(0===h){var
C=a(d[9],n,tZ),D=a(d[9],c,e),E=b(d[3],D),F=a(d[9],o,E),G=a(d[1],F,C),H=eE(h,f),I=a(d[9],c,e),J=[0,cc([0,i,b(d[3],I)],[0,g,t0]),H,G],K=a(d[9],c,e);return[0,[0,cc([0,m,b(d[3],K)],[0,k,t1]),J]]}if(0===f){var
L=a(d[9],o,t2),M=a(d[9],e,c),N=b(d[3],M),O=a(d[9],n,N),P=a(d[1],O,L),Q=eE(h,f),R=a(d[9],e,c),S=[0,cc([0,g,b(d[3],R)],[0,i,t3]),Q,P],T=a(d[9],e,c);return[0,[0,cc([0,k,b(d[3],T)],[0,m,t4]),S]]}return 0}}return 0}var
jG=[0,function(y,c){function
f(c){switch(c[0]){case
0:var
k=c[1],z=a(m[17][7],y,k);return[0,[0,G(k,t9,K),z],0];case
1:var
A=c[3],B=c[1],C=f(c[2]),D=f(A),v=0,w=function(a,c){function
b(a,d){var
b=jF(B,c,d);return b?[0,b[1],a]:a}return g(m[17][15],b,a,D)};return g(m[17][15],w,v,C);default:var
E=c[2],F=f(c[1]),H=f(E),I=a(m[18],F,H),x=function(b,d){var
c=d[2],e=d[1];if(0===b[0]){var
f=b[1],a=jx(c,0);return typeof
a==="number"?0===a?[1,[0,e,c]]:[0,f]:[0,[0,[0,e,c,a[1],a[2]],f]]}return b},i=g(m[17][15],x,t5,I);if(0===i[0]){var
J=i[1],L=function(k,j){if(0===k[0]){var
t=k[1],l=j[2],m=j[1],n=j[4][1],x=t[2],y=t[1],u=n[2],v=n[1],o=function(e,c,b){if(c){var
f=c[1][3];if(b){var
d=b[1];return a(e,f,d)?[0,[0,m,l,d]]:c}return c}return b?[0,[0,m,l,b[1]]]:0},c=o(d[29],y,v),f=o(d[30],x,u);if(c)if(f){var
g=f[1],h=g[2],p=g[1],i=c[1],q=i[1],w=i[2];if(a(d[29],i[3],g[3]))return[0,[0,c,f]];var
r=aX(h[1]);if(r){var
s=jF(r[1][1],[0,q,w],[0,p,h]);return s?[1,s[1]]:b(e[3],t6)}return[1,[0,cc([0,q,t8],[0,p,t7]),h]]}return[0,[0,c,f]]}return k},j=g(m[17][15],L,t_,J);if(0===j[0]){var
l=j[1],h=l[2],n=l[1];if(n){var
o=n[1],p=o[2],q=o[1];if(h){var
r=h[1];return[0,[0,q,p],[0,[0,r[1],r[2]],0]]}var
t=p,s=q}else{if(!h)return 0;var
u=h[1],t=u[2],s=u[1]}return[0,[0,s,t],0]}return[0,j[1],0]}return[0,i[1],0]}}return f(c)},eE],eF=[0,tY,tU];aA(1001,[0,[0,H[1],H[2],H[3],H[4],H[5],H[6],H[7],H[8],H[9],H[10],H[11],H[12],H[13],H[14],H[15],H[16],H[17],H[18],H[19],H[20],H[21],H[22],H[23],H[24],H[25],H[26]],eF,dn,jG,eD],"Micromega_plugin__Mfourier");function
gA(c,b){var
a=b[2];return a?c===a[1]?1:0:0}function
dp(b,a){var
c=a[1]<=b?1:0,d=c?1-gA(b,a):c;return d}function
eG(a){return[0,a,0]}function
jH(b,a){return[0,a[1],[0,b]]}function
ua(c,b){return eb(function(e,b){return a(d[28],b,ub)?0:dp(e,c)},b)}function
uc(c,b){try{var
a=bc(b),d=a[1],e=ua(c,a[2])?[0,d]:0;return e}catch(a){a=n(a);if(a===L)return 0;throw a}}function
gB(f,d,c){try{var
g=a(r[27],d,c);return g}catch(a){a=n(a);if(a===L)return b(e[3],f);throw a}}function
jI(j,f,c){var
k=gB(up,f,j),i=au(c,k);if(a(d[26],i,uh))var
h=b(e[3],ui);else
var
l=a(d[9],uj,i),h=ao(l,G(f,ul,G(c,uk,k)));var
o=a(r[7],f,j);function
m(b){var
e=au(c,b);return a(d[26],e,um)?b:gd(e,h,uo,G(c,un,b))}var
n=a(r[33],m,o);return g(r[4],c,h,n)}function
ur(b,a){return 0}var
us=[0,b(r[10],ur)];b(f6[1],us);function
gC(D,h,k,C){var
c=C;for(;;){if(!D){var
G=de(a(r[27],h,c));if(a(d[30],G,uu))return[0,c,0]}var
s=gB(ug,h,c),t=uc(k,s);if(t)var
f=[0,[0,t[1]]];else{var
p=bc(s)[2];for(;;){var
q=aX(p);if(q){var
l=q[1],m=l[1],x=l[3];if(a(d[27],l[2],ud)){if(dp(m,k)){var
p=x;continue}var
j=[0,m,-1]}else
var
j=[0,m,1]}else
var
j=b(e[3],ue);var
n=j[1],z=j[2],A=a(r[7],h,c),y=0,v=a(r[39],k[1],A),w=function(p,q){return function(e,g,c){if(gA(e,k))return c;var
j=au(q,g),m=a(d[6],[0,p],j);if(a(d[27],m,uf)){var
n=de(g),o=a(d[9],n,j),f=b(d[15],o);if(c){var
h=c[1],i=h[2],l=h[1];return a(d[27],i,f)?c:a(d[27],f,i)?[0,[0,e,f]]:bX(l,e)?c:[0,[0,e,f]]}return[0,[0,e,f]]}return c}}(z,n),o=g(r[13],w,v,y);if(o)var
u=o[1],f=[1,u[1],n,u[2]];else
var
f=[0,[1,n]];break}}if(0===f[0]){var
i=f[1];if(typeof
i==="number")throw[0,jJ,ut];else{if(0===i[0])return[0,c,i];var
E=i[1],B=de(a(r[27],h,c)),F=a(d[30],B,uq)?c:jI(c,h,E);return[0,F,i]}}var
c=jI(c,f[1],f[2]);continue}}function
gD(d,e,c){var
b=Z(function(d,c,b){try{var
f=aW(ao(b,a(r[27],c,e)),d);return f}catch(a){a=n(a);if(a===L)return aW(G(c,b,K),d);throw a}},K,c);return g(r[4],d,b,e)}function
jK(j,b,i,h,g){var
f=gC(j,b,h,gD(b,g,i)),c=f[2],e=f[1];return typeof
c==="number"?[1,e,0]:0===c[0]?a(d[30],c[1],uv)?[1,e,0]:[0,G(b,uz,G(0,uy,ao(ux,gB(uw,b,e))))]:[1,e,[0,c[1]]]}function
eH(d){try{var
e=s[1],h=function(c,b){var
d=gf(b[1]);return a(s[7],c,d)},i=g(f[20],h,e,d),j=b(s[24],i),c=j}catch(a){a=n(a);if(a!==L)throw a;var
c=0}return 1+c|0}function
eI(m,l){var
c=0,a=m,h=r[1],f=l,e=0;for(;;){if(f){var
j=f[2],i=f[1];switch(i[2]){case
0:var
n=i[1],k=G(0,b(d[3],i[3]),n),o=ao(uA,k),p=g(r[4],a+1|0,[0,c,0],h),q=g(r[4],a,[0,c,1],p),c=c+1|0,s=[0,[0,a,k],[0,[0,a+1|0,o],e]],a=a+2|0,h=q,f=j,e=s;continue;case
1:var
t=i[1],u=[0,[0,a,G(0,b(d[3],i[3]),t)],e],v=g(r[4],a,[0,c,1],h),c=c+1|0,a=a+1|0,h=v,f=j,e=u;continue;default:throw eh}}return[0,a,h,e]}}function
gE(c,a){function
b(b,d,a){return dp(b,c)?a:G(b,de(d),a)}return g(r[13],b,a,K)}function
eJ(E,D,f,C){var
h=D,g=C;for(;;){var
n=G(0,uB,gE(f,g));if(h){var
t=h[1],u=t[2],A=h[2],B=t[1],c=A,o=ec(n,u),e=[0,B,u],b=0;for(;;){var
j=e[2],k=e[1];if(c){var
p=c[2],q=c[1],l=q[2],r=q[1],s=ec(n,l);if(a(d[29],s,o)){var
c=p,o=s,e=[0,r,l],b=[0,[0,k,j],b];continue}var
c=p,e=[0,k,j],b=[0,[0,r,l],b];continue}var
m=[0,[0,[0,k,j],b]];break}}else
var
m=0;if(m){var
v=m[1],w=v[2],x=v[1],y=x[1],F=x[2],i=jK(E,y,F,jH(y,f),g);if(0===i[0])return[1,i[1]];var
z=i[1],H=i[2];if(w){var
h=w,g=z;continue}return[0,[0,f,z,H]]}return[0,[0,f,g,0]]}}function
jL(c){var
e=eH(c),f=eI(e,c),h=f[3],j=f[2],i=r[1],g=eJ(0,h,eG(e),i);if(0===g[0])return 0;var
k=g[1];return[0,cA(Z(function(g,f,c){var
e=a(r[27],f,j),h=e[1],i=e[2]?c:b(d[3],c);return G(h,i,g)},K,k))]}function
jM(a){var
b=eH(a),e=eI(b,a)[3],f=r[1],c=eJ(0,e,eG(b),f);if(0===c[0]){var
d=c[1];return[0,gE(d[1],d[2])]}return 0}function
jN(e,c){var
a=eH(c),k=eI(a+1|0,c)[3];function
f(f,e){var
a=e[2];if(typeof
a==="number")return 0;else{if(0===a[0]){var
c=a[1],g=f?c:b(d[3],c);return[0,g]}return 0}}var
l=r[1],g=eJ(0,k,eG(a),l);if(0===g[0]){var
h=g[1],i=h[2],j=h[1],m=f(1,gC(1,a,j,gD(a,i,e)));return[0,[0,f(0,gC(1,a,j,gD(a,i,cz(e)))),m]]}return 0}function
eK(c){var
e=b(d[22],c);return a(d[4],c,e)}var
jO=[aS,uC,aR(0)];function
uD(c,d,b){var
e=G(c,uE,K);try{var
f=function(a,f){var
b=dp(a,d);if(b){if(cw(e,f))throw[0,jO,a];var
c=0}else
var
c=b;return c};a(r[12],f,b);var
g=0;return g}catch(a){a=n(a);if(a[1]===jO)return[0,a[2]];throw a}}function
jP(i,z,o,s,h,m,g){var
j=g[2],k=g[1],c=eK(bc(j)[1]);if(a(d[26],c,uH))return 0;var
p=a(d[9],uJ,uI);if(a(d[27],c,p))var
e=a(d[9],uK,c),q=b(d[20],e)?a(d[4],e,uL):b(d[22],e),l=q;else
var
l=uR;function
t(e){var
b=eK(e),f=a(d[4],uM,c);if(a(d[29],b,f)){var
g=a(d[4],uN,c);return a(d[9],b,g)}var
h=a(d[4],uO,b);return a(d[9],h,c)}var
u=[0,t,[0,function(b){return eK(a(d[6],l,b))},0]];function
v(n){var
k=G(0,uF,j),c=b(i5(function(e,c){var
b=1-dp(e,h);if(b){var
f=eK(c);return a(d[31],f,uG)}return b}),k),e=c[2],f=c[1],g=bw(f)?[0,e]:[0,Z(function(a,d,c){var
b=uD(d,h,m);return b?G(b[1],c,a):a},e,f)];if(g)var
l=g[1],i=Z(function(d,c,a){return G(c,b(n,a),d)},K,l);else
var
i=K;return cA(i)}var
w=a(f[17],v,u);function
x(e){var
c=av[6];return Z(function(h,e,c){try{var
g=a(r[27],e,s),l=g[1],m=g[2]?c:b(d[3],c),o=a(r[27],l,i),p=gc(m),q=a(av[10],p,o),f=q}catch(b){b=n(b);if(b!==L)throw b;var
j=a(r[27],e,i),k=gc(c),f=a(av[10],k,j)}return a(av[9],h,f)},c,e)}var
y=a(f[17],x,w);return iO(function(g){var
d=b(av[11],g);if(d){var
e=d[1],f=e[2],c=e[1];if(0===c[2])return[0,[0,k,[0,c,f]]];var
h=G(0,uP,o),i=ec(c[1],h);return a(ei(1),i,uQ)?0:[0,[0,k,[0,c,f]]]}return 0},y)}function
jQ(m){var
h=b(f[46],m)[1],i=eH(h),c=eI(i,h),l=c[2],q=c[3],u=c[1],v=a(f[17],av[3],m),o=[0,0,r[1]];function
p(a,c){var
b=a[1];return[0,b+1|0,g(r[4],b,c,a[2])]}var
s=[0,0],w=g(f[20],p,o,v)[2];function
t(h,u,c,m){s[1]++;if(0===m[0]){var
v=m[1],f=v[2],j=v[1],w=gE(j,f);if(0===(s[1]%2|0))var
H=0,I=function(c,b,a){return a?[0,a[1]]:jP(h,u,w,l,j,f,[0,c,b])},o=g(r[13],I,f,H);else
var
J=0,K=function(t,s,c){var
g=jP(h,u,w,l,j,f,[0,t,s]);if(g){var
e=g[1];if(c){var
i=c[1],k=i[2],m=k[2],n=k[1],o=e[2],p=o[2],q=o[1],v=n[2],x=n[1],y=i[1],z=q[2],A=q[1],B=e[1],C=b(R[1],m),D=b(R[1],p),E=a(d[27],D,C)?[0,B,[0,[0,A,z],p]]:[0,y,[0,[0,x,v],m]];return[0,E]}var
r=e}else{if(!c)return 0;var
r=c[1]}return[0,r]},o=g(r[13],K,f,J);if(o){var
x=o[1],y=x[2],z=y[2],A=y[1],B=A[2],C=A[1],O=x[1];if(0===B)return[0,[0,c,[9,z],0]];var
p=jH(c,j),i=jK(1,c,C,p,f);if(0===i[0])var
D=[1,i[1]];else{var
M=i[2],N=i[1];if(gA(c,p))var
q=[0,p[1],0];else
var
F=a(k[4],t$,c),q=b(e[3],F);var
D=[0,[0,q,N,M]]}var
E=t(g(r[4],c,[0,[0,C,B],[2,c]],h),[0,O],c+1|0,D);return E?[0,[0,c,[9,z],E[1]]]:0}return 0}var
P=0,Q=cA(m[1]),G=0;return[0,[0,c,Z(function(i,e,c){try{var
g=a(r[27],e,l),k=g[2],m=a(r[27],g[1],h)[2],o=k?c:b(d[3],c),p=a(R[8],o,m),f=p}catch(b){b=n(b);if(b!==L)throw b;var
j=a(r[27],e,h)[2],f=a(R[8],c,j)}return a(R[7],i,f)},G,Q),P]]}var
x=r[1],j=t(w,0,u,eJ(1,q,eG(i),x));return j?[0,j[1]]:0}aA(1003,[0,jN,jM,jL,jQ],"Micromega_plugin__Simplex");function
a5(f,c){if(typeof
c==="number")return a(e[55],f,uS);else
switch(c[0]){case
0:var
m=b(d[40],c[1]);return a(e[55],f,m);case
1:return g(k[1],f,uT,c[1]);case
2:return D(k[1],f,uU,a5,c[1]);case
3:var
h=c[1];return V(k[1],f,uV,a5,h[1],a5,h[2]);case
4:var
i=c[1];return V(k[1],f,uW,a5,i[1],a5,i[2]);case
5:var
j=c[1];return V(k[1],f,uX,a5,j[1],a5,j[2]);default:var
l=c[1];return S(k[1],f,uY,a5,l[1],l[2])}}function
cG(e,c){switch(c[0]){case
0:return g(k[1],e,uZ,c[1]);case
1:return g(k[1],e,u0,c[1]);case
2:return g(k[1],e,u1,c[1]);case
3:var
f=b(d[40],c[1]);return g(k[1],e,u2,f);case
4:var
h=b(d[40],c[1]);return g(k[1],e,u3,h);case
5:var
i=b(d[40],c[1]);return g(k[1],e,u4,i);case
6:return D(k[1],e,u5,a5,c[1]);case
7:return a(k[1],e,u6);case
8:return V(k[1],e,u7,a5,c[1],cG,c[2]);case
9:return V(k[1],e,u8,cG,c[1],cG,c[2]);default:return V(k[1],e,u9,cG,c[1],cG,c[2])}}aA(1004,[0,a5,cG],"Micromega_plugin__Sos_types");var
bR=[0,1],u_=0,u$=o[8],vb=0;function
vc(a){return[1,b(ag[1],a)]}var
eL=[0,z[2],vc,vb,va,u$,aL],vf=ag[2],gF=[0,function(a){return[0,b(z[2],a),0]},vf,ve,vd,aT,at];function
jR(a,i){var
b=i;for(;;){var
d=a[6],e=a[5],f=a[4],g=a[3],h=function(b,c,d,e){return function(a){return iq(e,d,c,b,a)}}(d,e,f,g),c=function(c){function
b(a){if(typeof
a!=="number")switch(a[0]){case
3:var
d=a[1],e=b(a[2]);return c([3,b(d),e]);case
4:var
f=a[1],g=b(a[2]);return c([4,b(f),g])}return c(a)}return b}(h)(b);if(W(c,b))return c;var
b=c;continue}}function
eM(a){var
e=a[2],c=bc(a[1]),f=c[2];return[0,f,e,b(d[3],c[1])]}function
vi(c){var
p=s[1];function
q(d,c){var
b=gf(c[1]);return a(s[7],d,b)}var
r=g(f[20],q,p,c),t=0;function
u(k,j){var
a=0;function
d(b,a){return[0,au(k,a[1]),b]}var
e=g(f[20],d,a,c),h=[1,l[1]],i=b(f[9],e);return[0,[0,b9([0,[1,l[1]],[0,[1,l[1]],i]]),0,h],j]}var
v=g(s[15],u,r,t),i=0;function
j(c,a){return[0,b(d[3],a[3]),c]}var
k=g(f[20],j,i,c),m=[1,l[1]],n=b(f[9],k),o=[0,b9([0,[1,l[1]],[0,[1,l[2]],n]]),0,m],w=[1,l[2]],x=1;function
y(a){return jh(a)?[1,l[2]]:[1,l[1]]}var
z=a(f[17],y,c),A=[0,b9([0,[1,l[1]],[0,[1,l[2]],z]]),x,w],B=[0,o,v];function
h(e,d){var
b=e,a=d;for(;;){if(a){var
c=a[2];if(0===a[1][2]){var
b=b+1|0,a=c;continue}var
f=h(b+1|0,c),g=1;return[0,[0,gb(b+1|0,function(a){return vh},K),g,vg],f]}return 0}}var
C=[0,A,h(1,c)],D=a(e[26],C,B),E=[1,l[1]];return[0,[0,b9([0,[1,l[1]],[0,[1,l[2]],0]]),1,E],D]}function
gG(c){if(bR[1])return jL(c);var
d=b(eF[1],c);if(0===d[0])return 0;var
e=a(jG[1],c,d[1]);return[0,cA(b(m[17][5],e)[1])]}function
vj(a){if(bR[1])return jM(a);var
c=b(eF[1],a);return 0===c[0]?[0,c[1]]:0}function
vm(g){try{var
a=gG(g);return a}catch(a){a=n(a);if(a===eh){var
h=vi(g);try{var
c=vj(h);if(c)var
d=c[1],i=aX(d)?[0,cA(i3(2,G(1,vk,d)))]:b(e[3],vl),f=i;else
var
f=0;return f}catch(a){a=n(a);if(b(cb[18],a))return 0;throw a}}throw a}}function
gH(a){var
b=[0,0,r[1]];function
c(a,c){var
b=a[1];return[0,b+1|0,g(r[4],b,c,a[2])]}return g(m[17][15],c,b,a)[2]}function
gI(e){var
c=b(m[17][mD],e),f=c[2],d=vm(c[1]);if(d){var
g=d[1],h=gH(f);return[0,a(R[12],h,g)]}return 0}var
dq=[aS,vo,aR(0)];function
gJ(k){var
f=k[2],g=k[1],h=g[3],i=g[2],j=g[1];if(aX(j)){var
l=gh(j),c=[1,l];if(a(d[32],c,vp))return[2,g,f];var
m=a(d[12],h,c),n=b(d[25],m);if(a(E[2],n,0)){if(1<=b(d[25],c)){var
o=a(d[9],h,c);return[2,[0,cy(c,j),i,o],[6,l,f]]}throw[0,aV,vq]}switch(i){case
0:return[0,[9,f]];case
1:var
p=a(d[9],h,c),q=b(d[24],p);return[1,[0,cy(c,j),i,q],[9,f]];default:return b(e[3],vr)}}return a(ei(i),vs,h)?0:[0,f]}function
jS(h,f,a){var
c=0;function
d(c,d){var
e=b(f,d);if(e){var
a=b(h,e[1]);if(typeof
a==="number")return c;else
switch(a[0]){case
0:throw[0,dq,a[1]];case
1:return[0,[0,a[1],a[2]],c];default:return[0,[0,a[1],a[2]],c]}}return[0,d,c]}return g(m[17][15],d,c,a)}function
jT(c){return d5(function(f){var
e=bu(function(l){var
c=l[1],g=c[2],h=c[1];function
i(b){var
c=a(d[26],b,vt);return c?c:a(d[26],b,vu)}if(0===g){var
j=a(ai[13],i,h),k=function(e){function
c(d){var
c=b(ai[9],d[1][1]);return c?c:a(ai[10],e,d[1][1])}return a(m[17][21],c,f)},e=a(m[17][61],k,j);return e?[0,e[1]]:0}return 0},f),h=e[1],j=e[2];if(h){var
i=h[1];return d3(g(av[12],c,i[2],i[1]),j)}return 0},c)}function
gK(b){return a(av[15],0,b)}function
jU(c,b){if(1===c)return b;var
d=jU(c-1|0,b);return a(av[8],b,d)}function
vv(d,c){if(!b(eC[6],c))if(!b(eC[3],c))try{var
e=b(av[7],vw),f=function(e,c,b){var
f=jU(c,a(r[27],e,d));return a(av[8],f,b)},h=[0,g(eC[1],f,c,e)];return h}catch(a){a=n(a);if(a===L)return 0;throw a}return 0}function
dr(g,f,d){b(ai[1][1],0);var
c=b(m[17][1],d),h=a(e[6],g,fq(c,g));gi[1]=a(e[6],c,h);function
i(e){var
g=e[1];switch(e[2]){case
0:var
c=0;break;case
1:throw[0,aV,vn];case
2:var
c=2;break;default:var
c=1}function
d(c){switch(c[0]){case
0:var
g=b(f[2],c[1]);return b(be[1],g);case
1:var
h=b(ag[3],c[1]);return b(be[2],h);case
2:var
i=c[1],j=d(c[2]),k=d(i);return a(be[3],k,j);case
3:var
l=c[1],m=d(c[2]),n=b(be[5],m),o=d(l);return a(be[3],o,n);case
4:var
p=c[2],q=d(c[1]),r=d(p);return a(be[4],q,r);case
5:var
s=d(c[1]);return b(be[5],s);default:var
t=c[2],u=d(c[1]),v=b(ag[4],t),e=function(c){if(a(E[2],c,0)){var
d=b(f[2],f[4]);return b(be[1],d)}var
g=e(c-1|0);return a(be[4],u,g)};return e(v)}}return[0,d(g),c]}var
j=a(m[17][68],i,d);function
k(c,a){var
d=a[2];return[0,[0,b(ai[2],a[1]),d],[1,c]]}return a(m[17][13],k,j)}function
jV(c){function
f(a){return b(ai[9],a[1][1])}if(a(m[17][21],f,c))return c;var
h=cB[1];function
i(c,a){var
d=b(ai[16],a[1][1]);function
e(c,a,b){return[0,a]}return g(cB[38],e,c,d)}var
j=g(m[17][15],i,h,c);function
k(d,c,a){var
e=b(ai[5],d);return[0,[0,[0,b(ai[5],c),1],[4,e]],a]}var
d=g(cB[12],k,j,c),l=s[1];function
n(d,c){var
e=b(ai[7],c[1][1]);return a(s[7],d,e)}var
o=g(m[17][15],n,l,d);function
p(e,d){var
c=b(ai[3],e);return[0,[0,[0,a(ai[14],c,c),1],[4,c]],d]}var
e=g(s[15],p,o,d),q=iM(av[8],e),r=a(m[18],e,q),t=b(av[2],vx);return a(m[17][68],t,r)}function
jW(i,h){var
c=jT(dr(i,gF,h)),j=gK(c),k=jV(c),l=a(m[18],k,j);function
n(a){var
b=a[1],c=a[2];return[0,eM([0,b[1],b[2]]),c]}var
d=a(m[17][68],n,l),o=0;function
p(d,c){var
f=b(R[2],c[2]);return a(e[6],d,f)}var
q=g(m[17][15],p,o,d),r=a(gL[53],0,q),f=gI(d);return f?[0,D(R[11],f5,z[5],r,f[1])]:0}function
gM(e,d){var
f=dr(e,gF,d);function
g(a){var
b=a[2];return[0,eM(a[1]),b]}var
b=a(m[17][68],g,f),c=gI(b);if(c){var
h=c[1],i=function(a,b){return a},j=a(m[17][13],i,b);return[0,D(R[11],f5,z[5],j,h)]}return 0}function
cd(c){if(typeof
c==="number")return[0,l[2],0];else
switch(c[0]){case
0:var
f=c[1],y=[0,[1,af(f)]];return[0,a4(f),y];case
1:return[0,l[2],[1,c[1]]];case
2:var
g=cd(c[1]);return[0,g[1],[2,g[2]]];case
3:var
h=c[1],z=h[2],i=cd(h[1]),j=i[2],k=i[1],m=cd(z),n=m[2],o=m[1],d=a(l[17],k,o),p=a(l[15],k,d),q=a(l[15],o,d),A=a(l[10],p,q),r=a(l[10],d,A),B=a(l[23],r,l[2]);return a(E[2],B,0)?[0,l[2],[3,[0,j,n]]]:[0,r,[3,[0,[5,[0,[0,[1,q]],j]],[5,[0,[0,[1,p]],n]]]]];case
4:return b(e[3],vy);case
5:var
s=c[1],C=s[2],t=cd(s[1]),D=t[2],F=t[1],u=cd(C),G=[5,[0,D,u[2]]];return[0,a(l[10],F,u[1]),G];default:var
v=c[1],w=v[2],x=cd(v[1]),H=[6,[0,x[2],w]];return[0,a(l[19],x[1],w),H]}}function
jX(b){var
a=cd(b);return[0,a[1],a[2]]}function
cH(b){switch(b[0]){case
0:return[0,l[2],[0,b[1]]];case
1:return[0,l[2],[1,b[1]]];case
2:return[0,l[2],[2,b[1]]];case
3:var
d=b[1],t=[3,[1,af(d)]];return[0,a4(d),t];case
4:var
e=b[1],u=[4,[1,af(e)]];return[0,a4(e),u];case
5:var
f=b[1],v=[5,[1,af(f)]];return[0,a4(f),v];case
6:var
g=jX(b[1]),h=g[1],w=[6,g[2]];return[0,a(l[10],h,h),w];case
7:return[0,l[2],[7,b[1]]];case
8:var
x=b[2],i=jX(b[1]),y=i[2],z=i[1],j=cH(x),A=[8,y,j[2]];return[0,a(l[10],z,j[1]),A];case
9:var
B=b[2],k=cH(b[1]),m=k[1],C=k[2],n=cH(B),o=n[1],D=n[2],c=a(l[17],m,o),p=a(l[15],m,c),q=a(l[15],o,c),E=a(l[10],p,q);return[0,a(l[10],c,E),[9,[10,[4,[1,q]],C],[10,[4,[1,p]],D]]];default:var
F=b[2],r=cH(b[1]),G=r[2],H=r[1],s=cH(F),I=[10,G,s[2]];return[0,a(l[10],H,s[1]),I]}}function
bA(a){if(typeof
a==="number")return[0,b(z[5],vz)];else
switch(a[0]){case
0:return[0,b(z[5],a[1])];case
1:var
c=a[1],i=lY(g(m[15][4],c,1,cn(c)-1|0));return[1,b(z[6],i)];case
2:return[5,bA(a[1])];case
3:var
d=a[1],j=d[1],k=bA(d[2]);return[2,bA(j),k];case
4:var
e=a[1],l=e[1],n=bA(e[2]);return[3,bA(l),n];case
5:var
f=a[1],o=f[1],p=bA(f[2]);return[4,bA(o),p];default:var
h=a[1],q=h[1],r=b(z[3],h[2]);return[6,bA(q),r]}}function
jY(a){var
c=bA(a),d=b(z[5],vA);return X(b(z[5],vB),d,aM,aT,bP,bs,at,c)}function
gN(a){if(a){var
c=a[2],d=a[1];if(c){var
e=gN(c);return[3,[0,b(z[4],d)],e]}return[0,b(z[4],d)]}return 0}function
jZ(c){function
e(c){switch(c[0]){case
0:return[0,b(z[4],c[1])];case
1:return[0,b(z[4],c[1])];case
2:return[0,b(z[4],c[1])];case
6:return[1,jY(c[1])];case
7:return gN(c[1]);case
8:var
h=c[1],i=e(c[2]);return[2,jY(h),i];case
9:var
j=c[1],k=e(c[2]);return[4,e(j),k];case
10:var
l=c[1],m=e(c[2]);return[3,e(l),m];default:var
f=c[1],g=a(d[37],f,vC);return a(E[2],g,0)?0:[5,b(z[5],f)]}}return jR(gF,e(c))}function
bB(a){if(typeof
a==="number")return vD;else
switch(a[0]){case
0:var
j=b(d[52],a[1]);return[0,b(z[2],j)];case
1:var
c=a[1],k=lY(g(m[15][4],c,1,cn(c)-1|0));return[1,b(z[6],k)];case
2:return[5,bB(a[1])];case
3:var
e=a[1],l=e[1],n=bB(e[2]);return[2,bB(l),n];case
4:var
f=a[1],o=f[1],p=bB(f[2]);return[3,bB(o),p];case
5:var
h=a[1],q=h[1],r=bB(h[2]);return[4,bB(q),r];default:var
i=a[1],s=i[1],t=b(z[3],i[2]);return[6,bB(s),t]}}function
j0(a){var
c=bB(a),d=o[6],e=o[7],f=o[8],g=o[5],h=b(z[7],1);return X(b(z[7],0),h,g,f,e,d,aL,c)}function
j1(c){var
f=cH(c)[2];function
e(k){var
c=k;for(;;)switch(c[0]){case
0:return[0,b(z[4],c[1])];case
1:return[0,b(z[4],c[1])];case
2:return[0,b(z[4],c[1])];case
6:return[1,j0(c[1])];case
7:return gN(c[1]);case
8:var
i=c[2],f=c[1];if(typeof
f==="number")var
g=0;else
if(0===f[0])var
j=a(d[26],f[1],vF),g=1;else
var
g=0;if(!g)var
j=0;if(j){var
c=i;continue}var
n=e(i);return[2,j0(f),n];case
9:var
o=c[1],p=e(c[2]);return[4,e(o),p];case
10:var
q=c[1],r=e(c[2]);return[3,e(q),r];default:var
h=c[1],l=a(d[37],h,vE);if(a(E[2],l,0))return 0;var
m=b(d[52],h);return[5,b(z[2],m)]}}return jR(eL,e(f))}function
vG(a){var
b=0;function
c(b,c){var
a=gJ([0,c[1],c[2]]);if(typeof
a==="number")return b;else
switch(a[0]){case
0:throw[0,dq,a[1]];case
1:return[0,[0,a[1],a[2]],b];default:return[0,[0,a[1],a[2]],b]}}return g(m[17][15],c,b,a)}function
gO(g,c){var
h=b(l[22],c);if(a(E[2],h,0))return[0,l[2],l[1]];var
d=a(l[14],g,c),i=d[1],e=gO(c,d[2]),f=e[2],j=e[1],k=a(l[10],i,f);return[0,f,a(l[8],j,k)]}function
j2(n,m,c){return jS(gJ,function(o){var
f=o[1],g=m[1],i=f[2],j=f[1],k=g[2],l=g[1],p=o[2],q=m[2],r=f[3],s=g[3];function
h(c,b){var
e=a(R[8],b,p),f=a(R[8],c,q),g=a(R[7],f,e),h=a(d[6],r,b),m=a(d[6],s,c),n=a(d[1],m,h),o=ej(k,i),t=ao(b,j);return[0,[0,aW(ao(c,l),t),o,n],g]}var
c=au(n,l),e=au(n,j),C=0===c[0]?0===c[1]?1:0:0;if(!C){var
D=0===e[0]?0===e[1]?1:0:0;if(!D){var
t=b(d[25],e),u=fq(b(d[25],c),t);if(a(E[2],u,-1)){var
v=b(d[15],e);return[0,h(v,b(d[15],c))]}if(0===k){var
w=[0,b(d[25],c)],x=a(d[6],e,w),y=b(d[3],x);return[0,h(y,b(d[15],c))]}if(0===i){var
z=b(d[15],e),A=[0,b(d[25],e)],B=a(d[6],c,A);return[0,h(z,b(d[3],B))]}return 0}}return 0},c)}function
vH(z){var
c=0,b=z;for(;;){if(b){var
n=b[2],e=b[1],o=bu(function(g){return function(f){var
b=f[1],c=g[1];if(0===c[2])if(0===b[2]){var
d=b[1],e=c[1];return i4(function(c,b){var
d=l[2],e=af(b),f=af(c),g=a(l[17],f,e),h=a(l[23],g,d);return a(E[2],h,0)},e,d)}return 0}}(e),n),p=o[1];if(!p){var
c=[0,e,c],b=n;continue}var
q=p[1],x=q[2],y=q[1],f=[0,[0,[0,y,e,x]],a(m[17][10],c,o[2])]}else
var
f=[0,0,c];var
r=f[1],A=f[2];if(r){var
g=r[1],s=g[3],t=s[1],u=g[2],v=u[2],h=u[1],i=g[1],B=s[2],C=i[2],D=i[1],F=af(i[3]),w=gO(af(C),F),j=[1,w[1]],k=[1,w[2]],G=a(d[6],k,t[3]),H=a(d[6],j,h[3]),I=a(d[1],H,G),J=ao(k,t[1]),K=[0,aW(ao(j,h[1]),J),0,I],L=a(R[8],k,B),M=a(R[8],j,v);return[0,j2(D,[0,K,a(R[7],M,L)],[0,[0,h,v],A])]}return 0}}function
vI(f){var
b=bu(function(c){var
b=c[1];if(0===b[2]){var
e=b[1];return gg(function(c,b){if(!a(d[26],b,vJ))if(!a(d[26],b,vK))return 0;return[0,c]},e)}return 0},f),c=b[1],g=b[2];if(c){var
e=c[1];return[0,j2(e[1],e[2],g)]}return 0}function
vL(n){var
c=bu(function(k){var
i=k[1];if(0===i[2]){var
c=i[1];for(;;){var
d=aX(c);if(d){var
b=d[1],e=b[3],j=b[1],f=af(b[2]),g=gg(function(g){return function(d,c){var
b=af(c),e=l[2],f=a(l[17],g,b);return a(l[24],f,e)?[0,[0,d,b]]:0}}(f),e);if(g){var
h=g[1];return[0,[0,[0,j,f],[0,h[1],h[2]]]]}var
c=e;continue}return 0}}return 0},n),e=c[1],o=c[2];if(e){var
f=e[1],g=f[2],h=g[1],i=f[1],j=i[2],k=i[1],p=g[2],q=j[1],r=k[1],m=gO(k[2],j[2]),s=[1,m[2]],t=[1,m[1]];return[0,jS(gJ,function(g){var
c=g[1],e=c[1],i=g[2],j=c[3],k=c[2],l=au(r,e),m=au(q,e),n=a(d[6],m,s),o=a(d[6],l,t),u=a(d[1],o,n),f=b(d[3],u),v=a(R[8],f,p),w=a(R[7],v,i),x=a(d[6],f,h[3]),y=a(d[1],x,j);return[0,[0,[0,aW(ao(f,h[1]),e),k,y],w]]},o)]}return 0}function
gP(a){var
b=[0,vI,[0,vH,[0,vL,0]]];return d5(function(a){return iT(b,a)},a)}function
j3(c){function
e(a){var
c=a[1][1];return eb(function(c,a){return 0!==b(d[25],a)?1:0},c)}return a(m[17][21],e,c)}function
vP(k,j,h){function
o(F,o){if(j3(o)){var
G=b(m[17][mD],o),H=G[2],c=G[1],J=function(a){return 0===a[2]?1:0},u=a(m[17][30],J,c),v=u[2],w=u[1];if(w)var
L=0,M=function(c,b){function
d(a){return cw(b[1],a[1])}return a(m[17][22],d,w)?c:[0,b[1],c]},x=g(m[17][15],M,L,v);else
var
N=function(a){return a[1]},x=a(m[17][14],N,v);var
O=[0,K,vN],P=function(b,e){var
f=dM(b[2]),k=f?a(d[29],f[1],vM):0;if(k)return b;var
h=bR[1]?jN(e,c):a(eF[2],e,c);if(h){var
i=h[1],g=b[2],j=b[1];return hW(i,g)?[0,e,i]:[0,j,g]}return b},y=g(m[17][15],P,O,x),z=y[2],A=z[1],Q=y[1];if(A){var
B=z[2];if(B)var
h=[0,[0,A[1],Q,B[1]]],s=1;else
var
s=0}else
var
s=0;if(!s)var
h=0;if(h){var
i=h[1],j=i[3],k=i[2],n=i[1],S=a4(n),T=l[2],U=af(n),V=a(l[8],U,T),W=a4(j),X=af(j),Y=[1,a(l[5],l[2],X)],C=gG([0,[0,ao([1,W],k),1,Y],c]),Z=b(d[3],[1,V]),D=gG([0,[0,ao(b(d[3],[1,S]),k),1,Z],c]);if(C)if(D)var
_=D[1],$=ga(C[1]),aa=b(m[17][6],$),ab=ga(_),f=[0,[0,b(m[17][6],ab),[0,n,k,j],aa]],t=1;else
var
t=0;else
var
t=0;if(!t)var
f=b(e[3],vO)}else
var
f=0;if(f){var
p=f[1],q=p[2],I=q[2],ac=p[3],ad=q[1],ae=p[1],ag=b(d[22],q[3]),r=E(F,I,b(d[24],ad),ag,o);if(typeof
r!=="number"&&0===r[0]){var
ah=r[1],ai=b9(ac),aj=gH(H),ak=a(R[12],aj,ai),al=b9(ae),am=gH(H);return[0,[1,F,a(R[12],am,al),I,ak,ah]]}return 0}return 0}throw[0,aV,vQ]}function
E(c,j,b,h,g){if(a(d[28],b,h))return vR;var
e=i(c+1|0,[0,[0,[0,j,0,b],[2,c]],g]);if(typeof
e!=="number"&&0===e[0]){var
k=e[1],f=E(c,j,a(d[1],b,vS),h,g);if(typeof
f!=="number"&&0===f[0])return[0,[0,k,f[1]]];return 0}return 0}function
i(c,a){if(j3(a))try{var
d=b(j,a),e=gI(d),f=e?[0,[0,c,e[1],0]]:k?o(c,d):0;return f}catch(a){a=n(a);if(a[1]===dq)return[0,[0,c,a[2],0]];throw a}throw[0,aV,vT]}var
p=0;function
q(d,c){var
f=b(R[2],c[2]);return a(e[6],d,f)}var
f=1+g(m[17][15],q,p,h)|0;try{var
t=i(f,vG(h)),c=t}catch(a){a=n(a);if(a[1]!==dq)throw a;var
c=[0,[0,f,a[2],0]]}if(typeof
c!=="number"&&0===c[0]){var
r=c[1],s=a(gL[53],0,f-1|0);return[0,a(R[10],s,r)]}return 0}function
vU(k,i,c){function
d(d,c){var
f=0;function
h(d,c){var
f=b(R[2],c[2]);return a(e[6],d,f)}var
i=(1+g(m[17][15],h,f,d)|0)-1|0,j=a(gL[53],0,i);return[0,a(R[10],j,c)]}try{var
f=b(i,c),h=jQ(f),j=h?d(f,h[1]):0;return j}catch(a){a=n(a);if(a[1]===dq)return d(c,[0,0,a[2],0]);throw a}}function
gQ(d,c,b,a){return bR[1]?vU(d,b,a):vP(c,b,a)}var
eN=[0,0];function
j4(i,n,h,f){var
j=i[1],d=g(i[2],n,h,f),l=eN[1];if(l){var
o=l[1],p=[0,C.caml_sys_getcwd(0)],q=g(bC[14],p,o,vV),c=b(e[49],q),r=dr(h,eL,f);a(k[1],c,vW);var
s=a(m[17][68],bL,r),t=b(ai[19],vX);D(k[1],c,vY,t,s);var
u=typeof
d==="number"?0:0===d[0]?(g(k[1],c,v0,j),1):0;if(!u)g(k[1],c,vZ,j);b(e[52],c);b(e[65],c)}return d}function
v1(t,s,q){var
u=dr(s,eL,q),c=b(av[13],u),e=iP(function(a){return b(ai[8],a[1][1])},c)[1],f=r[1];function
h(b,a){return g(r[4],a[1],a[2],b)}var
i=g(m[17][15],h,f,e),j=r[1];function
k(c,a){var
d=a[1][1];return Z(function(c,a,e){var
d=vv(i,b(ai[1][2],a));return d?g(r[4],a,d[1],c):c},c,d)}var
l=g(m[17][15],k,j,c),n=0;function
o(c,b,a){return[0,b,a]}var
p=g(r[13],o,l,n),v=gK(c),w=a(m[18],v,c),d=a(m[18],p,w);function
x(a){var
b=a[1],c=a[2];return[0,eM([0,b[1],b[2]]),c]}var
y=a(m[17][68],x,d);return gQ(a(m[17][68],bL,d),t,gP,y)}function
j5(b){function
c(a){var
b=a[1],c=a[2];return[0,eM([0,b[1],b[2]]),c]}return a(m[17][68],c,b)}function
v2(d,g,f){var
c=dr(g,eL,f);function
h(a){return b(ai[9],a[1][1])}if(a(m[17][21],h,c)){var
i=j5(c);return gQ(a(m[17][68],bL,c),d,gP,i)}var
e=jT(c),j=gK(e),k=j5(jV(a(m[18],e,j)));return gQ(a(m[17][68],bL,c),d,gP,k)}function
j6(c,b,a){return j4([0,v3,v1],c,b,a)}function
j7(c,b,a){return j4([0,v4,v2],c,b,a)}aA(1007,[0,u_,bR,eN,jZ,j1,j6,j7,gM,jW],"Micromega_plugin__Certificate");function
eO(m){var
c=b(bb[25],m),l=[aS,v5,aR(0)],f=[aS,v6,aR(0)];function
o(a,c){try{var
d=b(a,0);b(c,0);return d}catch(a){a=n(a);try{b(c,0)}catch(b){throw a}throw a}}function
p(a){try{var
c=[0,b(d9[3],a)];return c}catch(a){a=n(a);if(a===j8)return 0;if(b(cb[18],a))throw l;throw a}}function
q(c,a){var
d=g(N[34],a,0,1);try{g(N[34],a,0,0);var
e=0===c?4:1;g(N[83],a,e,1);var
f=1,b=f}catch(a){a=n(a);if(a[1]!==N[1])throw a;var
b=0}g(N[34],a,d,0);return b}function
r(a){var
c=g(N[34],a,0,1);try{g(N[34],a,0,0);var
b=g(N[83],a,0,1);return b}catch(b){b=n(b);if(b[1]===N[1]){g(N[34],a,c,0);return 0}throw b}}function
h(d,c,a){return q(d,c)?o(a,function(a){return r(c)}):b(a,0)}function
d(i){var
f=g(N[23],i,v7,hG),j=b(N[30],f),d=b(c[1],100);function
o(e){for(;;){var
a=p(j);if(a){var
b=a[1];g(c[10],d,b[1],b[2]);continue}return 0}}try{h(0,f,o);b(e[83],j);var
q=g(N[23],i,v_,hG),r=[0,b(N[31],q),1,d];return r}catch(f){f=n(f);if(f===l){b(e[83],j);var
m=g(N[23],i,v8,hG),k=b(N[31],m);h(1,m,function(h){function
f(b,a){return g(d9[1],k,[0,b,a],v9)}a(c[12],f,d);return b(e[52],k)});return[0,k,1,d]}throw f}}function
j(a,j,i){var
d=a[1],k=a[3];if(0===a[2])throw f;var
l=b(N[33],d);g(c[10],k,j,i);return h(1,l,function(a){g(d9[1],d,[0,j,i],v$);return b(e[52],d)})}function
k(b,d){var
e=b[3];if(0===b[2])throw f;return a(c[7],e,d)}return[0,d,k,j,function(c,e){var
a=[i,function(b){try{var
a=[0,d(c)];return a}catch(a){return 0}}];return function(c){var
d=lZ(a),f=mc===d?a[1]:i===d?b(j9[2],a):a;if(f){var
g=f[1];try{var
l=k(g,c);return l}catch(a){a=n(a);if(a===L){var
h=b(e,c);j(g,c,h);return h}throw a}}return b(e,c)}}]}aA(1010,[0,eO],"Micromega_plugin__Persistent_cache");function
h(a){var
c=lZ(a);return mc===c?a[1]:i===c?b(j9[2],a):a}var
gR=e[8],j_=[0,gR],gS=[0,1],j$=[0,gR];function
ka(a){return[0,bR[1],gS[1],j$[1]]}function
gT(a){return j_[1]}function
kb(b,a){function
c(b){var
c=b?b[1]:gR;a[1]=c;return 0}function
d(b){return[0,a[1]]}return[0,0,g(f[21],e[17],b,wa),b,d,c]}function
wb(a){gS[1]=a;return 0}var
we=[0,0,wd,wc,function(a){return gS[1]},wb];function
wf(a){bR[1]=a;return 0}var
wi=[0,0,wh,wg,function(a){return bR[1]},wf];function
wj(a){eN[1]=a;return 0}var
wm=[0,0,wl,wk,function(a){return eN[1]},wj];a(ds[4],0,wi);a(ds[6],0,wm);var
wo=kb(wn,j_);a(ds[3],0,wo);var
wq=kb(wp,j$);a(ds[3],0,wq);a(ds[4],0,we);var
ws=a(e[26],dt[20],kc),wt=a(e[26],dt[19],ws),wu=a(e[26],[0,wr,0],wt),wv=a(e[26],dt[21],wu);function
U(d,c,a){var
e=g(dt[18],d,c,a),f=b(wz[23],e);return b(j[9],f)}var
wA=dt[21];function
aw(a){return U(wB,wA,a)}function
t(a){return U(wC,wv,a)}function
bD(a){return U(wD,ww,a)}function
aO(a){return U(wE,wx,a)}function
bE(a){return U(wF,wy,a)}function
a6(a){return U(wG,kc,a)}var
gU=[i,function(a){return aw(wH)}],gV=[i,function(a){return aw(wI)}],kd=[i,function(a){return aw(wJ)}],wL=[i,function(a){return aw(wK)}],ke=[i,function(a){return aw(wM)}],gW=[i,function(a){return aw(wN)}],wP=[i,function(a){return t(wO)}],wR=[i,function(a){return t(wQ)}],kf=[i,function(a){return t(wS)}],wU=[i,function(a){return aw(wT)}],wW=[i,function(a){return aw(wV)}],kg=[i,function(a){return aw(wX)}],gX=[i,function(a){return aw(wY)}],w0=[i,function(a){return aw(wZ)}],w2=[i,function(a){return aw(w1)}],w4=[i,function(a){return aw(w3)}],w6=[i,function(a){return aw(w5)}],w8=[i,function(a){return bD(w7)}],w_=[i,function(a){return bD(w9)}],xa=[i,function(a){return bD(w$)}],xc=[i,function(a){return bD(xb)}],xe=[i,function(a){return bD(xd)}],aP=[i,function(a){return bD(xf)}],xh=[i,function(a){return bD(xg)}],xj=[i,function(a){return bD(xi)}],xl=[i,function(a){return bD(xk)}],du=[i,function(a){return t(xm)}],eP=[i,function(a){return t(xn)}],kh=[i,function(a){return t(xo)}],ki=[i,function(a){return t(xp)}],xr=[i,function(a){return a6(xq)}],xt=[i,function(a){return a6(xs)}],xv=[i,function(a){return a6(xu)}],xx=[i,function(a){return a6(xw)}],xz=[i,function(a){return a6(xy)}],xB=[i,function(a){return a6(xA)}],xD=[i,function(a){return a6(xC)}],xF=[i,function(a){return a6(xE)}],xH=[i,function(a){return a6(xG)}],xJ=[i,function(a){return a6(xI)}],kj=[i,function(a){return t(xK)}],kk=[i,function(a){return t(xL)}],kl=[i,function(a){return t(xM)}],xO=[i,function(a){return t(xN)}],xQ=[i,function(a){return t(xP)}],xS=[i,function(a){return t(xR)}],xU=[i,function(a){return t(xT)}],xW=[i,function(a){return bE(xV)}],xY=[i,function(a){return bE(xX)}],x0=[i,function(a){return bE(xZ)}],x2=[i,function(a){return bE(x1)}],gY=[i,function(a){return aw(x3)}],km=[i,function(a){return bE(x4)}],kn=[i,function(a){return bE(x5)}],ko=[i,function(a){return bE(x6)}],kp=[i,function(a){return bE(x7)}],kq=[i,function(a){return bE(x8)}],x_=[i,function(a){return t(x9)}],ya=[i,function(a){return t(x$)}],yc=[i,function(a){return t(yb)}],kr=[i,function(a){return t(yd)}],ks=[i,function(a){return t(ye)}],kt=[i,function(a){return t(yf)}],ku=[i,function(a){return t(yg)}],kv=[i,function(a){return t(yh)}],yj=[i,function(a){return aO(yi)}],yl=[i,function(a){return aO(yk)}],yn=[i,function(a){return aO(ym)}],yp=[i,function(a){return aO(yo)}],eQ=[i,function(a){return aO(yq)}],eR=[i,function(a){return aO(yr)}],gZ=[i,function(a){return aO(ys)}],eS=[i,function(a){return aO(yt)}],kw=[i,function(a){return aO(yu)}],eT=[i,function(a){return aO(yv)}],yx=[i,function(a){return aO(yw)}],kx=[i,function(a){return aO(yy)}],ky=[i,function(a){return aO(yz)}],yB=[i,function(a){return t(yA)}],yD=[i,function(a){return t(yC)}],yF=[i,function(a){return t(yE)}],yH=[i,function(a){return t(yG)}],yJ=[i,function(a){return t(yI)}],yL=[i,function(a){return t(yK)}],yN=[i,function(a){return t(yM)}],yP=[i,function(a){return t(yO)}],yR=[i,function(a){return t(yQ)}],yT=[i,function(a){return t(yS)}],yV=[i,function(a){return t(yU)}],yX=[i,function(a){return t(yW)}],yZ=[i,function(a){return t(yY)}],y1=[i,function(a){return t(y0)}],y3=[i,function(a){return t(y2)}],y5=[i,function(a){return t(y4)}],y7=[i,function(a){return t(y6)}],y9=[i,function(a){return t(y8)}],y$=[i,function(a){return t(y_)}],zb=[i,function(a){return t(za)}],zd=[i,function(a){return t(zc)}],zf=[i,function(a){return t(ze)}],zh=[i,function(a){return t(zg)}],zj=[i,function(a){return a6(zi)}],zn=[i,function(a){return U(zm,zl,zk)}],zr=[i,function(a){return U(zq,zp,zo)}],zv=[i,function(a){return U(zu,zt,zs)}],zz=[i,function(a){return U(zy,zx,zw)}],zD=[i,function(a){return U(zC,zB,zA)}],zH=[i,function(a){return U(zG,zF,zE)}],zL=[i,function(a){return U(zK,zJ,zI)}],zP=[i,function(a){return U(zO,zN,zM)}],kz=[i,function(a){return U(zS,zR,zQ)}],g0=[i,function(a){return U(zV,zU,zT)}],zZ=[i,function(a){return U(zY,zX,zW)}],kA=[i,function(a){return U(z2,z1,z0)}],_=[aS,z3,aR(0)];function
g1(c,e){var
b=a(j[3],c,e);switch(b[0]){case
9:var
f=b[2],d=a(j[3],c,b[1]);if(12===d[0])return[0,d[1][1][2],f];throw _;case
12:return[0,b[1][1][2],[0]];default:throw _}}function
g2(a,d){var
b=g1(a,d),c=b[1],e=b[2];if(1===c)return 0;if(2===c)return[0,g2(a,w(e,0)[1])];throw _}function
z4(c,a){var
d=b(ag[5],a);return g(k[1],c,z5,d)}function
dv(a){if(a){var
c=[0,dv(a[1])],d=[0,h(wW),c];return b(j[23],d)}return h(wU)}function
dw(a,e){var
b=g1(a,e),c=b[2],d=b[1]-1|0;if(2<d>>>0)throw _;switch(d){case
0:return[0,dw(a,w(c,0)[1])];case
1:return[1,dw(a,w(c,0)[1])];default:return 0}}function
bF(a){if(typeof
a==="number")return h(xa);else{if(0===a[0]){var
c=[0,bF(a[1])],d=[0,h(xe),c];return b(j[23],d)}var
e=[0,bF(a[1])],f=[0,h(xc),e];return b(j[23],f)}}function
g3(c,a){var
d=b(ag[3],a);return g(k[1],c,z6,d)}function
kB(d,c,a){var
e=S(kC[2],0,0,d,c,a);try{var
f=[0,h(zj),[0,e,a]],g=b(j[23],f);D(z7[24],0,d,c,g);var
i=1;return i}catch(a){a=n(a);if(a===L)return 0;throw a}}function
kD(a,e){var
b=g1(a,e),c=b[2],d=b[1]-1|0;if(2<d>>>0)throw _;switch(d){case
0:return 0;case
1:return[0,dw(a,w(c,0)[1])];default:return[1,dw(a,w(c,0)[1])]}}function
ap(a){if(typeof
a==="number")return h(xh);else{if(0===a[0]){var
c=[0,bF(a[1])],d=[0,h(xj),c];return b(j[23],d)}var
e=[0,bF(a[1])],f=[0,h(xl),e];return b(j[23],f)}}function
bT(c,a){var
d=b(ag[1],a),e=b(l[33],d);return g(k[1],c,z8,e)}function
ce(a){var
c=bF(a[2]),d=[0,ap(a[1]),c],e=[0,h(kh),d];return b(j[23],e)}function
z9(b,e){var
c=a(j[3],b,e);if(9===c[0]){var
d=c[2],f=c[1],i=h(kh);if(g(j[ad],b,f,i)){var
k=dw(b,w(d,1)[2]);return[0,kD(b,w(d,0)[1]),k]}throw _}throw _}function
bf(a){if(typeof
a==="number")return 0===a?h(xr):h(xt);else
switch(a[0]){case
0:var
e=[0,ce(a[1])],f=[0,h(xv),e];return b(j[23],f);case
1:var
g=[0,ap(a[1])],i=[0,h(xx),g];return b(j[23],i);case
2:var
k=a[1],l=bf(a[2]),m=[0,bf(k),l],n=[0,h(xz),m];return b(j[23],n);case
3:var
o=a[1],p=bf(a[2]),q=[0,bf(o),p],r=[0,h(xB),q];return b(j[23],r);case
4:var
s=a[1],t=bf(a[2]),u=[0,bf(s),t],v=[0,h(xD),u];return b(j[23],v);case
5:var
c=a[2],w=a[1];if(0===c[0])var
x=ap(c[1]),y=h(kg),z=[0,h(aP),y,x],A=[0,h(w4),z],d=b(j[23],A);else
var
D=dv(c[1]),E=h(kg),F=[0,h(aP),E,D],G=[0,h(w6),F],d=b(j[23],G);var
B=[0,bf(w),d],C=[0,h(xF),B];return b(j[23],C);case
6:var
H=[0,bf(a[1])],I=[0,h(xH),H];return b(j[23],I);default:var
J=[0,bf(a[1])],K=[0,h(xJ),J];return b(j[23],K)}}function
g4(c,d,a){if(a){var
e=a[1],f=g4(c,d,a[2]),g=[0,c,b(d,e),f],i=[0,h(wP),g];return b(j[23],i)}var
k=[0,h(wR),[0,c]];return b(j[23],k)}function
kE(d,k,a){function
c(a){switch(a[0]){case
0:var
l=[0,d,b(k,a[1])],m=[0,h(yD),l];return b(j[23],m);case
1:var
n=[0,d,bF(a[1])],o=[0,h(yB),n];return b(j[23],o);case
2:var
p=a[1],q=c(a[2]),r=[0,d,c(p),q],s=[0,h(yF),r];return b(j[23],s);case
3:var
t=a[1],u=c(a[2]),v=[0,d,c(t),u],w=[0,h(yL),v];return b(j[23],w);case
4:var
x=a[1],y=c(a[2]),z=[0,d,c(x),y],A=[0,h(yJ),z];return b(j[23],A);case
5:var
B=[0,d,c(a[1])],C=[0,h(yH),B];return b(j[23],C);default:var
e=a[2],D=a[1];if(e)var
g=[0,bF(e[1])],i=[0,h(w_),g],f=b(j[23],i);else
var
f=h(w8);var
E=[0,d,c(D),f],F=[0,h(yN),E];return b(j[23],F)}}return c(a)}function
kF(d,e,a){function
c(a){switch(a[0]){case
0:var
f=[0,d,b(e,a[1])],g=[0,h(yR),f];return b(j[23],g);case
1:var
i=a[1],k=c(a[2]),l=[0,d,bF(i),k],m=[0,h(yT),l];return b(j[23],m);default:var
n=a[2],o=a[1],p=c(a[3]),q=bF(n),r=[0,d,c(o),q,p],s=[0,h(yP),r];return b(j[23],s)}}return c(a)}function
bg(d,c,a){function
b(c,a){switch(a[0]){case
0:return D(k[1],c,Ab,d,a[1]);case
1:return V(k[1],c,Ac,g3,a[1],b,a[2]);default:return l0(k[1],c,Ad,b,a[1],g3,a[2],b,a[3])}}return b(c,a)}function
cI(f,e,a){var
c=h(f);function
d(a){if(typeof
a==="number"){var
f=[0,h(zh),[0,c]];return b(j[23],f)}else
switch(a[0]){case
0:var
g=[0,c,dv(a[1])],i=[0,h(y7),g];return b(j[23],i);case
1:var
k=[0,c,kF(c,e,a[1])],l=[0,h(y9),k];return b(j[23],l);case
2:var
m=a[1],n=d(a[2]),o=[0,c,kF(c,e,m),n],p=[0,h(zb),o];return b(j[23],p);case
3:var
q=a[1],r=d(a[2]),s=[0,c,d(q),r],t=[0,h(y$),s];return b(j[23],t);case
4:var
u=a[1],v=d(a[2]),w=[0,c,d(u),v],x=[0,h(zd),w];return b(j[23],x);default:var
y=[0,c,b(e,a[1])],z=[0,h(zf),y];return b(j[23],z)}}return d(a)}function
bG(e,c,b){function
d(c,b){if(typeof
b==="number")return a(k[1],c,Ae);else
switch(b[0]){case
0:return D(k[1],c,Af,z4,b[1]);case
1:var
f=b[1],g=function(a,b){return bg(e,a,b)};return D(k[1],c,Ag,g,f);case
2:var
h=b[2],i=b[1],j=function(a,b){return bg(e,a,b)};return V(k[1],c,Ah,j,i,d,h);case
3:return V(k[1],c,Ai,d,b[1],d,b[2]);case
4:return V(k[1],c,Aj,d,b[1],d,b[2]);default:return D(k[1],c,Ak,e,b[1])}}return d(c,b)}function
dx(d,e,c){var
f=c[2],g=c[1],i=kE(d,e,c[3]);switch(f){case
0:var
a=h(yV);break;case
1:var
a=h(yX);break;case
2:var
a=h(yZ);break;case
3:var
a=h(y3);break;case
4:var
a=h(y1);break;default:var
a=h(y5)}var
k=[0,d,kE(d,e,g),a,i],l=[0,h(zZ),k];return b(j[23],l)}function
eU(d,c,b){try{var
e=function(a){var
b=h(a[1]);return g(j[ad],d,c,b)},i=a(f[33],e,b)[2];return i}catch(a){a=n(a);if(a===L)throw _;throw a}}var
kG=[0,[0,xW,5],[0,[0,xY,3],[0,[0,x2,4],[0,[0,x0,2],0]]]],kH=[0,[0,yj,5],[0,[0,yl,3],[0,[0,yp,4],[0,[0,yn,2],0]]]],kI=[0,[0,ya,4],[0,[0,x_,2],[0,[0,yc,0],0]]];function
kJ(a,c,b){return S(Al[81],0,a[1],a[2],c,b)}function
Am(k,i){var
c=i[2],d=i[1],f=k[2],l=a(j[3],f,d);switch(l[0]){case
10:var
m=w(c,1)[2],n=w(c,0)[1];return[0,eU(f,d,kG),n,m];case
11:if(0===l[1][1][2]){var
o=h(gY);if(g(j[ad],f,d,o)){var
p=h(aP);if(kJ(k,w(c,0)[1],p)){var
q=w(c,2)[3];return[0,0,w(c,1)[2],q]}}throw _}break}return b(e[3],An)}function
Ao(k,i){var
c=i[2],d=i[1],f=k[2],l=a(j[3],f,d);switch(l[0]){case
10:var
m=w(c,1)[2],n=w(c,0)[1];return[0,eU(f,d,kH),n,m];case
11:if(0===l[1][1][2]){var
o=h(gY);if(g(j[ad],f,d,o)){var
p=h(eP);if(kJ(k,w(c,0)[1],p)){var
q=w(c,2)[3];return[0,0,w(c,1)[2],q]}}throw _}break}return b(e[3],Ap)}function
Aq(c,a){var
b=a[2],d=a[1],e=w(b,1)[2],f=w(b,0)[1];return[0,eU(c[2],d,kI),f,e]}function
g5(a){return[0,0,a]}function
As(c,h,f){var
d=c[2],e=D(j[105],c[1],d,h,f);if(e){var
i=e[1],k=b(kK[152],d),l=g(At[4],0,k,i);try{var
m=a(kK[37],d,l)}catch(a){a=n(a);if(a[1]===Au[26])return 0;throw a}return[0,[0,c[1],m]]}return 0}function
eV(c,d){function
f(d,a,c,b){if(a){var
g=a[1],i=a[2],h=As(d,g,b);if(h)return[0,h[1],a,c];var
e=f(d,i,c+1|0,b);return[0,e[1],[0,g,e[2]],e[3]]}return[0,d,[0,b,0],c]}var
a=f(c[2],c[1],1,d),e=a[2],g=a[1];return[0,[0,e,g],b(z[1],a[3])]}function
kL(c,d){var
a=c[1],b=1,e=c[2][2];for(;;){if(a){var
f=a[2];if(g(j[ad],e,a[1],d))return b;var
a=f,b=b+1|0;continue}throw[0,jJ,Av]}}function
g6(l,m,z,y,d,c){function
p(c,b){var
a=eV(c,b);return[0,[1,a[2]],a[1]]}function
e(c,d){function
A(g,f,b){var
h=b[2],c=e(g,b[1]),i=c[1],d=e(c[2],h),j=d[2];return[0,a(f,i,d[1]),j]}try{var
H=[0,[0,a(m,l,d)],c];return H}catch(m){m=n(m);if(m===_){var
o=a(j[3],l[2],d);if(9===o[0]){var
i=o[2],q=o[1];if(10===a(j[3],l[2],q)[0]){var
B=l[2];try{var
v=function(a){var
b=h(a[1]);return g(j[ad],B,q,b)},x=a(f[33],v,y)[2],k=x}catch(a){a=n(a);if(a!==L)throw a;var
k=Ar}if(typeof
k==="number"){if(0===k){var
r=e(c,w(i,0)[1]);return[0,[5,r[1]],r[2]]}try{var
t=e(c,w(i,0)[1]),C=t[2],D=t[1],E=[0,a(z,D,w(i,1)[2]),C];return E}catch(a){a=n(a);if(b(cb[18],a)){var
s=eV(c,d);return[0,[1,s[2]],s[1]]}throw a}}else{if(0===k[0]){var
F=k[1],G=w(i,1)[2];return A(c,F,[0,w(i,0)[1],G])}var
u=eV(c,d);return[0,[1,u[2]],u[1]]}}return p(c,d)}return p(c,d)}throw m}}return e(d,c)}var
Aw=[0,[0,ko,0],[0,[0,kq,1],0]],Ax=[0,[0,kp,[0,function(b,a){return[4,b,a]}]],Aw],Ay=[0,[0,kn,[0,function(b,a){return[3,b,a]}]],Ax],Az=[0,[0,km,[0,function(b,a){return[2,b,a]}]],Ay],AA=[0,[0,kt,0],[0,[0,kv,1],0]],AB=[0,[0,ku,[0,function(b,a){return[4,b,a]}]],AA],AC=[0,[0,ks,[0,function(b,a){return[3,b,a]}]],AB],AD=[0,[0,kr,[0,function(b,a){return[2,b,a]}]],AC],AE=[0,[0,gZ,0],[0,[0,eT,1],0]],AF=[0,[0,eS,[0,function(b,a){return[4,b,a]}]],AE],AG=[0,[0,eR,[0,function(b,a){return[3,b,a]}]],AF],AH=[0,[0,eQ,[0,function(b,a){return[2,b,a]}]],AG];function
g7(d,b,c){if(kB(b[1],b[2],c)){var
e=g(AI[6],b[1],b[2],c);return a(d,b[2],e)}throw _}function
eW(a,b){return g7(kD,a,b)}function
kM(a,b){return g7(z9,a,b)}function
AJ(a,b){return g7(g2,a,b)}var
AK=0,AL=[0,[0,eS,function(b,a){return[4,b,a]}],AK],AM=[0,[0,eR,function(b,a){return[3,b,a]}],AL],AN=[0,[0,eQ,function(b,a){return[2,b,a]}],AM];function
AP(f,c){var
b=f[2];function
d(i){var
k=a(j[3],b,i);switch(k[0]){case
9:var
c=k[2],e=k[1];try{var
s=eU(b,e,AN),t=d(w(c,0)[1]),u=a(s,t,d(w(c,1)[2]));return u}catch(a){a=n(a);if(a===_){var
m=h(kw);if(g(j[ad],b,e,m)){var
l=d(w(c,0)[1]);if(at(aD(l),AO))throw _;return[6,l]}var
o=h(eT);if(g(j[ad],b,e,o)){var
p=[1,AJ(f,w(c,1)[2])];return[5,d(w(c,0)[1]),p]}var
q=h(ky);if(g(j[ad],b,e,q))return[0,kM(f,w(c,0)[1])];var
r=h(kx);if(g(j[ad],b,e,r))return[1,eW(f,w(c,0)[1])];throw _}throw a}case
10:var
v=h(kj);if(g(j[ad],b,i,v))return 0;var
x=h(kk);if(g(j[ad],b,i,x))return 1;throw _;default:throw _}}return d(c)}function
AQ(c){function
a(e,d){var
a=eW(c,d);if(typeof
a!=="number"&&1===a[0])return AR;return[6,e,b(o[15],a)]}return function(b,d){return g6(c,eW,a,Az,b,d)}}function
AS(d){function
a(c,f){var
a=eW(d,f);if(typeof
a!=="number"&&1===a[0]){if(0===c[0])return[0,fR(c[1],a)];b(e[31],AT);b(e[52],e[28]);throw _}return[6,c,b(o[15],a)]}return function(b,c){return g6(d,kM,a,AD,b,c)}}function
AU(a){function
c(d,c){var
e=g2(a[2],c);return[6,d,b(h3[1],e)]}return function(b,d){return g6(a,AP,c,AH,b,d)}}function
g8(n,h,m,l,c){var
d=a(j[3],c[2],l);if(9===d[0]){var
f=a(n,c,[0,d[1],d[2]]),o=f[3],p=f[1],i=g(h,c,m,f[2]),q=i[1],k=g(h,c,i[2],o);return[0,[0,q,p,k[1]],k[2]]}return b(e[3],AV)}function
eX(a,b,c){return g8(Am,AQ,a,b,c)}function
eY(a,b,c){return g8(Aq,AS,a,b,c)}function
AW(a,b,c){return g8(Ao,AU,a,b,c)}function
AX(b,a){return[2,b,a]}function
AY(b,a){return[3,b,a]}function
AZ(b,a){return[2,[5,b,0,a],[5,a,0,b]]}function
A0(b,a){return[5,b,0,a]}function
eZ(e,d,c,b){if(typeof
c!=="number"&&0===c[0])if(typeof
b!=="number"&&0===b[0])return[0,d];return a(e,c,b)}function
kN(l,k,f,e,d){var
i=l[2];function
B(e,d,c){try{var
a=g(k,e,c,l),f=a[2],h=a[1],i=[0,[1,h,[0,d,c]],f,b(bv[2],d)];return i}catch(a){a=n(a);if(b(cb[18],a))return[0,[0,c],e,d];throw a}}function
c(f,e,d){var
k=a(j[3],i,d);switch(k[0]){case
6:var
z=k[3],G=k[2];if(g(j[ft][13],i,1,z)){var
o=c(f,e,G),H=o[1],p=c(o[2],o[3],z),I=p[3],J=p[2];return[0,eZ(A0,d,H,p[1]),J,I]}break;case
9:var
m=k[2],n=k[1],A=m.length-1;if(!(3<=A))switch(A){case
0:break;case
1:var
K=m[1],L=h(kd);if(g(j[ad],i,n,L)){var
q=c(f,e,K);return[0,[4,q[1]],q[2],q[3]]}break;default:var
r=m[1],s=m[2],M=h(gU);if(g(j[ad],i,n,M)){var
t=c(f,e,r),N=t[1],u=c(t[2],t[3],s),O=u[3],P=u[2];return[0,eZ(AX,d,N,u[1]),P,O]}var
Q=h(gV);if(g(j[ad],i,n,Q)){var
v=c(f,e,r),R=v[1],w=c(v[2],v[3],s),S=w[3],T=w[2];return[0,eZ(AY,d,R,w[1]),T,S]}var
U=h(wL);if(g(j[ad],i,n,U)){var
x=c(f,e,r),V=x[1],y=c(x[2],x[3],s),W=y[3],X=y[2];return[0,eZ(AZ,d,V,y[1]),X,W]}}return B(f,e,d)}var
E=h(ke);if(g(j[ad],i,d,E))return[0,0,f,e];var
F=h(gW);if(g(j[ad],i,d,F))return[0,1,f,e];var
C=D(kC[3],0,l[1],l[2],d);if(b(A1[10],C))return[0,[0,d],f,e];throw _}return c(f,e,d)}function
kO(f,e,a){function
c(c,a){var
d=[0,h(gX),a],e=[0,h(gX),d],g=b(A2[12],[0,f,[0,j[16],e]]),i=[0,h(c),g];return b(j[23],i)}function
d(a){if(typeof
a==="number")return 0===a?c(zn,0):c(zr,0);else
switch(a[0]){case
0:return c(zL,[0,a[1],0]);case
1:var
f=a[1],g=[0,h(w2),0];return c(zH,[0,b(e,f),g]);case
2:var
i=a[1],k=[0,d(a[2]),0];return c(zv,[0,d(i),k]);case
3:var
l=a[1],m=[0,d(a[2]),0];return c(zz,[0,d(l),m]);case
4:return c(zD,[0,d(a[1]),0]);default:var
n=a[1],o=[0,d(a[3]),0],p=[0,h(gX)],q=[0,h(w0),p],r=[0,b(j[23],q),o];return c(zP,[0,d(n),r])}}return d(a)}function
g9(b,a){function
d(h,g){var
b=h,a=g;for(;;){if(typeof
a==="number")var
c=0;else
switch(a[0]){case
0:return eV(b,a[1])[1];case
4:var
a=a[1];continue;case
5:var
f=a[3],e=a[1],c=1;break;case
1:var
c=0;break;default:var
f=a[2],e=a[1],c=1}if(c){var
b=d(b,e),a=f;continue}return b}}return d(g5(b),a)}var
e0=[i,function(m){function
c(a){var
b=a[2];return[0,b,h(a[1])]}var
d=a(f[17],c,kG);function
e(a){var
c=b(ag[4],a);return ap(b(z[7],c))}var
g=h(kq),i=h(kp),j=h(ko),k=h(kn),l=h(km);return[0,h(aP),ap,l,k,j,i,g,e,d]}],e1=[i,function(m){function
c(a){var
b=a[2];return[0,b,h(a[1])]}var
d=a(f[17],c,kI);function
e(a){var
c=b(ag[4],a);return ap(b(z[7],c))}var
g=h(kv),i=h(ku),j=h(kt),k=h(ks),l=h(kr);return[0,h(du),ce,l,k,j,i,g,e,d]}];function
a7(a){if(typeof
a==="number")return 0===a?h(kj):h(kk);else
switch(a[0]){case
0:var
e=[0,ce(a[1])],f=[0,h(ky),e];return b(j[23],f);case
1:var
g=[0,ap(a[1])],i=[0,h(kx),g];return b(j[23],i);case
2:var
k=a[1],l=a7(a[2]),m=[0,a7(k),l],n=[0,h(eQ),m];return b(j[23],n);case
3:var
o=a[1],p=a7(a[2]),q=[0,a7(o),p],r=[0,h(eR),q];return b(j[23],r);case
4:var
s=a[1],t=a7(a[2]),u=[0,a7(s),t],v=[0,h(eS),u];return b(j[23],v);case
5:var
c=a[2],d=a[1];if(0===c[0]){var
w=ap(c[1]),x=[0,a7(d),w],y=[0,h(yx),x];return b(j[23],y)}var
z=dv(c[1]),A=[0,a7(d),z],B=[0,h(eT),A];return b(j[23],B);case
6:var
C=[0,a7(a[1])],D=[0,h(kw),C];return b(j[23],D);default:var
E=[0,a7(a[1])],F=[0,h(gZ),E];return b(j[23],F)}}var
A3=[i,function(m){function
c(a){var
b=a[2];return[0,b,h(a[1])]}var
d=a(f[17],c,kH);function
e(a){var
c=b(ag[4],a);return dv(b(z[4],c))}var
g=h(eT),i=h(eS),j=h(gZ),k=h(eR),l=h(eQ);return[0,h(eP),a7,l,k,j,i,g,e,d]}];function
kP(i,h,g){var
c=[0,i,h,g];for(;;){var
e=c[1];if(0===e)return c[3];var
d=c[2];if(d){var
f=d[1],k=c[3],l=d[2],m=f[2],n=[0,a(kQ[4],f[1],0),m,k],c=[0,e-1|0,l,b(j[20],n)];continue}throw[0,aV,A4]}}function
kR(u,d,c){function
i(d){var
c=d;for(;;)switch(c[0]){case
0:return s[1];case
1:var
e=b(ag[3],c[1]);return b(s[5],e);case
5:case
6:var
c=c[1];continue;default:var
f=c[1],g=i(c[2]),h=i(f);return a(s[7],h,g)}}function
m(k){var
b=k;for(;;){if(typeof
b==="number")var
c=0;else
switch(b[0]){case
1:var
d=b[1],g=d[1],h=i(d[3]),j=i(g);return a(s[7],j,h);case
4:var
b=b[1];continue;case
5:var
f=b[3],e=b[1],c=1;break;case
0:var
c=0;break;default:var
f=b[2],e=b[1],c=1}if(c){var
l=m(f),n=m(e);return a(s[7],n,l)}return s[1]}}var
t=m(c),v=b(s[21],t);function
w(b,a){return[0,a,b+1|0]}var
o=a(f[18],w,v),p=g9(u,c);function
x(c){var
e=d[1],f=a(k[4],A5,c[2]);return[0,b(bS[1][6],f),e]}var
l=a(f[17],x,o),y=p[1];function
z(c,f){var
d=j[16],e=a(k[4],A6,c+1|0);return[0,b(bS[1][6],e),d]}var
q=a(f[18],z,y);function
A(b,a){return[0,a[1],b[1]]}var
B=g(f[23],A,o,l);function
r(g,c){function
e(c){switch(c[0]){case
0:return b(d[2],c[1]);case
1:var
h=b(ag[3],c[1]),i=g+a(f[38],h,o)|0;return b(j[10],i);case
2:var
k=c[1],l=e(c[2]),m=[0,e(k),l];return b(j[23],[0,d[3],m]);case
3:var
n=c[1],p=e(c[2]),q=[0,e(n),p];return b(j[23],[0,d[4],q]);case
4:var
r=c[1],s=e(c[2]),t=[0,e(r),s];return b(j[23],[0,d[6],t]);case
5:var
u=[0,e(c[1])];return b(j[23],[0,d[5],u]);default:var
v=c[1],w=b(d[8],c[2]),x=[0,e(v),w];return b(j[23],[0,d[7],x])}}return e(c)}function
C(g,e,c){try{var
l=[0,a(f[38],g,d[9]),[0,e,c]],m=b(j[23],l);return m}catch(a){a=n(a);if(a===L){var
i=[0,d[1],e,c],k=[0,h(gY),i];return b(j[23],k)}throw a}}function
e(d,c,a){if(typeof
a==="number")return 0===a?h(ke):h(gW);else
switch(a[0]){case
0:var
m=d+kL(p,a[1])|0;return b(j[10],m);case
1:var
f=a[1],i=f[2],k=f[1],l=r(c,f[3]);return C(i,r(c,k),l);case
2:var
n=a[1],o=e(d,c,a[2]),q=[0,e(d,c,n),o],s=[0,h(gU),q];return b(j[23],s);case
3:var
t=a[1],u=e(d,c,a[2]),v=[0,e(d,c,t),u],w=[0,h(gV),v];return b(j[23],w);case
4:var
x=a[1],y=h(gW),z=e(d,c,x);return g(j[35],z,0,y);default:var
A=a[1],B=e(d+1|0,c+1|0,a[3]),D=e(d,c,A);return g(j[35],D,0,B)}}var
D=b(f[1],l),E=b(f[1],q),F=bq(function(c){var
d=kL(p,c),e=a(k[4],A7,d),f=b(bS[1][6],e);return b(j[11],f)},c),G=b(f[9],B),H=b(f[9],q),I=e(b(f[1],l),0,c);function
J(a){return[0,[0,a[1]],a[2]]}var
K=kP(D,a(f[17],J,l),I);function
M(a){return[0,[0,a[1]],a[2]]}return[0,kP(E,a(f[17],M,q),K),H,G,F]}function
kS(g,f){var
d=f,c=g;for(;;){if(c){var
e=c[1],h=c[2],i=e[3],k=e[2],l=b(bS[1][6],e[1]),m=a(kQ[4],l,0),d=D(j[47],m,k,i,d),c=h;continue}return d}}var
A$=[i,function(a){return U(A_,A9,A8)}],Bd=[i,function(a){return U(Bc,Bb,Ba)}],Bh=[i,function(a){return U(Bg,Bf,Be)}],Bl=[i,function(a){return U(Bk,Bj,Bi)}];function
e2(c,a){if(typeof
a==="number"){var
d=[0,h(Bh),[0,c]];return b(j[23],d)}else{if(0===a[0]){var
e=[0,c,a[1]],f=[0,h(Bd),e];return b(j[23],f)}var
g=a[2],i=a[1],k=e2(c,a[3]),l=[0,c,e2(c,i),g,k],m=[0,h(A$),l];return b(j[23],m)}}function
kT(a){if(a){var
c=a[1][1],d=0,e=function(d,a){var
e=a[1];return dY(c,b(z[1],a[2]),e,d)};return g(f[20],e,d,a)}return 0}function
e3(a){if(typeof
a==="number")return h(xO);else
switch(a[0]){case
0:var
c=a[1],d=e3(a[2]),e=[0,cI(aP,ap,c),d],f=[0,h(xQ),e];return b(j[23],f);case
1:var
g=a[1],i=e3(a[2]),k=[0,cI(aP,ap,g),i],l=[0,h(xS),k];return b(j[23],l);default:var
m=a[3],n=a[2],o=a[1],p=g4(h(kl),e3,m),q=cI(aP,ap,n),r=[0,cI(aP,ap,o),q,p],s=[0,h(xU),r];return b(j[23],s)}}function
kU(a){return e3(a)}function
bi(b,a){return V(k[1],b,Bm,bT,a[1],g3,a[2])}function
cf(c,b){if(typeof
b==="number")return a(k[1],c,Bn);else
switch(b[0]){case
0:var
d=b[2],e=b[1],f=function(a,b){return bG(bT,a,b)};return V(k[1],c,Bo,f,e,cf,d);case
1:var
g=b[2],h=b[1],i=function(a,b){return bG(bT,a,b)};return V(k[1],c,Bp,i,h,cf,g);default:var
j=b[3],l=b[2],m=b[1],n=function(a,c){function
b(c,a){if(a){var
d=a[2],e=a[1];return d?V(k[1],c,z_,cf,e,b,d):D(k[1],c,z$,cf,e)}return 0}return V(k[1],a,Aa,Br,b,c,Bq)},o=function(a,b){return bG(bT,a,b)},p=function(a,b){return bG(bT,a,b)};return l0(k[1],c,Bs,p,m,o,l,n,j)}}function
kV(h,g,f,e,a){if(a){var
i=a[1],m=i[2],o=i[1],c=kV(h,g,f,e,a[2]),j=c[3],k=c[2],l=c[1];try{var
d=kN(h,g,k,j,m),p=[0,[0,[0,o,d[1]],l],d[2],d[3]];return p}catch(a){a=n(a);if(b(cb[18],a))return[0,l,k,j];throw a}}return[0,0,f,e]}function
kW(d,c,h,g,f){var
a=kN(d,c,h,b(bv[4],0),f),i=a[1],e=kV(d,c,a[2],a[3],g);return[0,e[1],i,e[2]]}var
e4=[i,function(c){var
a=h(kl),b=h(aP);return[0,h(aP),b,ap,a,kU]}],e5=[i,function(d){function
a(a){return cI(du,ce,a)}var
b=h(g0),c=h(du);return[0,h(du),c,ce,b,a]}];function
Bt(d,c){function
e(a){return(2*a|0)+1|0}return iC(function(d,c,g){var
i=b(ag[3],c),f=b(ag[3],d)+i|0;if(g){if(0===g[1]){var
j=[1,a(u[2],d,c)],k=-(2*e(f)|0)|0,l=b(bv[4],k),m=dc([1,j]);return[0,l,dx(h(aP),ap,m)]}var
n=[0,a(u[2],d,c)],o=-e(e(f))|0,p=b(bv[4],o),q=dc([0,n]);return[0,p,dx(h(aP),ap,q)]}var
r=[1,a(u[2],d,c)],s=[0,a(u[2],d,c)],t=b(bv[4],-(2*(2*f|0)|0)|0),v=fY(c,r,s);return[0,t,dx(h(aP),ap,v)]},d,c)}function
Bu(a,g,f,e,d){var
i=[0,a[2]],k=[0,h(kA),i],c=b(j[23],k),l=a[3],m=a[2],n=kO(c,function(a){return dx(m,l,a)},d),o=kT(e),p=e2(a[1],o);function
q(d){var
e=b(aZ[35][6],d),i=[0,a[1]],k=[0,h(Bl),i],l=[0,[0,Bw,p,b(j[23],k)],[0,[0,Bv,g,f],0]],m=[0,h(kz),[0,c]],o=kS([0,[0,Bx,n,b(j[23],m)],l],e),q=[0,b(aF[54],o),0];return b(M[65][22],q)}return b(cJ[68][8],q)}function
bU(c,a){if(typeof
c==="number"){if(0===c){if(typeof
a==="number")if(0===a)return 0}else
if(typeof
a==="number")if(0!==a)return 1}else
switch(c[0]){case
0:return[0,c[1]];case
1:if(typeof
a!=="number"&&1===a[0])return a;break;case
2:if(typeof
a!=="number"&&2===a[0]){var
d=a[1],f=c[1],g=bU(c[2],a[2]);return[2,bU(f,d),g]}break;case
3:if(typeof
a!=="number"&&3===a[0]){var
h=a[1],i=c[1],j=bU(c[2],a[2]);return[3,bU(i,h),j]}break;case
4:if(typeof
a!=="number"&&4===a[0])return[4,bU(c[1],a[1])];break;default:if(typeof
a!=="number"&&5===a[0]){var
k=a[2],l=a[1],m=c[1],n=bU(c[3],a[3]);return[5,bU(m,l),k,n]}}return b(e[3],BD)}var
g_=[aS,BE,aR(0)];function
kX(b,a){var
c=[0,a,0];function
d(c,b){var
d=b[2],e=b[1],a=c[2],f=c[1];if(typeof
a!=="number"&&0===a[0])return[0,e,d];return[0,[5,a,[0,f],e],[0,f,d]]}return g(f[21],d,b,c)}function
BF(t,r,q,l,T,F,E,S){var
m=kX(F,E)[1],x=b(bv[4],0),y=c4(function(c,b){return a(bv[3],c,b[1])},m,x),A=1+b(bv[5],y)|0,u=b(z[1],A),v=b(r,a(t,u,m)),o=v[1],G=v[2];function
p(g){if(g){var
h=g[1],d=p(g[2]);if(typeof
d==="number")return 0;else{if(0===d[0]){var
n=d[1],j=function(a){return a[1]},k=a(f[17],j,h),m=[0,b(l[2],0),k],c=b(l[3],m),e=typeof
c==="number"?0:0===c[0]?[0,[0,c[1],l]]:[1,c[1]];return typeof
e==="number"?0:0===e[0]?[0,[0,e[1],n]]:[1,[0,e[1],h]]}var
i=d[1];return[1,[0,i[1],i[2]]]}}return By}var
c=p(o);if(typeof
c==="number")return 0;else{if(0===c[0]){var
w=c[1],H=a(f[47],o,w),I=function(a){return a[1]},J=a(f[17],I,G),K=b7[1],M=function(c,b){return a(b7[4],b,c)},N=g(f[20],M,K,J),O=function(e,c){var
d=c[2],h=c[1],i=b7[1],j=b(d[2][4],d[1]);function
k(c,b){var
d=a(f[7],h,c)[2][1];return a(b7[4],d,b)}var
l=g(s[15],k,j,i);return a(b7[7],e,l)},P=g(f[20],O,N,H),d=function(c){if(typeof
c==="number")return 0===c?0:1;else
switch(c[0]){case
0:return[0,c[1]];case
1:var
o=c[2],p=o[2],q=o[1],s=c[1];return a(b7[3],q,P)?[1,s,[0,q,p]]:[0,p];case
2:var
t=c[2],f=d(c[1]),i=d(t);if(typeof
f!=="number"&&0===f[0])if(typeof
i!=="number"&&0===i[0]){var
u=[0,f[1],i[1]],v=[0,h(gU),u];return[0,b(j[23],v)]}return[2,f,i];case
3:var
w=c[2],k=d(c[1]),l=d(w);if(typeof
k!=="number"&&0===k[0])if(typeof
l!=="number"&&0===l[0]){var
x=[0,k[1],l[1]],y=[0,h(gV),x];return[0,b(j[23],y)]}return[3,k,l];case
4:var
m=d(c[1]);if(typeof
m!=="number"&&0===m[0]){var
z=[0,m[1]],A=[0,h(kd),z];return[0,b(j[23],A)]}return[4,m];default:var
r=c[2],B=c[3],n=d(c[1]),e=d(B);if(typeof
n!=="number"&&0===n[0]){var
C=n[1];if(r)return e;if(typeof
e!=="number"&&0===e[0])return[0,g(j[35],C,0,e[1])]}return[5,n,r,e]}},i=d(m),Q=b(r,a(t,u,i))[1],B=a(f[47],o,w),C=function(m){try{var
y=function(c){var
e=c[2],f=c[1],i=b(e[2][4],e[1]);function
d(g,f){var
c=g,b=f;for(;;){if(b){var
e=b[2],h=b[1];if(a(s[3],c,i))return[0,h,d(c+1|0,e)];var
c=c+1|0,b=e;continue}return 0}}return iN(W,d(0,f),m)},z=a(f[33],y,B),c=z}catch(a){a=n(a);if(a!==L)throw a;b(k[2],BB);b(e[52],e[28]);var
c=b(e[3],BC)}var
o=c[2],d=o[2],x=c[1],p=o[1];function
q(b,a){return[0,a[1],b]}var
i=a(f[18],q,m);function
r(d){try{var
g=a(f[7],x,d)[1],c=g}catch(a){a=n(a);if(a[1]!==e6)throw a;var
c=b(e[3],Bz)}return a(f[38],c,i)}try{var
w=a(d[5],p,r),l=w}catch(c){c=n(c);if(!b(cb[18],c))throw c;var
t=function(a){return a[1]},u=a(f[17],t,i),v=[0,b(d[2],0),u],g=b(d[3],v);if(typeof
g==="number")var
h=0;else
if(0===g[0])var
j=g[1],h=1;else
var
h=0;if(!h)var
j=b(e[3],BA);var
l=j}return l},D=a(f[17],C,Q),R=fJ(i);return[0,[0,R,i,g4(q[4],q[5],D)]]}return[1,c[1]]}}function
kY(j,i,h,g,f,d,c,a){try{var
k=BF(j,i,h,g,f,d,c,a);return k}catch(a){a=n(a);if(a===L){b(d4[4],e[28]);b(e[52],e[28]);return 0}throw a}}function
kZ(d,c,a){var
e=b(cJ[68][4],a);return g(aF[13],d,c,e)}function
bV(A,z,y,x,w,v,u){function
c(c){var
B=b(aZ[35][4],c),C=b(aZ[35][6],c),E=b(aZ[35][14],c);try{var
d=[0,b(aZ[35][5],c),B],i=kW(d,A,g5(d),E,C),q=i[3][1],L=i[2],N=i[1],k=h(x),O=h(w),l=kY(z,y,k,v,q,N,L,d);if(typeof
l==="number"){b(e[52],e[28]);var
P=b(bh[3],BM),m=a(M[65][4],0,P)}else
if(0===l[0])var
o=l[1],r=o[2],Q=o[3],R=o[1],g=kR(d,O,r),p=g[3],S=g[4],T=g[2],U=g[1],s=function(a){return b(aF[2],a[1])},V=a(f[17],s,p),W=b(M[65][22],V),X=a(f[17],s,T),Y=b(M[65][22],X),Z=function(b){return[0,a(k0[1],0,[1,[0,b]])]},$=b(bS[1][6],BN),t=kZ(bS[1][10][1],$,c),aa=function(a){var
c=a[2];return[0,b(j[11],a[1]),c]},ab=a(f[17],aa,p),ac=[0,k[4]],ad=[0,h(kf),ac],ae=[0,Y,[0,W,[0,Bu(k,Q,b(j[23],ad),ab,S),0]]],af=b(M[65][22],ae),ag=g9(d,r)[1],ah=b(f[9],ag),ai=function(b){return a(f[7],q,b[2]-1|0)},aj=a(f[17],ai,p),ak=a(e[26],ah,aj),al=a(M[65][3],af,u),am=b(aF[79],0),an=a(M[65][3],am,al),ao=[0,b(j[11],t),ak],ap=b(j[40],ao),aq=[0,b(aF[46],ap),0],ar=a(f[17],j[11],R),as=[0,b(aF[l9],ar),aq],at=[0,an,[0,b(M[65][22],as),0]],au=Z(t),av=D(aF[mU],1,BO,au,U),m=a(M[65][21],av,at);else
var
aw=b(bh[3],BP),m=a(M[65][4],0,aw);return m}catch(c){c=n(c);if(c===_){var
F=b(bh[3],BG);return a(M[65][4],0,F)}if(c===eD){var
G=b(bh[3],BH);return a(M[65][4],0,G)}if(c===g_){b(e[52],e[28]);var
H=a(e[17],BJ,BI),I=a(e[17],BK,H),J=a(e[17],BL,I),K=b(bh[3],J);return a(M[65][4],0,K)}throw c}}return b(cJ[68][8],c)}function
BQ(g,f,e){var
a=h(ki),c=h(eP),i=[0,h(g0)],k=[0,h(kf),i],l=b(j[23],k),m=[0,h(kA),[0,a]],d=b(j[23],m),n=kO(d,function(b){return dx(a,bf,b)},e),o=e2(c,kT(f));function
p(a){var
e=b(aZ[35][6],a),f=[0,U(BU,BT,BS),[0,c]],i=[0,[0,BV,o,b(j[23],f)],[0,[0,BR,g,l],0]],k=[0,h(kz),[0,d]],m=kS([0,[0,BW,n,b(j[23],k)],i],e),p=[0,b(aF[54],m),0];return b(M[65][22],p)}return b(cJ[68][8],p)}function
e7(au){return function(av){var
x=[i,function(d){function
a(a){return cI(du,ce,a)}var
b=h(g0),c=h(ki);return[0,h(eP),c,ce,b,a]}];function
c(c){var
y=b(aZ[35][4],c),z=b(aZ[35][6],c),A=b(aZ[35][14],c);try{var
d=[0,b(aZ[35][5],c),y],i=kW(d,AW,g5(d),A,z),p=i[2],q=i[1],r=i[3][1],I=h(x),J=function(a){var
b=a[2],c=a[1];return[0,c,a1(function(a){return dX(aD,a)},b)]},K=a(f[17],J,q),L=a1(function(a){return dX(aD,a)},p),k=kY(function(b,a){return a},cu,I,au,r,K,L,d);if(typeof
k==="number")var
o=0;else
if(0===k[0])var
l=k[1],O=l[3],P=l[2],Q=l[1],R=function(b){return a(f[31],b[1],Q)},t=kX(a(f[35],R,q),p),S=t[2],u=bU(P,t[1]),g=kR(d,h(A3),u),m=g[3],T=g[4],U=g[2],V=g[1],v=function(a){return b(aF[2],a[1])},W=a(f[17],v,m),X=b(M[65][22],W),Y=a(f[17],v,U),Z=b(M[65][22],Y),$=function(b){return[0,a(k0[1],0,[1,[0,b]])]},aa=b(bS[1][6],B4),w=kZ(bS[1][10][1],aa,c),ab=function(a){var
c=a[2];return[0,b(j[11],a[1]),c]},ac=[0,Z,[0,X,[0,BQ(O,a(f[17],ab,m),T),0]]],ad=b(M[65][22],ac),ae=g9(d,u)[1],af=b(f[9],ae),ag=function(b){return a(f[7],r,b[2]-1|0)},ah=a(f[17],ag,m),ai=a(e[26],af,ah),aj=a(M[65][3],ad,av),ak=b(aF[79],0),al=a(M[65][3],ak,aj),am=[0,b(j[11],w),ai],an=b(j[40],am),ao=[0,b(aF[46],an),0],ap=a(f[17],j[11],S),aq=[0,b(aF[l9],ap),ao],ar=[0,al,[0,b(M[65][22],aq),0]],as=$(w),at=D(aF[mU],1,B5,as,V),s=a(M[65][21],at,ar),o=1;else
var
o=0;if(!o){b(e[52],e[28]);var
N=b(bh[3],B3),s=a(M[65][4],0,N)}return s}catch(c){c=n(c);if(c===_){var
B=b(bh[3],BX);return a(M[65][4],0,B)}if(c===eD){var
C=b(bh[3],BY);return a(M[65][4],0,C)}if(c===g_){b(e[52],e[28]);var
E=a(e[17],B0,BZ),F=a(e[17],B1,E),G=a(e[17],B2,F),H=b(bh[3],G);return a(M[65][4],0,H)}throw c}}return b(cJ[68][8],c)}}var
B6=eO([0,W,bb[27]]),B_=b(B9[8],B8)?0:[i,function(a){throw g_}];function
Ce(i){var
l=i[2],m=i[1];h(B_);var
j=[0,Cc,[0,Cb,[0,a(e[17],Ca,B$[22]),0]]],k=b(Cd[3],0),d=g(f[20],bC[4],k,j),c=iX(d,[0,d],[0,m,l]);if(0===c[0])return c[1];throw b(e[3],c[1])}var
Cf=a(B6[4],B7,Ce);function
k1(c,a){return b(Cf,[0,c,a])}function
e8(a){switch(a[0]){case
0:return[0,[0,a[1],0]];case
1:var
b=a[1];return[1,b,e8(a[2])];default:var
c=a[2],d=a[1],e=e8(a[3]);return[2,e8(d),c,e]}}function
k2(f,a){var
c=k1(f,a);if(c){var
d=jZ(c[1]);return f0(a,d)?[0,d]:(b(e[31],Cg),0)}return 0}function
dy(e,d,c){function
f(i,h){var
c=i,d=h;for(;;){if(typeof
c!=="number")switch(c[0]){case
0:var
g=b(ag[5],c[1]);return e<=g?a(s[4],g-e|0,d):d;case
2:var
c=c[2];continue;case
3:case
4:var
j=c[1],k=f(c[2],d),c=j,d=k;continue}return d}}return f(c,d)}function
dz(a){return dy(0,s[1],a)}function
bH(a,d){function
c(a){if(typeof
a!=="number")switch(a[0]){case
0:var
e=b(d,b(ag[5],a[1]));return[0,b(z[4],e)];case
2:var
f=a[1];return[2,f,c(a[2])];case
3:var
g=a[1],h=c(a[2]);return[3,c(g),h];case
4:var
i=a[1],j=c(a[2]);return[4,c(i),j]}return a}return c(a)}function
g$(a){function
d(i,h,e){var
b=i,a=h,c=e;for(;;)if(typeof
a==="number")return c;else
switch(a[0]){case
0:var
j=a[2],k=dy(b,c,a[1]),b=b+1|0,a=j,c=k;continue;case
1:var
l=a[2],m=dy(b,c,a[1]),b=b+1|0,a=l,c=m;continue;default:var
n=a[3],o=a[1],p=dy(b,dy(b,c,a[2]),o),q=function(c,a){return d(b+1|0,a,c)};return g(f[20],q,p,n)}}return d(0,a,s[1])}function
ha(a,e){function
c(c,a){return a<c?a:b(e,a-c|0)+c|0}function
d(b,a){if(typeof
a==="number")return 0;else
switch(a[0]){case
0:var
e=a[1],f=d(b+1|0,a[2]);return[0,bH(e,function(a){return c(b,a)}),f];case
1:var
g=a[1],h=d(b+1|0,a[2]);return[1,bH(g,function(a){return c(b,a)}),h];default:var
i=a[3],j=a[2],k=a[1],l=ba(function(a){return d(b+1|0,a)},i),m=bH(j,function(a){return c(b,a)});return[2,bH(k,function(a){return c(b,a)}),m,l]}}return d(0,a)}function
dA(d,c){function
e(a){var
b=a[2];return[0,ip(a[1]),b]}return b(d,a(f[17],e,c))}var
k3=eO([0,W,bb[27]]),Ci=eO([0,W,bb[27]]);function
Cj(a){var
b=a[1],c=a[2],d=b[3],e=b[2];return dA(function(a){return j6(e,d,a)},c)}var
Cl=a(k3[4],Ck,Cj);function
Cm(a){var
b=a[1],c=a[2],d=b[3],e=b[2];return dA(function(a){return j7(e,d,a)},c)}var
Co=a(k3[4],Cn,Cm);function
Cp(a){var
b=a[2],c=a[1];return dA(function(a){return jW(c,a)},b)}var
Cr=a(Ci[4],Cq,Cp);function
Cs(b,a){return bg(bi,b,a[1])}function
Ct(a,b){return bG(bi,a,b)}var
Cv=[0,Cu,gT,function(a){var
b=a[2],c=a[1];return dA(function(a){return gM(c,a)},b)},dz,bH,Ct,Cs];function
Cw(b,a){return bg(bi,b,a[1])}function
Cx(a,b){return bG(bi,a,b)}var
Cz=[0,Cy,gT,function(a){var
b=a[2],c=a[1];return dA(function(a){return gM(c,a)},b)},dz,bH,Cx,Cw];function
CA(b,a){return bg(bi,b,a[1])}var
k4=[0,CB,gT,Cr,dz,bH,function(a,b){return bG(bi,a,b)},CA];function
k5(b,a){function
c(b,a){return bg(bi,b,a[1])}function
d(a,b){return bG(bi,a,b)}function
e(a){return k2(a[1],a[2])}return[0,CC,function(c){return[0,b,a]},e,dz,bH,d,c]}function
k6(b,a){function
c(b,a){return bg(bi,b,a[1])}function
d(a,b){return bG(bi,a,b)}function
e(a){return k2(a[1],a[2])}return[0,CD,function(c){return[0,b,a]},e,dz,bH,d,c]}function
k7(d,c){function
g(b,a){return bg(bT,b,a[1])}function
h(h){var
i=h[2],k=h[1];function
j(a){var
b=a[2];return[0,e8(a[1]),b]}var
d=k1(k,a(f[17],j,i));if(d)var
g=j1(d[1]),c=ir(i,g)?[0,g]:(b(e[31],Ch),b(e[52],e[28]),0);else
var
c=0;if(typeof
c!=="number"&&0===c[0])return[0,[0,c[1],0]];return 0}return[0,CE,function(a){return[0,d,c]},h,g$,ha,cf,g]}var
CG=[0,CF,ka,Cl,g$,ha,cf,function(b,a){return bg(bT,b,a[1])}],CI=[0,CH,ka,Co,g$,ha,cf,function(b,a){return bg(bT,b,a[1])}];function
CJ(b,a){return a}function
k8(a){return bV(eY,CJ,cu,e5,e1,Cv,a)}function
hb(a){var
b=k5(CK,[0,a]);function
c(b,a){return a}return function(a){return bV(eY,c,cu,e5,e1,b,a)}}var
k9=e7(Cz);function
hc(a){return e7(k6(CL,[0,a]))}function
hd(a){var
b=k7(CM,[0,a]);function
c(b,a){return a}return function(a){return bV(eX,c,c_,e4,e0,b,a)}}var
CO=k7(CN,0);function
CP(b,a){return a}function
k_(a){return bV(eX,CP,c_,e4,e0,CO,a)}var
CR=k5(CQ,0);function
CS(b,a){return a}function
k$(a){return bV(eY,CS,cu,e5,e1,CR,a)}var
la=e7(k6(CT,0));function
lb(a){return bV(eX,Bt,c_,e4,e0,CG,a)}function
CU(b,a){return a}function
lc(a){return bV(eX,CU,c_,e4,e0,CI,a)}var
ld=e7(k4);function
CV(b,a){return a}function
le(a){return bV(eY,CV,cu,e5,e1,k4,a)}function
lf(d){function
c(c){var
e=b(aZ[35][4],c);if(kB(b(aZ[35][5],c),e,d))return M[65][2];var
f=b(bh[3],CW);return a(M[65][4],0,f)}return b(cJ[68][8],c)}aA(1038,[0,lf,hd,hb,hc,lb,lc,ld,le,k_,k$,la,k8,k9,kU],"Micromega_plugin__Coq_micromega");b(CX[9],ax);var
CY=0,C0=[0,[0,CZ,function(a){return aF[56]}],CY];S(aG[8],ax,C1,0,0,C0);var
C2=0;function
C3(a,b){return lf(a)}var
C5=[0,[0,[0,C4,[1,[5,b(aa[16],e9[11])],0]],C3],C2];S(aG[8],ax,C6,0,0,C5);var
C7=0;function
C8(d,c){var
e=a(ay[24],c,d);return b(hd(-1),e)}var
C_=[0,[0,[0,C9,[1,[5,b(aa[16],az[8])],0]],C8],C7];function
C$(e,d,c){var
f=a(ay[24],c,d);return b(hd(e),f)}var
Da=[1,[5,b(aa[16],az[8])],0],Dc=[0,[0,[0,Db,[1,[5,b(aa[16],e9[6])],Da]],C$],C_];S(aG[8],ax,Dd,0,0,Dc);var
De=0;function
Df(c,b){return lb(a(ay[24],b,c))}var
Dh=[0,[0,[0,Dg,[1,[5,b(aa[16],az[8])],0]],Df],De];S(aG[8],ax,Di,0,0,Dh);var
Dj=0;function
Dk(c,b){return lc(a(ay[24],b,c))}var
Dm=[0,[0,[0,Dl,[1,[5,b(aa[16],az[8])],0]],Dk],Dj];S(aG[8],ax,Dn,0,0,Dm);var
Do=0;function
Dp(d,c){return b(ld,a(ay[24],c,d))}var
Dr=[0,[0,[0,Dq,[1,[5,b(aa[16],az[8])],0]],Dp],Do];S(aG[8],ax,Ds,0,0,Dr);var
Dt=0;function
Du(c,b){return le(a(ay[24],b,c))}var
Dw=[0,[0,[0,Dv,[1,[5,b(aa[16],az[8])],0]],Du],Dt];S(aG[8],ax,Dx,0,0,Dw);var
Dy=0;function
Dz(c,b){return k_(a(ay[24],b,c))}var
DB=[0,[0,[0,DA,[1,[5,b(aa[16],az[8])],0]],Dz],Dy];S(aG[8],ax,DC,0,0,DB);var
DD=0;function
DE(c,b){return k$(a(ay[24],b,c))}var
DG=[0,[0,[0,DF,[1,[5,b(aa[16],az[8])],0]],DE],DD];S(aG[8],ax,DH,0,0,DG);var
DI=0;function
DJ(d,c){return b(la,a(ay[24],c,d))}var
DL=[0,[0,[0,DK,[1,[5,b(aa[16],az[8])],0]],DJ],DI];S(aG[8],ax,DM,0,0,DL);var
DN=0;function
DO(c,b){return k8(a(ay[24],b,c))}var
DQ=[0,[0,[0,DP,[1,[5,b(aa[16],az[8])],0]],DO],DN];S(aG[8],ax,DR,0,0,DQ);var
DS=0;function
DT(d,c){return b(k9,a(ay[24],c,d))}var
DV=[0,[0,[0,DU,[1,[5,b(aa[16],az[8])],0]],DT],DS];S(aG[8],ax,DW,0,0,DV);var
DX=0;function
DY(d,c){var
e=a(ay[24],c,d);return b(hc(-1),e)}var
D0=[0,[0,[0,DZ,[1,[5,b(aa[16],az[8])],0]],DY],DX];function
D1(e,d,c){var
f=a(ay[24],c,d);return b(hc(e),f)}var
D2=[1,[5,b(aa[16],az[8])],0],D4=[0,[0,[0,D3,[1,[5,b(aa[16],e9[6])],D2]],D1],D0];S(aG[8],ax,D5,0,0,D4);var
D6=0;function
D7(d,c){var
e=a(ay[24],c,d);return b(hb(-1),e)}var
D9=[0,[0,[0,D8,[1,[5,b(aa[16],az[8])],0]],D7],D6];function
D_(e,d,c){var
f=a(ay[24],c,d);return b(hb(e),f)}var
D$=[1,[5,b(aa[16],az[8])],0],Eb=[0,[0,[0,Ea,[1,[5,b(aa[16],e9[6])],D$]],D_],D9];S(aG[8],ax,Ec,0,0,Eb);aA(1045,[0],"Micromega_plugin__G_micromega");function
dB(b,a){return 0===fs(b,a)?1:0}function
dC(b,a){return fs(b,a)<0?1:0}function
Ed(b,a){return fs(b,a)<=0?1:0}function
aj(d,c,a){return b(d,b(c,a))}function
dD(b){return a(d[14],Ee,[0,b])}function
e_(b){return a(d[14],Ef,[0,b])}function
lg(c){var
e=b(d[54],c),a=b(dd[5],e),f=b(dd[3],a),g=b(d[51],f),h=b(dd[2],a);return[0,b(d[51],h),g]}function
Eg(a){return a[1]}function
hf(a){return aj(Eg,lg,a)}function
Eh(a){return a[2]}function
e$(a){return aj(Eh,lg,a)}function
fa(e,c){var
f=b(d[52],c),g=b(d[52],e),h=a(l[17],g,f);return b(d[51],h)}function
fb(e,c){if(a(d[26],e,he))if(a(d[26],c,he))return he;var
f=fa(e,c),g=a(d[6],e,c),h=a(d[9],g,f);return b(d[15],h)}function
bk(d,c){if(c){var
f=c[2],g=c[1];return f?a(d,g,bk(d,f)):g}return b(e[3],Ei)}function
fc(d,b,c){if(b){var
e=b[1],h=fc(d,b[2],c),i=function(c,b){return[0,a(d,e,c),b]};return g(f[21],i,c,h)}return 0}function
fd(a){return g(f[21],e[17],a,Ej)}function
a8(c){var
a=cn(c)-1|0,b=0;for(;;){if(0<=a){var
d=[0,g(a9[4],c,a,1),b],a=a-1|0,b=d;continue}return b}}function
hg(f,e,d){var
c=f,a=d;for(;;){if(1<=c){var
c=c-1|0,a=b(e,a);continue}return a}}function
P(a,b){return b<a?0:[0,a,P(a+1|0,b)]}function
hh(d,c){var
a=c;for(;;){if(a){var
f=a[2],g=a[1];try{var
h=b(d,g);return h}catch(b){b=n(b);if(b[1]===e6){var
a=f;continue}throw b}}return b(e[3],Ek)}}function
lh(d,c){var
a=c;for(;;){if(a){var
e=a[2],b=dB(d,a[1]);if(b)return b;var
a=e;continue}return 0}}function
El(b,a){return lh(b,a)?a:[0,b,a]}function
hi(b,a){return g(f[21],El,b,a)}function
hj(c,b){function
d(a){return 1-lh(a,b)}return a(f[35],d,c)}function
dE(a,d,c){var
e=b(a,c);return dC(b(a,d),e)}function
cK(d,c){var
a=c;for(;;){if(a){var
e=a[2];b(d,a[1]);var
a=e;continue}return 0}}function
aQ(d,c){if(c){var
g=c[1],i=c[2],j=b(d,g),h=a(f[37],j,i),k=h[2],l=[0,g,aQ(d,h[1])],m=aQ(d,k);return a(e[26],m,l)}return 0}function
li(a){if(a){var
b=a[2];if(b){var
d=a[1],e=b[1],c=li(b);return dB(d,e)?c:c===b?a:[0,d,c]}}return a}function
cL(a){return li(aQ(Ed,a))}var
q=0;function
aq(a){return typeof
a==="number"?1:0}function
lj(c,a){if(a){var
d=a[1],e=d[2],f=d[1],g=lj(c,a[2]);return[0,[0,f,b(c,e)],g]}return 0}function
aH(b,a){if(typeof
a==="number")return 0;else{if(0===a[0]){var
c=a[1];return[0,c,lj(b,a[2])]}var
d=a[3],e=a[2],f=a[1],g=aH(b,a[4]);return[1,f,e,aH(b,d),g]}}function
B(f,j,i){var
c=j,a=i;for(;;)if(typeof
a==="number")return c;else{if(0===a[0]){var
d=c,b=a[2];for(;;){if(b){var
e=b[1],h=b[2],d=g(f,d,e[1],e[2]),b=h;continue}return d}}var
k=a[4],c=B(f,c,a[3]),a=k;continue}}function
lk(c,a,b){if(a){var
d=a[1],e=d[2],f=d[1];return g(c,f,e,lk(c,a[2],b))}return b}function
dF(c,e,d){var
a=e,b=d;for(;;)if(typeof
a==="number")return b;else{if(0===a[0])return lk(c,a[2],b);var
f=a[3],g=dF(c,a[4],b),a=f,b=g;continue}}function
cg(b,e,g,d){var
c=b^g,a=c&(-c|0),f=b&(a-1|0);return 0===(b&a)?[1,f,a,e,d]:[1,f,a,d,e]}function
ll(a,b){var
c=a[1];if(b){var
d=b[2],e=b[1],f=e[1];return dB(c,f)?[0,a,d]:dC(c,f)?[0,a,b]:[0,e,ll(a,d)]}return[0,a,0]}function
fe(f,e,d,c){if(d){if(c){var
j=c[2],g=c[1],k=g[1],l=d[2],h=d[1],i=h[1],o=g[2],p=h[2];if(dC(i,k))return[0,h,fe(f,e,l,c)];if(dC(k,i))return[0,g,fe(f,e,d,j)];var
m=a(f,p,o),n=fe(f,e,l,j);return b(e,m)?n:[0,[0,i,m],n]}return d}return c}function
F(d,e){var
c=b(bb[27],d);function
g(a){if(typeof
a==="number")return[0,c,[0,[0,d,e],0]];else{if(0===a[0]){var
h=a[1],k=a[2];return h===c?[0,h,ll([0,d,e],k)]:cg(h,a,c,[0,c,[0,[0,d,e],0]])}var
i=a[4],j=a[3],b=a[2],f=a[1];return(c&(b-1|0))!==f?cg(f,a,c,[0,c,[0,[0,d,e],0]]):0===(c&b)?[1,f,b,g(j),i]:[1,f,b,j,g(i)]}}return g}function
aI(e,d,b,a){if(typeof
b==="number")return a;else
if(0===b[0]){var
m=b[1],F=b[2];if(typeof
a==="number")var
t=0;else{if(0===a[0]){var
w=a[1],G=a[2];if(m===w){var
x=fe(e,d,F,G);return 0===x?0:[0,m,x]}return cg(m,b,w,a)}var
y=a,q=a[4],p=a[3],j=a[2],i=a[1],o=b,n=m,t=1}}else{var
k=b[4],l=b[3],g=b[2],c=b[1];if(typeof
a==="number")var
t=0;else{if(0!==a[0]){var
r=a[4],s=a[3],h=a[2],f=a[1];if(g<h){if((f&(g-1|0))!==c)return cg(c,b,f,a);if(0===(f&g)){var
B=aI(e,d,l,a);return aq(B)?k:[1,c,g,B,k]}var
C=aI(e,d,k,a);return aq(C)?l:[1,c,g,l,C]}if(h<g){if((c&(h-1|0))!==f)return cg(c,b,f,a);if(0===(c&h)){var
D=aI(e,d,b,s);return aq(D)?r:[1,f,h,D,r]}var
E=aI(e,d,b,r);return aq(E)?s:[1,f,h,s,E]}if(c===f){var
u=aI(e,d,l,s),v=aI(e,d,k,r);return aq(u)?v:aq(v)?u:[1,c,g,u,v]}return cg(c,b,f,a)}var
y=b,q=k,p=l,j=g,i=c,o=a,n=a[1],t=1}}if(t){if((n&(j-1|0))===i){if(0===(n&j)){var
z=aI(e,d,o,p);return aq(z)?q:[1,i,j,z,q]}var
A=aI(e,d,o,q);return aq(A)?p:[1,i,j,p,A]}return cg(n,o,i,y)}return b}function
a0(c,a){return b(F(c,a),q)}function
hk(c){var
a=c;for(;;)if(typeof
a==="number")return b(e[3],Em);else{if(0===a[0])return b(f[5],a[2]);var
a=a[3];continue}}function
lm(k,e,c){var
h=b(bb[27],c),a=k;for(;;){if(typeof
a!=="number"){if(0!==a[0]){var
m=a[4],n=a[3],o=0===(h&a[2])?n:m,a=o;continue}var
l=a[2];if(a[1]===h){var
d=l;for(;;){if(d){var
f=d[1],g=f[1],i=d[2],j=f[2];if(dB(c,g))return j;if(0<fs(c,g)){var
d=i;continue}return b(e,c)}return b(e,c)}}}return b(e,c)}}function
ff(a){function
c(a){return b(e[3],En)}return function(b){return lm(a,c,b)}}function
a_(c,b,a){return lm(c,function(b){return a},b)}function
ln(b,a){if(a){var
c=a[2],d=a[1],e=d[1];if(dB(b,e))return c;if(dC(b,e))return a;var
f=ln(b,c);return f===c?a:[0,d,f]}return 0}function
hl(k){var
e=b(bb[27],k);function
f(a){if(typeof
a!=="number")if(0===a[0]){var
l=a[2],m=a[1];if(m===e){var
g=ln(k,l);return g===l?a:0===g?0:[0,m,g]}}else{var
b=a[4],c=a[3],d=a[2],h=a[1];if((e&(d-1|0))===h){if(0===(e&d)){var
i=f(c);return i===c?a:aq(i)?b:[1,h,d,i,b]}var
j=f(b);return j===b?a:aq(j)?c:[1,h,d,c,j]}}return a}return f}function
ch(a){var
b=0;return cL(B(function(c,b,a){return[0,[0,b,a],c]},b,a))}function
fg(a){var
b=0;return cL(B(function(b,a,c){return[0,a,b]},b,a))}var
cM=[aS,Eo,aR(0)];function
Ep(a){return bK(a,0)}var
Eq=a(e[17],ls,lt),Er=a(e[17],lr,Eq),Es=a(e[17],lq,Er),Et=a(e[17],lp,Es),Ev=a8(a(e[17],lo,Et)),Eu=256,Ew=e[6];function
Ex(a){return aj(Ew,Ep,a)}var
bW=C.caml_make_vect(g(f[21],Ex,Ev,Eu),0),Ey=a8(lo);cK(function(b){var
a=bK(b,0);return w(bW,a)[a+1]=1},Ey);var
Ez=a8(lp);cK(function(b){var
a=bK(b,0);return w(bW,a)[a+1]=2},Ez);var
EA=a8(lq);cK(function(b){var
a=bK(b,0);return w(bW,a)[a+1]=4},EA);var
EB=a8(lr);cK(function(b){var
a=bK(b,0);return w(bW,a)[a+1]=8},EB);var
EC=a8(ls);cK(function(b){var
a=bK(b,0);return w(bW,a)[a+1]=16},EC);var
ED=a8(lt);cK(function(b){var
a=bK(b,0);return w(bW,a)[a+1]=32},ED);function
hm(b){var
a=bK(b,0);return 1===w(bW,a)[a+1]?1:0}function
lu(b){var
a=bK(b,0);return 32===w(bW,a)[a+1]?1:0}function
fh(a,d,c){try{var
e=b(a,c);return e}catch(a){a=n(a);if(a===cM)return b(d,c);throw a}}function
ac(f,e,d){var
a=b(f,d),g=a[1],c=b(e,a[2]);return[0,[0,g,c[1]],c[2]]}function
ci(a,c){try{var
d=b(a,c),f=d[1],e=ci(a,d[2]),g=[0,[0,f,e[1]],e[2]];return g}catch(a){a=n(a);if(a===cM)return[0,0,c];throw a}}function
ak(e,d,c){var
a=b(e,c),f=a[2];return[0,b(d,a[1]),f]}function
EE(f,d,c){try{var
h=b(d,c);return h}catch(c){c=n(c);if(c===cM){var
g=a(e[17],f,EF);return b(e[3],g)}throw c}}function
EG(a,c,b){function
d(a){return[0,a[1],a[2]]}function
e(a){return a[2]}function
f(c){return EE(b,a,c)}function
g(a){return ac(c,f,a)}function
h(a){return ak(g,e,a)}function
i(a){return ci(h,a)}function
j(b){return ac(a,i,b)}return function(a){return ak(j,d,a)}}function
hn(d,c){try{var
a=b(d,c),e=[0,[0,a[1],0],a[2]];return e}catch(a){a=n(a);if(a===cM)return[0,0,c];throw a}}function
dG(d,a){if(a){var
c=a[1],e=a[2];if(b(d,c))return[0,c,e];throw cM}throw cM}function
bl(a){function
b(b){return W(b,a)}return function(a){return dG(b,a)}}function
fi(b,a,d){if(0<b)var
e=function(a){return[0,a[1],a[2]]},f=b-1|0,g=function(b){return fi(f,a,b)},h=function(b){return ac(a,g,b)},c=function(a){return ak(h,e,a)};else
var
c=function(b){return ci(a,b)};return c(d)}var
cj=b(bC[16],0);function
EH(g){try{var
j=b(e[1][67],g),d=j}catch(c){c=n(c);if(c[1]!==EI)throw c;var
h=a(e[17],EJ,g),d=b(e[3],h)}function
c(g){try{var
a=c([0,b(e[1][71],d),g]);return a}catch(a){a=n(a);if(a===j8)return b(f[9],g);throw a}}var
i=c(0);b(e[1][81],d);return i}function
fj(b){var
c=EH(b);return a(a9[7],EK,c)}function
ck(f,d){var
c=b(e[1][48],f);a(e[55],c,d);return b(e[65],c)}function
EL(d,a){var
c=a;for(;;)try{var
e=b(d,c);return e}catch(a){a=n(a);if(a[1]===e6){var
c=c+1|0;continue}throw a}}var
ho=[aS,EM,aR(0)];aA(1048,[0,aj,bj,e_,dD,fd,a8,hg,hh,q,aq,F,a0,hk,aI,P,a_,ff,B,dF,aH,hl,fg,ch,hi,hj,aQ,cL,dE,fc,fa,fb,hf,e$,bk,ak,ac,bl,ci,dG,hn,hm,fh,lu,fi,EG,cj,fj,ck,function(d,c,a){var
e=a$(d,0);if(-1===e)return EL(c,a);if(0===e)throw ho;return function(e,c){var
a=c;for(;;)try{var
f=b(e,a);return f}catch(b){b=n(b);if(b[1]===e6){if(a===d)throw ho;var
a=a+1|0;continue}throw b}}(c,a)},ho],"Micromega_plugin__Sos_lib");var
hp=[aS,EN,aR(0)];function
hq(c){var
e=a(d[9],EP,EO),f=b(d[15],c);if(a(d[27],f,e))return hq(a(d[6],EQ,c))-1|0;var
g=b(d[15],c);return a(d[30],g,ER)?hq(a(d[9],c,ES))+1|0:0}function
dH(j,c){if(a(d[26],c,ET))return EU;var
h=b(d[15],c),g=hq(h),k=e_(-g|0),l=a(d[6],k,h),m=a(d[1],l,EV),n=e_(j),o=a(d[6],n,m),p=b(d[23],o);if(0===g)var
i=EW;else
var
u=b(e[22],g),i=a(e[17],E0,u);var
q=a8(b(d[40],p)),r=fd(b(f[6],q)),s=a(e[17],r,i),t=a(d[27],c,EX)?EY:EZ;return a(e[17],t,s)}function
cN(h,f,e,d){var
c=h,a=f,b=d;for(;;){if(a){var
i=a[2],j=g(e,a[1],c,b),c=c+1|0,a=i,b=j;continue}return b}}function
dI(h,g,f){var
c=h,b=f;for(;;){var
e=c[2],d=c[1];if(e<d)return b;var
c=[0,d+1|0,e],b=a(g,d,b);continue}}function
cO(f,e,c){return a(d[26],e,E1)?c:b(F(f,e),c)}function
bm(b,a){return a_(b[2],a,E2)}function
hr(c,a){var
d=a[2],e=a[1];return[0,e,B(function(e,d,a){return cO(d,b(c,a),e)},q,d)]}function
lv(a){return typeof
a[2]==="number"?1:0}function
fk(a){return[0,a,q]}function
lw(c,b){var
e=b[1];if(a(d[26],c,E4))return fk(e);var
f=b[2];return[0,e,aH(function(b){return a(d[6],c,b)},f)]}function
E5(a){var
c=b(f[1],a),d=P(1,c);return[0,c,D(f[26],F,d,a,q)]}function
lx(a){var
b=aH(d[3],a[2]);return[0,a[1],b]}function
ly(d,a){var
c=a[1][2],e=a[2];return[0,c,B(function(c,a,e){var
f=a[2];return a[1]===d?b(F(f,e),c):c},q,e)]}function
E9(a){return 0}function
E_(b,a){return b+a|0}function
fl(a,b){return aI(E_,E9,a,b)}function
lz(b,a){return a_(a,b,0)}function
E$(a){var
b=1;return B(function(c,b,e){var
a=W(b,q),d=a?c:a;return d},b,a)}function
cl(b){return a(d[26],b,Fb)?q:a0(q,b)}function
lA(b,c){return a(d[26],b,Fc)?q:aH(function(c){return a(d[6],b,c)},c)}function
dJ(a){return aH(d[3],a)}function
cm(c,b){function
e(b){return a(d[26],b,Fd)}return aI(d[1],e,c,b)}function
hs(b,a){return cm(b,dJ(a))}function
bI(c,e){return B(function(g,f,c){var
h=a(d[26],c,Fe)?q:W(f,q)?aH(function(b){return a(d[6],c,b)},e):B(function(h,g,e){var
i=a(d[6],c,e);return b(F(fl(f,g),i),h)},q,e);return cm(h,g)},q,c)}function
fm(b,a){if(0===a)return cl(Ff);if(1===a)return b;var
d=fm(b,a/2|0),c=bI(d,d);return 1===(a%2|0)?bI(b,c):c}function
fn(b){var
c=0;return B(function(f,d,g){var
b=0,c=B(function(b,c,a){return a+b|0},b,d);return a(e[6],c,f)},c,b)}function
ht(a){var
b=0;return dF(function(b,c){var
a=fg(b);return function(b){return hi(a,b)}},a,b)}function
fo(b,a){var
c=a[1],d=b[1],e=bX(d,c),h=a[2],i=b[2];if(e)var
f=e;else
var
g=W(d,c),f=g?C.caml_greaterthan(i,h):g;return f}function
lB(c){if(W(c,q))return Fh;var
d=0,h=aQ(fo,ch(c));function
i(c,j){var
d=c[2],f=c[1];if(1===d)var
g=f;else
var
h=b(e[22],d),i=a(e[17],Fg,h),g=a(e[17],f,i);return[0,g,j]}var
j=g(f[21],i,h,d);return a(a9[7],Fi,j)}function
lC(g){var
c=g[2],f=g[1];if(W(c,q))return b(d[40],f);if(a(d[26],f,Fj))return lB(c);var
h=lB(c),i=a(e[17],Fk,h),j=b(d[40],f);return a(e[17],j,i)}function
Fl(h){if(W(h,q))return Fm;var
j=ch(h),k=aQ(function(o,n){var
i=n[1],j=o[1],h=W(j,i);if(h)return h;var
m=aQ(fo,ch(i)),b=aQ(fo,ch(j)),a=m;for(;;){if(a){if(b){var
c=a[1],d=b[1],k=a[2],l=b[2],e=fo(d,c);if(e)var
f=e;else{var
g=W(d,c);if(g){var
b=l,a=k;continue}var
f=g}return f}return 0}return 1}},j);function
l(g,f){var
c=f[2],h=f[1];if(a(d[27],c,Fo)){var
i=lC([0,b(d[3],c),h]),j=a(e[17],Fp,i);return a(e[17],g,j)}var
k=lC([0,c,h]),l=a(e[17],Fq,k);return a(e[17],g,l)}var
c=g(f[20],l,Fn,k),m=g(a9[4],c,0,3),i=g(a9[4],c,3,cn(c)-3|0),n=lX(m,Fs)?i:a(e[17],Fu,i),o=a(e[17],n,Fr);return a(e[17],Ft,o)}function
bJ(a){if(typeof
a==="number")return q;else
switch(a[0]){case
0:return cl(a[1]);case
1:return a0(a0(a[1],1),Fa);case
2:return dJ(bJ(a[1]));case
3:var
b=a[1],f=b[1],g=bJ(b[2]);return cm(bJ(f),g);case
4:var
c=a[1],h=c[1],i=bJ(c[2]);return hs(bJ(h),i);case
5:var
d=a[1],j=d[1],k=bJ(d[2]);return bI(bJ(j),k);default:var
e=a[1],l=e[2];return fm(bJ(e[1]),l)}}function
lD(b){var
c=P(1,b[1]);function
d(a){return bm(b,a)}var
g=20;function
h(a){return dH(g,a)}function
i(a){return aj(h,d,a)}var
j=a(f[17],i,c),k=a(a9[7],Fw,j);return a(e[17],k,Fv)}function
lE(b){var
c=a8(b),d=a(f[17],bl,c);return bk(function(c,b){function
d(b){return a(e[17],b[1],b[2])}function
f(a){return ac(c,b,a)}return function(a){return ak(f,d,a)}},d)}function
fp(a){function
b(a){return a[1][2]}function
c(a){return dG(hm,a)}function
d(a){return ci(c,a)}var
e=lE(a);function
f(a){return dG(hm,a)}function
g(a){return ci(f,a)}function
h(a){return ac(g,e,a)}function
i(a){return ac(h,d,a)}return function(a){return ak(i,b,a)}}function
lF(a){return dG(lu,a)}var
FI=d[43];function
FJ(a){return aj(FI,fd,a)}var
FK=1;function
FL(a){return fi(FK,lF,a)}function
lG(a){return ak(FL,FJ,a)}function
FM(c){var
e=e_(b(f[1],c)),g=fd(c),h=b(d[43],g);return a(d[9],h,e)}var
FN=1;function
FO(a){return fi(FN,lF,a)}function
FP(a){return ak(FO,FM,a)}function
FQ(c){var
b=c[2],e=c[1];if(b)if(!b[2])return a(d[1],e,b[1]);return e}function
FR(a){return a[2]}var
FT=bl(FS);function
FU(a){return ac(FT,FP,a)}function
FV(a){return ak(FU,FR,a)}function
FW(a){return hn(FV,a)}function
FX(a){return ac(lG,FW,a)}function
FY(a){return ak(FX,FQ,a)}function
lH(a){function
b(a){return a[2]}var
c=bl(FZ);function
e(b){return ac(c,a,b)}function
f(a){return ak(e,b,a)}function
g(b){return fh(f,a,b)}function
h(a){return a[2]}var
i=d[3];function
j(a){return aj(i,h,a)}var
k=bl(F0);function
l(b){return ac(k,a,b)}function
m(a){return ak(l,j,a)}return function(a){return fh(m,g,a)}}function
F1(a){return a[2]}var
F2=lH(lG),F4=bl(F3),F6=bl(F5);function
F7(a){return fh(F6,F4,a)}function
F8(a){return ac(F7,F2,a)}function
F9(a){return ak(F8,F1,a)}function
F_(c){var
b=c[2],e=c[1];if(b)if(!b[2]){var
f=a(d[14],F$,b[1]);return a(d[6],e,f)}return e}function
Ga(a){return hn(F9,a)}var
Gb=lH(FY);function
Gc(a){return ac(Gb,Ga,a)}function
lI(a){return ak(Gc,F_,a)}fp(Ge);fp(Gf);fp(Gg);function
Gh(a){return Gi}fp(Gj);lE(Gk);function
Gl(a){return a[1]}function
Gm(a){return aj(E5,Gl,a)}var
Go=bl(Gn),Gq=bl(Gp);function
Gr(a){return ac(Gq,Go,a)}function
Gs(a){return ac(Gr,Gh,a)}function
Gt(a){return[0,a[1],a[2]]}function
Gu(a){return a[2]}var
Gw=bl(Gv);function
Gx(a){return ac(Gw,lI,a)}function
Gy(a){return ak(Gx,Gu,a)}function
Gz(a){return ci(Gy,a)}function
GA(a){return ac(lI,Gz,a)}function
GB(a){return ak(GA,Gt,a)}function
GC(a){return ac(GB,Gs,a)}function
hu(d){var
a=ak(GC,Gm,a8(d)),c=a[1];return 0===a[2]?c:b(e[3],Gd)}function
lJ(b,a){return B(function(b,c,a){return fb(e$(a),b)},a,b)}function
lK(e,c){return B(function(e,g,c){var
f=b(d[15],c);return a(d[38],e,f)},c,e)}function
lL(c){function
e(g){var
e=a(d[6],c,g),f=b(d[23],e);return a(d[9],f,c)}return function(a){return hr(e,a)}}function
lN(o,n){function
W(a){return[0,1,a]}var
X=[0,[0,1,n],a(f[17],W,o)];function
Y(b){function
c(a){return-a|0}var
d=a(f[17],c,b);return a(e[26],d,b)}var
Z=a(f[17],Y,X),l=b(f[1],o)+1|0,p=2*(b(f[1],n)+1|0)|0,h=(p+l|0)-1|0,_=dI([0,1,l],function(a){return F([0,p+a|0,a+1|0],GR)},q),$=cN(1,Z,function(b,a){function
c(c,b){return F([0,b,a],[0,c])}var
d=1;return function(a){return cN(d,b,c,a)}},_),U=P(1,l);function
V(f){var
a=B(function(c,a,d){var
e=a[1];return a[2]===f?b(F(e,d),c):c},q,$);return[0,[0,h,h],B(function(d,a,c){return b(F([0,a,a],c),d)},q,a)]}var
i=a(f[17],V,U);if(a(d[26],lM,E3))var
m=fk(h);else
var
r=P(1,h),s=function(a){return F(a,lM)},m=[0,h,g(f[21],s,r,q)];var
c=g(bC[14],0,GE,GD),M=g(a9[4],c,0,cn(c)-6|0),j=a(e[17],M,GF),N=a(bC[4],cj,GG),t=b(f[1],i)-1|0,u=b(f[5],i)[1][1],v=P(1,b(f[1],i));function
w(q,p,o){var
c=b(e[22],q-1|0),h=a(e[17],c,Fx),d=0,i=p[2],j=dF(function(b,e,a){var
c=b[2],d=b[1];return c<d?a:[0,[0,[0,d,c],e],a]},i,d);function
k(a){return a[1]}var
l=aQ(function(a,b){return dE(k,a,b)},j);function
m(c,f){var
d=c[1],g=c[2],i=d[2],j=d[1],k=a(e[17],Fz,f),l=dH(20,g),m=a(e[17],l,k),n=a(e[17],FA,m),o=b(e[22],i),p=a(e[17],o,n),q=a(e[17],FB,p),r=b(e[22],j),s=a(e[17],r,q);return a(e[17],h,s)}var
n=g(f[21],m,l,Fy);return a(e[17],n,o)}var
x=D(f[26],w,v,i,FC),y=lD(m),z=a(e[17],y,x),A=a(e[17],FD,z),C=b(e[22],u),E=a(e[17],C,A),G=a(e[17],FE,E),H=a(e[17],FF,G),I=b(e[22],t),J=a(e[17],I,H),K=a(e[17],FG,J),L=a(e[17],GH,K);ck(c,a(e[17],FH,L));ck(N,hv);var
O=a(e[17],j,GL),Q=a(e[17],GI,O),R=a(e[17],c,Q),S=a(e[17],GJ,R),T=a(e[17],cj,S),k=hC(a(e[17],GK,T));hu(fj(j));cP(c);cP(j);if(1!==k)if(2!==k)return 0===k?1:b(e[3],GQ);return 0}function
lO(b){if(b){var
c=b[2],d=b[1];return lN(c,d)?c:a(e[26],c,[0,d,0])}throw[0,aV,GS]}function
GT(b,a){return hg(3,lO,[0,b,a])}function
hw(b,c){return a(d[26],b,GU)?0:aH(function(c){return a(d[6],b,c)},c)}function
dK(c,b){function
e(b){return a(d[26],b,GV)}return aI(d[1],e,c,b)}function
lP(e,c){return B(function(h,g,f){var
c=b(ff(e),g),i=a(d[6],c,f);return a(d[1],h,i)},GW,c)}function
lQ(k){return function(u){var
i=q,g=u;for(;;){if(g){var
m=g[2],c=g[1];if(aq(c)){var
g=m;continue}var
j=hk(c)[1];if(W(j,k))var
l=b(hl(j),c),h=aq(l)?b(e[3],GX):hk(l)[1];else
var
h=j;var
n=b(ff(c),h),p=b(hl(h),c),r=hw(a(d[9],GY,n),p),o=function(g,h,i){return function(c){var
e=a_(c,h,GZ);if(a(d[26],e,G0))return c;var
f=b(d[3],e);return dK(c,hw(a(d[9],f,i),g))}}(c,h,n),s=a(f[17],o,m),t=aH(o,i),i=b(F(h,r),t),g=s;continue}var
v=0;return[0,cL(B(function(c,f,b){var
d=hj(fg(b),[0,k,0]);return a(e[26],d,c)},v,i)),i]}}}function
hx(c){var
g=c[1],f=g[1];if(g[2]!==f)return b(e[3],G2);function
i(l,g){var
c=l;for(;;){if(lv(g))return 0;var
h=bm(g,[0,c,c]);if(a(d[27],h,G3))return b(e[3],G4);if(a(d[26],h,G5)){if(lv(ly(c,g))){var
c=c+1|0;continue}return b(e[3],G6)}var
j=ly(c,g),k=hr(function(b){return a(d[9],b,h)},j);return[0,[0,h,k],i(c+1|0,[0,[0,f,f],dI([0,c+1|0,f],function(b){function
e(c){var
e=bm(k,c),f=bm(j,b),h=a(d[6],f,e),i=bm(g,[0,b,c]),l=a(d[4],i,h),m=[0,b,c];return function(a){return cO(m,l,a)}}var
h=[0,c+1|0,f];return function(a){return dI(h,e,a)}},q)])]}}return i(1,c)}function
lR(b){if(0===b)return[0,G7,b];function
h(e){var
b=e[2],f=e[1],g=b[2],h=B(function(b,c,a){return fa(b,hf(a))},G8,g),i=b[2],j=B(function(b,c,a){return fb(b,e$(a))},G9,i),c=a(d[9],j,h),k=hr(function(b){return a(d[6],c,b)},b),l=a(d[6],c,c);return[0,a(d[9],f,l),k]}var
c=a(f[17],h,b);function
i(a){return a[1]}function
j(a){return aj(hf,i,a)}function
k(a){return aj(fa,j,a)}var
l=g(f[21],k,c,G_);function
m(a){return a[1]}function
n(a){return aj(e$,m,a)}function
o(a){return aj(fb,n,a)}var
p=g(f[21],o,c,G$),e=a(d[9],p,l);function
q(b){var
c=b[2];return[0,a(d[6],e,b[1]),c]}var
r=a(f[17],q,c);return[0,a(d[9],Ha,e),r]}function
hy(c,d){if(0<=c){if(0===c)return[0,q,0];if(0===d)return[0,q,0];var
g=P(0,c),h=function(e){var
g=hy(c-e|0,b(f[6],d));function
h(a){return 0===e?a:b(F(b(f[5],d),e),a)}return a(f[17],h,g)},i=a(f[17],h,g);return bk(e[26],i)}return 0}function
hz(b,j){var
c=j;for(;;){if(0===b)return[0,[0,cl(bj),[5,bj]],0];if(0<=b){if(c){var
d=c[2],g=c[1],h=g[1],k=g[2],i=fn(h);if(0===i){var
c=d;continue}var
l=hz(b-i|0,d),m=function(a){var
b=[10,k,a[2]];return[0,bI(h,a[1]),b]},n=a(f[17],m,l),o=hz(b,d);return a(e[26],o,n)}return[0,[0,cl(bj),[5,bj]],0]}return 0}}function
lS(d,c,a){return B(function(a,e,d){return B(function(a,g,f){var
c=fl(e,g),h=a_(a,c,q);return b(F(c,dK(hw(d,f),h)),a)},a,c)},a,d)}function
HA(b){return a(d[26],b,HB)}var
HC=d[1];function
lT(b,c){return a(d[26],b,HD)?q:aH(function(c){return a(d[6],b,c)},c)}function
HF(aC,m,k,s,r){var
aD=0;function
aE(a){return a[1]}var
aF=a(f[17],aE,s),aG=a(e[26],[0,r,k],aF);function
aJ(a){return aj(hi,ht,a)}var
y=g(f[21],aJ,aG,aD);if(aC)var
aK=function(a){return fn(a[1])<=m?1:0},aL=a(f[35],aK,s),h=[0,[0,cl(bj),[5,bj]],aL];else
var
h=hz(m,s);var
aM=b(f[1],h);function
aN(e,d){var
c=hy(m-fn(d)|0,y),h=P(1,b(f[1],c)),i=a(f[47],c,h);function
j(a){var
b=a[2],c=a[1];return F(c,a0([0,-e|0,-b|0,b],HG))}return[0,c,g(f[21],j,i,q)]}function
aO(h,e){var
c=hy((m-fn(e[1])|0)/2|0,y),i=P(1,b(f[1],c)),d=a(f[47],c,i);function
j(e){var
c=e[2],g=e[1];function
i(e,a){var
d=e[2],f=fl(g,e[1]);if(d<c)return a;var
i=c===d?HH:HI,j=a_(a,f,q);return b(F(f,dK(a0([0,h,c,d],i),j)),a)}return a(f[21],i,d)}return[0,c,g(f[21],j,d,q)]}var
aP=P(1,b(f[1],h)),aR=g(f[23],aO,aP,h),z=b(f[46],aR),A=z[1],aS=z[2],aT=P(1,b(f[1],k)),aU=g(f[23],aN,aT,k),C=b(f[46],aU)[2],t=a(f[17],f[1],A),aV=dJ(r),Z=B(function(e,c,a){return b(F(c,a0(Hb,b(d[3],a))),e)},q,aV);function
aW(c,b,a){return lS(c[1],b,a)}var
aX=D(f[26],aW,h,aS,Z);function
aY(c,b,a){return lS(c,b,a)}var
aZ=D(f[26],aY,k,C,aX),a1=0,a2=B(function(b,c,a){return[0,a,b]},a1,aZ),E=b(lQ(HJ),a2),c=E[1],a3=E[2],a4=[0,HK,c];function
a5(a){return F(a,a0(a,HL))}var
u=g(f[21],a5,c,a3);function
a6(j){return B(function(e,c,k){var
h=c[3],i=c[2],f=c[1];if(0<=f){var
g=a_(k,j,HM);if(a(d[26],g,HN))return e;var
l=b(F([0,f,i,h],g),e);return b(F([0,f,h,i],g),l)}return e},q,u)}var
a7=B(function(b,a,c){var
d=a[3],e=a[2];if(0<a[1])if(e===d)return dK(c,b);return b},q,u),n=a(f[17],a6,a4),a8=cN(1,c,function(b,a){var
c=a_(a7,b,HO);return function(b){return cO(a,c,b)}},q),G=[0,b(f[1],c),a8];if(0===c)var
H=fk(0);else{var
N=g(f[21],lJ,n,GM),O=lJ(G[2],GN),Q=function(b){return a(d[6],N,b)},R=function(a){return aH(Q,a)},w=a(f[17],R,n),x=lw(O,G),S=g(f[21],lK,w,GO),T=lK(x[2],GP),U=dD(20-(Math.log(b(d[56],S))/mM|0)|0),V=dD(20-(Math.log(b(d[56],T))/mM|0)|0),W=function(b){return a(d[6],b,U)},X=function(a){return aH(W,a)},o=a(f[17],X,w),Y=lw(V,x),i=g(bC[14],0,Hq,Hp),as=g(a9[4],i,0,cn(i)-6|0),p=a(e[17],as,Hr),at=a(bC[4],cj,Hs),_=b(f[1],o)-1|0,$=P(1,b(f[1],o)),aa=function(p,o,n){var
c=b(e[22],p-1|0),h=a(e[17],c,Hc),d=0,i=B(function(b,a,e){var
c=a[3],d=a[2],f=a[1];return c<d?b:[0,[0,[0,f,d,c],e],b]},d,o);function
j(a){return a[1]}var
k=aQ(function(a,b){return dE(j,a,b)},i);function
l(d,f){var
c=d[1],g=d[2],i=c[3],j=c[2],k=c[1],l=a(e[17],He,f),m=dH(20,g),n=a(e[17],m,l),o=a(e[17],Hf,n),p=b(e[22],i),q=a(e[17],p,o),r=a(e[17],Hg,q),s=b(e[22],j),t=a(e[17],s,r),u=a(e[17],Hh,t),v=b(e[22],k),w=a(e[17],v,u);return a(e[17],h,w)}var
m=g(f[21],l,k,Hd);return a(e[17],m,n)},ab=D(f[26],aa,$,o,Hi),ac=lD(Y),ad=a(e[17],ac,ab),ae=a(e[17],Hj,ad),af=a(f[17],e[22],t),ag=a(a9[7],Hk,af),ah=a(e[17],ag,ae),ai=a(e[17],Hl,ah),ak=b(e[22],aM),al=a(e[17],ak,ai),am=a(e[17],Hm,al),an=b(e[22],_),ao=a(e[17],an,am),ap=a(e[17],Hn,ao),ar=a(e[17],Ht,ap);ck(i,a(e[17],Ho,ar));ck(at,hv);var
au=a(e[17],p,Hx),av=a(e[17],Hu,au),aw=a(e[17],i,av),ax=a(e[17],Hv,aw),ay=a(e[17],cj,ax),j=hC(a(e[17],Hw,ay)),az=hu(fj(p));cP(i);cP(p);if(1===j)var
l=0;else
if(2===j)var
l=0;else
if(3===j)var
l=1;else
if(0===j)var
l=1;else{var
aA=b(e[22],j),aB=a(e[17],Hz,aA);b(e[3],aB);var
l=1}if(!l)b(e[3],Hy);var
H=az}function
I(i){var
c=b(lL(i),H),l=lT(HE,a(f[7],n,0));function
j(b,d){var
e=a(f[7],n,b);return aI(HC,HA,lT(bm(c,b),e),d)}var
k=dI([0,1,c[1]],j,l),d=P(1,b(f[1],t)),e=a(f[47],t,d);function
g(a){var
c=a[1],d=a[2];return[0,[0,c,c],B(function(c,a,e){var
f=a[3],g=a[2];return a[1]===d?b(F([0,g,f],e),c):c},q,k)]}var
h=a(f[17],g,e);return[0,c,a(f[17],hx,h)]}if(0===c)var
v=I(bj);else
var
br=P(5,66),bs=a(f[17],dD,br),bt=P(1,31),bu=a(f[17],d[47],bt),v=hh(I,a(e[26],bu,bs));var
J=v[1],a$=v[2],ba=a0(HQ,HP),bb=P(1,J[1]);function
bc(b){var
d=bm(J,b);return F(a(f[7],c,b-1|0),d)}var
K=g(f[21],bc,bb,ba),bd=B(function(d,c,a){return b(F(c,lP(K,a)),d)},K,u);function
be(a){return B(function(c,b,a){return cO(b,lP(bd,a),c)},q,a)}function
bf(c){function
d(d){var
e=d[2],h=d[1],i=P(1,b(f[1],c));function
j(b,d){var
g=bm(e,b);return cO(a(f[7],c,b-1|0),g,d)}return[0,h,g(f[21],j,i,q)]}return b(f[17],d)}var
bg=g(f[23],bf,A,a$),L=a(f[17],be,C);function
bh(b,a){return[0,b,a]}var
bi=g(f[23],bh,h,bg);function
bk(a){return 0!==a[2]?1:0}var
M=a(f[35],bk,bi),bl=dJ(r);function
bn(b,a){var
c=bI(b,a);return function(a){return cm(c,a)}}var
bo=D(f[26],bn,L,k,bl);function
bp(a){var
c=a[2],d=a[1][1];function
b(a){var
b=a[2],c=a[1],d=lA(c,bI(b,b));return function(a){return cm(d,a)}}var
e=bI(d,g(f[21],b,c,q));return function(a){return cm(e,a)}}if(aq(g(f[21],bp,M,bo))){var
bq=function(a){return[0,a[1][2],a[2]]};return[0,L,a(f[17],bq,M)]}throw hp}function
hA(a){var
b=ch(a);function
c(a){return a[1]}return aQ(function(a,b){return dE(c,a,b)},b)}function
lU(a){if(W(a,q))return[0,bj];var
b=hA(a),c=0;function
d(a,d){var
b=a[2],c=a[1],e=1===b?[1,c]:[6,[0,[1,c],b]];return[0,e,d]}var
e=g(f[21],d,b,c);return bk(function(b,a){return[5,[0,b,a]]},e)}function
HR(e){var
b=e[2],c=e[1];return W(c,q)?[0,b]:a(d[26],b,bj)?lU(c):[5,[0,[0,b],lU(c)]]}function
lV(b){if(W(b,q))return 0;var
c=ch(b),d=aQ(function(C,B){var
o=B[1],p=C[1];if(W(o,q))return 1;if(W(p,q))return 0;var
k=hA(p),l=hA(o),t=0;function
u(a){return a[2]}function
v(b,a){return b+a|0}function
w(a){return aj(v,u,a)}var
m=g(f[21],w,k,t),x=0;function
y(a){return a[2]}function
z(b,a){return b+a|0}function
A(a){return aj(z,y,a)}var
n=g(f[21],A,l,x);if(m<n)return 0;if(n<m)return 1;var
b=k,a=l;for(;;){if(b){if(a){var
c=a[1],d=c[2],e=c[1],h=b[1],i=h[2],j=h[1],r=a[2],s=b[2];if(bX(j,e))return 1;if(bX(e,j))return 0;if(bX(i,d))return 0;if(bX(d,i))return 1;var
b=s,a=r;continue}return 0}return a?1:1}},c),e=a(f[17],HR,d);return bk(function(b,a){return[3,[0,b,a]]},e)}function
HS(a){var
b=a[1];return[10,[5,b],[6,lV(a[2])]]}function
HT(b){var
c=b[2],d=b[1];if(0===c)return d;var
e=a(f[17],HS,c);return[10,d,bk(function(b,a){return[9,b,a]},e)]}function
lW(b){if(0===b)return HU;var
c=0;function
d(c,d){var
g=lW(hj(b,[0,c,0]));function
h(a){return[0,c,a]}var
i=a(f[17],h,g);return a(e[26],i,d)}return g(f[21],d,b,c)}function
hB(d,c){return B(function(g,e,c){return b(F(a(f[38],e,d),c),g)},q,c)}aA(1050,[0,E$,dJ,bI,fm,cl,bJ,lV,HT,Fl,HF,function(c){var
n=ht(c),o=ht(c),K=fg(c);function
L(b){function
c(a){return lz(a,b)}return a(f[17],c,o)}var
u=a(f[17],L,K);function
M(f){var
b=0;return(B(function(c,b,g){var
d=lz(f,b);return a(e[6],d,c)},b,c)+1|0)/2|0}var
N=a(f[17],M,o);function
O(a){var
b=P(0,a);function
c(b,a){return[0,b,a]}return function(a){return fc(c,b,a)}}var
Q=g(f[21],O,N,G1),H=[0,b(f[5],u),0],I=b(f[6],u),t=g(f[21],GT,I,H),J=hg(b(f[1],t),lO,t);function
R(b){function
c(a){return 2*a|0}return lN(J,a(f[17],c,b))}var
S=a(f[35],R,Q),T=b(f[9],S);function
U(a){function
c(d,c,a){return 0===c?a:b(F(d,c),a)}return D(f[26],c,o,a,q)}var
i=a(f[17],U,T),r=b(f[1],i),aD=lW(n);function
aE(d){var
e=a(f[47],n,d);return aq(hs(c,B(function(d,c,a){return b(F(hB(e,c),a),d)},q,c)))}var
aF=a(f[35],aE,aD),aG=P(1,b(f[1],i)),v=a(f[47],i,aG),aJ=fc(function(b,a){return[0,[0,b[1],a[1]],[0,b[2],a[2]]]},v,v);function
aK(b){var
a=b[2];return a[1]<=a[2]?1:0}var
aL=a(f[35],aK,aJ);function
aM(b){var
c=b[2],d=b[1],e=c[2],g=c[1],h=d[2],i=d[1];function
j(b){var
c=hB(a(f[47],n,b),h);return[0,[0,hB(a(f[47],n,b),i),c],[0,g,e]]}return a(f[17],j,aF)}var
aN=a(f[17],aM,aL),w=bk(e[26],aN);function
aO(a){return a[1]}var
aP=cL(a(f[17],aO,w));function
aR(b){function
c(a){return W(a[1],b)}return a(f[35],c,w)}var
aS=a(f[17],aR,aP);function
aT(a){return a[2]}var
aU=b(f[17],aT);function
aV(a){return aj(cL,aU,a)}var
aW=a(f[17],aV,aS);function
aX(c,d){if(c){var
g=c[2],h=c[1];if(g){var
i=function(a){var
c=a0(h,Ih);return b(F(a,Ii),c)},j=a(f[17],i,g);return a(e[26],j,d)}return d}throw hp}var
aY=g(f[21],aX,aW,0),aZ=B(function(d,c,a){return b(F(c,a0(Ij,a)),d)},q,c),a1=cN(1,i,function(f,a){function
c(g,d,c){var
e=fl(f,g);if(d<a)return c;var
h=a===d?Ik:Il,i=a_(c,e,q);return b(F(e,b(F([0,a,d],h),i)),c)}var
d=1;return function(a){return cN(d,i,c,a)}},aZ),a2=0,a3=B(function(b,c,a){return[0,a,b]},a2,a1),a4=a(e[26],a3,aY),x=b(lQ(Im),a4),j=x[1],a5=x[2];function
a6(a){return F(a,a0(a,In))}var
y=g(f[21],a6,j,a5),a7=[0,Io,j],a8=P(1,r);function
a$(a){return b(ff(y),[0,a,a])}var
ba=bk(dK,a(f[17],a$,a8));function
bb(i){return[0,[0,r,r],B(function(f,e,j){var
g=e[2],h=e[1],c=a_(j,i,Ip);if(a(d[26],c,Iq))return f;var
k=b(F([0,h,g],c),f);return b(F([0,g,h],c),k)},q,y)]}var
h=a(f[17],bb,a7),bc=cN(1,j,function(b,a){var
c=a_(ba,b,Ir);return function(b){return cO(a,c,b)}},q),z=[0,b(f[1],j),bc];if(0===j)var
A=fk(0);else{var
k=g(bC[14],0,H9,H8),at=g(a9[4],k,0,cn(k)-6|0),p=a(e[17],at,H_),au=a(bC[4],cj,H$),ac=b(f[1],h)-1|0,ad=b(f[5],h)[1][1],ae=P(1,b(f[1],h)),af=function(q,p,o){var
c=b(e[22],q-1|0),h=a(e[17],c,HX),d=0,i=p[2],j=dF(function(b,e,a){var
c=b[2],d=b[1];return c<d?a:[0,[0,[0,d,c],e],a]},i,d);function
k(a){return a[1]}var
l=aQ(function(a,b){return dE(k,a,b)},j);function
m(c,f){var
d=c[1],g=c[2],i=d[2],j=d[1],k=a(e[17],HZ,f),l=dH(20,g),m=a(e[17],l,k),n=a(e[17],H0,m),o=b(e[22],i),p=a(e[17],o,n),q=a(e[17],H1,p),r=b(e[22],j),s=a(e[17],r,q);return a(e[17],h,s)}var
n=g(f[21],m,l,HY);return a(e[17],n,o)},ag=D(f[26],af,ae,h,H2),V=P(1,z[1]),X=function(a){return bm(z,a)},Y=20,Z=function(a){return dH(Y,a)},_=function(a){return aj(Z,X,a)},$=a(f[17],_,V),aa=a(a9[7],HW,$),ab=a(e[17],aa,HV),ah=a(e[17],ab,ag),ai=a(e[17],H3,ah),ak=b(e[22],ad),al=a(e[17],ak,ai),am=a(e[17],H4,al),an=a(e[17],H5,am),ao=b(e[22],ac),ap=a(e[17],ao,an),ar=a(e[17],H6,ap),as=a(e[17],Ia,ar);ck(k,a(e[17],H7,as));ck(au,hv);var
av=a(e[17],p,Ie),aw=a(e[17],Ib,av),ax=a(e[17],k,aw),ay=a(e[17],Ic,ax),az=a(e[17],cj,ay),l=hC(a(e[17],Id,az)),aA=hu(fj(p));cP(k);cP(p);if(1===l)var
m=0;else
if(2===l)var
m=0;else
if(3===l)var
m=1;else
if(0===l)var
m=1;else{var
aB=b(e[22],l),aC=a(e[17],Ig,aB);b(e[3],aC);var
m=1}if(!m)b(e[3],If);var
A=aA}function
bd(c){var
l=b(lL(c),A),g=lx(a(f[7],h,0));function
i(n,m){var
o=a(f[7],h,n),p=bm(l,n),g=o[1],i=g[2],j=g[1];if(a(d[26],p,E6))var
c=[0,[0,j,i],q];else
var
r=o[2],c=[0,[0,j,i],aH(function(b){return a(d[6],p,b)},r)];var
k=c[1];if(C.caml_notequal(k,m[1]))return b(e[3],E7);var
s=m[2],t=c[2];function
u(b){return a(d[26],b,E8)}return[0,k,aI(d[1],u,t,s)]}return lR(hx(dI([0,1,l[1]],i,g)))}if(0===j)var
s=lR(hx(lx(a(f[7],h,0))));else
var
bh=P(5,66),bi=a(f[17],dD,bh),bj=P(1,31),bl=a(f[17],d[47],bj),s=hh(bd,a(e[26],bl,bi));var
E=s[1],be=s[2];function
bf(c){var
d=c[1],e=c[2][2];return[0,d,B(function(e,d,c){return b(F(a(f[7],i,d-1|0),c),e)},q,e)]}var
G=a(f[17],bf,be);function
bg(a){var
b=a[1],c=fm(a[2],2);return bI(cl(b),c)}if(aq(hs(lA(E,bk(cm,a(f[17],bg,G))),c)))return[0,E,G];throw hp}],"Micromega_plugin__Sos");return}
