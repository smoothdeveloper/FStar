open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> normalize [] e t
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> FStar_TypeChecker_Normalize.unfold_whnf e t
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun e ->
    fun t ->
      FStar_Syntax_Print.term_to_string' e.FStar_TypeChecker_Env.dsenv t
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu____58 =
      let uu____59 = FStar_Tactics_Types.goal_env g in
      let uu____60 = FStar_Tactics_Types.goal_type g in
      bnorm uu____59 uu____60 in
    FStar_Tactics_Types.goal_with_type g uu____58
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu____76 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____76
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu____92 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____92
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu____113 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____113
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu____124 =
       let uu____125 = FStar_Options.silent () in Prims.op_Negation uu____125 in
     if uu____124 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____133 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu____139 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu____139)
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps ->
         let psc = ps.FStar_Tactics_Types.psc in
         let subst = FStar_TypeChecker_Cfg.psc_subst psc in
         (let uu____157 = FStar_Tactics_Types.subst_proof_state subst ps in
          FStar_Tactics_Printing.do_dump_proofstate uu____157 msg);
         FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuuu164 .
    Prims.string -> Prims.string -> 'uuuuuu164 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      let uu____177 = FStar_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu____177
let fail2 :
  'uuuuuu186 .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuuu186 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu____204 = FStar_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu____204
let fail3 :
  'uuuuuu215 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuuu215 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu____238 = FStar_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu____238
let fail4 :
  'uuuuuu251 .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuuu251 FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu____279 = FStar_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu____279
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____297 = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu____297 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu____307::(e1, FStar_Pervasives_Native.None)::(e2,
                                                         FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l, uu____367::uu____368::(e1, uu____370)::(e2, uu____372)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq3_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____449 ->
        let uu____452 = FStar_Syntax_Util.unb2t typ in
        (match uu____452 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu____466 = FStar_Syntax_Util.head_and_args t in
             (match uu____466 with
              | (hd, args) ->
                  let uu____515 =
                    let uu____530 =
                      let uu____531 = FStar_Syntax_Subst.compress hd in
                      uu____531.FStar_Syntax_Syntax.n in
                    (uu____530, args) in
                  (match uu____515 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu____551, FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____552))::(e1,
                                                                   FStar_Pervasives_Native.None)::
                      (e2, FStar_Pervasives_Native.None)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu____619 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu____655 = destruct_eq' typ in
    match uu____655 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None ->
        let uu____685 = FStar_Syntax_Util.un_squash typ in
        (match uu____685 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (guard_is_trivial : FStar_TypeChecker_Common.guard_t -> Prims.bool) =
  fun g ->
    match g.FStar_TypeChecker_Common.guard_f with
    | FStar_TypeChecker_Common.Trivial -> true
    | uu____712 -> false
let (__do_unify :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
            FStar_Tactics_Monad.tac)
  =
  fun smt_ok ->
    fun env1 ->
      fun t1 ->
        fun t2 ->
          try
            (fun uu___118_749 ->
               match () with
               | () ->
                   ((let uu____755 =
                       FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TacUnify") in
                     if uu____755
                     then
                       let uu____756 = FStar_Util.string_of_bool smt_ok in
                       let uu____757 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____758 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print3
                         "%%%%%%%%do_unify (smt_ok=%s) %s =? %s\n" uu____756
                         uu____757 uu____758
                     else ());
                    (let res =
                       FStar_TypeChecker_Rel.try_teq smt_ok env1 t1 t2 in
                     (let uu____764 =
                        FStar_TypeChecker_Env.debug env1
                          (FStar_Options.Other "TacUnify") in
                      if uu____764
                      then
                        let uu____765 = FStar_Util.string_of_bool smt_ok in
                        let uu____766 =
                          FStar_Common.string_of_option
                            (FStar_TypeChecker_Rel.guard_to_string env1) res in
                        let uu____767 = FStar_Syntax_Print.term_to_string t1 in
                        let uu____768 = FStar_Syntax_Print.term_to_string t2 in
                        FStar_Util.print4
                          "%%%%%%%%do_unify (smt_ok=%s) (RESULT %s) %s =? %s\n"
                          uu____765 uu____766 uu____767 uu____768
                      else ());
                     FStar_Tactics_Monad.ret res))) ()
          with
          | FStar_Errors.Err (uu____780, msg) ->
              FStar_Tactics_Monad.mlog
                (fun uu____785 ->
                   FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
                (fun uu____787 ->
                   FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
          | FStar_Errors.Error (uu____790, msg, r) ->
              FStar_Tactics_Monad.mlog
                (fun uu____797 ->
                   let uu____798 = FStar_Range.string_of_range r in
                   FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                     uu____798)
                (fun uu____800 ->
                   FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
let (do_unify' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
            FStar_Tactics_Monad.tac)
  =
  fun smt_ok ->
    fun env1 ->
      fun t1 ->
        fun t2 ->
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
            (fun uu____836 ->
               (let uu____838 =
                  FStar_TypeChecker_Env.debug env1
                    (FStar_Options.Other "TacUnify") in
                if uu____838
                then
                  (FStar_Options.push ();
                   (let uu____840 =
                      FStar_Options.set_options
                        "--debug_level Rel --debug_level RelCheck" in
                    ()))
                else ());
               (let uu____842 = __do_unify smt_ok env1 t1 t2 in
                FStar_Tactics_Monad.bind uu____842
                  (fun r ->
                     (let uu____857 =
                        FStar_TypeChecker_Env.debug env1
                          (FStar_Options.Other "TacUnify") in
                      if uu____857 then FStar_Options.pop () else ());
                     FStar_Tactics_Monad.ret r)))
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____880 = do_unify' false env1 t1 t2 in
        FStar_Tactics_Monad.bind uu____880
          (fun gopt ->
             let gopt1 =
               FStar_Util.bind_opt gopt
                 (fun g' ->
                    FStar_TypeChecker_Rel.discharge_guard'
                      FStar_Pervasives_Native.None env1 g' false) in
             match gopt1 with
             | FStar_Pervasives_Native.Some g ->
                 ((let uu____907 =
                     let uu____908 = guard_is_trivial g in
                     Prims.op_Negation uu____908 in
                   if uu____907
                   then
                     failwith
                       "INTERNAL ERROR: Tactics.Basic.do_unify: with smt_ok=false, guard should be trivial if any"
                   else ());
                  (let uu____910 =
                     FStar_Tactics_Monad.add_implicits
                       g.FStar_TypeChecker_Common.implicits in
                   FStar_Tactics_Monad.bind uu____910
                     (fun uu____914 -> FStar_Tactics_Monad.ret true)))
             | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (do_unify_with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
          FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____938 = do_unify' true env1 t1 t2 in
        FStar_Tactics_Monad.bind uu____938
          (fun r ->
             match r with
             | FStar_Pervasives_Native.Some g ->
                 let uu____958 =
                   FStar_Tactics_Monad.add_implicits
                     g.FStar_TypeChecker_Common.implicits in
                 FStar_Tactics_Monad.bind uu____958
                   (fun uu____964 ->
                      FStar_Tactics_Monad.ret
                        (FStar_Pervasives_Native.Some g))
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.ret FStar_Pervasives_Native.None)
let (do_match :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____988 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____988
          (fun tx ->
             let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
             let uu____1002 = do_unify env1 t1 t2 in
             FStar_Tactics_Monad.bind uu____1002
               (fun r ->
                  if r
                  then
                    let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
                    let uu____1015 =
                      let uu____1016 = FStar_Util.set_eq uvs1 uvs2 in
                      Prims.op_Negation uu____1016 in
                    (if uu____1015
                     then
                       (FStar_Syntax_Unionfind.rollback tx;
                        FStar_Tactics_Monad.ret false)
                     else FStar_Tactics_Monad.ret true)
                  else FStar_Tactics_Monad.ret false))
let (do_match_on_lhs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun t1 ->
      fun t2 ->
        let uu____1041 =
          FStar_Tactics_Monad.mk_tac
            (fun ps ->
               let tx = FStar_Syntax_Unionfind.new_transaction () in
               FStar_Tactics_Result.Success (tx, ps)) in
        FStar_Tactics_Monad.bind uu____1041
          (fun tx ->
             let uu____1051 = destruct_eq t1 in
             match uu____1051 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "do_match_on_lhs: not an eq"
             | FStar_Pervasives_Native.Some (lhs, uu____1065) ->
                 let uvs1 = FStar_Syntax_Free.uvars_uncached lhs in
                 let uu____1073 = do_unify env1 t1 t2 in
                 FStar_Tactics_Monad.bind uu____1073
                   (fun r ->
                      if r
                      then
                        let uvs2 = FStar_Syntax_Free.uvars_uncached lhs in
                        let uu____1086 =
                          let uu____1087 = FStar_Util.set_eq uvs1 uvs2 in
                          Prims.op_Negation uu____1087 in
                        (if uu____1086
                         then
                           (FStar_Syntax_Unionfind.rollback tx;
                            FStar_Tactics_Monad.ret false)
                         else FStar_Tactics_Monad.ret true)
                      else FStar_Tactics_Monad.ret false))
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1107 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu____1107 with
      | FStar_Pervasives_Native.Some uu____1112 ->
          let uu____1113 =
            let uu____1114 =
              FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Util.format1 "Goal %s is already solved" uu____1114 in
          FStar_Tactics_Monad.fail uu____1113
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           FStar_Tactics_Monad.ret ())
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1130 = FStar_Tactics_Types.goal_env goal in
      let uu____1131 = FStar_Tactics_Types.goal_witness goal in
      do_unify uu____1130 solution uu____1131
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu____1150 ->
           let uu____1151 =
             let uu____1152 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu____1152 in
           let uu____1153 = FStar_Syntax_Print.term_to_string solution in
           FStar_Util.print2 "solve %s := %s\n" uu____1151 uu____1153)
        (fun uu____1156 ->
           let uu____1157 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu____1157
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____1165 ->
                       FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu____1167 =
                     let uu____1168 =
                       let uu____1169 = FStar_Tactics_Types.goal_env goal in
                       tts uu____1169 solution in
                     let uu____1170 =
                       let uu____1171 = FStar_Tactics_Types.goal_env goal in
                       let uu____1172 = FStar_Tactics_Types.goal_witness goal in
                       tts uu____1171 uu____1172 in
                     let uu____1173 =
                       let uu____1174 = FStar_Tactics_Types.goal_env goal in
                       let uu____1175 = FStar_Tactics_Types.goal_type goal in
                       tts uu____1174 uu____1175 in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1168 uu____1170 uu____1173 in
                   FStar_Tactics_Monad.fail uu____1167)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu____1190 = set_solution goal solution in
      FStar_Tactics_Monad.bind uu____1190
        (fun uu____1194 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu____1196 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu____1203 = FStar_Syntax_Util.un_squash t1 in
    match uu____1203 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu____1214 =
          let uu____1215 = FStar_Syntax_Subst.compress t'1 in
          uu____1215.FStar_Syntax_Syntax.n in
        (match uu____1214 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1219 -> false)
    | uu____1220 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1230 = FStar_Syntax_Util.un_squash t in
    match uu____1230 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1240 =
          let uu____1241 = FStar_Syntax_Subst.compress t' in
          uu____1241.FStar_Syntax_Syntax.n in
        (match uu____1240 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1245 -> false)
    | uu____1246 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____1260 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu____1269 =
                   let uu____1270 = FStar_Tactics_Types.goal_type g in
                   uu____1270.FStar_Syntax_Syntax.pos in
                 let uu____1273 =
                   let uu____1278 =
                     let uu____1279 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1279 in
                   (FStar_Errors.Warning_TacAdmit, uu____1278) in
                 FStar_Errors.log_issue uu____1269 uu____1273);
                solve' g t)) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tadmit_t") uu____1260
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1294 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           let uu___244_1304 = ps in
           {
             FStar_Tactics_Types.main_context =
               (uu___244_1304.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (uu___244_1304.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___244_1304.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___244_1304.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___244_1304.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___244_1304.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___244_1304.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___244_1304.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___244_1304.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___244_1304.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___244_1304.FStar_Tactics_Types.local_state)
           } in
         let uu____1305 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu____1305
           (fun uu____1310 ->
              let uu____1311 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu____1311))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu____1318 ->
    let uu____1321 =
      let uu____1322 = FStar_Util.now_ms () in
      FStar_All.pipe_right uu____1322 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu____1321
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1365 ->
                let uu____1366 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1366)
             (fun uu____1369 ->
                let e1 =
                  let uu___253_1371 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___253_1371.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___253_1371.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___253_1371.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___253_1371.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___253_1371.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___253_1371.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___253_1371.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___253_1371.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___253_1371.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___253_1371.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___253_1371.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___253_1371.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___253_1371.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___253_1371.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___253_1371.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___253_1371.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___253_1371.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___253_1371.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___253_1371.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___253_1371.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___253_1371.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___253_1371.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___253_1371.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___253_1371.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___253_1371.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___253_1371.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___253_1371.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___253_1371.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___253_1371.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___253_1371.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___253_1371.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___253_1371.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___253_1371.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___253_1371.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___253_1371.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___253_1371.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___253_1371.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___253_1371.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___253_1371.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___253_1371.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___253_1371.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___253_1371.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___253_1371.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___253_1371.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___253_1371.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___253_1371.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___257_1382 ->
                     match () with
                     | () ->
                         let uu____1391 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t in
                         FStar_Tactics_Monad.ret uu____1391) ()
                with
                | FStar_Errors.Err (uu____1418, msg) ->
                    let uu____1420 = tts e1 t in
                    let uu____1421 =
                      let uu____1422 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1422
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1420 uu____1421 msg
                | FStar_Errors.Error (uu____1429, msg, uu____1431) ->
                    let uu____1432 = tts e1 t in
                    let uu____1433 =
                      let uu____1434 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1434
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1432 uu____1433 msg))
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1483 ->
                let uu____1484 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____1484)
             (fun uu____1487 ->
                let e1 =
                  let uu___274_1489 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___274_1489.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___274_1489.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___274_1489.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___274_1489.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___274_1489.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___274_1489.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___274_1489.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___274_1489.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___274_1489.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___274_1489.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___274_1489.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___274_1489.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___274_1489.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___274_1489.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___274_1489.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___274_1489.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___274_1489.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___274_1489.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___274_1489.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___274_1489.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___274_1489.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___274_1489.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___274_1489.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___274_1489.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___274_1489.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___274_1489.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___274_1489.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___274_1489.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___274_1489.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___274_1489.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___274_1489.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___274_1489.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___274_1489.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___274_1489.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___274_1489.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___274_1489.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___274_1489.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___274_1489.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___274_1489.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___274_1489.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___274_1489.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___274_1489.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___274_1489.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___274_1489.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___274_1489.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___274_1489.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___278_1503 ->
                     match () with
                     | () ->
                         let uu____1512 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t in
                         (match uu____1512 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu____1550, msg) ->
                    let uu____1552 = tts e1 t in
                    let uu____1553 =
                      let uu____1554 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1554
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1552 uu____1553 msg
                | FStar_Errors.Error (uu____1561, msg, uu____1563) ->
                    let uu____1564 = tts e1 t in
                    let uu____1565 =
                      let uu____1566 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_All.pipe_right uu____1566
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1564 uu____1565 msg))
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu____1615 ->
                let uu____1616 = FStar_Syntax_Print.term_to_string t in
                FStar_Util.print1 "Tac> __tc_lax(%s)\n" uu____1616)
             (fun uu____1620 ->
                let e1 =
                  let uu___299_1622 = e in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___299_1622.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___299_1622.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___299_1622.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___299_1622.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___299_1622.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___299_1622.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___299_1622.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___299_1622.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___299_1622.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___299_1622.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___299_1622.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___299_1622.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___299_1622.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___299_1622.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___299_1622.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___299_1622.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___299_1622.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___299_1622.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___299_1622.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___299_1622.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___299_1622.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___299_1622.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___299_1622.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___299_1622.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___299_1622.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___299_1622.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___299_1622.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___299_1622.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___299_1622.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___299_1622.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___299_1622.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___299_1622.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___299_1622.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___299_1622.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___299_1622.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___299_1622.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___299_1622.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___299_1622.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___299_1622.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___299_1622.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___299_1622.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___299_1622.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___299_1622.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___299_1622.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___299_1622.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___299_1622.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                let e2 =
                  let uu___302_1624 = e1 in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___302_1624.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___302_1624.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___302_1624.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___302_1624.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___302_1624.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___302_1624.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___302_1624.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___302_1624.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___302_1624.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___302_1624.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___302_1624.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___302_1624.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___302_1624.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___302_1624.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___302_1624.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___302_1624.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___302_1624.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (uu___302_1624.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___302_1624.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___302_1624.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___302_1624.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___302_1624.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___302_1624.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___302_1624.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___302_1624.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___302_1624.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___302_1624.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___302_1624.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___302_1624.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___302_1624.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___302_1624.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___302_1624.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___302_1624.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___302_1624.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___302_1624.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (uu___302_1624.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___302_1624.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___302_1624.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___302_1624.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___302_1624.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___302_1624.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___302_1624.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___302_1624.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___302_1624.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___302_1624.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (uu___302_1624.FStar_TypeChecker_Env.enable_defer_to_tac)
                  } in
                try
                  (fun uu___306_1635 ->
                     match () with
                     | () ->
                         let uu____1644 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t in
                         FStar_Tactics_Monad.ret uu____1644) ()
                with
                | FStar_Errors.Err (uu____1671, msg) ->
                    let uu____1673 = tts e2 t in
                    let uu____1674 =
                      let uu____1675 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1675
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1673 uu____1674 msg
                | FStar_Errors.Error (uu____1682, msg, uu____1684) ->
                    let uu____1685 = tts e2 t in
                    let uu____1686 =
                      let uu____1687 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_All.pipe_right uu____1687
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1685 uu____1686 msg))
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta] in
      let t1 = normalize steps e t in is_true t1
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu____1714 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           (let uu___327_1732 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___327_1732.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___327_1732.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___327_1732.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___327_1732.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___327_1732.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___327_1732.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___327_1732.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___327_1732.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___327_1732.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___327_1732.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___327_1732.FStar_Tactics_Types.local_state)
            }))
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu____1756 = get_guard_policy () in
      FStar_Tactics_Monad.bind uu____1756
        (fun old_pol ->
           let uu____1762 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu____1762
             (fun uu____1766 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu____1770 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu____1770
                       (fun uu____1774 -> FStar_Tactics_Monad.ret r))))
let (proc_guard :
  Prims.string ->
    env -> FStar_TypeChecker_Common.guard_t -> unit FStar_Tactics_Monad.tac)
  =
  fun reason ->
    fun e ->
      fun g ->
        FStar_Tactics_Monad.mlog
          (fun uu____1796 ->
             let uu____1797 = FStar_TypeChecker_Rel.guard_to_string e g in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____1797)
          (fun uu____1800 ->
             let uu____1801 =
               FStar_Tactics_Monad.add_implicits
                 g.FStar_TypeChecker_Common.implicits in
             FStar_Tactics_Monad.bind uu____1801
               (fun uu____1806 ->
                  let uu____1807 =
                    let uu____1808 = FStar_TypeChecker_Rel.simplify_guard e g in
                    uu____1808.FStar_TypeChecker_Common.guard_f in
                  match uu____1807 with
                  | FStar_TypeChecker_Common.Trivial ->
                      FStar_Tactics_Monad.ret ()
                  | FStar_TypeChecker_Common.NonTrivial f ->
                      let uu____1812 = istrivial e f in
                      if uu____1812
                      then FStar_Tactics_Monad.ret ()
                      else
                        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
                          (fun ps ->
                             match ps.FStar_Tactics_Types.guard_policy with
                             | FStar_Tactics_Types.Drop ->
                                 ((let uu____1822 =
                                     let uu____1827 =
                                       let uu____1828 =
                                         FStar_TypeChecker_Rel.guard_to_string
                                           e g in
                                       FStar_Util.format1
                                         "Tactics admitted guard <%s>\n\n"
                                         uu____1828 in
                                     (FStar_Errors.Warning_TacAdmit,
                                       uu____1827) in
                                   FStar_Errors.log_issue
                                     e.FStar_TypeChecker_Env.range uu____1822);
                                  FStar_Tactics_Monad.ret ())
                             | FStar_Tactics_Types.Goal ->
                                 FStar_Tactics_Monad.mlog
                                   (fun uu____1831 ->
                                      let uu____1832 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g in
                                      FStar_Util.print2
                                        "Making guard (%s:%s) into a goal\n"
                                        reason uu____1832)
                                   (fun uu____1835 ->
                                      let uu____1836 =
                                        FStar_Tactics_Monad.goal_of_guard
                                          reason e f in
                                      FStar_Tactics_Monad.bind uu____1836
                                        (fun g1 ->
                                           FStar_Tactics_Monad.push_goals
                                             [g1]))
                             | FStar_Tactics_Types.SMT ->
                                 FStar_Tactics_Monad.mlog
                                   (fun uu____1843 ->
                                      let uu____1844 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g in
                                      FStar_Util.print2
                                        "Sending guard (%s:%s) to SMT goal\n"
                                        reason uu____1844)
                                   (fun uu____1847 ->
                                      let uu____1848 =
                                        FStar_Tactics_Monad.goal_of_guard
                                          reason e f in
                                      FStar_Tactics_Monad.bind uu____1848
                                        (fun g1 ->
                                           FStar_Tactics_Monad.push_smt_goals
                                             [g1]))
                             | FStar_Tactics_Types.Force ->
                                 FStar_Tactics_Monad.mlog
                                   (fun uu____1855 ->
                                      let uu____1856 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g in
                                      FStar_Util.print2
                                        "Forcing guard (%s:%s)\n" reason
                                        uu____1856)
                                   (fun uu____1858 ->
                                      try
                                        (fun uu___359_1863 ->
                                           match () with
                                           | () ->
                                               let uu____1866 =
                                                 let uu____1867 =
                                                   let uu____1868 =
                                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                       e g in
                                                   FStar_All.pipe_left
                                                     FStar_TypeChecker_Env.is_trivial
                                                     uu____1868 in
                                                 Prims.op_Negation uu____1867 in
                                               if uu____1866
                                               then
                                                 FStar_Tactics_Monad.mlog
                                                   (fun uu____1873 ->
                                                      let uu____1874 =
                                                        FStar_TypeChecker_Rel.guard_to_string
                                                          e g in
                                                      FStar_Util.print1
                                                        "guard = %s\n"
                                                        uu____1874)
                                                   (fun uu____1876 ->
                                                      fail1
                                                        "Forcing the guard failed (%s)"
                                                        reason)
                                               else
                                                 FStar_Tactics_Monad.ret ())
                                          ()
                                      with
                                      | uu___358_1879 ->
                                          FStar_Tactics_Monad.mlog
                                            (fun uu____1884 ->
                                               let uu____1885 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   e g in
                                               FStar_Util.print1
                                                 "guard = %s\n" uu____1885)
                                            (fun uu____1887 ->
                                               fail1
                                                 "Forcing the guard failed (%s)"
                                                 reason)))))
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____1902 =
        let uu____1905 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu____1905
          (fun uu____1925 ->
             match uu____1925 with
             | (uu____1934, lc, uu____1936) ->
                 let uu____1937 =
                   let uu____1938 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_All.pipe_right uu____1938
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu____1937) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tcc") uu____1902
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Reflection_Data.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu____1965 =
        let uu____1970 = tcc e t in
        FStar_Tactics_Monad.bind uu____1970
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "tc") uu____1965
let (trivial : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____1993 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____1999 =
           let uu____2000 = FStar_Tactics_Types.goal_env goal in
           let uu____2001 = FStar_Tactics_Types.goal_type goal in
           istrivial uu____2000 uu____2001 in
         if uu____1999
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2005 =
              let uu____2006 = FStar_Tactics_Types.goal_env goal in
              let uu____2007 = FStar_Tactics_Types.goal_type goal in
              tts uu____2006 uu____2007 in
            fail1 "Not a trivial goal: %s" uu____2005))
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac ->
        'b FStar_Tactics_Monad.tac -> ('a * 'b) FStar_Tactics_Monad.tac
  =
  fun n ->
    fun l ->
      fun r ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun p ->
             let uu____2056 =
               try
                 (fun uu___410_2079 ->
                    match () with
                    | () ->
                        let uu____2090 =
                          let uu____2099 = FStar_BigInt.to_int_fs n in
                          FStar_List.splitAt uu____2099
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu____2090) ()
               with
               | uu___409_2109 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu____2056
               (fun uu____2145 ->
                  match uu____2145 with
                  | (lgs, rgs) ->
                      let lp =
                        let uu___392_2171 = p in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___392_2171.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (uu___392_2171.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___392_2171.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___392_2171.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___392_2171.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___392_2171.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___392_2171.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___392_2171.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___392_2171.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___392_2171.FStar_Tactics_Types.local_state)
                        } in
                      let uu____2172 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu____2172
                        (fun uu____2180 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       let uu___398_2196 = lp' in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___398_2196.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___398_2196.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___398_2196.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___398_2196.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___398_2196.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___398_2196.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___398_2196.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___398_2196.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___398_2196.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___398_2196.FStar_Tactics_Types.local_state)
                                       } in
                                     let uu____2197 =
                                       FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu____2197
                                       (fun uu____2205 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      let uu___404_2221 = rp' in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___404_2221.FStar_Tactics_Types.local_state)
                                                      } in
                                                    let uu____2222 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu____2222
                                                      (fun uu____2230 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu____2236 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu____2257 = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu____2257
      (fun uu____2270 ->
         match uu____2270 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu____2307::uu____2308 ->
             let uu____2311 =
               let uu____2320 = map tau in
               divide FStar_BigInt.one tau uu____2320 in
             FStar_Tactics_Monad.bind uu____2311
               (fun uu____2338 ->
                  match uu____2338 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu____2379 =
        FStar_Tactics_Monad.bind t1
          (fun uu____2384 ->
             let uu____2385 = map t2 in
             FStar_Tactics_Monad.bind uu____2385
               (fun uu____2393 -> FStar_Tactics_Monad.ret ())) in
      focus uu____2379
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu____2402 ->
    let uu____2405 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____2414 =
             let uu____2421 =
               let uu____2422 = FStar_Tactics_Types.goal_env goal in
               let uu____2423 = FStar_Tactics_Types.goal_type goal in
               whnf uu____2422 uu____2423 in
             FStar_Syntax_Util.arrow_one uu____2421 in
           match uu____2414 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____2432 =
                 let uu____2433 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu____2433 in
               if uu____2432
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2438 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.push_binders uu____2438 [b] in
                  let typ' = FStar_Syntax_Util.comp_result c in
                  let uu____2454 =
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' in
                  FStar_Tactics_Monad.bind uu____2454
                    (fun uu____2470 ->
                       match uu____2470 with
                       | (body, ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)) in
                           let uu____2494 = set_solution goal sol in
                           FStar_Tactics_Monad.bind uu____2494
                             (fun uu____2500 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu____2502 =
                                  let uu____2505 = bnorm_goal g in
                                  FStar_Tactics_Monad.replace_cur uu____2505 in
                                FStar_Tactics_Monad.bind uu____2502
                                  (fun uu____2507 ->
                                     FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu____2512 =
                 let uu____2513 = FStar_Tactics_Types.goal_env goal in
                 let uu____2514 = FStar_Tactics_Types.goal_type goal in
                 tts uu____2513 uu____2514 in
               fail1 "goal is not an arrow (%s)" uu____2512) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "intro") uu____2405
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu____2529 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2550 =
            let uu____2557 =
              let uu____2558 = FStar_Tactics_Types.goal_env goal in
              let uu____2559 = FStar_Tactics_Types.goal_type goal in
              whnf uu____2558 uu____2559 in
            FStar_Syntax_Util.arrow_one uu____2557 in
          match uu____2550 with
          | FStar_Pervasives_Native.Some (b, c) ->
              let uu____2572 =
                let uu____2573 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu____2573 in
              if uu____2572
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu____2586 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____2586 in
                 let bs =
                   let uu____2596 = FStar_Syntax_Syntax.mk_binder bv in
                   [uu____2596; b] in
                 let env' =
                   let uu____2622 = FStar_Tactics_Types.goal_env goal in
                   FStar_TypeChecker_Env.push_binders uu____2622 bs in
                 let uu____2623 =
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) in
                 FStar_Tactics_Monad.bind uu____2623
                   (fun uu____2648 ->
                      match uu____2648 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu____2662 =
                              FStar_Tactics_Types.goal_type goal in
                            let uu____2665 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____2662
                              FStar_Parser_Const.effect_Tot_lid uu____2665 []
                              FStar_Range.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu____2683 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu____2683 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu____2705 =
                                   let uu____2706 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu____2706.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1)) uu____2705 in
                               let uu____2719 = set_solution goal tm in
                               FStar_Tactics_Monad.bind uu____2719
                                 (fun uu____2728 ->
                                    let uu____2729 =
                                      let uu____2732 =
                                        bnorm_goal
                                          (let uu___475_2735 = goal in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___475_2735.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___475_2735.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___475_2735.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___475_2735.FStar_Tactics_Types.label)
                                           }) in
                                      FStar_Tactics_Monad.replace_cur
                                        uu____2732 in
                                    FStar_Tactics_Monad.bind uu____2729
                                      (fun uu____2742 ->
                                         let uu____2743 =
                                           let uu____2748 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu____2748, b) in
                                         FStar_Tactics_Monad.ret uu____2743)))))
          | FStar_Pervasives_Native.None ->
              let uu____2757 =
                let uu____2758 = FStar_Tactics_Types.goal_env goal in
                let uu____2759 = FStar_Tactics_Types.goal_type goal in
                tts uu____2758 uu____2759 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2757))
let (norm :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____2781 ->
              let uu____2782 =
                let uu____2783 = FStar_Tactics_Types.goal_witness goal in
                FStar_Syntax_Print.term_to_string uu____2783 in
              FStar_Util.print1 "norm: witness = %s\n" uu____2782)
           (fun uu____2788 ->
              let steps =
                let uu____2792 = FStar_TypeChecker_Normalize.tr_norm_steps s in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____2792 in
              let t =
                let uu____2796 = FStar_Tactics_Types.goal_env goal in
                let uu____2797 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu____2796 uu____2797 in
              let uu____2798 = FStar_Tactics_Types.goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu____2798))
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu____2822 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____2830 -> g.FStar_Tactics_Types.opts
                 | uu____2833 -> FStar_Options.peek () in
               FStar_Tactics_Monad.mlog
                 (fun uu____2838 ->
                    let uu____2839 = FStar_Syntax_Print.term_to_string t in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____2839)
                 (fun uu____2842 ->
                    let uu____2843 = __tc_lax e t in
                    FStar_Tactics_Monad.bind uu____2843
                      (fun uu____2864 ->
                         match uu____2864 with
                         | (t1, uu____2874, uu____2875) ->
                             let steps =
                               let uu____2879 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____2879 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             FStar_Tactics_Monad.mlog
                               (fun uu____2885 ->
                                  let uu____2886 =
                                    FStar_Syntax_Print.term_to_string t2 in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____2886)
                               (fun uu____2888 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_term")
          uu____2822
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____2899 ->
    let uu____2902 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____2909 =
             let uu____2920 = FStar_Tactics_Types.goal_env g in
             let uu____2921 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu____2920 uu____2921 in
           match uu____2909 with
           | (uu____2924, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t in
               let uu____2949 =
                 let uu____2954 =
                   let uu____2959 =
                     let uu____2960 = FStar_Syntax_Syntax.mk_binder bv in
                     [uu____2960] in
                   FStar_Syntax_Subst.open_term uu____2959 phi in
                 match uu____2954 with
                 | (bvs, phi1) ->
                     let uu____2985 =
                       let uu____2986 = FStar_List.hd bvs in
                       FStar_Pervasives_Native.fst uu____2986 in
                     (uu____2985, phi1) in
               (match uu____2949 with
                | (bv1, phi1) ->
                    let uu____3005 =
                      let uu____3008 = FStar_Tactics_Types.goal_env g in
                      let uu____3009 =
                        let uu____3010 =
                          let uu____3013 =
                            let uu____3014 =
                              let uu____3021 =
                                FStar_Tactics_Types.goal_witness g in
                              (bv1, uu____3021) in
                            FStar_Syntax_Syntax.NT uu____3014 in
                          [uu____3013] in
                        FStar_Syntax_Subst.subst uu____3010 phi1 in
                      FStar_Tactics_Monad.mk_irrelevant_goal
                        "refine_intro refinement" uu____3008 uu____3009
                        g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label in
                    FStar_Tactics_Monad.bind uu____3005
                      (fun g2 ->
                         FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                           (fun uu____3029 ->
                              FStar_Tactics_Monad.add_goals [g1; g2])))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "refine_intro")
      uu____2902
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu____3053 = FStar_Tactics_Types.goal_env goal in
               let uu____3054 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu____3053 uu____3054
             else FStar_Tactics_Types.goal_env goal in
           let uu____3056 = __tc env1 t in
           FStar_Tactics_Monad.bind uu____3056
             (fun uu____3075 ->
                match uu____3075 with
                | (t1, typ, guard) ->
                    FStar_Tactics_Monad.mlog
                      (fun uu____3090 ->
                         let uu____3091 =
                           FStar_Syntax_Print.term_to_string typ in
                         let uu____3092 =
                           let uu____3093 = FStar_Tactics_Types.goal_env goal in
                           FStar_TypeChecker_Rel.guard_to_string uu____3093
                             guard in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3091 uu____3092)
                      (fun uu____3096 ->
                         let uu____3097 =
                           let uu____3100 = FStar_Tactics_Types.goal_env goal in
                           proc_guard "__exact typing" uu____3100 guard in
                         FStar_Tactics_Monad.bind uu____3097
                           (fun uu____3102 ->
                              FStar_Tactics_Monad.mlog
                                (fun uu____3106 ->
                                   let uu____3107 =
                                     FStar_Syntax_Print.term_to_string typ in
                                   let uu____3108 =
                                     let uu____3109 =
                                       FStar_Tactics_Types.goal_type goal in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3109 in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3107 uu____3108)
                                (fun uu____3112 ->
                                   let uu____3113 =
                                     let uu____3116 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu____3117 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify uu____3116 typ uu____3117 in
                                   FStar_Tactics_Monad.bind uu____3113
                                     (fun b ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3123 =
                                             let uu____3128 =
                                               let uu____3133 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu____3133 in
                                             let uu____3134 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu____3128 typ uu____3134 in
                                           match uu____3123 with
                                           | (typ1, goalt) ->
                                               let uu____3139 =
                                                 let uu____3140 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu____3140 t1 in
                                               let uu____3141 =
                                                 let uu____3142 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu____3143 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu____3142 uu____3143 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu____3139 typ1 goalt
                                                 uu____3141)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu____3163 =
          FStar_Tactics_Monad.mlog
            (fun uu____3168 ->
               let uu____3169 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3169)
            (fun uu____3172 ->
               let uu____3173 =
                 let uu____3180 = __exact_now set_expected_typ tm in
                 FStar_Tactics_Monad.catch uu____3180 in
               FStar_Tactics_Monad.bind uu____3173
                 (fun uu___1_3189 ->
                    match uu___1_3189 with
                    | FStar_Util.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Util.Inl e ->
                        FStar_Tactics_Monad.mlog
                          (fun uu____3200 ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3203 ->
                             let uu____3204 =
                               let uu____3211 =
                                 let uu____3214 =
                                   norm [FStar_Syntax_Embeddings.Delta] in
                                 FStar_Tactics_Monad.bind uu____3214
                                   (fun uu____3219 ->
                                      let uu____3220 = refine_intro () in
                                      FStar_Tactics_Monad.bind uu____3220
                                        (fun uu____3224 ->
                                           __exact_now set_expected_typ tm)) in
                               FStar_Tactics_Monad.catch uu____3211 in
                             FStar_Tactics_Monad.bind uu____3204
                               (fun uu___0_3231 ->
                                  match uu___0_3231 with
                                  | FStar_Util.Inr r ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3240 ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____3242 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Util.Inl uu____3243 ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu____3245 ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____3247 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "exact") uu____3163
let rec (__try_unify_by_application :
  Prims.bool ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
              FStar_Syntax_Syntax.ctx_uvar) Prims.list
              FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun acc ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            let f = if only_match then do_match else do_unify in
            let uu____3340 = f e ty2 ty1 in
            FStar_Tactics_Monad.bind uu____3340
              (fun uu___2_3352 ->
                 if uu___2_3352
                 then FStar_Tactics_Monad.ret acc
                 else
                   (let uu____3371 = FStar_Syntax_Util.arrow_one ty1 in
                    match uu____3371 with
                    | FStar_Pervasives_Native.None ->
                        let uu____3392 = term_to_string e ty1 in
                        let uu____3393 = term_to_string e ty2 in
                        fail2 "Could not instantiate, %s to %s" uu____3392
                          uu____3393
                    | FStar_Pervasives_Native.Some (b, c) ->
                        let uu____3408 =
                          let uu____3409 = FStar_Syntax_Util.is_total_comp c in
                          Prims.op_Negation uu____3409 in
                        if uu____3408
                        then FStar_Tactics_Monad.fail "Codomain is effectful"
                        else
                          (let uu____3429 =
                             FStar_Tactics_Monad.new_uvar "apply arg" e
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           FStar_Tactics_Monad.bind uu____3429
                             (fun uu____3453 ->
                                match uu____3453 with
                                | (uvt, uv) ->
                                    FStar_Tactics_Monad.mlog
                                      (fun uu____3480 ->
                                         let uu____3481 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             uv in
                                         FStar_Util.print1
                                           "t_apply: generated uvar %s\n"
                                           uu____3481)
                                      (fun uu____3485 ->
                                         let typ =
                                           FStar_Syntax_Util.comp_result c in
                                         let typ' =
                                           FStar_Syntax_Subst.subst
                                             [FStar_Syntax_Syntax.NT
                                                ((FStar_Pervasives_Native.fst
                                                    b), uvt)] typ in
                                         __try_unify_by_application
                                           only_match
                                           ((uvt,
                                              (FStar_Pervasives_Native.snd b),
                                              uv) :: acc) e typ' ty2)))))
let (try_unify_by_application :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list FStar_Tactics_Monad.tac)
  =
  fun only_match ->
    fun e ->
      fun ty1 ->
        fun ty2 -> __try_unify_by_application only_match [] e ty1 ty2
let (t_apply :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tm ->
        let uu____3567 =
          FStar_Tactics_Monad.mlog
            (fun uu____3572 ->
               let uu____3573 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.print1 "t_apply: tm = %s\n" uu____3573)
            (fun uu____3575 ->
               FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                 (fun goal ->
                    let e = FStar_Tactics_Types.goal_env goal in
                    FStar_Tactics_Monad.mlog
                      (fun uu____3584 ->
                         let uu____3585 =
                           FStar_Syntax_Print.term_to_string tm in
                         let uu____3586 =
                           FStar_Tactics_Printing.goal_to_string_verbose goal in
                         let uu____3587 =
                           FStar_TypeChecker_Env.print_gamma
                             e.FStar_TypeChecker_Env.gamma in
                         FStar_Util.print3
                           "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\n"
                           uu____3585 uu____3586 uu____3587)
                      (fun uu____3590 ->
                         let uu____3591 = __tc e tm in
                         FStar_Tactics_Monad.bind uu____3591
                           (fun uu____3612 ->
                              match uu____3612 with
                              | (tm1, typ, guard) ->
                                  let typ1 = bnorm e typ in
                                  let uu____3625 =
                                    let uu____3636 =
                                      FStar_Tactics_Types.goal_type goal in
                                    try_unify_by_application only_match e
                                      typ1 uu____3636 in
                                  FStar_Tactics_Monad.bind uu____3625
                                    (fun uvs ->
                                       FStar_Tactics_Monad.mlog
                                         (fun uu____3657 ->
                                            let uu____3658 =
                                              FStar_Common.string_of_list
                                                (fun uu____3669 ->
                                                   match uu____3669 with
                                                   | (t, uu____3677,
                                                      uu____3678) ->
                                                       FStar_Syntax_Print.term_to_string
                                                         t) uvs in
                                            FStar_Util.print1
                                              "t_apply: found args = %s\n"
                                              uu____3658)
                                         (fun uu____3685 ->
                                            let fix_qual q =
                                              match q with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.Meta
                                                  uu____3700) ->
                                                  FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       false)
                                              | uu____3701 -> q in
                                            let w =
                                              FStar_List.fold_right
                                                (fun uu____3724 ->
                                                   fun w ->
                                                     match uu____3724 with
                                                     | (uvt, q, uu____3742)
                                                         ->
                                                         FStar_Syntax_Util.mk_app
                                                           w
                                                           [(uvt,
                                                              (fix_qual q))])
                                                uvs tm1 in
                                            let uvset =
                                              let uu____3774 =
                                                FStar_Syntax_Free.new_uv_set
                                                  () in
                                              FStar_List.fold_right
                                                (fun uu____3791 ->
                                                   fun s ->
                                                     match uu____3791 with
                                                     | (uu____3803,
                                                        uu____3804, uv) ->
                                                         let uu____3806 =
                                                           FStar_Syntax_Free.uvars
                                                             uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                         FStar_Util.set_union
                                                           s uu____3806) uvs
                                                uu____3774 in
                                            let free_in_some_goal uv =
                                              FStar_Util.set_mem uv uvset in
                                            let uu____3815 = solve' goal w in
                                            FStar_Tactics_Monad.bind
                                              uu____3815
                                              (fun uu____3820 ->
                                                 let uu____3821 =
                                                   FStar_Tactics_Monad.mapM
                                                     (fun uu____3838 ->
                                                        match uu____3838 with
                                                        | (uvt, q, uv) ->
                                                            let uu____3850 =
                                                              FStar_Syntax_Unionfind.find
                                                                uv.FStar_Syntax_Syntax.ctx_uvar_head in
                                                            (match uu____3850
                                                             with
                                                             | FStar_Pervasives_Native.Some
                                                                 uu____3855
                                                                 ->
                                                                 FStar_Tactics_Monad.ret
                                                                   ()
                                                             | FStar_Pervasives_Native.None
                                                                 ->
                                                                 let uu____3856
                                                                   =
                                                                   uopt &&
                                                                    (free_in_some_goal
                                                                    uv) in
                                                                 if
                                                                   uu____3856
                                                                 then
                                                                   FStar_Tactics_Monad.ret
                                                                    ()
                                                                 else
                                                                   (let uu____3860
                                                                    =
                                                                    let uu____3863
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___638_3866
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___638_3866.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = uv;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___638_3866.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false;
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___638_3866.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    [uu____3863] in
                                                                    FStar_Tactics_Monad.add_goals
                                                                    uu____3860)))
                                                     uvs in
                                                 FStar_Tactics_Monad.bind
                                                   uu____3821
                                                   (fun uu____3870 ->
                                                      proc_guard
                                                        "apply guard" e guard)))))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply") uu____3567
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c in
    let uu____3895 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid in
    if uu____3895
    then
      let uu____3902 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3917 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3970 -> failwith "apply_lemma: impossible: not a lemma" in
      match uu____3902 with
      | (pre, post) ->
          let post1 =
            let uu____4002 =
              let uu____4013 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
              [uu____4013] in
            FStar_Syntax_Util.mk_app post uu____4002 in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4043 =
         (FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name)
           ||
           (FStar_Syntax_Util.is_ghost_effect
              ct.FStar_Syntax_Syntax.effect_name) in
       if uu____4043
       then
         let uu____4050 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ in
         FStar_Util.map_opt uu____4050
           (fun post -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStar_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStar_Tactics_Monad.tac
  =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> FStar_Tactics_Monad.ret e
        | x::xs1 ->
            let uu____4127 = f x e in
            FStar_Tactics_Monad.bind uu____4127
              (fun e' -> fold_left f e' xs1)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu____4151 =
          let uu____4154 =
            FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
              (fun ps ->
                 FStar_Tactics_Monad.mlog
                   (fun uu____4161 ->
                      let uu____4162 = FStar_Syntax_Print.term_to_string tm in
                      FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4162)
                   (fun uu____4165 ->
                      let is_unit_t t =
                        let uu____4172 =
                          let uu____4173 = FStar_Syntax_Subst.compress t in
                          uu____4173.FStar_Syntax_Syntax.n in
                        match uu____4172 with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.unit_lid
                            -> true
                        | uu____4177 -> false in
                      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let env1 = FStar_Tactics_Types.goal_env goal in
                           let uu____4183 = __tc env1 tm in
                           FStar_Tactics_Monad.bind uu____4183
                             (fun uu____4206 ->
                                match uu____4206 with
                                | (tm1, t, guard) ->
                                    let uu____4218 =
                                      FStar_Syntax_Util.arrow_formals_comp t in
                                    (match uu____4218 with
                                     | (bs, comp) ->
                                         let uu____4227 = lemma_or_sq comp in
                                         (match uu____4227 with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Tactics_Monad.fail
                                                "not a lemma or squashed function"
                                          | FStar_Pervasives_Native.Some
                                              (pre, post) ->
                                              let uu____4246 =
                                                fold_left
                                                  (fun uu____4308 ->
                                                     fun uu____4309 ->
                                                       match (uu____4308,
                                                               uu____4309)
                                                       with
                                                       | ((b, aq),
                                                          (uvs, imps, subst))
                                                           ->
                                                           let b_t =
                                                             FStar_Syntax_Subst.subst
                                                               subst
                                                               b.FStar_Syntax_Syntax.sort in
                                                           let uu____4460 =
                                                             is_unit_t b_t in
                                                           if uu____4460
                                                           then
                                                             FStar_All.pipe_left
                                                               FStar_Tactics_Monad.ret
                                                               (((FStar_Syntax_Util.exp_unit,
                                                                   aq) ::
                                                                 uvs), imps,
                                                                 ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                 :: subst))
                                                           else
                                                             (let uu____4580
                                                                =
                                                                FStar_Tactics_Monad.new_uvar
                                                                  "apply_lemma"
                                                                  env1 b_t in
                                                              FStar_Tactics_Monad.bind
                                                                uu____4580
                                                                (fun
                                                                   uu____4616
                                                                   ->
                                                                   match uu____4616
                                                                   with
                                                                   | 
                                                                   (t1, u) ->
                                                                    FStar_All.pipe_left
                                                                    FStar_Tactics_Monad.ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst)))))
                                                  ([], [], []) bs in
                                              FStar_Tactics_Monad.bind
                                                uu____4246
                                                (fun uu____4804 ->
                                                   match uu____4804 with
                                                   | (uvs, implicits1, subst)
                                                       ->
                                                       let implicits2 =
                                                         FStar_List.rev
                                                           implicits1 in
                                                       let uvs1 =
                                                         FStar_List.rev uvs in
                                                       let pre1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst pre in
                                                       let post1 =
                                                         FStar_Syntax_Subst.subst
                                                           subst post in
                                                       let post_u =
                                                         env1.FStar_TypeChecker_Env.universe_of
                                                           env1 post1 in
                                                       let cmp_func =
                                                         if noinst
                                                         then do_match
                                                         else
                                                           if noinst_lhs
                                                           then
                                                             do_match_on_lhs
                                                           else do_unify in
                                                       let uu____4932 =
                                                         let uu____4935 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal in
                                                         let uu____4936 =
                                                           FStar_Syntax_Util.mk_squash
                                                             post_u post1 in
                                                         cmp_func env1
                                                           uu____4935
                                                           uu____4936 in
                                                       FStar_Tactics_Monad.bind
                                                         uu____4932
                                                         (fun b ->
                                                            if
                                                              Prims.op_Negation
                                                                b
                                                            then
                                                              let uu____4945
                                                                =
                                                                let uu____4950
                                                                  =
                                                                  FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                let uu____4951
                                                                  =
                                                                  FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                FStar_TypeChecker_Err.print_discrepancy
                                                                  (tts env1)
                                                                  uu____4950
                                                                  uu____4951 in
                                                              match uu____4945
                                                              with
                                                              | (post2,
                                                                 goalt) ->
                                                                  let uu____4956
                                                                    =
                                                                    tts env1
                                                                    tm1 in
                                                                  fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu____4956
                                                                    post2
                                                                    goalt
                                                            else
                                                              (let uu____4958
                                                                 =
                                                                 solve' goal
                                                                   FStar_Syntax_Util.exp_unit in
                                                               FStar_Tactics_Monad.bind
                                                                 uu____4958
                                                                 (fun
                                                                    uu____4966
                                                                    ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu____4993
                                                                    =
                                                                    let uu____4996
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Util.set_elements
                                                                    uu____4996 in
                                                                    FStar_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____4993 in
                                                                    FStar_List.existsML
                                                                    (fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu____5033
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5033)
                                                                    goals in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu____5049
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu____5049
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5067)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu____5093)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5110
                                                                    -> false) in
                                                                    let uu____5111
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    implicits2
                                                                    (FStar_Tactics_Monad.mapM
                                                                    (fun imp
                                                                    ->
                                                                    let uu____5152
                                                                    = imp in
                                                                    match uu____5152
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    ctx_uvar)
                                                                    ->
                                                                    let uu____5163
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term in
                                                                    (match uu____5163
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu____5185)
                                                                    ->
                                                                    let uu____5210
                                                                    =
                                                                    let uu____5211
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd in
                                                                    uu____5211.FStar_Syntax_Syntax.n in
                                                                    (match uu____5210
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,
                                                                    uu____5219)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___764_5239
                                                                    = goal in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___764_5239.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___764_5239.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___764_5239.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___764_5239.FStar_Tactics_Types.label)
                                                                    }) in
                                                                    FStar_Tactics_Monad.ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5242
                                                                    ->
                                                                    FStar_Tactics_Monad.mlog
                                                                    (fun
                                                                    uu____5248
                                                                    ->
                                                                    let uu____5249
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                                                                    let uu____5250
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5249
                                                                    uu____5250)
                                                                    (fun
                                                                    uu____5254
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env1
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                                    let uu____5256
                                                                    =
                                                                    let uu____5259
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5260
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar in
                                                                    let uu____5261
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5260
                                                                    uu____5261
                                                                    else
                                                                    "apply_lemma solved arg" in
                                                                    proc_guard
                                                                    uu____5259
                                                                    env1
                                                                    g_typ in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5256
                                                                    (fun
                                                                    uu____5266
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    [])))))) in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5111
                                                                    (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____5328
                                                                    = f x xs1 in
                                                                    if
                                                                    uu____5328
                                                                    then
                                                                    let uu____5331
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu____5331
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu____5345
                                                                    =
                                                                    let uu____5346
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu____5346
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu____5345)
                                                                    sub_goals1 in
                                                                    let uu____5347
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5347
                                                                    (fun
                                                                    uu____5353
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu____5355
                                                                    =
                                                                    let uu____5358
                                                                    =
                                                                    let uu____5359
                                                                    =
                                                                    let uu____5360
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    pre_u
                                                                    pre1 in
                                                                    istrivial
                                                                    env1
                                                                    uu____5360 in
                                                                    Prims.op_Negation
                                                                    uu____5359 in
                                                                    if
                                                                    uu____5358
                                                                    then
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    else
                                                                    FStar_Tactics_Monad.ret
                                                                    () in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____5355
                                                                    (fun
                                                                    uu____5365
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2))))))))))))) in
          focus uu____4154 in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "apply_lemma")
          uu____4151
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu____5416 = FStar_TypeChecker_Env.pop_bv e1 in
        match uu____5416 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu____5451 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu____5451
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____5473 = aux e' in
               FStar_Util.map_opt uu____5473
                 (fun uu____5504 ->
                    match uu____5504 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu____5530 = aux e in
      FStar_Util.map_opt uu____5530
        (fun uu____5561 ->
           match uu____5561 with
           | (e', bv, bvs) -> (e', bv, (FStar_List.rev bvs)))
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e ->
    fun bvs ->
      FStar_List.fold_left
        (fun e1 -> fun b -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun b1 ->
    fun b2 ->
      fun g ->
        let uu____5636 =
          let uu____5647 = FStar_Tactics_Types.goal_env g in
          split_env b1 uu____5647 in
        match uu____5636 with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_List.map FStar_Syntax_Syntax.mk_binder (b11 :: bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu____5687 =
              let uu____5700 = FStar_Syntax_Subst.close_binders bs in
              let uu____5709 = FStar_Syntax_Subst.close bs t in
              (uu____5700, uu____5709) in
            (match uu____5687 with
             | (bs', t') ->
                 let bs'1 =
                   let uu____5753 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu____5760 = FStar_List.tail bs' in uu____5753 ::
                     uu____5760 in
                 let uu____5781 = FStar_Syntax_Subst.open_term bs'1 t' in
                 (match uu____5781 with
                  | (bs'', t'') ->
                      let b21 =
                        let uu____5797 = FStar_List.hd bs'' in
                        FStar_Pervasives_Native.fst uu____5797 in
                      let new_env =
                        let uu____5813 =
                          FStar_List.map FStar_Pervasives_Native.fst bs'' in
                        push_bvs e0 uu____5813 in
                      let uu____5824 =
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t'' in
                      FStar_Tactics_Monad.bind uu____5824
                        (fun uu____5847 ->
                           match uu____5847 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu____5866 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu____5869 =
                                   FStar_List.map
                                     (fun uu____5890 ->
                                        match uu____5890 with
                                        | (bv, q) ->
                                            let uu____5903 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu____5903) bs in
                                 FStar_Syntax_Util.mk_app uu____5866
                                   uu____5869 in
                               let uu____5904 = set_solution g sol in
                               FStar_Tactics_Monad.bind uu____5904
                                 (fun uu____5914 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu____5952 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____5960 = h in
           match uu____5960 with
           | (bv, uu____5964) ->
               FStar_Tactics_Monad.mlog
                 (fun uu____5972 ->
                    let uu____5973 = FStar_Syntax_Print.bv_to_string bv in
                    let uu____5974 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5973
                      uu____5974)
                 (fun uu____5977 ->
                    let uu____5978 =
                      let uu____5989 = FStar_Tactics_Types.goal_env goal in
                      split_env bv uu____5989 in
                    match uu____5978 with
                    | FStar_Pervasives_Native.None ->
                        FStar_Tactics_Monad.fail
                          "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                        let uu____6015 =
                          let uu____6022 =
                            whnf e0 bv1.FStar_Syntax_Syntax.sort in
                          destruct_eq uu____6022 in
                        (match uu____6015 with
                         | FStar_Pervasives_Native.Some (x, e) ->
                             let uu____6031 =
                               let uu____6032 = FStar_Syntax_Subst.compress x in
                               uu____6032.FStar_Syntax_Syntax.n in
                             (match uu____6031 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                                  let t = FStar_Tactics_Types.goal_type goal in
                                  let bs =
                                    FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder bvs in
                                  let uu____6059 =
                                    let uu____6064 =
                                      FStar_Syntax_Subst.close_binders bs in
                                    let uu____6065 =
                                      FStar_Syntax_Subst.close bs t in
                                    (uu____6064, uu____6065) in
                                  (match uu____6059 with
                                   | (bs', t') ->
                                       let uu____6070 =
                                         let uu____6075 =
                                           FStar_Syntax_Subst.subst_binders s
                                             bs' in
                                         let uu____6076 =
                                           FStar_Syntax_Subst.subst s t in
                                         (uu____6075, uu____6076) in
                                       (match uu____6070 with
                                        | (bs'1, t'1) ->
                                            let uu____6081 =
                                              FStar_Syntax_Subst.open_term
                                                bs'1 t'1 in
                                            (match uu____6081 with
                                             | (bs'', t'') ->
                                                 let new_env =
                                                   let uu____6091 =
                                                     let uu____6094 =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.fst
                                                         bs'' in
                                                     bv1 :: uu____6094 in
                                                   push_bvs e0 uu____6091 in
                                                 let uu____6105 =
                                                   FStar_Tactics_Monad.new_uvar
                                                     "rewrite" new_env t'' in
                                                 FStar_Tactics_Monad.bind
                                                   uu____6105
                                                   (fun uu____6122 ->
                                                      match uu____6122 with
                                                      | (uvt, uv) ->
                                                          let goal' =
                                                            FStar_Tactics_Types.mk_goal
                                                              new_env uv
                                                              goal.FStar_Tactics_Types.opts
                                                              goal.FStar_Tactics_Types.is_guard
                                                              goal.FStar_Tactics_Types.label in
                                                          let sol =
                                                            let uu____6135 =
                                                              FStar_Syntax_Util.abs
                                                                bs'' uvt
                                                                FStar_Pervasives_Native.None in
                                                            let uu____6138 =
                                                              FStar_List.map
                                                                (fun
                                                                   uu____6159
                                                                   ->
                                                                   match uu____6159
                                                                   with
                                                                   | 
                                                                   (bv2,
                                                                    uu____6167)
                                                                    ->
                                                                    let uu____6172
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____6172)
                                                                bs in
                                                            FStar_Syntax_Util.mk_app
                                                              uu____6135
                                                              uu____6138 in
                                                          let uu____6173 =
                                                            set_solution goal
                                                              sol in
                                                          FStar_Tactics_Monad.bind
                                                            uu____6173
                                                            (fun uu____6177
                                                               ->
                                                               FStar_Tactics_Monad.replace_cur
                                                                 goal')))))
                              | uu____6178 ->
                                  FStar_Tactics_Monad.fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6179 ->
                             FStar_Tactics_Monad.fail
                               "Not an equality hypothesis"))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rewrite") uu____5952
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu____6204 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6226 = b in
             match uu____6226 with
             | (bv, q) ->
                 let bv' =
                   let uu____6242 =
                     let uu___886_6243 = bv in
                     let uu____6244 =
                       let uu____6245 =
                         let uu____6250 =
                           FStar_Ident.range_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         (s, uu____6250) in
                       FStar_Ident.mk_ident uu____6245 in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6244;
                       FStar_Syntax_Syntax.index =
                         (uu___886_6243.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___886_6243.FStar_Syntax_Syntax.sort)
                     } in
                   FStar_Syntax_Syntax.freshen_bv uu____6242 in
                 let uu____6251 = subst_goal bv bv' goal in
                 FStar_Tactics_Monad.bind uu____6251
                   (fun uu___3_6273 ->
                      match uu___3_6273 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Tactics_Monad.fail
                            "binder not found in environment"
                      | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                          let uu____6304 =
                            FStar_Tactics_Monad.replace_cur goal1 in
                          FStar_Tactics_Monad.bind uu____6304
                            (fun uu____6314 ->
                               FStar_Tactics_Monad.ret (bv'1, q)))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "rename_to")
        uu____6204
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu____6348 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu____6357 = b in
           match uu____6357 with
           | (bv, uu____6361) ->
               let uu____6366 =
                 let uu____6377 = FStar_Tactics_Types.goal_env goal in
                 split_env bv uu____6377 in
               (match uu____6366 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu____6403 = FStar_Syntax_Util.type_u () in
                    (match uu____6403 with
                     | (ty, u) ->
                         let uu____6412 =
                           FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty in
                         FStar_Tactics_Monad.bind uu____6412
                           (fun uu____6430 ->
                              match uu____6430 with
                              | (t', u_t') ->
                                  let bv'' =
                                    let uu___913_6440 = bv1 in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___913_6440.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___913_6440.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    } in
                                  let s =
                                    let uu____6444 =
                                      let uu____6445 =
                                        let uu____6452 =
                                          FStar_Syntax_Syntax.bv_to_name bv'' in
                                        (bv1, uu____6452) in
                                      FStar_Syntax_Syntax.NT uu____6445 in
                                    [uu____6444] in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1 ->
                                         let uu___918_6464 = b1 in
                                         let uu____6465 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___918_6464.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___918_6464.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6465
                                         }) bvs in
                                  let env' = push_bvs e0 (bv'' :: bvs1) in
                                  FStar_Tactics_Monad.bind
                                    FStar_Tactics_Monad.dismiss
                                    (fun uu____6472 ->
                                       let new_goal =
                                         let uu____6474 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env' in
                                         let uu____6475 =
                                           let uu____6476 =
                                             FStar_Tactics_Types.goal_type
                                               goal in
                                           FStar_Syntax_Subst.subst s
                                             uu____6476 in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6474 uu____6475 in
                                       let uu____6477 =
                                         FStar_Tactics_Monad.add_goals
                                           [new_goal] in
                                       FStar_Tactics_Monad.bind uu____6477
                                         (fun uu____6482 ->
                                            let uu____6483 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t' in
                                            FStar_Tactics_Monad.add_irrelevant_goal
                                              goal "binder_retype equation"
                                              e0 uu____6483)))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "binder_retype")
      uu____6348
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu____6506 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let uu____6515 = b in
             match uu____6515 with
             | (bv, uu____6519) ->
                 let uu____6524 =
                   let uu____6535 = FStar_Tactics_Types.goal_env goal in
                   split_env bv uu____6535 in
                 (match uu____6524 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                      let steps =
                        let uu____6564 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6564 in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                      let bv' =
                        let uu___939_6569 = bv1 in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___939_6569.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___939_6569.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        } in
                      let env' = push_bvs e0 (bv' :: bvs) in
                      let uu____6571 =
                        FStar_Tactics_Types.goal_with_env goal env' in
                      FStar_Tactics_Monad.replace_cur uu____6571)) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "norm_binder_type")
        uu____6506
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6582 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6588 =
           let uu____6595 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6595 in
         match uu____6588 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu____6611 =
                 let uu____6614 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu____6614 in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6611 in
             let uu____6629 = FStar_Tactics_Monad.new_uvar "revert" env' typ' in
             FStar_Tactics_Monad.bind uu____6629
               (fun uu____6644 ->
                  match uu____6644 with
                  | (r, u_r) ->
                      let uu____6653 =
                        let uu____6656 =
                          let uu____6657 =
                            let uu____6658 =
                              let uu____6667 =
                                FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu____6667 in
                            [uu____6658] in
                          let uu____6684 =
                            let uu____6685 =
                              FStar_Tactics_Types.goal_type goal in
                            uu____6685.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu____6657
                            uu____6684 in
                        set_solution goal uu____6656 in
                      FStar_Tactics_Monad.bind uu____6653
                        (fun uu____6690 ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label in
                           FStar_Tactics_Monad.replace_cur g)))
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____6702 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____6702
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = FStar_Pervasives_Native.fst b in
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Tactics_Monad.mlog
           (fun uu____6722 ->
              let uu____6723 = FStar_Syntax_Print.binder_to_string b in
              let uu____6724 =
                let uu____6725 =
                  let uu____6726 =
                    let uu____6735 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.all_binders uu____6735 in
                  FStar_All.pipe_right uu____6726 FStar_List.length in
                FStar_All.pipe_right uu____6725 FStar_Util.string_of_int in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6723 uu____6724)
           (fun uu____6752 ->
              let uu____6753 =
                let uu____6764 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu____6764 in
              match uu____6753 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu____6808 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu____6808
                        then
                          let uu____6811 =
                            let uu____6812 =
                              FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6812 in
                          FStar_Tactics_Monad.fail uu____6811
                        else check bvs2 in
                  let uu____6814 =
                    let uu____6815 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu____6815 in
                  if uu____6814
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu____6819 = check bvs in
                     FStar_Tactics_Monad.bind uu____6819
                       (fun uu____6825 ->
                          let env' = push_bvs e' bvs in
                          let uu____6827 =
                            let uu____6834 =
                              FStar_Tactics_Types.goal_type goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu____6834 in
                          FStar_Tactics_Monad.bind uu____6827
                            (fun uu____6843 ->
                               match uu____6843 with
                               | (ut, uvar_ut) ->
                                   let uu____6852 = set_solution goal ut in
                                   FStar_Tactics_Monad.bind uu____6852
                                     (fun uu____6857 ->
                                        let uu____6858 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu____6858))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____6865 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu____6871 =
           let uu____6878 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu____6878 in
         match uu____6871 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu____6886) ->
             let uu____6891 = FStar_Syntax_Syntax.mk_binder x in
             clear uu____6891)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____6908 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6908 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu____6926 = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6926 in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (_trefl_with_guard :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun l ->
    fun r ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let succeed_with guard =
             let f =
               match guard.FStar_TypeChecker_Common.guard_f with
               | FStar_TypeChecker_Common.Trivial -> FStar_Syntax_Util.t_true
               | FStar_TypeChecker_Common.NonTrivial f -> f in
             let uu____6958 = solve' g FStar_Syntax_Util.exp_unit in
             FStar_Tactics_Monad.bind uu____6958
               (fun uu____6963 ->
                  let uu____6964 =
                    let uu____6967 = FStar_Tactics_Types.goal_env g in
                    FStar_Tactics_Monad.goal_of_guard "trefl guard"
                      uu____6967 f in
                  FStar_Tactics_Monad.bind uu____6964
                    (fun g' -> FStar_Tactics_Monad.add_goals [g'])) in
           let uu____6970 =
             let uu____6975 = FStar_Tactics_Types.goal_env g in
             do_unify_with_guard uu____6975 l r in
           FStar_Tactics_Monad.bind uu____6970
             (fun uu___5_6980 ->
                match uu___5_6980 with
                | FStar_Pervasives_Native.Some guard -> succeed_with guard
                | FStar_Pervasives_Native.None ->
                    let norm1 =
                      let uu____6991 = FStar_Tactics_Types.goal_env g in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.UnfoldTac] uu____6991 in
                    let l1 = norm1 l in
                    let r1 = norm1 r in
                    let uu____6994 =
                      let uu____6999 = FStar_Tactics_Types.goal_env g in
                      do_unify_with_guard uu____6999 l1 r1 in
                    FStar_Tactics_Monad.bind uu____6994
                      (fun uu___4_7004 ->
                         match uu___4_7004 with
                         | FStar_Pervasives_Native.Some guard ->
                             succeed_with guard
                         | FStar_Pervasives_Native.None ->
                             let uu____7010 =
                               let uu____7015 =
                                 let uu____7020 =
                                   FStar_Tactics_Types.goal_env g in
                                 tts uu____7020 in
                               FStar_TypeChecker_Err.print_discrepancy
                                 uu____7015 l1 r1 in
                             (match uu____7010 with
                              | (ls, rs) ->
                                  fail2
                                    "could not unify (with guard) terms ((%s) and (%s))"
                                    ls rs))))
let (trefl_with_guard : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7031 ->
    let uu____7034 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7042 =
             let uu____7049 =
               let uu____7050 = FStar_Tactics_Types.goal_env g in
               let uu____7051 = FStar_Tactics_Types.goal_type g in
               whnf uu____7050 uu____7051 in
             destruct_eq uu____7049 in
           match uu____7042 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl_with_guard l r
           | FStar_Pervasives_Native.None ->
               let uu____7064 =
                 let uu____7065 = FStar_Tactics_Types.goal_env g in
                 let uu____7066 = FStar_Tactics_Types.goal_type g in
                 tts uu____7065 uu____7066 in
               fail1 "not an equality (%s)" uu____7064) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7034
let (_trefl :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun l ->
    fun r ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7088 =
             let uu____7091 = FStar_Tactics_Types.goal_env g in
             do_unify uu____7091 l r in
           FStar_Tactics_Monad.bind uu____7088
             (fun b ->
                if b
                then solve' g FStar_Syntax_Util.exp_unit
                else
                  (let l1 =
                     let uu____7098 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7098 l in
                   let r1 =
                     let uu____7100 = FStar_Tactics_Types.goal_env g in
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                       FStar_TypeChecker_Env.Primops;
                       FStar_TypeChecker_Env.UnfoldTac] uu____7100 r in
                   let uu____7101 =
                     let uu____7104 = FStar_Tactics_Types.goal_env g in
                     do_unify uu____7104 l1 r1 in
                   FStar_Tactics_Monad.bind uu____7101
                     (fun b1 ->
                        if b1
                        then solve' g FStar_Syntax_Util.exp_unit
                        else
                          (let uu____7110 =
                             let uu____7115 =
                               let uu____7120 =
                                 FStar_Tactics_Types.goal_env g in
                               tts uu____7120 in
                             FStar_TypeChecker_Err.print_discrepancy
                               uu____7115 l1 r1 in
                           match uu____7110 with
                           | (ls, rs) ->
                               fail2 "not a trivial equality ((%s) vs (%s))"
                                 ls rs)))))
let (trefl : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7131 ->
    let uu____7134 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____7142 =
             let uu____7149 =
               let uu____7150 = FStar_Tactics_Types.goal_env g in
               let uu____7151 = FStar_Tactics_Types.goal_type g in
               whnf uu____7150 uu____7151 in
             destruct_eq uu____7149 in
           match uu____7142 with
           | FStar_Pervasives_Native.Some (l, r) -> _trefl l r
           | FStar_Pervasives_Native.None ->
               let uu____7164 =
                 let uu____7165 = FStar_Tactics_Types.goal_env g in
                 let uu____7166 = FStar_Tactics_Types.goal_type g in
                 tts uu____7165 uu____7166 in
               fail1 "not an equality (%s)" uu____7164) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "trefl") uu____7134
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7177 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu____7185 =
           let uu____7192 = FStar_Tactics_Types.goal_type g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu____7192 in
         FStar_Tactics_Monad.bind uu____7185
           (fun uu____7201 ->
              match uu____7201 with
              | (u, u_uvar) ->
                  let g' =
                    let uu___1057_7211 = g in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1057_7211.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1057_7211.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1057_7211.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1057_7211.FStar_Tactics_Types.label)
                    } in
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu____7215 ->
                       let t_eq =
                         let uu____7217 =
                           let uu____7218 = FStar_Tactics_Types.goal_type g in
                           env1.FStar_TypeChecker_Env.universe_of env1
                             uu____7218 in
                         let uu____7219 = FStar_Tactics_Types.goal_type g in
                         let uu____7220 = FStar_Tactics_Types.goal_witness g in
                         FStar_Syntax_Util.mk_eq2 uu____7217 uu____7219 u
                           uu____7220 in
                       let uu____7221 =
                         FStar_Tactics_Monad.add_irrelevant_goal g
                           "dup equation" env1 t_eq in
                       FStar_Tactics_Monad.bind uu____7221
                         (fun uu____7226 ->
                            let uu____7227 =
                              FStar_Tactics_Monad.add_goals [g'] in
                            FStar_Tactics_Monad.bind uu____7227
                              (fun uu____7231 -> FStar_Tactics_Monad.ret ())))))
let longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs, y::ys) ->
              let uu____7354 = f x y in
              if uu____7354 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____7374 -> (acc, l11, l21) in
        let uu____7389 = aux [] l1 l2 in
        match uu____7389 with | (pr, t1, t2) -> ((FStar_List.rev pr), t1, t2)
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs bs f =
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f in
      let uu____7494 = FStar_Tactics_Types.get_phi g1 in
      match uu____7494 with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____7500 = FStar_Tactics_Types.get_phi g2 in
          (match uu____7500 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu____7512 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2) in
               (match uu____7512 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu____7543 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1) in
                      close_forall_no_univs uu____7543 phi1 in
                    let t2 =
                      let uu____7553 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2) in
                      close_forall_no_univs uu____7553 phi2 in
                    let uu____7562 =
                      set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.bind uu____7562
                      (fun uu____7567 ->
                         let uu____7568 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.bind uu____7568
                           (fun uu____7575 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___1109_7580 =
                                  FStar_Tactics_Types.goal_env g1 in
                                let uu____7581 =
                                  FStar_Util.smap_create (Prims.of_int (100)) in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1109_7580.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1109_7580.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1109_7580.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1109_7580.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____7581;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1109_7580.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1109_7580.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1109_7580.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1109_7580.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1109_7580.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1109_7580.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1109_7580.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1109_7580.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1109_7580.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1109_7580.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1109_7580.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___1109_7580.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1109_7580.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1109_7580.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1109_7580.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1109_7580.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1109_7580.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1109_7580.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1109_7580.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1109_7580.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1109_7580.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1109_7580.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1109_7580.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1109_7580.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1109_7580.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1109_7580.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1109_7580.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1109_7580.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1109_7580.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1109_7580.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___1109_7580.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1109_7580.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___1109_7580.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1109_7580.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1109_7580.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1109_7580.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1109_7580.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1109_7580.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___1109_7580.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___1109_7580.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___1109_7580.FStar_TypeChecker_Env.enable_defer_to_tac)
                                } in
                              let uu____7584 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.bind uu____7584
                                (fun goal ->
                                   FStar_Tactics_Monad.mlog
                                     (fun uu____7593 ->
                                        let uu____7594 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g1 in
                                        let uu____7595 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            g2 in
                                        let uu____7596 =
                                          FStar_Tactics_Printing.goal_to_string_verbose
                                            goal in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____7594 uu____7595 uu____7596)
                                     (fun uu____7598 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu____7605 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____7621 =
               FStar_Tactics_Monad.set
                 (let uu___1124_7626 = ps in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1124_7626.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1124_7626.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1124_7626.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1124_7626.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1124_7626.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1124_7626.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1124_7626.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1124_7626.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1124_7626.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1124_7626.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1124_7626.FStar_Tactics_Types.local_state)
                  }) in
             FStar_Tactics_Monad.bind uu____7621
               (fun uu____7629 ->
                  let uu____7630 = join_goals g1 g2 in
                  FStar_Tactics_Monad.bind uu____7630
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu____7635 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu____7647 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu____7660 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu____7660);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   let uu___1135_7667 = g in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1135_7667.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1135_7667.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1135_7667.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1135_7667.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "set_options")
      uu____7647
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu____7679 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_All.pipe_left FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu____7692 ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu____7698 =
           (FStar_Options.lax ()) ||
             (let uu____7700 = FStar_Tactics_Types.goal_env g in
              uu____7700.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu____7698)
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu____7715 =
        FStar_Tactics_Monad.mlog
          (fun uu____7720 ->
             let uu____7721 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "unquote: tm = %s\n" uu____7721)
          (fun uu____7723 ->
             FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu____7729 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu____7729 ty in
                  let uu____7730 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.bind uu____7730
                    (fun uu____7749 ->
                       match uu____7749 with
                       | (tm1, typ, guard) ->
                           FStar_Tactics_Monad.mlog
                             (fun uu____7763 ->
                                let uu____7764 =
                                  FStar_Syntax_Print.term_to_string tm1 in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____7764)
                             (fun uu____7766 ->
                                FStar_Tactics_Monad.mlog
                                  (fun uu____7769 ->
                                     let uu____7770 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____7770)
                                  (fun uu____7773 ->
                                     let uu____7774 =
                                       proc_guard "unquote" env1 guard in
                                     FStar_Tactics_Monad.bind uu____7774
                                       (fun uu____7778 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unquote") uu____7715
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      let uu____7801 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> FStar_Tactics_Monad.ret ty1
        | FStar_Pervasives_Native.None ->
            let uu____7807 =
              let uu____7814 =
                let uu____7815 = FStar_Syntax_Util.type_u () in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7815 in
              FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu____7814 in
            FStar_Tactics_Monad.bind uu____7807
              (fun uu____7831 ->
                 match uu____7831 with
                 | (typ, uvar_typ) -> FStar_Tactics_Monad.ret typ) in
      FStar_Tactics_Monad.bind uu____7801
        (fun typ ->
           let uu____7843 = FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ in
           FStar_Tactics_Monad.bind uu____7843
             (fun uu____7857 ->
                match uu____7857 with
                | (t, uvar_t) -> FStar_Tactics_Monad.ret t))
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu____7875 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____7894 -> g.FStar_Tactics_Types.opts
             | uu____7897 -> FStar_Options.peek () in
           let uu____7900 = FStar_Syntax_Util.head_and_args t in
           match uu____7900 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu____7920);
                FStar_Syntax_Syntax.pos = uu____7921;
                FStar_Syntax_Syntax.vars = uu____7922;_},
              uu____7923) ->
               let env2 =
                 let uu___1189_7965 = env1 in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1189_7965.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1189_7965.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1189_7965.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1189_7965.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1189_7965.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1189_7965.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1189_7965.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1189_7965.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1189_7965.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1189_7965.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1189_7965.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1189_7965.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1189_7965.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1189_7965.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1189_7965.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1189_7965.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (uu___1189_7965.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1189_7965.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1189_7965.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1189_7965.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1189_7965.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1189_7965.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1189_7965.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1189_7965.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1189_7965.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1189_7965.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1189_7965.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1189_7965.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1189_7965.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1189_7965.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1189_7965.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1189_7965.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1189_7965.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1189_7965.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1189_7965.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___1189_7965.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1189_7965.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (uu___1189_7965.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1189_7965.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1189_7965.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1189_7965.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1189_7965.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1189_7965.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___1189_7965.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___1189_7965.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (uu___1189_7965.FStar_TypeChecker_Env.enable_defer_to_tac)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let uu____7967 = let uu____7970 = bnorm_goal g in [uu____7970] in
               FStar_Tactics_Monad.add_goals uu____7967
           | uu____7971 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unshelve") uu____7875
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.bind t1
          (fun b ->
             let uu____8020 = if b then t2 else FStar_Tactics_Monad.ret false in
             FStar_Tactics_Monad.bind uu____8020
               (fun b' ->
                  if b'
                  then FStar_Tactics_Monad.ret b'
                  else FStar_Tactics_Monad.fail "")) in
      let uu____8031 = FStar_Tactics_Monad.trytac comp in
      FStar_Tactics_Monad.bind uu____8031
        (fun uu___6_8039 ->
           match uu___6_8039 with
           | FStar_Pervasives_Native.Some (true) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (match_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8065 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8071 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8071
                 (fun uu____8091 ->
                    match uu____8091 with
                    | (t11, ty1, g1) ->
                        let uu____8103 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8103
                          (fun uu____8123 ->
                             match uu____8123 with
                             | (t21, ty2, g2) ->
                                 let uu____8135 =
                                   proc_guard "match_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8135
                                   (fun uu____8140 ->
                                      let uu____8141 =
                                        proc_guard "match_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8141
                                        (fun uu____8147 ->
                                           let uu____8148 =
                                             do_match e ty1 ty2 in
                                           let uu____8151 =
                                             do_match e t11 t21 in
                                           tac_and uu____8148 uu____8151))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "match_env")
          uu____8065
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu____8177 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let uu____8183 = __tc e t1 in
               FStar_Tactics_Monad.bind uu____8183
                 (fun uu____8203 ->
                    match uu____8203 with
                    | (t11, ty1, g1) ->
                        let uu____8215 = __tc e t2 in
                        FStar_Tactics_Monad.bind uu____8215
                          (fun uu____8235 ->
                             match uu____8235 with
                             | (t21, ty2, g2) ->
                                 let uu____8247 =
                                   proc_guard "unify_env g1" e g1 in
                                 FStar_Tactics_Monad.bind uu____8247
                                   (fun uu____8252 ->
                                      let uu____8253 =
                                        proc_guard "unify_env g2" e g2 in
                                      FStar_Tactics_Monad.bind uu____8253
                                        (fun uu____8259 ->
                                           let uu____8260 =
                                             do_unify e ty1 ty2 in
                                           let uu____8263 =
                                             do_unify e t11 t21 in
                                           tac_and uu____8260 uu____8263))))) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "unify_env")
          uu____8177
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
          (fun uu____8296 ->
             let uu____8297 = FStar_Options.unsafe_tactic_exec () in
             if uu____8297
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input) in
               FStar_Tactics_Monad.ret s
             else
               FStar_Tactics_Monad.fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let (fresh_bv_named :
  Prims.string ->
    FStar_Reflection_Data.typ ->
      FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac)
  =
  fun nm ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
        (fun uu____8318 ->
           let uu____8319 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t in
           FStar_Tactics_Monad.ret uu____8319)
let (change : FStar_Reflection_Data.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu____8329 =
      FStar_Tactics_Monad.mlog
        (fun uu____8334 ->
           let uu____8335 = FStar_Syntax_Print.term_to_string ty in
           FStar_Util.print1 "change: ty = %s\n" uu____8335)
        (fun uu____8337 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu____8341 =
                  let uu____8350 = FStar_Tactics_Types.goal_env g in
                  __tc uu____8350 ty in
                FStar_Tactics_Monad.bind uu____8341
                  (fun uu____8362 ->
                     match uu____8362 with
                     | (ty1, uu____8372, guard) ->
                         let uu____8374 =
                           let uu____8377 = FStar_Tactics_Types.goal_env g in
                           proc_guard "change" uu____8377 guard in
                         FStar_Tactics_Monad.bind uu____8374
                           (fun uu____8380 ->
                              let uu____8381 =
                                let uu____8384 =
                                  FStar_Tactics_Types.goal_env g in
                                let uu____8385 =
                                  FStar_Tactics_Types.goal_type g in
                                do_unify uu____8384 uu____8385 ty1 in
                              FStar_Tactics_Monad.bind uu____8381
                                (fun bb ->
                                   if bb
                                   then
                                     let uu____8391 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1 in
                                     FStar_Tactics_Monad.replace_cur
                                       uu____8391
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu____8397 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu____8398 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu____8397 uu____8398 in
                                      let nty =
                                        let uu____8400 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu____8400 ty1 in
                                      let uu____8401 =
                                        let uu____8404 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify uu____8404 ng nty in
                                      FStar_Tactics_Monad.bind uu____8401
                                        (fun b ->
                                           if b
                                           then
                                             let uu____8410 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu____8410
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "change") uu____8329
let failwhen :
  'a .
    Prims.bool ->
      Prims.string ->
        (unit -> 'a FStar_Tactics_Monad.tac) -> 'a FStar_Tactics_Monad.tac
  =
  fun b ->
    fun msg -> fun k -> if b then FStar_Tactics_Monad.fail msg else k ()
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu____8473 =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu____8491 =
             let uu____8500 = FStar_Tactics_Types.goal_env g in
             __tc uu____8500 s_tm in
           FStar_Tactics_Monad.bind uu____8491
             (fun uu____8518 ->
                match uu____8518 with
                | (s_tm1, s_ty, guard) ->
                    let uu____8536 =
                      let uu____8539 = FStar_Tactics_Types.goal_env g in
                      proc_guard "destruct" uu____8539 guard in
                    FStar_Tactics_Monad.bind uu____8536
                      (fun uu____8552 ->
                         let s_ty1 =
                           let uu____8554 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu____8554
                             s_ty in
                         let uu____8555 =
                           let uu____8570 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args' uu____8570 in
                         match uu____8555 with
                         | (h, args) ->
                             let uu____8601 =
                               let uu____8608 =
                                 let uu____8609 =
                                   FStar_Syntax_Subst.compress h in
                                 uu____8609.FStar_Syntax_Syntax.n in
                               match uu____8608 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____8624;
                                      FStar_Syntax_Syntax.vars = uu____8625;_},
                                    us)
                                   -> FStar_Tactics_Monad.ret (fv, us)
                               | uu____8635 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.bind uu____8601
                               (fun uu____8655 ->
                                  match uu____8655 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu____8671 =
                                        let uu____8674 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____8674 t_lid in
                                      (match uu____8671 with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Tactics_Monad.fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid, t_us, t_ps, t_ty, mut,
                                                 c_lids)
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr in
                                                let uu____8713 =
                                                  erasable &&
                                                    (let uu____8715 =
                                                       FStar_Tactics_Types.is_irrelevant
                                                         g in
                                                     Prims.op_Negation
                                                       uu____8715) in
                                                failwhen uu____8713
                                                  "cannot destruct erasable type to solve proof-relevant goal"
                                                  (fun uu____8723 ->
                                                     failwhen
                                                       ((FStar_List.length
                                                           a_us)
                                                          <>
                                                          (FStar_List.length
                                                             t_us))
                                                       "t_us don't match?"
                                                       (fun uu____8735 ->
                                                          let uu____8736 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu____8736
                                                          with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu____8751
                                                                =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu____8779
                                                                    =
                                                                    let uu____8782
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____8782
                                                                    c_lid in
                                                                    match uu____8779
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,
                                                                    c_us,
                                                                    c_ty,
                                                                    _t_lid,
                                                                    nparam,
                                                                    mut1) ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor) in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____8855
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu____8860
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu____8860
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu____8883
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu____8883
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu____8902
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu____8925
                                                                    =
                                                                    let uu____8930
                                                                    =
                                                                    let uu____8931
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu____8931 in
                                                                    let uu____8932
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu____8930,
                                                                    uu____8932) in
                                                                    FStar_Ident.mk_ident
                                                                    uu____8925 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    (let uu___1331_8935
                                                                    = bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1331_8935.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (uu___1331_8935.FStar_Syntax_Syntax.sort)
                                                                    }) in
                                                                    let bs' =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____8961
                                                                    ->
                                                                    match uu____8961
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    let uu____8980
                                                                    =
                                                                    rename_bv
                                                                    bv in
                                                                    (uu____8980,
                                                                    aq)) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map2
                                                                    (fun
                                                                    uu____9005
                                                                    ->
                                                                    fun
                                                                    uu____9006
                                                                    ->
                                                                    match 
                                                                    (uu____9005,
                                                                    uu____9006)
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9032),
                                                                    (bv',
                                                                    uu____9034))
                                                                    ->
                                                                    let uu____9055
                                                                    =
                                                                    let uu____9062
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu____9062) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____9055)
                                                                    bs bs' in
                                                                    let uu____9067
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu____9076
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu____9067,
                                                                    uu____9076) in
                                                                    (match uu____8902
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu____9123
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu____9123
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu____9196
                                                                    =
                                                                    let uu____9197
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu____9197 in
                                                                    failwhen
                                                                    uu____9196
                                                                    "not total?"
                                                                    (fun
                                                                    uu____9214
                                                                    ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    } in
                                                                    let is_imp
                                                                    uu___7_9230
                                                                    =
                                                                    match uu___7_9230
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____9233)
                                                                    -> true
                                                                    | 
                                                                    uu____9234
                                                                    -> false in
                                                                    let uu____9237
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu____9237
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____9372
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9434
                                                                    ->
                                                                    match uu____9434
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9454),
                                                                    (t,
                                                                    uu____9456))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9524
                                                                    ->
                                                                    match uu____9524
                                                                    with
                                                                    | 
                                                                    ((bv,
                                                                    uu____9550),
                                                                    (t,
                                                                    uu____9552))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____9607
                                                                    ->
                                                                    match uu____9607
                                                                    with
                                                                    | 
                                                                    (bv, aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs3 in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats)) in
                                                                    let env1
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1
                                                                    s_ty1 in
                                                                    let uu____9657
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1390_9680
                                                                    = env1 in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (uu___1390_9680.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                    }) s_ty1
                                                                    pat in
                                                                    match uu____9657
                                                                    with
                                                                    | 
                                                                    (uu____9693,
                                                                    uu____9694,
                                                                    uu____9695,
                                                                    uu____9696,
                                                                    pat_t,
                                                                    uu____9698,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____9710
                                                                    =
                                                                    let uu____9711
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____9711 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____9710 in
                                                                    let cod1
                                                                    =
                                                                    let uu____9715
                                                                    =
                                                                    let uu____9724
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu____9724] in
                                                                    let uu____9743
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9715
                                                                    uu____9743 in
                                                                    let nty =
                                                                    let uu____9749
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu____9749 in
                                                                    let uu____9752
                                                                    =
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____9752
                                                                    (fun
                                                                    uu____9781
                                                                    ->
                                                                    match uu____9781
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env1 uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3 in
                                                                    let brt1
                                                                    =
                                                                    let uu____9807
                                                                    =
                                                                    let uu____9818
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu____9818] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____9807 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu____9854
                                                                    =
                                                                    let uu____9865
                                                                    =
                                                                    let uu____9870
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu____9870) in
                                                                    (g', br,
                                                                    uu____9865) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu____9854)))))))
                                                                    | 
                                                                    uu____9891
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.bind
                                                                uu____8751
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu____9940
                                                                    =
                                                                    FStar_List.unzip3
                                                                    goal_brs in
                                                                   match uu____9940
                                                                   with
                                                                   | 
                                                                   (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu____10013
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10013
                                                                    (fun
                                                                    uu____10024
                                                                    ->
                                                                    let uu____10025
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.bind
                                                                    uu____10025
                                                                    (fun
                                                                    uu____10035
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos)))))
                                            | uu____10042 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "destruct") uu____8473
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10087::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10115 = init xs in x :: uu____10115
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu____10127 =
      let uu____10130 = top_env () in
      FStar_Tactics_Monad.bind uu____10130
        (fun e ->
           let t1 = FStar_Syntax_Util.unascribe t in
           let t2 = FStar_Syntax_Util.un_uinst t1 in
           let t3 = FStar_Syntax_Util.unlazy_emb t2 in
           match t3.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta (t4, uu____10146) -> inspect t4
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_app (hd, []) ->
               failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app (hd, args) ->
               let uu____10211 = last args in
               (match uu____10211 with
                | (a, q) ->
                    let q' = FStar_Reflection_Basic.inspect_aqual q in
                    let uu____10241 =
                      let uu____10242 =
                        let uu____10247 =
                          let uu____10248 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu____10248
                            t3.FStar_Syntax_Syntax.pos in
                        (uu____10247, (a, q')) in
                      FStar_Reflection_Data.Tv_App uu____10242 in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10241)
           | FStar_Syntax_Syntax.Tm_abs ([], uu____10259, uu____10260) ->
               failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs (bs, t4, k) ->
               let uu____10312 = FStar_Syntax_Subst.open_term bs t4 in
               (match uu____10312 with
                | (bs1, t5) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu____10353 =
                           let uu____10354 =
                             let uu____10359 = FStar_Syntax_Util.abs bs2 t5 k in
                             (b, uu____10359) in
                           FStar_Reflection_Data.Tv_Abs uu____10354 in
                         FStar_All.pipe_left FStar_Tactics_Monad.ret
                           uu____10353))
           | FStar_Syntax_Syntax.Tm_type uu____10362 ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Type ())
           | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
               failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu____10386 ->
               let uu____10401 = FStar_Syntax_Util.arrow_one t3 in
               (match uu____10401 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu____10431 = FStar_Syntax_Subst.open_term [b] t4 in
               (match uu____10431 with
                | (b', t5) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu____10484 -> failwith "impossible" in
                    FStar_All.pipe_left FStar_Tactics_Monad.ret
                      (FStar_Reflection_Data.Tv_Refine
                         ((FStar_Pervasives_Native.fst b1), t5)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu____10496 =
                 let uu____10497 = FStar_Reflection_Basic.inspect_const c in
                 FStar_Reflection_Data.Tv_Const uu____10497 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10496
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu____10518 =
                 let uu____10519 =
                   let uu____10524 =
                     let uu____10525 =
                       FStar_Syntax_Unionfind.uvar_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu____10525 in
                   (uu____10524, (ctx_u, s)) in
                 FStar_Reflection_Data.Tv_Uvar uu____10519 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10518
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10559 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu____10564 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu____10564 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b1::[] -> b1
                             | uu____10617 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders" in
                           FStar_All.pipe_left FStar_Tactics_Monad.ret
                             (FStar_Reflection_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (FStar_Pervasives_Native.fst b1),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_All.pipe_left FStar_Tactics_Monad.ret
                   FStar_Reflection_Data.Tv_Unknown
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Util.Inr uu____10653 ->
                      FStar_All.pipe_left FStar_Tactics_Monad.ret
                        FStar_Reflection_Data.Tv_Unknown
                  | FStar_Util.Inl bv ->
                      let uu____10657 =
                        FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu____10657 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____10677 ->
                                     FStar_Tactics_Monad.ret
                                       FStar_Reflection_Data.Tv_Unknown
                                 | FStar_Util.Inl bv1 ->
                                     FStar_All.pipe_left
                                       FStar_Tactics_Monad.ret
                                       (FStar_Reflection_Data.Tv_Let
                                          (true,
                                            (lb1.FStar_Syntax_Syntax.lbattrs),
                                            bv1,
                                            (lb1.FStar_Syntax_Syntax.lbdef),
                                            t22)))
                            | uu____10683 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu____10737 = FStar_Reflection_Basic.inspect_const c in
                     FStar_Reflection_Data.Pat_Constant uu____10737
                 | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
                     let uu____10756 =
                       let uu____10767 =
                         FStar_List.map
                           (fun uu____10788 ->
                              match uu____10788 with
                              | (p1, b) ->
                                  let uu____10805 = inspect_pat p1 in
                                  (uu____10805, b)) ps in
                       (fv, uu____10767) in
                     FStar_Reflection_Data.Pat_Cons uu____10756
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_Data.Pat_Var bv
                 | FStar_Syntax_Syntax.Pat_wild bv ->
                     FStar_Reflection_Data.Pat_Wild bv
                 | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
                     FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
               let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_List.map
                   (fun uu___8_10899 ->
                      match uu___8_10899 with
                      | (pat, uu____10921, t5) ->
                          let uu____10939 = inspect_pat pat in
                          (uu____10939, t5)) brs1 in
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 (FStar_Reflection_Data.Tv_Match (t4, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_All.pipe_left FStar_Tactics_Monad.ret
                 FStar_Reflection_Data.Tv_Unknown
           | uu____10948 ->
               ((let uu____10950 =
                   let uu____10955 =
                     let uu____10956 = FStar_Syntax_Print.tag_of_term t3 in
                     let uu____10957 = term_to_string e t3 in
                     FStar_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu____10956 uu____10957 in
                   (FStar_Errors.Warning_CantInspect, uu____10955) in
                 FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos
                   uu____10950);
                FStar_All.pipe_left FStar_Tactics_Monad.ret
                  FStar_Reflection_Data.Tv_Unknown)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu____10127
let (pack :
  FStar_Reflection_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10970 = FStar_Syntax_Syntax.bv_to_name bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10970
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10974 = FStar_Syntax_Syntax.bv_to_tm bv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10974
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10978 = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10978
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q in
        let uu____10985 = FStar_Syntax_Util.mk_app l [(r, q')] in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____10985
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        let uu____11010 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11010
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        let uu____11027 = FStar_Syntax_Util.arrow [b] c in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11027
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left FStar_Tactics_Monad.ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        let uu____11046 = FStar_Syntax_Util.refine bv t in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11046
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11050 =
          let uu____11051 =
            let uu____11052 = FStar_Reflection_Basic.pack_const c in
            FStar_Syntax_Syntax.Tm_constant uu____11052 in
          FStar_Syntax_Syntax.mk uu____11051 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11050
    | FStar_Reflection_Data.Tv_Uvar (_u, ctx_u_s) ->
        let uu____11057 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11057
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11069 =
          let uu____11070 =
            let uu____11071 =
              let uu____11084 =
                let uu____11087 =
                  let uu____11088 = FStar_Syntax_Syntax.mk_binder bv in
                  [uu____11088] in
                FStar_Syntax_Subst.close uu____11087 t2 in
              ((false, [lb]), uu____11084) in
            FStar_Syntax_Syntax.Tm_let uu____11071 in
          FStar_Syntax_Syntax.mk uu____11070 FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11069
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        let uu____11128 = FStar_Syntax_Subst.close_let_rec [lb] t2 in
        (match uu____11128 with
         | (lbs, body) ->
             let uu____11143 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Range.dummyRange in
             FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11143)
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11177 =
                let uu____11178 = FStar_Reflection_Basic.pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____11178 in
              FStar_All.pipe_left wrap uu____11177
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____11193 =
                let uu____11194 =
                  let uu____11207 =
                    FStar_List.map
                      (fun uu____11228 ->
                         match uu____11228 with
                         | (p1, b) ->
                             let uu____11239 = pack_pat p1 in
                             (uu____11239, b)) ps in
                  (fv, uu____11207) in
                FStar_Syntax_Syntax.Pat_cons uu____11194 in
              FStar_All.pipe_left wrap uu____11193
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___9_11285 ->
               match uu___9_11285 with
               | (pat, t1) ->
                   let uu____11302 = pack_pat pat in
                   (uu____11302, FStar_Pervasives_Native.None, t1)) brs in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1 in
        let uu____11350 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11350
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        let uu____11378 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11378
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        let uu____11424 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11424
    | FStar_Reflection_Data.Tv_Unknown ->
        let uu____11463 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Range.dummyRange in
        FStar_All.pipe_left FStar_Tactics_Monad.ret uu____11463
let (lget :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu____11480 =
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun ps ->
             let uu____11486 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k in
             match uu____11486 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lget") uu____11480
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu____11515 =
          FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1695_11522 = ps in
                 let uu____11523 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___1695_11522.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___1695_11522.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___1695_11522.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___1695_11522.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___1695_11522.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___1695_11522.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___1695_11522.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___1695_11522.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___1695_11522.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___1695_11522.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___1695_11522.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____11523
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_All.pipe_left (FStar_Tactics_Monad.wrap_err "lset") uu____11515
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Common.guard_t))
  =
  fun env1 ->
    fun typ ->
      let uu____11548 =
        FStar_TypeChecker_Env.new_implicit_var_aux "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env1 typ
          FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
      match uu____11548 with
      | (u, ctx_uvars, g_u) ->
          let uu____11580 = FStar_List.hd ctx_uvars in
          (match uu____11580 with
           | (ctx_uvar, uu____11594) ->
               let g =
                 let uu____11596 = FStar_Options.peek () in
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar uu____11596 false
                   "" in
               (g, g_u))
let (tac_env : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env1 ->
    let uu____11602 = FStar_TypeChecker_Env.clear_expected_typ env1 in
    match uu____11602 with
    | (env2, uu____11610) ->
        let env3 =
          let uu___1712_11616 = env2 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1712_11616.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1712_11616.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1712_11616.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1712_11616.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1712_11616.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1712_11616.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1712_11616.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1712_11616.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1712_11616.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1712_11616.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp = false;
            FStar_TypeChecker_Env.effects =
              (uu___1712_11616.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1712_11616.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1712_11616.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1712_11616.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1712_11616.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1712_11616.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1712_11616.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1712_11616.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1712_11616.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1712_11616.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1712_11616.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1712_11616.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1712_11616.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1712_11616.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1712_11616.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1712_11616.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1712_11616.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1712_11616.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1712_11616.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1712_11616.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1712_11616.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1712_11616.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1712_11616.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1712_11616.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1712_11616.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1712_11616.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1712_11616.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1712_11616.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1712_11616.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1712_11616.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1712_11616.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1712_11616.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1712_11616.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1712_11616.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1712_11616.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1712_11616.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env4 =
          let uu___1715_11618 = env3 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1715_11618.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1715_11618.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1715_11618.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1715_11618.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1715_11618.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1715_11618.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1715_11618.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1715_11618.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1715_11618.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1715_11618.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1715_11618.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1715_11618.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1715_11618.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1715_11618.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1715_11618.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1715_11618.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1715_11618.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1715_11618.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1715_11618.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1715_11618.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1715_11618.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1715_11618.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1715_11618.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard = true;
            FStar_TypeChecker_Env.nosynth =
              (uu___1715_11618.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1715_11618.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1715_11618.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1715_11618.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1715_11618.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1715_11618.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1715_11618.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1715_11618.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1715_11618.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1715_11618.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1715_11618.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1715_11618.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1715_11618.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1715_11618.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1715_11618.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1715_11618.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1715_11618.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1715_11618.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1715_11618.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1715_11618.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1715_11618.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1715_11618.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1715_11618.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let env5 =
          let uu___1718_11620 = env4 in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1718_11620.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1718_11620.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1718_11620.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1718_11620.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1718_11620.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1718_11620.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1718_11620.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1718_11620.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1718_11620.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1718_11620.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1718_11620.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1718_11620.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1718_11620.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1718_11620.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1718_11620.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1718_11620.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1718_11620.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1718_11620.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1718_11620.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1718_11620.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___1718_11620.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1718_11620.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1718_11620.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1718_11620.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1718_11620.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1718_11620.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1718_11620.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1718_11620.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1718_11620.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1718_11620.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1718_11620.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1718_11620.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1718_11620.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1718_11620.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1718_11620.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1718_11620.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1718_11620.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1718_11620.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1718_11620.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1718_11620.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1718_11620.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1718_11620.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1718_11620.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1718_11620.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1718_11620.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1718_11620.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac = false
          } in
        env5
let (proofstate_of_goals :
  FStar_Range.range ->
    env ->
      FStar_Tactics_Types.goal Prims.list ->
        FStar_TypeChecker_Common.implicit Prims.list ->
          FStar_Tactics_Types.proofstate)
  =
  fun rng ->
    fun env1 ->
      fun goals ->
        fun imps ->
          let env2 = tac_env env1 in
          let ps =
            let uu____11651 =
              FStar_TypeChecker_Env.debug env2
                (FStar_Options.Other "TacVerbose") in
            let uu____11652 = FStar_Util.psmap_empty () in
            {
              FStar_Tactics_Types.main_context = env2;
              FStar_Tactics_Types.all_implicits = imps;
              FStar_Tactics_Types.goals = goals;
              FStar_Tactics_Types.smt_goals = [];
              FStar_Tactics_Types.depth = Prims.int_zero;
              FStar_Tactics_Types.__dump =
                FStar_Tactics_Printing.do_dump_proofstate;
              FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
              FStar_Tactics_Types.entry_range = rng;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = Prims.int_zero;
              FStar_Tactics_Types.tac_verb_dbg = uu____11651;
              FStar_Tactics_Types.local_state = uu____11652
            } in
          ps
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun typ ->
        let env2 = tac_env env1 in
        let uu____11675 = goal_of_goal_ty env2 typ in
        match uu____11675 with
        | (g, g_u) ->
            let ps =
              proofstate_of_goals rng env2 [g]
                g_u.FStar_TypeChecker_Common.implicits in
            let uu____11687 = FStar_Tactics_Types.goal_witness g in
            (ps, uu____11687)
let (goal_of_implicit :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicit -> FStar_Tactics_Types.goal)
  =
  fun env1 ->
    fun i ->
      let uu____11698 = FStar_Options.peek () in
      FStar_Tactics_Types.mk_goal
        (let uu___1737_11701 = env1 in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1737_11701.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1737_11701.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1737_11701.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             ((i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1737_11701.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1737_11701.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1737_11701.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1737_11701.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1737_11701.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1737_11701.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1737_11701.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1737_11701.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1737_11701.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1737_11701.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1737_11701.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1737_11701.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1737_11701.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1737_11701.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (uu___1737_11701.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___1737_11701.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___1737_11701.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1737_11701.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1737_11701.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1737_11701.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1737_11701.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1737_11701.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1737_11701.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1737_11701.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1737_11701.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1737_11701.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1737_11701.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1737_11701.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1737_11701.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1737_11701.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1737_11701.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1737_11701.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1737_11701.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1737_11701.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1737_11701.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1737_11701.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1737_11701.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1737_11701.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1737_11701.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1737_11701.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1737_11701.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1737_11701.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1737_11701.FStar_TypeChecker_Env.enable_defer_to_tac)
         }) i.FStar_TypeChecker_Common.imp_uvar uu____11698 false
        i.FStar_TypeChecker_Common.imp_reason
let (proofstate_of_all_implicits :
  FStar_Range.range ->
    env ->
      implicits ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng ->
    fun env1 ->
      fun imps ->
        let env2 = tac_env env1 in
        let goals = FStar_List.map (goal_of_implicit env2) imps in
        let w =
          let uu____11726 = FStar_List.hd goals in
          FStar_Tactics_Types.goal_witness uu____11726 in
        let ps =
          let uu____11728 =
            FStar_TypeChecker_Env.debug env2
              (FStar_Options.Other "TacVerbose") in
          let uu____11729 = FStar_Util.psmap_empty () in
          {
            FStar_Tactics_Types.main_context = env2;
            FStar_Tactics_Types.all_implicits = imps;
            FStar_Tactics_Types.goals = goals;
            FStar_Tactics_Types.smt_goals = [];
            FStar_Tactics_Types.depth = Prims.int_zero;
            FStar_Tactics_Types.__dump =
              (fun ps ->
                 fun msg -> FStar_Tactics_Printing.do_dump_proofstate ps msg);
            FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
            FStar_Tactics_Types.entry_range = rng;
            FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
            FStar_Tactics_Types.freshness = Prims.int_zero;
            FStar_Tactics_Types.tac_verb_dbg = uu____11728;
            FStar_Tactics_Types.local_state = uu____11729
          } in
        (ps, w)