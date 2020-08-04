open Prims
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee -> match projectee with | { tac_f;_} -> tac_f
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f -> { tac_f = f }
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t -> fun ps -> t.tac_f ps
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t ->
    fun ps ->
      let uu____111 = FStar_Options.tactics_failhard () in
      if uu____111
      then run t ps
      else
        (try (fun uu___21_118 -> match () with | () -> run t ps) ()
         with
         | FStar_Errors.Err (uu____127, msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Common.TacticFailure msg), ps)
         | FStar_Errors.Error (uu____129, msg, uu____131) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Common.TacticFailure msg), ps)
         | e -> FStar_Tactics_Result.Failed (e, ps))
let ret : 'a . 'a -> 'a tac =
  fun x -> mk_tac (fun ps -> FStar_Tactics_Result.Success (x, ps))
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1 ->
    fun t2 ->
      mk_tac
        (fun ps ->
           let uu____188 = run t1 ps in
           match uu____188 with
           | FStar_Tactics_Result.Success (a1, q) ->
               let uu____195 = t2 a1 in run uu____195 q
           | FStar_Tactics_Result.Failed (msg, q) ->
               FStar_Tactics_Result.Failed (msg, q))
let (idtac : unit tac) = ret ()
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun ps -> mk_tac (fun uu____214 -> FStar_Tactics_Result.Success ((), ps))
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun ps -> FStar_Tactics_Result.Success (ps, ps))
let traise : 'a . Prims.exn -> 'a tac =
  fun e -> mk_tac (fun ps -> FStar_Tactics_Result.Failed (e, ps))
let (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps -> fun f -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
let fail : 'a . Prims.string -> 'a tac =
  fun msg ->
    mk_tac
      (fun ps ->
         (let uu____267 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail") in
          if uu____267
          then
            FStar_Tactics_Printing.do_dump_proofstate ps
              (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Common.TacticFailure msg), ps))
let catch : 'a . 'a tac -> (Prims.exn, 'a) FStar_Util.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         let uu____301 = run t ps in
         match uu____301 with
         | FStar_Tactics_Result.Success (a1, q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q))
         | FStar_Tactics_Result.Failed (m, q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___82_325 = ps in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___82_325.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (uu___82_325.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___82_325.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___82_325.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___82_325.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___82_325.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___82_325.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___82_325.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___82_325.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___82_325.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___82_325.FStar_Tactics_Types.local_state)
                 } in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
let recover : 'a . 'a tac -> (Prims.exn, 'a) FStar_Util.either tac =
  fun t ->
    mk_tac
      (fun ps ->
         let uu____363 = run t ps in
         match uu____363 with
         | FStar_Tactics_Result.Success (a1, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a1), q)
         | FStar_Tactics_Result.Failed (m, q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t ->
    let uu____410 = catch t in
    bind uu____410
      (fun r ->
         match r with
         | FStar_Util.Inr v -> ret (FStar_Pervasives_Native.Some v)
         | FStar_Util.Inl uu____437 -> ret FStar_Pervasives_Native.None)
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t ->
    mk_tac
      (fun ps ->
         try
           (fun uu___110_468 ->
              match () with
              | () -> let uu____473 = trytac t in run uu____473 ps) ()
         with
         | FStar_Errors.Err (uu____489, msg) ->
             (log ps
                (fun uu____493 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____498, msg, uu____500) ->
             (log ps
                (fun uu____503 ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f ->
    fun l ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____553 = f x in
          bind uu____553
            (fun y ->
               let uu____561 = mapM f xs in
               bind uu____561 (fun ys -> ret (y :: ys)))
let (nwarn : Prims.int FStar_ST.ref) = FStar_Util.mk_ref Prims.int_zero
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g ->
    let uu____583 = FStar_Options.defensive () in
    if uu____583
    then
      let b = true in
      let env = FStar_Tactics_Types.goal_env g in
      let b1 =
        b &&
          (let uu____588 = FStar_Tactics_Types.goal_witness g in
           FStar_TypeChecker_Env.closed env uu____588) in
      let b2 =
        b1 &&
          (let uu____591 = FStar_Tactics_Types.goal_type g in
           FStar_TypeChecker_Env.closed env uu____591) in
      let rec aux b3 e =
        let uu____603 = FStar_TypeChecker_Env.pop_bv e in
        match uu____603 with
        | FStar_Pervasives_Native.None -> b3
        | FStar_Pervasives_Native.Some (bv, e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort) in
            aux b4 e1 in
      let uu____621 =
        (let uu____624 = aux b2 env in Prims.op_Negation uu____624) &&
          (let uu____626 = FStar_ST.op_Bang nwarn in
           uu____626 < (Prims.of_int (5))) in
      (if uu____621
       then
         ((let uu____634 =
             let uu____635 = FStar_Tactics_Types.goal_type g in
             uu____635.FStar_Syntax_Syntax.pos in
           let uu____638 =
             let uu____643 =
               let uu____644 =
                 FStar_Tactics_Printing.goal_to_string_verbose g in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____644 in
             (FStar_Errors.Warning_IllFormedGoal, uu____643) in
           FStar_Errors.log_issue uu____634 uu____638);
          (let uu____645 =
             let uu____646 = FStar_ST.op_Bang nwarn in
             uu____646 + Prims.int_one in
           FStar_ST.op_Colon_Equals nwarn uu____645))
       else ())
    else ()
let (check_valid_goals : FStar_Tactics_Types.goal Prims.list -> unit) =
  fun gs ->
    let uu____670 = FStar_Options.defensive () in
    if uu____670 then FStar_List.iter check_valid_goal gs else ()
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___157_689 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___157_689.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___157_689.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___157_689.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___157_689.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___157_689.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___157_689.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___157_689.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___157_689.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___157_689.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___157_689.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___157_689.FStar_Tactics_Types.local_state)
            }))
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         set
           (let uu___161_707 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___161_707.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___161_707.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___161_707.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___161_707.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___161_707.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___161_707.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___161_707.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___161_707.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___161_707.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___161_707.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___161_707.FStar_Tactics_Types.local_state)
            }))
let (cur_goals : FStar_Tactics_Types.goal Prims.list tac) =
  bind get (fun ps -> ret ps.FStar_Tactics_Types.goals)
let (cur_goal : FStar_Tactics_Types.goal tac) =
  bind cur_goals
    (fun uu___0_725 ->
       match uu___0_725 with
       | [] -> fail "No more goals"
       | hd::tl ->
           let uu____734 = FStar_Tactics_Types.check_goal_solved' hd in
           (match uu____734 with
            | FStar_Pervasives_Native.None -> ret hd
            | FStar_Pervasives_Native.Some t ->
                ((let uu____741 =
                    FStar_Tactics_Printing.goal_to_string_verbose hd in
                  let uu____742 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print2
                    "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                    uu____741 uu____742);
                 ret hd)))
let (remove_solved_goals : unit tac) =
  bind cur_goals
    (fun gs ->
       let gs1 =
         FStar_List.filter
           (fun g ->
              let uu____760 = FStar_Tactics_Types.check_goal_solved g in
              Prims.op_Negation uu____760) gs in
       set_goals gs1)
let (dismiss_all : unit tac) = set_goals []
let (dismiss : unit tac) =
  bind get
    (fun ps ->
       let uu____772 =
         let uu___177_773 = ps in
         let uu____774 = FStar_List.tl ps.FStar_Tactics_Types.goals in
         {
           FStar_Tactics_Types.main_context =
             (uu___177_773.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (uu___177_773.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____774;
           FStar_Tactics_Types.smt_goals =
             (uu___177_773.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___177_773.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___177_773.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___177_773.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___177_773.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___177_773.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___177_773.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___177_773.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___177_773.FStar_Tactics_Types.local_state)
         } in
       set uu____772)
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g ->
    bind get
      (fun ps ->
         check_valid_goal g;
         (let uu____791 =
            let uu___182_792 = ps in
            let uu____793 =
              let uu____796 = FStar_List.tl ps.FStar_Tactics_Types.goals in g
                :: uu____796 in
            {
              FStar_Tactics_Types.main_context =
                (uu___182_792.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___182_792.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = uu____793;
              FStar_Tactics_Types.smt_goals =
                (uu___182_792.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___182_792.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___182_792.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___182_792.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___182_792.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___182_792.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___182_792.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___182_792.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___182_792.FStar_Tactics_Types.local_state)
            } in
          set uu____791))
let (getopts : FStar_Options.optionstate tac) =
  let uu____803 = trytac cur_goal in
  bind uu____803
    (fun uu___1_812 ->
       match uu___1_812 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None ->
           let uu____818 = FStar_Options.peek () in ret uu____818)
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___191_838 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___191_838.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___191_838.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___191_838.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___191_838.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___191_838.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___191_838.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___191_838.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___191_838.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___191_838.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___191_838.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___191_838.FStar_Tactics_Types.local_state)
            }))
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___196_858 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___196_858.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___196_858.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___196_858.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs ps.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___196_858.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___196_858.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___196_858.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___196_858.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___196_858.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___196_858.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___196_858.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___196_858.FStar_Tactics_Types.local_state)
            }))
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___201_878 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___201_878.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___201_878.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append ps.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___201_878.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___201_878.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___201_878.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___201_878.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___201_878.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___201_878.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___201_878.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___201_878.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___201_878.FStar_Tactics_Types.local_state)
            }))
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs ->
    bind get
      (fun ps ->
         check_valid_goals gs;
         set
           (let uu___206_898 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___206_898.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (uu___206_898.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___206_898.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append ps.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___206_898.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___206_898.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___206_898.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___206_898.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___206_898.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___206_898.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___206_898.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___206_898.FStar_Tactics_Types.local_state)
            }))
let (add_implicits : FStar_TypeChecker_Env.implicits -> unit tac) =
  fun i ->
    bind get
      (fun ps ->
         set
           (let uu___210_912 = ps in
            {
              FStar_Tactics_Types.main_context =
                (uu___210_912.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i ps.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___210_912.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___210_912.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___210_912.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___210_912.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___210_912.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___210_912.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___210_912.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___210_912.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___210_912.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___210_912.FStar_Tactics_Types.local_state)
            }))
let (new_uvar :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason ->
    fun env ->
      fun typ ->
        let uu____940 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None in
        match uu____940 with
        | (u, ctx_uvar, g_u) ->
            let uu____974 =
              add_implicits g_u.FStar_TypeChecker_Common.implicits in
            bind uu____974
              (fun uu____983 ->
                 let uu____984 =
                   let uu____989 =
                     let uu____990 = FStar_List.hd ctx_uvar in
                     FStar_Pervasives_Native.fst uu____990 in
                   (u, uu____989) in
                 ret uu____984)
let (mk_irrelevant_goal :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label ->
            let typ =
              let uu____1035 = env.FStar_TypeChecker_Env.universe_of env phi in
              FStar_Syntax_Util.mk_squash uu____1035 phi in
            let uu____1036 = new_uvar reason env typ in
            bind uu____1036
              (fun uu____1051 ->
                 match uu____1051 with
                 | (uu____1058, ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label in
                     ret goal)
let (add_irrelevant_goal' :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason ->
    fun env ->
      fun phi ->
        fun opts ->
          fun label ->
            let uu____1090 = mk_irrelevant_goal reason env phi opts label in
            bind uu____1090 (fun goal -> add_goals [goal])
let (add_irrelevant_goal :
  FStar_Tactics_Types.goal ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> unit tac)
  =
  fun base_goal ->
    fun reason ->
      fun env ->
        fun phi ->
          add_irrelevant_goal' reason env phi
            base_goal.FStar_Tactics_Types.opts
            base_goal.FStar_Tactics_Types.label
let (goal_of_guard :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Tactics_Types.goal tac)
  =
  fun reason ->
    fun e ->
      fun f ->
        bind getopts
          (fun opts ->
             let uu____1141 = mk_irrelevant_goal reason e f opts "" in
             bind uu____1141
               (fun goal ->
                  let goal1 =
                    let uu___245_1148 = goal in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___245_1148.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar =
                        (uu___245_1148.FStar_Tactics_Types.goal_ctx_uvar);
                      FStar_Tactics_Types.opts =
                        (uu___245_1148.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard = true;
                      FStar_Tactics_Types.label =
                        (uu___245_1148.FStar_Tactics_Types.label)
                    } in
                  ret goal1))
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref ->
    fun t ->
      mk_tac
        (fun ps ->
           let uu____1177 = run t ps in
           match uu____1177 with
           | FStar_Tactics_Result.Success (a1, q) ->
               FStar_Tactics_Result.Success (a1, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Common.TacticFailure msg, q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Common.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e, q) ->
               FStar_Tactics_Result.Failed (e, q))
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f -> fun cont -> bind get (fun ps -> log ps f; cont ())
let (compress_implicits : unit tac) =
  bind get
    (fun ps ->
       let imps = ps.FStar_Tactics_Types.all_implicits in
       let g =
         let uu___274_1237 = FStar_TypeChecker_Env.trivial_guard in
         {
           FStar_TypeChecker_Common.guard_f =
             (uu___274_1237.FStar_TypeChecker_Common.guard_f);
           FStar_TypeChecker_Common.deferred_to_tac =
             (uu___274_1237.FStar_TypeChecker_Common.deferred_to_tac);
           FStar_TypeChecker_Common.deferred =
             (uu___274_1237.FStar_TypeChecker_Common.deferred);
           FStar_TypeChecker_Common.univ_ineqs =
             (uu___274_1237.FStar_TypeChecker_Common.univ_ineqs);
           FStar_TypeChecker_Common.implicits = imps
         } in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g in
       let ps' =
         let uu___278_1240 = ps in
         {
           FStar_Tactics_Types.main_context =
             (uu___278_1240.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Common.implicits);
           FStar_Tactics_Types.goals =
             (uu___278_1240.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___278_1240.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___278_1240.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___278_1240.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___278_1240.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___278_1240.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___278_1240.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___278_1240.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___278_1240.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___278_1240.FStar_Tactics_Types.local_state)
         } in
       set ps')