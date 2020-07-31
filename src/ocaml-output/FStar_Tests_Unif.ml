open Prims
let (tcenv : unit -> FStar_TypeChecker_Env.env) =
  fun uu____4 -> FStar_Tests_Pars.init ()
let (guard_to_string :
  FStar_TypeChecker_Common.guard_formula -> Prims.string) =
  fun g ->
    match g with
    | FStar_TypeChecker_Common.Trivial -> "trivial"
    | FStar_TypeChecker_Common.NonTrivial f ->
        let uu____11 = tcenv () in
        FStar_TypeChecker_Normalize.term_to_string uu____11 f
let (success : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true
let (fail : Prims.string -> unit) =
  fun msg ->
    FStar_Util.print_string msg; FStar_ST.op_Colon_Equals success false
let (guard_eq :
  Prims.int ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula -> unit)
  =
  fun i ->
    fun g ->
      fun g' ->
        let uu____41 =
          match (g, g') with
          | (FStar_TypeChecker_Common.Trivial,
             FStar_TypeChecker_Common.Trivial) -> (true, g, g')
          | (FStar_TypeChecker_Common.NonTrivial f,
             FStar_TypeChecker_Common.NonTrivial f') ->
              let f1 =
                let uu____57 = tcenv () in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____57 f in
              let f'1 =
                let uu____59 = tcenv () in
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] uu____59 f' in
              let uu____60 = FStar_Tests_Util.term_eq f1 f'1 in
              (uu____60, (FStar_TypeChecker_Common.NonTrivial f1),
                (FStar_TypeChecker_Common.NonTrivial f'1))
          | uu____61 -> (false, g, g') in
        match uu____41 with
        | (b, g1, g'1) ->
            (if Prims.op_Negation b
             then
               (let uu____70 =
                  let uu____71 = FStar_Util.string_of_int i in
                  let uu____72 = guard_to_string g'1 in
                  let uu____73 = guard_to_string g1 in
                  FStar_Util.format3
                    "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n"
                    uu____71 uu____72 uu____73 in
                FStar_All.pipe_left fail uu____70)
             else ();
             (let uu____75 = (FStar_ST.op_Bang success) && b in
              FStar_ST.op_Colon_Equals success uu____75))
let (unify :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.guard_formula -> (unit -> unit) -> unit)
  =
  fun i ->
    fun x ->
      fun y ->
        fun g' ->
          fun check ->
            (let uu____127 = FStar_Util.string_of_int i in
             FStar_Util.print1 "%s ..." uu____127);
            (let uu____129 = FStar_Main.process_args () in
             FStar_All.pipe_right uu____129 (fun uu____142 -> ()));
            (let uu____144 = FStar_Syntax_Print.term_to_string x in
             let uu____145 = FStar_Syntax_Print.term_to_string y in
             FStar_Util.print2 "Unify %s\nand %s\n" uu____144 uu____145);
            (let g =
               let uu____147 =
                 let uu____148 =
                   let uu____149 = tcenv () in
                   FStar_TypeChecker_Rel.teq uu____149 x y in
                 let uu____150 =
                   let uu____155 = tcenv () in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____155 in
                 FStar_All.pipe_right uu____148 uu____150 in
               let uu____156 =
                 let uu____161 = tcenv () in
                 FStar_TypeChecker_Rel.simplify_guard uu____161 in
               FStar_All.pipe_right uu____147 uu____156 in
             guard_eq i g.FStar_TypeChecker_Common.guard_f g';
             check ();
             FStar_Options.init ())
let (should_fail :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun x ->
    fun y ->
      try
        (fun uu___41_185 ->
           match () with
           | () ->
               let g =
                 let uu____187 =
                   let uu____188 = tcenv () in
                   FStar_TypeChecker_Rel.teq uu____188 x y in
                 let uu____189 =
                   let uu____194 = tcenv () in
                   FStar_TypeChecker_Rel.solve_deferred_constraints uu____194 in
                 FStar_All.pipe_right uu____187 uu____189 in
               (match g.FStar_TypeChecker_Common.guard_f with
                | FStar_TypeChecker_Common.Trivial ->
                    let uu____195 =
                      let uu____196 = FStar_Syntax_Print.term_to_string x in
                      let uu____197 = FStar_Syntax_Print.term_to_string y in
                      FStar_Util.format2
                        "%s and %s should not be unifiable\n" uu____196
                        uu____197 in
                    fail uu____195
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let uu____199 = FStar_Syntax_Print.term_to_string x in
                    let uu____200 = FStar_Syntax_Print.term_to_string y in
                    let uu____201 = FStar_Syntax_Print.term_to_string f in
                    FStar_Util.print3 "%s and %s are unifiable if %s\n"
                      uu____199 uu____200 uu____201)) ()
      with
      | FStar_Errors.Error (e, msg, r, _ctx) -> FStar_Util.print1 "%s\n" msg
let (unify' : Prims.string -> Prims.string -> unit) =
  fun x ->
    fun y ->
      let x1 = FStar_Tests_Pars.pars x in
      let y1 = FStar_Tests_Pars.pars y in
      let g =
        let uu____229 =
          let uu____230 = tcenv () in
          FStar_TypeChecker_Rel.teq uu____230 x1 y1 in
        let uu____231 =
          let uu____236 = tcenv () in
          FStar_TypeChecker_Rel.solve_deferred_constraints uu____236 in
        FStar_All.pipe_right uu____229 uu____231 in
      let uu____237 = FStar_Syntax_Print.term_to_string x1 in
      let uu____238 = FStar_Syntax_Print.term_to_string y1 in
      let uu____239 = guard_to_string g.FStar_TypeChecker_Common.guard_f in
      FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____237
        uu____238 uu____239
let (norm : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____245 = tcenv () in
    FStar_TypeChecker_Normalize.normalize [] uu____245 t
let (inst :
  Prims.int ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term Prims.list))
  =
  fun n ->
    fun tm ->
      let rec aux out n1 =
        if n1 = Prims.int_zero
        then out
        else
          (let uu____286 =
             let uu____299 = FStar_Tests_Pars.init () in
             FStar_TypeChecker_Util.new_implicit_var ""
               FStar_Range.dummyRange uu____299 FStar_Syntax_Util.ktype0 in
           match uu____286 with
           | (t, uu____303, uu____304) ->
               let uu____317 =
                 let uu____330 = FStar_Tests_Pars.init () in
                 FStar_TypeChecker_Util.new_implicit_var ""
                   FStar_Range.dummyRange uu____330 t in
               (match uu____317 with
                | (u, uu____334, uu____335) ->
                    aux (u :: out) (n1 - Prims.int_one))) in
      let us = aux [] n in
      let uu____351 =
        let uu____352 = FStar_Tests_Util.app tm us in norm uu____352 in
      (uu____351, us)
let (run_all : unit -> Prims.bool) =
  fun uu____359 ->
    FStar_Util.print_string "Testing the unifier\n";
    FStar_Options.__set_unit_tests ();
    (let unify_check n x y g f = unify n x y g f in
     let unify1 n x y g = unify n x y g (fun uu____431 -> ()) in
     let int_t = FStar_Tests_Pars.tc "Prims.int" in
     let x =
       let uu____436 =
         FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t in
       FStar_All.pipe_right uu____436 FStar_Syntax_Syntax.bv_to_name in
     let y =
       let uu____442 =
         FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t in
       FStar_All.pipe_right uu____442 FStar_Syntax_Syntax.bv_to_name in
     unify1 Prims.int_zero x x FStar_TypeChecker_Common.Trivial;
     (let uu____447 =
        let uu____448 =
          FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero
            FStar_Syntax_Util.t_bool x y in
        FStar_TypeChecker_Common.NonTrivial uu____448 in
      unify1 Prims.int_one x y uu____447);
     (let id = FStar_Tests_Pars.tc "fun x -> x" in
      (let uu____451 = FStar_Tests_Util.app id [x] in
       unify1 (Prims.of_int (2)) x uu____451 FStar_TypeChecker_Common.Trivial);
      (let id1 = FStar_Tests_Pars.tc "fun x -> x" in
       unify1 (Prims.of_int (3)) id1 id1 FStar_TypeChecker_Common.Trivial;
       (let id2 = FStar_Tests_Pars.tc "fun x -> x" in
        let id' = FStar_Tests_Pars.tc "fun y -> y" in
        unify1 (Prims.of_int (4)) id2 id' FStar_TypeChecker_Common.Trivial;
        (let uu____460 = FStar_Tests_Pars.tc "fun x y -> x" in
         let uu____463 = FStar_Tests_Pars.tc "fun a b -> a" in
         unify1 (Prims.of_int (5)) uu____460 uu____463
           FStar_TypeChecker_Common.Trivial);
        (let uu____467 = FStar_Tests_Pars.tc "fun x y z -> y" in
         let uu____470 = FStar_Tests_Pars.tc "fun a b c -> b" in
         unify1 (Prims.of_int (6)) uu____467 uu____470
           FStar_TypeChecker_Common.Trivial);
        (let uu____474 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y" in
         let uu____477 = FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x" in
         let uu____480 =
           let uu____481 =
             FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))" in
           FStar_TypeChecker_Common.NonTrivial uu____481 in
         unify1 (Prims.of_int (7)) uu____474 uu____477 uu____480);
        (let uu____483 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y" in
         let uu____486 =
           FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z" in
         let uu____489 =
           let uu____490 =
             FStar_Tests_Pars.tc
               "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))" in
           FStar_TypeChecker_Common.NonTrivial uu____490 in
         unify1 (Prims.of_int (8)) uu____483 uu____486 uu____489);
        (let uu____492 = FStar_Main.process_args () in
         FStar_All.pipe_right uu____492 (fun uu____505 -> ()));
        (let uu____506 =
           let uu____513 = FStar_Tests_Pars.tc "fun u x -> u x" in
           inst Prims.int_one uu____513 in
         match uu____506 with
         | (tm, us) ->
             let sol = FStar_Tests_Pars.tc "fun x -> c_and x x" in
             (unify_check (Prims.of_int (9)) tm sol
                FStar_TypeChecker_Common.Trivial
                (fun uu____526 ->
                   let uu____527 =
                     let uu____528 =
                       let uu____531 = FStar_List.hd us in norm uu____531 in
                     let uu____532 = norm sol in
                     FStar_Tests_Util.term_eq uu____528 uu____532 in
                   FStar_Tests_Util.always (Prims.of_int (9)) uu____527);
              (let uu____535 =
                 let uu____542 = FStar_Tests_Pars.tc "fun u x -> u x" in
                 inst Prims.int_one uu____542 in
               match uu____535 with
               | (tm1, us1) ->
                   let sol1 = FStar_Tests_Pars.tc "fun x y -> x + y" in
                   (unify_check (Prims.of_int (10)) tm1 sol1
                      FStar_TypeChecker_Common.Trivial
                      (fun uu____555 ->
                         let uu____556 =
                           let uu____557 =
                             let uu____560 = FStar_List.hd us1 in
                             norm uu____560 in
                           let uu____561 = norm sol1 in
                           FStar_Tests_Util.term_eq uu____557 uu____561 in
                         FStar_Tests_Util.always (Prims.of_int (10))
                           uu____556);
                    (let tm11 =
                       FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool" in
                     let tm2 = FStar_Tests_Pars.tc "x:int -> y:int -> bool" in
                     (let uu____567 =
                        let uu____568 =
                          FStar_Tests_Pars.tc
                            "forall (x:int). (forall (y:int). y==x)" in
                        FStar_TypeChecker_Common.NonTrivial uu____568 in
                      unify1 (Prims.of_int (11)) tm11 tm2 uu____567);
                     (let tm12 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      let tm21 =
                        FStar_Tests_Pars.tc
                          "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0" in
                      unify1 (Prims.of_int (12)) tm12 tm21
                        FStar_TypeChecker_Common.Trivial;
                      (let uu____572 =
                         let int_typ = FStar_Tests_Pars.tc "int" in
                         let x1 =
                           FStar_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None int_typ in
                         let typ = FStar_Tests_Pars.tc "unit -> Type0" in
                         let l =
                           FStar_Tests_Pars.tc
                             "fun (q:(unit -> Type0)) -> q ()" in
                         let q =
                           FStar_Syntax_Syntax.new_bv
                             FStar_Pervasives_Native.None typ in
                         let tm13 =
                           let uu____587 =
                             let uu____588 =
                               let uu____591 =
                                 FStar_Syntax_Syntax.bv_to_name q in
                               [uu____591] in
                             FStar_Tests_Util.app l uu____588 in
                           norm uu____587 in
                         let l1 =
                           FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p" in
                         let unit = FStar_Tests_Pars.tc "()" in
                         let env =
                           let uu____595 = FStar_Tests_Pars.init () in
                           let uu____596 =
                             let uu____597 = FStar_Syntax_Syntax.mk_binder x1 in
                             let uu____604 =
                               let uu____613 =
                                 FStar_Syntax_Syntax.mk_binder q in
                               [uu____613] in
                             uu____597 :: uu____604 in
                           FStar_TypeChecker_Env.push_binders uu____595
                             uu____596 in
                         let uu____638 =
                           FStar_TypeChecker_Util.new_implicit_var ""
                             FStar_Range.dummyRange env typ in
                         match uu____638 with
                         | (u_p, uu____660, uu____661) ->
                             let tm22 =
                               let uu____677 =
                                 let uu____680 =
                                   FStar_Tests_Util.app l1 [u_p] in
                                 norm uu____680 in
                               FStar_Tests_Util.app uu____677 [unit] in
                             (tm13, tm22) in
                       match uu____572 with
                       | (tm13, tm22) ->
                           (unify1 (Prims.of_int (13)) tm13 tm22
                              FStar_TypeChecker_Common.Trivial;
                            (let uu____696 =
                               let int_typ = FStar_Tests_Pars.tc "int" in
                               let x1 =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None int_typ in
                               let typ = FStar_Tests_Pars.tc "pure_post unit" in
                               let l =
                                 FStar_Tests_Pars.tc
                                   "fun (q:pure_post unit) -> q ()" in
                               let q =
                                 FStar_Syntax_Syntax.new_bv
                                   FStar_Pervasives_Native.None typ in
                               let tm14 =
                                 let uu____711 =
                                   let uu____712 =
                                     let uu____715 =
                                       FStar_Syntax_Syntax.bv_to_name q in
                                     [uu____715] in
                                   FStar_Tests_Util.app l uu____712 in
                                 norm uu____711 in
                               let l1 =
                                 FStar_Tests_Pars.tc
                                   "fun (p:pure_post unit) -> p" in
                               let unit = FStar_Tests_Pars.tc "()" in
                               let env =
                                 let uu____719 = FStar_Tests_Pars.init () in
                                 let uu____720 =
                                   let uu____721 =
                                     FStar_Syntax_Syntax.mk_binder x1 in
                                   let uu____728 =
                                     let uu____737 =
                                       FStar_Syntax_Syntax.mk_binder q in
                                     [uu____737] in
                                   uu____721 :: uu____728 in
                                 FStar_TypeChecker_Env.push_binders uu____719
                                   uu____720 in
                               let uu____762 =
                                 FStar_TypeChecker_Util.new_implicit_var ""
                                   FStar_Range.dummyRange env typ in
                               match uu____762 with
                               | (u_p, uu____784, uu____785) ->
                                   let tm23 =
                                     let uu____801 =
                                       let uu____804 =
                                         FStar_Tests_Util.app l1 [u_p] in
                                       norm uu____804 in
                                     FStar_Tests_Util.app uu____801 [unit] in
                                   (tm14, tm23) in
                             match uu____696 with
                             | (tm14, tm23) ->
                                 (unify1 (Prims.of_int (14)) tm14 tm23
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_Options.__clear_unit_tests ();
                                  (let uu____822 = FStar_ST.op_Bang success in
                                   if uu____822
                                   then
                                     FStar_Util.print_string "Unifier ok\n"
                                   else ());
                                  FStar_ST.op_Bang success))))))))))))))