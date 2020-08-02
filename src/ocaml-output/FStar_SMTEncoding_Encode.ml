open Prims
let (norm_before_encoding :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.Eager_unfolding;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta] in
      let uu____15 =
        let uu____18 =
          let uu____19 =
            FStar_TypeChecker_Env.current_module
              env.FStar_SMTEncoding_Env.tcenv in
          FStar_Ident.string_of_lid uu____19 in
        FStar_Pervasives_Native.Some uu____18 in
      FStar_Profiling.profile
        (fun uu____21 ->
           FStar_TypeChecker_Normalize.normalize steps
             env.FStar_SMTEncoding_Env.tcenv t) uu____15
        "FStar.TypeChecker.SMTEncoding.Encode.norm_before_encoding"
let (norm_with_steps :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t ->
        let uu____37 =
          let uu____40 =
            let uu____41 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____41 in
          FStar_Pervasives_Native.Some uu____40 in
        FStar_Profiling.profile
          (fun uu____43 -> FStar_TypeChecker_Normalize.normalize steps env t)
          uu____37 "FStar.TypeChecker.SMTEncoding.Encode.norm"
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term * Prims.int *
          FStar_SMTEncoding_Term.decl Prims.list)
    ;
  is: FStar_Ident.lident -> Prims.bool }
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term * Prims.int *
          FStar_SMTEncoding_Term.decl Prims.list))
  = fun projectee -> match projectee with | { mk; is;_} -> mk
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee -> match projectee with | { mk; is;_} -> is
let (prims : prims_t) =
  let module_name = "Prims" in
  let uu____163 =
    FStar_SMTEncoding_Env.fresh_fvar module_name "a"
      FStar_SMTEncoding_Term.Term_sort in
  match uu____163 with
  | (asym, a) ->
      let uu____170 =
        FStar_SMTEncoding_Env.fresh_fvar module_name "x"
          FStar_SMTEncoding_Term.Term_sort in
      (match uu____170 with
       | (xsym, x) ->
           let uu____177 =
             FStar_SMTEncoding_Env.fresh_fvar module_name "y"
               FStar_SMTEncoding_Term.Term_sort in
           (match uu____177 with
            | (ysym, y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____242 =
                      let uu____253 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_SMTEncoding_Term.fv_sort) in
                      (x1, uu____253, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____242 in
                  let xtok = Prims.op_Hat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____267 =
                      let uu____274 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____274) in
                    FStar_SMTEncoding_Util.mkApp uu____267 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars in
                  let tot_fun_axioms =
                    let all_vars_but_one =
                      FStar_All.pipe_right (FStar_Util.prefix vars)
                        FStar_Pervasives_Native.fst in
                    let axiom_name = Prims.op_Hat "primitive_tot_fun_" x1 in
                    let tot_fun_axiom_for_x =
                      let uu____349 =
                        let uu____356 =
                          FStar_SMTEncoding_Term.mk_IsTotFun xtok1 in
                        (uu____356, FStar_Pervasives_Native.None, axiom_name) in
                      FStar_SMTEncoding_Util.mkAssume uu____349 in
                    let uu____357 =
                      FStar_List.fold_left
                        (fun uu____405 ->
                           fun var ->
                             match uu____405 with
                             | (axioms, app, vars1) ->
                                 let app1 =
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply app
                                     [var] in
                                 let vars2 = FStar_List.append vars1 [var] in
                                 let axiom_name1 =
                                   let uu____509 =
                                     let uu____510 =
                                       let uu____511 =
                                         FStar_All.pipe_right vars2
                                           FStar_List.length in
                                       Prims.string_of_int uu____511 in
                                     Prims.op_Hat "." uu____510 in
                                   Prims.op_Hat axiom_name uu____509 in
                                 let uu____526 =
                                   let uu____529 =
                                     let uu____532 =
                                       let uu____533 =
                                         let uu____540 =
                                           let uu____541 =
                                             let uu____552 =
                                               FStar_SMTEncoding_Term.mk_IsTotFun
                                                 app1 in
                                             ([[app1]], vars2, uu____552) in
                                           FStar_SMTEncoding_Term.mkForall
                                             rng uu____541 in
                                         (uu____540,
                                           FStar_Pervasives_Native.None,
                                           axiom_name1) in
                                       FStar_SMTEncoding_Util.mkAssume
                                         uu____533 in
                                     [uu____532] in
                                   FStar_List.append axioms uu____529 in
                                 (uu____526, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one in
                    match uu____357 with
                    | (axioms, uu____590, uu____591) -> axioms in
                  let uu____612 =
                    let uu____615 =
                      let uu____618 =
                        let uu____621 =
                          let uu____624 =
                            let uu____625 =
                              let uu____632 =
                                let uu____633 =
                                  let uu____644 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                  ([[xapp]], vars, uu____644) in
                                FStar_SMTEncoding_Term.mkForall rng uu____633 in
                              (uu____632, FStar_Pervasives_Native.None,
                                (Prims.op_Hat "primitive_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____625 in
                          [uu____624] in
                        xtok_decl :: uu____621 in
                      xname_decl :: uu____618 in
                    let uu____653 =
                      let uu____656 =
                        let uu____659 =
                          let uu____660 =
                            let uu____667 =
                              let uu____668 =
                                let uu____679 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp) in
                                ([[xtok_app]], vars, uu____679) in
                              FStar_SMTEncoding_Term.mkForall rng uu____668 in
                            (uu____667,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.op_Hat "token_correspondence_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____660 in
                        [uu____659] in
                      FStar_List.append tot_fun_axioms uu____656 in
                    FStar_List.append uu____615 uu____653 in
                  (xtok1, (FStar_List.length vars), uu____612) in
                let axy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(asym, FStar_SMTEncoding_Term.Term_sort);
                    (xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort);
                    (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx =
                  FStar_List.map FStar_SMTEncoding_Term.mk_fv
                    [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims =
                  let uu____810 =
                    let uu____829 =
                      let uu____846 =
                        let uu____847 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____847 in
                      quant axy uu____846 in
                    (FStar_Parser_Const.op_Eq, uu____829) in
                  let uu____862 =
                    let uu____883 =
                      let uu____902 =
                        let uu____919 =
                          let uu____920 =
                            let uu____921 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____921 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____920 in
                        quant axy uu____919 in
                      (FStar_Parser_Const.op_notEq, uu____902) in
                    let uu____936 =
                      let uu____957 =
                        let uu____976 =
                          let uu____993 =
                            let uu____994 =
                              let uu____995 =
                                let uu____1000 =
                                  FStar_SMTEncoding_Term.unboxBool x in
                                let uu____1001 =
                                  FStar_SMTEncoding_Term.unboxBool y in
                                (uu____1000, uu____1001) in
                              FStar_SMTEncoding_Util.mkAnd uu____995 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____994 in
                          quant xy uu____993 in
                        (FStar_Parser_Const.op_And, uu____976) in
                      let uu____1016 =
                        let uu____1037 =
                          let uu____1056 =
                            let uu____1073 =
                              let uu____1074 =
                                let uu____1075 =
                                  let uu____1080 =
                                    FStar_SMTEncoding_Term.unboxBool x in
                                  let uu____1081 =
                                    FStar_SMTEncoding_Term.unboxBool y in
                                  (uu____1080, uu____1081) in
                                FStar_SMTEncoding_Util.mkOr uu____1075 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____1074 in
                            quant xy uu____1073 in
                          (FStar_Parser_Const.op_Or, uu____1056) in
                        let uu____1096 =
                          let uu____1117 =
                            let uu____1136 =
                              let uu____1153 =
                                let uu____1154 =
                                  let uu____1155 =
                                    FStar_SMTEncoding_Term.unboxBool x in
                                  FStar_SMTEncoding_Util.mkNot uu____1155 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____1154 in
                              quant qx uu____1153 in
                            (FStar_Parser_Const.op_Negation, uu____1136) in
                          let uu____1170 =
                            let uu____1191 =
                              let uu____1210 =
                                let uu____1227 =
                                  let uu____1228 =
                                    let uu____1229 =
                                      let uu____1234 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____1235 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____1234, uu____1235) in
                                    FStar_SMTEncoding_Util.mkLT uu____1229 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____1228 in
                                quant xy uu____1227 in
                              (FStar_Parser_Const.op_LT, uu____1210) in
                            let uu____1250 =
                              let uu____1271 =
                                let uu____1290 =
                                  let uu____1307 =
                                    let uu____1308 =
                                      let uu____1309 =
                                        let uu____1314 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____1315 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____1314, uu____1315) in
                                      FStar_SMTEncoding_Util.mkLTE uu____1309 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxBool
                                      uu____1308 in
                                  quant xy uu____1307 in
                                (FStar_Parser_Const.op_LTE, uu____1290) in
                              let uu____1330 =
                                let uu____1351 =
                                  let uu____1370 =
                                    let uu____1387 =
                                      let uu____1388 =
                                        let uu____1389 =
                                          let uu____1394 =
                                            FStar_SMTEncoding_Term.unboxInt x in
                                          let uu____1395 =
                                            FStar_SMTEncoding_Term.unboxInt y in
                                          (uu____1394, uu____1395) in
                                        FStar_SMTEncoding_Util.mkGT
                                          uu____1389 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxBool
                                        uu____1388 in
                                    quant xy uu____1387 in
                                  (FStar_Parser_Const.op_GT, uu____1370) in
                                let uu____1410 =
                                  let uu____1431 =
                                    let uu____1450 =
                                      let uu____1467 =
                                        let uu____1468 =
                                          let uu____1469 =
                                            let uu____1474 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____1475 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____1474, uu____1475) in
                                          FStar_SMTEncoding_Util.mkGTE
                                            uu____1469 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxBool
                                          uu____1468 in
                                      quant xy uu____1467 in
                                    (FStar_Parser_Const.op_GTE, uu____1450) in
                                  let uu____1490 =
                                    let uu____1511 =
                                      let uu____1530 =
                                        let uu____1547 =
                                          let uu____1548 =
                                            let uu____1549 =
                                              let uu____1554 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____1555 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____1554, uu____1555) in
                                            FStar_SMTEncoding_Util.mkSub
                                              uu____1549 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1548 in
                                        quant xy uu____1547 in
                                      (FStar_Parser_Const.op_Subtraction,
                                        uu____1530) in
                                    let uu____1570 =
                                      let uu____1591 =
                                        let uu____1610 =
                                          let uu____1627 =
                                            let uu____1628 =
                                              let uu____1629 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              FStar_SMTEncoding_Util.mkMinus
                                                uu____1629 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1628 in
                                          quant qx uu____1627 in
                                        (FStar_Parser_Const.op_Minus,
                                          uu____1610) in
                                      let uu____1644 =
                                        let uu____1665 =
                                          let uu____1684 =
                                            let uu____1701 =
                                              let uu____1702 =
                                                let uu____1703 =
                                                  let uu____1708 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____1709 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____1708, uu____1709) in
                                                FStar_SMTEncoding_Util.mkAdd
                                                  uu____1703 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1702 in
                                            quant xy uu____1701 in
                                          (FStar_Parser_Const.op_Addition,
                                            uu____1684) in
                                        let uu____1724 =
                                          let uu____1745 =
                                            let uu____1764 =
                                              let uu____1781 =
                                                let uu____1782 =
                                                  let uu____1783 =
                                                    let uu____1788 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        x in
                                                    let uu____1789 =
                                                      FStar_SMTEncoding_Term.unboxInt
                                                        y in
                                                    (uu____1788, uu____1789) in
                                                  FStar_SMTEncoding_Util.mkMul
                                                    uu____1783 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxInt
                                                  uu____1782 in
                                              quant xy uu____1781 in
                                            (FStar_Parser_Const.op_Multiply,
                                              uu____1764) in
                                          let uu____1804 =
                                            let uu____1825 =
                                              let uu____1844 =
                                                let uu____1861 =
                                                  let uu____1862 =
                                                    let uu____1863 =
                                                      let uu____1868 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          x in
                                                      let uu____1869 =
                                                        FStar_SMTEncoding_Term.unboxInt
                                                          y in
                                                      (uu____1868,
                                                        uu____1869) in
                                                    FStar_SMTEncoding_Util.mkDiv
                                                      uu____1863 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxInt
                                                    uu____1862 in
                                                quant xy uu____1861 in
                                              (FStar_Parser_Const.op_Division,
                                                uu____1844) in
                                            let uu____1884 =
                                              let uu____1905 =
                                                let uu____1924 =
                                                  let uu____1941 =
                                                    let uu____1942 =
                                                      let uu____1943 =
                                                        let uu____1948 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            x in
                                                        let uu____1949 =
                                                          FStar_SMTEncoding_Term.unboxInt
                                                            y in
                                                        (uu____1948,
                                                          uu____1949) in
                                                      FStar_SMTEncoding_Util.mkMod
                                                        uu____1943 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxInt
                                                      uu____1942 in
                                                  quant xy uu____1941 in
                                                (FStar_Parser_Const.op_Modulus,
                                                  uu____1924) in
                                              let uu____1964 =
                                                let uu____1985 =
                                                  let uu____2004 =
                                                    let uu____2021 =
                                                      let uu____2022 =
                                                        let uu____2023 =
                                                          let uu____2028 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              x in
                                                          let uu____2029 =
                                                            FStar_SMTEncoding_Term.unboxReal
                                                              y in
                                                          (uu____2028,
                                                            uu____2029) in
                                                        FStar_SMTEncoding_Util.mkLT
                                                          uu____2023 in
                                                      FStar_All.pipe_left
                                                        FStar_SMTEncoding_Term.boxBool
                                                        uu____2022 in
                                                    quant xy uu____2021 in
                                                  (FStar_Parser_Const.real_op_LT,
                                                    uu____2004) in
                                                let uu____2044 =
                                                  let uu____2065 =
                                                    let uu____2084 =
                                                      let uu____2101 =
                                                        let uu____2102 =
                                                          let uu____2103 =
                                                            let uu____2108 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                x in
                                                            let uu____2109 =
                                                              FStar_SMTEncoding_Term.unboxReal
                                                                y in
                                                            (uu____2108,
                                                              uu____2109) in
                                                          FStar_SMTEncoding_Util.mkLTE
                                                            uu____2103 in
                                                        FStar_All.pipe_left
                                                          FStar_SMTEncoding_Term.boxBool
                                                          uu____2102 in
                                                      quant xy uu____2101 in
                                                    (FStar_Parser_Const.real_op_LTE,
                                                      uu____2084) in
                                                  let uu____2124 =
                                                    let uu____2145 =
                                                      let uu____2164 =
                                                        let uu____2181 =
                                                          let uu____2182 =
                                                            let uu____2183 =
                                                              let uu____2188
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  x in
                                                              let uu____2189
                                                                =
                                                                FStar_SMTEncoding_Term.unboxReal
                                                                  y in
                                                              (uu____2188,
                                                                uu____2189) in
                                                            FStar_SMTEncoding_Util.mkGT
                                                              uu____2183 in
                                                          FStar_All.pipe_left
                                                            FStar_SMTEncoding_Term.boxBool
                                                            uu____2182 in
                                                        quant xy uu____2181 in
                                                      (FStar_Parser_Const.real_op_GT,
                                                        uu____2164) in
                                                    let uu____2204 =
                                                      let uu____2225 =
                                                        let uu____2244 =
                                                          let uu____2261 =
                                                            let uu____2262 =
                                                              let uu____2263
                                                                =
                                                                let uu____2268
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                let uu____2269
                                                                  =
                                                                  FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                (uu____2268,
                                                                  uu____2269) in
                                                              FStar_SMTEncoding_Util.mkGTE
                                                                uu____2263 in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____2262 in
                                                          quant xy uu____2261 in
                                                        (FStar_Parser_Const.real_op_GTE,
                                                          uu____2244) in
                                                      let uu____2284 =
                                                        let uu____2305 =
                                                          let uu____2324 =
                                                            let uu____2341 =
                                                              let uu____2342
                                                                =
                                                                let uu____2343
                                                                  =
                                                                  let uu____2348
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                  let uu____2349
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                  (uu____2348,
                                                                    uu____2349) in
                                                                FStar_SMTEncoding_Util.mkSub
                                                                  uu____2343 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxReal
                                                                uu____2342 in
                                                            quant xy
                                                              uu____2341 in
                                                          (FStar_Parser_Const.real_op_Subtraction,
                                                            uu____2324) in
                                                        let uu____2364 =
                                                          let uu____2385 =
                                                            let uu____2404 =
                                                              let uu____2421
                                                                =
                                                                let uu____2422
                                                                  =
                                                                  let uu____2423
                                                                    =
                                                                    let uu____2428
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu____2429
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu____2428,
                                                                    uu____2429) in
                                                                  FStar_SMTEncoding_Util.mkAdd
                                                                    uu____2423 in
                                                                FStar_All.pipe_left
                                                                  FStar_SMTEncoding_Term.boxReal
                                                                  uu____2422 in
                                                              quant xy
                                                                uu____2421 in
                                                            (FStar_Parser_Const.real_op_Addition,
                                                              uu____2404) in
                                                          let uu____2444 =
                                                            let uu____2465 =
                                                              let uu____2484
                                                                =
                                                                let uu____2501
                                                                  =
                                                                  let uu____2502
                                                                    =
                                                                    let uu____2503
                                                                    =
                                                                    let uu____2508
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu____2509
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu____2508,
                                                                    uu____2509) in
                                                                    FStar_SMTEncoding_Util.mkMul
                                                                    uu____2503 in
                                                                  FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2502 in
                                                                quant xy
                                                                  uu____2501 in
                                                              (FStar_Parser_Const.real_op_Multiply,
                                                                uu____2484) in
                                                            let uu____2524 =
                                                              let uu____2545
                                                                =
                                                                let uu____2564
                                                                  =
                                                                  let uu____2581
                                                                    =
                                                                    let uu____2582
                                                                    =
                                                                    let uu____2583
                                                                    =
                                                                    let uu____2588
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu____2589
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu____2588,
                                                                    uu____2589) in
                                                                    FStar_SMTEncoding_Util.mkRealDiv
                                                                    uu____2583 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2582 in
                                                                  quant xy
                                                                    uu____2581 in
                                                                (FStar_Parser_Const.real_op_Division,
                                                                  uu____2564) in
                                                              let uu____2604
                                                                =
                                                                let uu____2625
                                                                  =
                                                                  let uu____2644
                                                                    =
                                                                    let uu____2661
                                                                    =
                                                                    let uu____2662
                                                                    =
                                                                    let uu____2663
                                                                    =
                                                                    FStar_SMTEncoding_Term.unboxInt
                                                                    x in
                                                                    FStar_SMTEncoding_Term.mkRealOfInt
                                                                    uu____2663
                                                                    FStar_Range.dummyRange in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxReal
                                                                    uu____2662 in
                                                                    quant qx
                                                                    uu____2661 in
                                                                  (FStar_Parser_Const.real_of_int,
                                                                    uu____2644) in
                                                                [uu____2625] in
                                                              uu____2545 ::
                                                                uu____2604 in
                                                            uu____2465 ::
                                                              uu____2524 in
                                                          uu____2385 ::
                                                            uu____2444 in
                                                        uu____2305 ::
                                                          uu____2364 in
                                                      uu____2225 ::
                                                        uu____2284 in
                                                    uu____2145 :: uu____2204 in
                                                  uu____2065 :: uu____2124 in
                                                uu____1985 :: uu____2044 in
                                              uu____1905 :: uu____1964 in
                                            uu____1825 :: uu____1884 in
                                          uu____1745 :: uu____1804 in
                                        uu____1665 :: uu____1724 in
                                      uu____1591 :: uu____1644 in
                                    uu____1511 :: uu____1570 in
                                  uu____1431 :: uu____1490 in
                                uu____1351 :: uu____1410 in
                              uu____1271 :: uu____1330 in
                            uu____1191 :: uu____1250 in
                          uu____1117 :: uu____1170 in
                        uu____1037 :: uu____1096 in
                      uu____957 :: uu____1016 in
                    uu____883 :: uu____936 in
                  uu____810 :: uu____862 in
                let mk l v =
                  let uu____3147 =
                    let uu____3158 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____3240 ->
                              match uu____3240 with
                              | (l', uu____3258) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____3158
                      (FStar_Option.map
                         (fun uu____3347 ->
                            match uu____3347 with
                            | (uu____3372, b) ->
                                let uu____3402 = FStar_Ident.range_of_lid l in
                                b uu____3402 v)) in
                  FStar_All.pipe_right uu____3147 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____3476 ->
                          match uu____3476 with
                          | (l', uu____3494) -> FStar_Ident.lid_equals l l')) in
                { mk; is }))
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string * FStar_SMTEncoding_Term.sort * Prims.bool) Prims.list
          -> FStar_SMTEncoding_Term.decl)
  =
  fun rng ->
    fun env ->
      fun tapp ->
        fun vars ->
          let uu____3559 =
            FStar_SMTEncoding_Env.fresh_fvar
              env.FStar_SMTEncoding_Env.current_module_name "x"
              FStar_SMTEncoding_Term.Term_sort in
          match uu____3559 with
          | (xxsym, xx) ->
              let uu____3566 =
                FStar_SMTEncoding_Env.fresh_fvar
                  env.FStar_SMTEncoding_Env.current_module_name "f"
                  FStar_SMTEncoding_Term.Fuel_sort in
              (match uu____3566 with
               | (ffsym, ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name in
                   let uu____3576 =
                     let uu____3583 =
                       let uu____3584 =
                         let uu____3595 =
                           let uu____3596 =
                             FStar_SMTEncoding_Term.mk_fv
                               (xxsym, FStar_SMTEncoding_Term.Term_sort) in
                           let uu____3603 =
                             let uu____3612 =
                               FStar_SMTEncoding_Term.mk_fv
                                 (ffsym, FStar_SMTEncoding_Term.Fuel_sort) in
                             uu____3612 :: vars in
                           uu____3596 :: uu____3603 in
                         let uu____3631 =
                           let uu____3632 =
                             let uu____3637 =
                               let uu____3638 =
                                 let uu____3643 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx]) in
                                 (tapp, uu____3643) in
                               FStar_SMTEncoding_Util.mkEq uu____3638 in
                             (xx_has_type, uu____3637) in
                           FStar_SMTEncoding_Util.mkImp uu____3632 in
                         ([[xx_has_type]], uu____3595, uu____3631) in
                       FStar_SMTEncoding_Term.mkForall rng uu____3584 in
                     let uu____3654 =
                       let uu____3655 =
                         let uu____3656 =
                           let uu____3657 =
                             FStar_Util.digest_of_string tapp_hash in
                           Prims.op_Hat "_pretyping_" uu____3657 in
                         Prims.op_Hat module_name uu____3656 in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____3655 in
                     (uu____3583, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____3654) in
                   FStar_SMTEncoding_Util.mkAssume uu____3576)
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx =
    FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy =
    FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mkForall_fuel env =
    let uu____3702 =
      let uu____3703 = FStar_TypeChecker_Env.current_module env in
      FStar_Ident.string_of_lid uu____3703 in
    FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3702 in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____3723 =
      let uu____3724 =
        let uu____3731 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____3731, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____3724 in
    let uu____3732 =
      let uu____3735 =
        let uu____3736 =
          let uu____3743 =
            let uu____3744 =
              let uu____3755 =
                let uu____3756 =
                  let uu____3761 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____3761) in
                FStar_SMTEncoding_Util.mkImp uu____3756 in
              ([[typing_pred]], [xx], uu____3755) in
            let uu____3782 =
              let uu____3797 = FStar_TypeChecker_Env.get_range env in
              let uu____3798 = mkForall_fuel env in uu____3798 uu____3797 in
            uu____3782 uu____3744 in
          (uu____3743, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____3736 in
      [uu____3735] in
    uu____3723 :: uu____3732 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____3837 =
      let uu____3838 =
        let uu____3845 =
          let uu____3846 = FStar_TypeChecker_Env.get_range env in
          let uu____3847 =
            let uu____3858 =
              let uu____3863 =
                let uu____3866 = FStar_SMTEncoding_Term.boxBool b in
                [uu____3866] in
              [uu____3863] in
            let uu____3871 =
              let uu____3872 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____3872 tt in
            (uu____3858, [bb], uu____3871) in
          FStar_SMTEncoding_Term.mkForall uu____3846 uu____3847 in
        (uu____3845, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____3838 in
    let uu____3889 =
      let uu____3892 =
        let uu____3893 =
          let uu____3900 =
            let uu____3901 =
              let uu____3912 =
                let uu____3913 =
                  let uu____3918 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____3918) in
                FStar_SMTEncoding_Util.mkImp uu____3913 in
              ([[typing_pred]], [xx], uu____3912) in
            let uu____3939 =
              let uu____3954 = FStar_TypeChecker_Env.get_range env in
              let uu____3955 = mkForall_fuel env in uu____3955 uu____3954 in
            uu____3939 uu____3901 in
          (uu____3900, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____3893 in
      [uu____3892] in
    uu____3837 :: uu____3889 in
  let mk_int env nm tt =
    let lex_t =
      let uu____3992 =
        let uu____3993 =
          let uu____3998 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid in
          (uu____3998, FStar_SMTEncoding_Term.Term_sort) in
        FStar_SMTEncoding_Term.mk_fv uu____3993 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3992 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes_y_x =
      let uu____4006 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4006 in
    let uu____4009 =
      let uu____4010 =
        let uu____4017 =
          let uu____4018 = FStar_TypeChecker_Env.get_range env in
          let uu____4019 =
            let uu____4030 =
              let uu____4035 =
                let uu____4038 = FStar_SMTEncoding_Term.boxInt b in
                [uu____4038] in
              [uu____4035] in
            let uu____4043 =
              let uu____4044 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____4044 tt in
            (uu____4030, [bb], uu____4043) in
          FStar_SMTEncoding_Term.mkForall uu____4018 uu____4019 in
        (uu____4017, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____4010 in
    let uu____4061 =
      let uu____4064 =
        let uu____4065 =
          let uu____4072 =
            let uu____4073 =
              let uu____4084 =
                let uu____4085 =
                  let uu____4090 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____4090) in
                FStar_SMTEncoding_Util.mkImp uu____4085 in
              ([[typing_pred]], [xx], uu____4084) in
            let uu____4111 =
              let uu____4126 = FStar_TypeChecker_Env.get_range env in
              let uu____4127 = mkForall_fuel env in uu____4127 uu____4126 in
            uu____4111 uu____4073 in
          (uu____4072, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____4065 in
      let uu____4145 =
        let uu____4148 =
          let uu____4149 =
            let uu____4156 =
              let uu____4157 =
                let uu____4168 =
                  let uu____4169 =
                    let uu____4174 =
                      let uu____4175 =
                        let uu____4178 =
                          let uu____4181 =
                            let uu____4184 =
                              let uu____4185 =
                                let uu____4190 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____4191 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    Prims.int_zero in
                                (uu____4190, uu____4191) in
                              FStar_SMTEncoding_Util.mkGT uu____4185 in
                            let uu____4192 =
                              let uu____4195 =
                                let uu____4196 =
                                  let uu____4201 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____4202 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      Prims.int_zero in
                                  (uu____4201, uu____4202) in
                                FStar_SMTEncoding_Util.mkGTE uu____4196 in
                              let uu____4203 =
                                let uu____4206 =
                                  let uu____4207 =
                                    let uu____4212 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____4213 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____4212, uu____4213) in
                                  FStar_SMTEncoding_Util.mkLT uu____4207 in
                                [uu____4206] in
                              uu____4195 :: uu____4203 in
                            uu____4184 :: uu____4192 in
                          typing_pred_y :: uu____4181 in
                        typing_pred :: uu____4178 in
                      FStar_SMTEncoding_Util.mk_and_l uu____4175 in
                    (uu____4174, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____4169 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4168) in
              let uu____4240 =
                let uu____4255 = FStar_TypeChecker_Env.get_range env in
                let uu____4256 = mkForall_fuel env in uu____4256 uu____4255 in
              uu____4240 uu____4157 in
            (uu____4156,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____4149 in
        [uu____4148] in
      uu____4064 :: uu____4145 in
    uu____4009 :: uu____4061 in
  let mk_real env nm tt =
    let lex_t =
      let uu____4293 =
        let uu____4294 =
          let uu____4299 =
            FStar_Ident.string_of_lid FStar_Parser_Const.lex_t_lid in
          (uu____4299, FStar_SMTEncoding_Term.Term_sort) in
        FStar_SMTEncoding_Term.mk_fv uu____4294 in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4293 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa =
      FStar_SMTEncoding_Term.mk_fv
        ("a", (FStar_SMTEncoding_Term.Sort "Real")) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStar_SMTEncoding_Term.mk_fv
        ("b", (FStar_SMTEncoding_Term.Sort "Real")) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes_y_x =
      let uu____4307 =
        FStar_SMTEncoding_Util.mkApp ("Prims.precedes", [lex_t; lex_t; y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____4307 in
    let uu____4310 =
      let uu____4311 =
        let uu____4318 =
          let uu____4319 = FStar_TypeChecker_Env.get_range env in
          let uu____4320 =
            let uu____4331 =
              let uu____4336 =
                let uu____4339 = FStar_SMTEncoding_Term.boxReal b in
                [uu____4339] in
              [uu____4336] in
            let uu____4344 =
              let uu____4345 = FStar_SMTEncoding_Term.boxReal b in
              FStar_SMTEncoding_Term.mk_HasType uu____4345 tt in
            (uu____4331, [bb], uu____4344) in
          FStar_SMTEncoding_Term.mkForall uu____4319 uu____4320 in
        (uu____4318, (FStar_Pervasives_Native.Some "real typing"),
          "real_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____4311 in
    let uu____4362 =
      let uu____4365 =
        let uu____4366 =
          let uu____4373 =
            let uu____4374 =
              let uu____4385 =
                let uu____4386 =
                  let uu____4391 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxRealFun) x in
                  (typing_pred, uu____4391) in
                FStar_SMTEncoding_Util.mkImp uu____4386 in
              ([[typing_pred]], [xx], uu____4385) in
            let uu____4412 =
              let uu____4427 = FStar_TypeChecker_Env.get_range env in
              let uu____4428 = mkForall_fuel env in uu____4428 uu____4427 in
            uu____4412 uu____4374 in
          (uu____4373, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____4366 in
      let uu____4446 =
        let uu____4449 =
          let uu____4450 =
            let uu____4457 =
              let uu____4458 =
                let uu____4469 =
                  let uu____4470 =
                    let uu____4475 =
                      let uu____4476 =
                        let uu____4479 =
                          let uu____4482 =
                            let uu____4485 =
                              let uu____4486 =
                                let uu____4491 =
                                  FStar_SMTEncoding_Term.unboxReal x in
                                let uu____4492 =
                                  FStar_SMTEncoding_Util.mkReal "0.0" in
                                (uu____4491, uu____4492) in
                              FStar_SMTEncoding_Util.mkGT uu____4486 in
                            let uu____4493 =
                              let uu____4496 =
                                let uu____4497 =
                                  let uu____4502 =
                                    FStar_SMTEncoding_Term.unboxReal y in
                                  let uu____4503 =
                                    FStar_SMTEncoding_Util.mkReal "0.0" in
                                  (uu____4502, uu____4503) in
                                FStar_SMTEncoding_Util.mkGTE uu____4497 in
                              let uu____4504 =
                                let uu____4507 =
                                  let uu____4508 =
                                    let uu____4513 =
                                      FStar_SMTEncoding_Term.unboxReal y in
                                    let uu____4514 =
                                      FStar_SMTEncoding_Term.unboxReal x in
                                    (uu____4513, uu____4514) in
                                  FStar_SMTEncoding_Util.mkLT uu____4508 in
                                [uu____4507] in
                              uu____4496 :: uu____4504 in
                            uu____4485 :: uu____4493 in
                          typing_pred_y :: uu____4482 in
                        typing_pred :: uu____4479 in
                      FStar_SMTEncoding_Util.mk_and_l uu____4476 in
                    (uu____4475, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____4470 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____4469) in
              let uu____4541 =
                let uu____4556 = FStar_TypeChecker_Env.get_range env in
                let uu____4557 = mkForall_fuel env in uu____4557 uu____4556 in
              uu____4541 uu____4458 in
            (uu____4457,
              (FStar_Pervasives_Native.Some "well-founded ordering on real"),
              "well-founded-ordering-on-real") in
          FStar_SMTEncoding_Util.mkAssume uu____4450 in
        [uu____4449] in
      uu____4365 :: uu____4446 in
    uu____4310 :: uu____4362 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____4596 =
      let uu____4597 =
        let uu____4604 =
          let uu____4605 = FStar_TypeChecker_Env.get_range env in
          let uu____4606 =
            let uu____4617 =
              let uu____4622 =
                let uu____4625 = FStar_SMTEncoding_Term.boxString b in
                [uu____4625] in
              [uu____4622] in
            let uu____4630 =
              let uu____4631 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____4631 tt in
            (uu____4617, [bb], uu____4630) in
          FStar_SMTEncoding_Term.mkForall uu____4605 uu____4606 in
        (uu____4604, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____4597 in
    let uu____4648 =
      let uu____4651 =
        let uu____4652 =
          let uu____4659 =
            let uu____4660 =
              let uu____4671 =
                let uu____4672 =
                  let uu____4677 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____4677) in
                FStar_SMTEncoding_Util.mkImp uu____4672 in
              ([[typing_pred]], [xx], uu____4671) in
            let uu____4698 =
              let uu____4713 = FStar_TypeChecker_Env.get_range env in
              let uu____4714 = mkForall_fuel env in uu____4714 uu____4713 in
            uu____4698 uu____4660 in
          (uu____4659, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____4652 in
      [uu____4651] in
    uu____4596 :: uu____4648 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    let uu____4753 =
      FStar_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp") in
    [uu____4753] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____4775 =
      let uu____4776 =
        let uu____4783 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____4783, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____4776 in
    [uu____4775] in
  let mk_and_interp env conj uu____4801 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____4818 =
      let uu____4819 =
        let uu____4826 =
          let uu____4827 = FStar_TypeChecker_Env.get_range env in
          let uu____4828 =
            let uu____4839 =
              let uu____4840 =
                let uu____4845 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____4845, valid) in
              FStar_SMTEncoding_Util.mkIff uu____4840 in
            ([[l_and_a_b]], [aa; bb], uu____4839) in
          FStar_SMTEncoding_Term.mkForall uu____4827 uu____4828 in
        (uu____4826, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____4819 in
    [uu____4818] in
  let mk_or_interp env disj uu____4889 =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____4906 =
      let uu____4907 =
        let uu____4914 =
          let uu____4915 = FStar_TypeChecker_Env.get_range env in
          let uu____4916 =
            let uu____4927 =
              let uu____4928 =
                let uu____4933 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____4933, valid) in
              FStar_SMTEncoding_Util.mkIff uu____4928 in
            ([[l_or_a_b]], [aa; bb], uu____4927) in
          FStar_SMTEncoding_Term.mkForall uu____4915 uu____4916 in
        (uu____4914, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____4907 in
    [uu____4906] in
  let mk_eq2_interp env eq2 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____4990 =
      let uu____4991 =
        let uu____4998 =
          let uu____4999 = FStar_TypeChecker_Env.get_range env in
          let uu____5000 =
            let uu____5011 =
              let uu____5012 =
                let uu____5017 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____5017, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5012 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____5011) in
          FStar_SMTEncoding_Term.mkForall uu____4999 uu____5000 in
        (uu____4998, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____4991 in
    [uu____4990] in
  let mk_eq3_interp env eq3 tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStar_SMTEncoding_Term.mk_fv ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____5082 =
      let uu____5083 =
        let uu____5090 =
          let uu____5091 = FStar_TypeChecker_Env.get_range env in
          let uu____5092 =
            let uu____5103 =
              let uu____5104 =
                let uu____5109 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____5109, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5104 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____5103) in
          FStar_SMTEncoding_Term.mkForall uu____5091 uu____5092 in
        (uu____5090, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5083 in
    [uu____5082] in
  let mk_imp_interp env imp tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____5182 =
      let uu____5183 =
        let uu____5190 =
          let uu____5191 = FStar_TypeChecker_Env.get_range env in
          let uu____5192 =
            let uu____5203 =
              let uu____5204 =
                let uu____5209 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____5209, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5204 in
            ([[l_imp_a_b]], [aa; bb], uu____5203) in
          FStar_SMTEncoding_Term.mkForall uu____5191 uu____5192 in
        (uu____5190, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5183 in
    [uu____5182] in
  let mk_iff_interp env iff tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb =
      FStar_SMTEncoding_Term.mk_fv ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____5270 =
      let uu____5271 =
        let uu____5278 =
          let uu____5279 = FStar_TypeChecker_Env.get_range env in
          let uu____5280 =
            let uu____5291 =
              let uu____5292 =
                let uu____5297 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____5297, valid) in
              FStar_SMTEncoding_Util.mkIff uu____5292 in
            ([[l_iff_a_b]], [aa; bb], uu____5291) in
          FStar_SMTEncoding_Term.mkForall uu____5279 uu____5280 in
        (uu____5278, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5271 in
    [uu____5270] in
  let mk_not_interp env l_not tt =
    let aa =
      FStar_SMTEncoding_Term.mk_fv ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____5351 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____5351 in
    let uu____5354 =
      let uu____5355 =
        let uu____5362 =
          let uu____5363 = FStar_TypeChecker_Env.get_range env in
          let uu____5364 =
            let uu____5375 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____5375) in
          FStar_SMTEncoding_Term.mkForall uu____5363 uu____5364 in
        (uu____5362, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5355 in
    [uu____5354] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____5417 =
      let uu____5418 =
        let uu____5425 =
          let uu____5426 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____5426 range_ty in
        let uu____5427 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const" in
        (uu____5425, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____5427) in
      FStar_SMTEncoding_Util.mkAssume uu____5418 in
    [uu____5417] in
  let mk_inversion_axiom env inversion tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 =
      FStar_SMTEncoding_Term.mk_fv ("x", FStar_SMTEncoding_Term.Term_sort) in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu____5459 = FStar_SMTEncoding_Term.n_fuel Prims.int_one in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____5459 x1 t in
      let uu____5460 = FStar_TypeChecker_Env.get_range env in
      let uu____5461 =
        let uu____5472 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____5472) in
      FStar_SMTEncoding_Term.mkForall uu____5460 uu____5461 in
    let uu____5493 =
      let uu____5494 =
        let uu____5501 =
          let uu____5502 = FStar_TypeChecker_Env.get_range env in
          let uu____5503 =
            let uu____5514 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____5514) in
          FStar_SMTEncoding_Term.mkForall uu____5502 uu____5503 in
        (uu____5501,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____5494 in
    [uu____5493] in
  let mk_with_type_axiom env with_type tt =
    let tt1 =
      FStar_SMTEncoding_Term.mk_fv ("t", FStar_SMTEncoding_Term.Term_sort) in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1 in
    let ee =
      FStar_SMTEncoding_Term.mk_fv ("e", FStar_SMTEncoding_Term.Term_sort) in
    let e = FStar_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type, [t; e]) in
    let uu____5560 =
      let uu____5561 =
        let uu____5568 =
          let uu____5569 = FStar_TypeChecker_Env.get_range env in
          let uu____5570 =
            let uu____5585 =
              let uu____5586 =
                let uu____5591 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu____5592 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu____5591, uu____5592) in
              FStar_SMTEncoding_Util.mkAnd uu____5586 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some Prims.int_zero), [tt1; ee],
              uu____5585) in
          FStar_SMTEncoding_Term.mkForall' uu____5569 uu____5570 in
        (uu____5568,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStar_SMTEncoding_Util.mkAssume uu____5561 in
    [uu____5560] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.real_lid, mk_real);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)] in
  fun env ->
    fun t ->
      fun s ->
        fun tt ->
          let uu____6100 =
            FStar_Util.find_opt
              (fun uu____6136 ->
                 match uu____6136 with
                 | (l, uu____6150) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____6100 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some (uu____6190, f) -> f env s tt
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decls_elt Prims.list)
  =
  fun env ->
    fun fv ->
      fun t ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____6247 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env in
        match uu____6247 with
        | (form, decls) ->
            let uu____6256 =
              let uu____6259 =
                let uu____6262 =
                  let uu____6263 =
                    let uu____6270 =
                      let uu____6271 =
                        let uu____6272 = FStar_Ident.string_of_lid lid in
                        Prims.op_Hat "Lemma: " uu____6272 in
                      FStar_Pervasives_Native.Some uu____6271 in
                    let uu____6273 =
                      let uu____6274 = FStar_Ident.string_of_lid lid in
                      Prims.op_Hat "lemma_" uu____6274 in
                    (form, uu____6270, uu____6273) in
                  FStar_SMTEncoding_Util.mkAssume uu____6263 in
                [uu____6262] in
              FStar_All.pipe_right uu____6259
                FStar_SMTEncoding_Term.mk_decls_trivial in
            FStar_List.append decls uu____6256
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted ->
    fun env ->
      fun fv ->
        fun tt ->
          fun t_norm ->
            fun quals ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let uu____6326 =
                ((let uu____6329 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_SMTEncoding_Util.is_smt_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____6329) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____6326
              then
                let arg_sorts =
                  let uu____6337 =
                    let uu____6338 = FStar_Syntax_Subst.compress t_norm in
                    uu____6338.FStar_Syntax_Syntax.n in
                  match uu____6337 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders, uu____6344) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____6382 ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____6389 -> [] in
                let arity = FStar_List.length arg_sorts in
                let uu____6391 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity in
                match uu____6391 with
                | (vname, vtok, env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function")) in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function")) in
                    let uu____6411 =
                      FStar_All.pipe_right [d; dd]
                        FStar_SMTEncoding_Term.mk_decls_trivial in
                    (uu____6411, env1)
              else
                (let uu____6415 = prims.is lid in
                 if uu____6415
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid in
                   let uu____6421 = prims.mk lid vname in
                   match uu____6421 with
                   | (tok, arity, definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok) in
                       let uu____6442 =
                         FStar_All.pipe_right definition
                           FStar_SMTEncoding_Term.mk_decls_trivial in
                       (uu____6442, env1)
                 else
                   (let encode_non_total_function_typ =
                      let uu____6447 = FStar_Ident.nsstr lid in
                      uu____6447 <> "Prims" in
                    let uu____6448 =
                      let uu____6467 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm in
                      match uu____6467 with
                      | (args, comp) ->
                          let comp1 =
                            let uu____6495 =
                              FStar_SMTEncoding_Util.is_smt_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp in
                            if uu____6495
                            then
                              let uu____6498 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___316_6501 =
                                     env.FStar_SMTEncoding_Env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___316_6501.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___316_6501.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___316_6501.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___316_6501.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___316_6501.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___316_6501.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___316_6501.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___316_6501.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___316_6501.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___316_6501.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___316_6501.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___316_6501.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___316_6501.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___316_6501.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___316_6501.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___316_6501.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___316_6501.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.use_eq_strict =
                                       (uu___316_6501.FStar_TypeChecker_Env.use_eq_strict);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___316_6501.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___316_6501.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___316_6501.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___316_6501.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___316_6501.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___316_6501.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___316_6501.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___316_6501.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___316_6501.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___316_6501.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___316_6501.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___316_6501.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___316_6501.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___316_6501.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___316_6501.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___316_6501.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___316_6501.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___316_6501.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___316_6501.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.mpreprocess =
                                       (uu___316_6501.FStar_TypeChecker_Env.mpreprocess);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___316_6501.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___316_6501.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___316_6501.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___316_6501.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___316_6501.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___316_6501.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___316_6501.FStar_TypeChecker_Env.erasable_types_tab);
                                     FStar_TypeChecker_Env.enable_defer_to_tac
                                       =
                                       (uu___316_6501.FStar_TypeChecker_Env.enable_defer_to_tac)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____6498
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____6521 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1 in
                            (args, uu____6521)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____6448 with
                    | (formals, (pre_opt, res_t)) ->
                        let mk_disc_proj_axioms guard encoded_res_t vapp vars
                          =
                          FStar_All.pipe_right quals
                            (FStar_List.collect
                               (fun uu___0_6626 ->
                                  match uu___0_6626 with
                                  | FStar_Syntax_Syntax.Discriminator d ->
                                      let uu____6630 = FStar_Util.prefix vars in
                                      (match uu____6630 with
                                       | (uu____6657, xxv) ->
                                           let xx =
                                             let uu____6688 =
                                               let uu____6689 =
                                                 let uu____6694 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv in
                                                 (uu____6694,
                                                   FStar_SMTEncoding_Term.Term_sort) in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____6689 in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____6688 in
                                           let uu____6695 =
                                             let uu____6696 =
                                               let uu____6703 =
                                                 let uu____6704 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv in
                                                 let uu____6705 =
                                                   let uu____6716 =
                                                     let uu____6717 =
                                                       let uu____6722 =
                                                         let uu____6723 =
                                                           let uu____6724 =
                                                             let uu____6725 =
                                                               FStar_Ident.string_of_lid
                                                                 d in
                                                             FStar_SMTEncoding_Env.escape
                                                               uu____6725 in
                                                           FStar_SMTEncoding_Term.mk_tester
                                                             uu____6724 xx in
                                                         FStar_All.pipe_left
                                                           FStar_SMTEncoding_Term.boxBool
                                                           uu____6723 in
                                                       (vapp, uu____6722) in
                                                     FStar_SMTEncoding_Util.mkEq
                                                       uu____6717 in
                                                   ([[vapp]], vars,
                                                     uu____6716) in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____6704 uu____6705 in
                                               let uu____6734 =
                                                 let uu____6735 =
                                                   let uu____6736 =
                                                     FStar_Ident.string_of_lid
                                                       d in
                                                   FStar_SMTEncoding_Env.escape
                                                     uu____6736 in
                                                 Prims.op_Hat
                                                   "disc_equation_"
                                                   uu____6735 in
                                               (uu____6703,
                                                 (FStar_Pervasives_Native.Some
                                                    "Discriminator equation"),
                                                 uu____6734) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6696 in
                                           [uu____6695])
                                  | FStar_Syntax_Syntax.Projector (d, f) ->
                                      let uu____6739 = FStar_Util.prefix vars in
                                      (match uu____6739 with
                                       | (uu____6766, xxv) ->
                                           let xx =
                                             let uu____6797 =
                                               let uu____6798 =
                                                 let uu____6803 =
                                                   FStar_SMTEncoding_Term.fv_name
                                                     xxv in
                                                 (uu____6803,
                                                   FStar_SMTEncoding_Term.Term_sort) in
                                               FStar_SMTEncoding_Term.mk_fv
                                                 uu____6798 in
                                             FStar_All.pipe_left
                                               FStar_SMTEncoding_Util.mkFreeV
                                               uu____6797 in
                                           let f1 =
                                             {
                                               FStar_Syntax_Syntax.ppname = f;
                                               FStar_Syntax_Syntax.index =
                                                 Prims.int_zero;
                                               FStar_Syntax_Syntax.sort =
                                                 FStar_Syntax_Syntax.tun
                                             } in
                                           let tp_name =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d f1 in
                                           let prim_app =
                                             FStar_SMTEncoding_Util.mkApp
                                               (tp_name, [xx]) in
                                           let uu____6809 =
                                             let uu____6810 =
                                               let uu____6817 =
                                                 let uu____6818 =
                                                   FStar_Syntax_Syntax.range_of_fv
                                                     fv in
                                                 let uu____6819 =
                                                   let uu____6830 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (vapp, prim_app) in
                                                   ([[vapp]], vars,
                                                     uu____6830) in
                                                 FStar_SMTEncoding_Term.mkForall
                                                   uu____6818 uu____6819 in
                                               (uu____6817,
                                                 (FStar_Pervasives_Native.Some
                                                    "Projector equation"),
                                                 (Prims.op_Hat
                                                    "proj_equation_" tp_name)) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6810 in
                                           [uu____6809])
                                  | uu____6839 -> [])) in
                        let uu____6840 =
                          FStar_SMTEncoding_EncodeTerm.encode_binders
                            FStar_Pervasives_Native.None formals env in
                        (match uu____6840 with
                         | (vars, guards, env', decls1, uu____6865) ->
                             let uu____6878 =
                               match pre_opt with
                               | FStar_Pervasives_Native.None ->
                                   let uu____6891 =
                                     FStar_SMTEncoding_Util.mk_and_l guards in
                                   (uu____6891, decls1)
                               | FStar_Pervasives_Native.Some p ->
                                   let uu____6895 =
                                     FStar_SMTEncoding_EncodeTerm.encode_formula
                                       p env' in
                                   (match uu____6895 with
                                    | (g, ds) ->
                                        let uu____6908 =
                                          FStar_SMTEncoding_Util.mk_and_l (g
                                            :: guards) in
                                        (uu____6908,
                                          (FStar_List.append decls1 ds))) in
                             (match uu____6878 with
                              | (guard, decls11) ->
                                  let dummy_var =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ("@dummy",
                                        FStar_SMTEncoding_Term.dummy_sort) in
                                  let dummy_tm =
                                    FStar_SMTEncoding_Term.mkFreeV dummy_var
                                      FStar_Range.dummyRange in
                                  let should_thunk uu____6928 =
                                    let is_type t =
                                      let uu____6935 =
                                        let uu____6936 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____6936.FStar_Syntax_Syntax.n in
                                      match uu____6935 with
                                      | FStar_Syntax_Syntax.Tm_type
                                          uu____6939 -> true
                                      | uu____6940 -> false in
                                    let is_squash t =
                                      let uu____6947 =
                                        FStar_Syntax_Util.head_and_args t in
                                      match uu____6947 with
                                      | (head, uu____6965) ->
                                          let uu____6990 =
                                            let uu____6991 =
                                              FStar_Syntax_Util.un_uinst head in
                                            uu____6991.FStar_Syntax_Syntax.n in
                                          (match uu____6990 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv1
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.squash_lid
                                           | FStar_Syntax_Syntax.Tm_refine
                                               ({
                                                  FStar_Syntax_Syntax.ppname
                                                    = uu____6995;
                                                  FStar_Syntax_Syntax.index =
                                                    uu____6996;
                                                  FStar_Syntax_Syntax.sort =
                                                    {
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_fvar
                                                        fv1;
                                                      FStar_Syntax_Syntax.pos
                                                        = uu____6998;
                                                      FStar_Syntax_Syntax.vars
                                                        = uu____6999;_};_},
                                                uu____7000)
                                               ->
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv1
                                                 FStar_Parser_Const.unit_lid
                                           | uu____7007 -> false) in
                                    (((let uu____7010 = FStar_Ident.nsstr lid in
                                       uu____7010 <> "Prims") &&
                                        (let uu____7012 =
                                           FStar_All.pipe_right quals
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Logic) in
                                         Prims.op_Negation uu____7012))
                                       &&
                                       (let uu____7016 = is_squash t_norm in
                                        Prims.op_Negation uu____7016))
                                      &&
                                      (let uu____7018 = is_type t_norm in
                                       Prims.op_Negation uu____7018) in
                                  let uu____7019 =
                                    match vars with
                                    | [] when should_thunk () ->
                                        (true, [dummy_var])
                                    | uu____7064 -> (false, vars) in
                                  (match uu____7019 with
                                   | (thunked, vars1) ->
                                       let arity = FStar_List.length formals in
                                       let uu____7104 =
                                         FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                           env lid arity thunked in
                                       (match uu____7104 with
                                        | (vname, vtok_opt, env1) ->
                                            let get_vtok uu____7129 =
                                              FStar_Option.get vtok_opt in
                                            let vtok_tm =
                                              match formals with
                                              | [] when
                                                  Prims.op_Negation thunked
                                                  ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [])
                                              | [] when thunked ->
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (vname, [dummy_tm])
                                              | uu____7147 ->
                                                  let uu____7156 =
                                                    let uu____7163 =
                                                      get_vtok () in
                                                    (uu____7163, []) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____7156 in
                                            let vtok_app =
                                              FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                vtok_tm vars1 in
                                            let vapp =
                                              let uu____7168 =
                                                let uu____7175 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    vars1 in
                                                (vname, uu____7175) in
                                              FStar_SMTEncoding_Util.mkApp
                                                uu____7168 in
                                            let uu____7186 =
                                              let vname_decl =
                                                let uu____7194 =
                                                  let uu____7205 =
                                                    FStar_All.pipe_right
                                                      vars1
                                                      (FStar_List.map
                                                         FStar_SMTEncoding_Term.fv_sort) in
                                                  (vname, uu____7205,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    FStar_Pervasives_Native.None) in
                                                FStar_SMTEncoding_Term.DeclFun
                                                  uu____7194 in
                                              let uu____7214 =
                                                let env2 =
                                                  let uu___411_7220 = env1 in
                                                  {
                                                    FStar_SMTEncoding_Env.bvar_bindings
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.bvar_bindings);
                                                    FStar_SMTEncoding_Env.fvar_bindings
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.fvar_bindings);
                                                    FStar_SMTEncoding_Env.depth
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.depth);
                                                    FStar_SMTEncoding_Env.tcenv
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.tcenv);
                                                    FStar_SMTEncoding_Env.warn
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.warn);
                                                    FStar_SMTEncoding_Env.nolabels
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.nolabels);
                                                    FStar_SMTEncoding_Env.use_zfuel_name
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.use_zfuel_name);
                                                    FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                      =
                                                      encode_non_total_function_typ;
                                                    FStar_SMTEncoding_Env.current_module_name
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.current_module_name);
                                                    FStar_SMTEncoding_Env.encoding_quantifier
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.encoding_quantifier);
                                                    FStar_SMTEncoding_Env.global_cache
                                                      =
                                                      (uu___411_7220.FStar_SMTEncoding_Env.global_cache)
                                                  } in
                                                let uu____7221 =
                                                  let uu____7222 =
                                                    FStar_SMTEncoding_EncodeTerm.head_normal
                                                      env2 tt in
                                                  Prims.op_Negation
                                                    uu____7222 in
                                                if uu____7221
                                                then
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    tt env2 vtok_tm
                                                else
                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                    FStar_Pervasives_Native.None
                                                    t_norm env2 vtok_tm in
                                              match uu____7214 with
                                              | (tok_typing, decls2) ->
                                                  let uu____7236 =
                                                    match vars1 with
                                                    | [] ->
                                                        let tok_typing1 =
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname)) in
                                                        let uu____7256 =
                                                          let uu____7259 =
                                                            FStar_All.pipe_right
                                                              [tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial in
                                                          FStar_List.append
                                                            decls2 uu____7259 in
                                                        let uu____7266 =
                                                          let uu____7267 =
                                                            let uu____7270 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (vname, []) in
                                                            FStar_All.pipe_left
                                                              (fun uu____7275
                                                                 ->
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____7275)
                                                              uu____7270 in
                                                          FStar_SMTEncoding_Env.push_free_var
                                                            env1 lid arity
                                                            vname uu____7267 in
                                                        (uu____7256,
                                                          uu____7266)
                                                    | uu____7278 when thunked
                                                        -> (decls2, env1)
                                                    | uu____7289 ->
                                                        let vtok =
                                                          get_vtok () in
                                                        let vtok_decl =
                                                          FStar_SMTEncoding_Term.DeclFun
                                                            (vtok, [],
                                                              FStar_SMTEncoding_Term.Term_sort,
                                                              FStar_Pervasives_Native.None) in
                                                        let name_tok_corr_formula
                                                          pat =
                                                          let uu____7308 =
                                                            FStar_Syntax_Syntax.range_of_fv
                                                              fv in
                                                          let uu____7309 =
                                                            let uu____7320 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vtok_app,
                                                                  vapp) in
                                                            ([[pat]], vars1,
                                                              uu____7320) in
                                                          FStar_SMTEncoding_Term.mkForall
                                                            uu____7308
                                                            uu____7309 in
                                                        let name_tok_corr =
                                                          let uu____7330 =
                                                            let uu____7337 =
                                                              name_tok_corr_formula
                                                                vtok_app in
                                                            (uu____7337,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Name-token correspondence"),
                                                              (Prims.op_Hat
                                                                 "token_correspondence_"
                                                                 vname)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____7330 in
                                                        let tok_typing1 =
                                                          let ff =
                                                            FStar_SMTEncoding_Term.mk_fv
                                                              ("ty",
                                                                FStar_SMTEncoding_Term.Term_sort) in
                                                          let f =
                                                            FStar_SMTEncoding_Util.mkFreeV
                                                              ff in
                                                          let vtok_app_r =
                                                            let uu____7342 =
                                                              let uu____7343
                                                                =
                                                                FStar_SMTEncoding_Term.mk_fv
                                                                  (vtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                              [uu____7343] in
                                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                              f uu____7342 in
                                                          let guarded_tok_typing
                                                            =
                                                            let uu____7363 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv in
                                                            let uu____7364 =
                                                              let uu____7375
                                                                =
                                                                let uu____7376
                                                                  =
                                                                  let uu____7381
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_NoHoist
                                                                    f
                                                                    tok_typing in
                                                                  let uu____7382
                                                                    =
                                                                    name_tok_corr_formula
                                                                    vapp in
                                                                  (uu____7381,
                                                                    uu____7382) in
                                                                FStar_SMTEncoding_Util.mkAnd
                                                                  uu____7376 in
                                                              ([[vtok_app_r]],
                                                                [ff],
                                                                uu____7375) in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____7363
                                                              uu____7364 in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            (guarded_tok_typing,
                                                              (FStar_Pervasives_Native.Some
                                                                 "function token typing"),
                                                              (Prims.op_Hat
                                                                 "function_token_typing_"
                                                                 vname)) in
                                                        let uu____7403 =
                                                          let uu____7406 =
                                                            FStar_All.pipe_right
                                                              [vtok_decl;
                                                              name_tok_corr;
                                                              tok_typing1]
                                                              FStar_SMTEncoding_Term.mk_decls_trivial in
                                                          FStar_List.append
                                                            decls2 uu____7406 in
                                                        (uu____7403, env1) in
                                                  (match uu____7236 with
                                                   | (tok_decl, env2) ->
                                                       let uu____7427 =
                                                         let uu____7430 =
                                                           FStar_All.pipe_right
                                                             [vname_decl]
                                                             FStar_SMTEncoding_Term.mk_decls_trivial in
                                                         FStar_List.append
                                                           uu____7430
                                                           tok_decl in
                                                       (uu____7427, env2)) in
                                            (match uu____7186 with
                                             | (decls2, env2) ->
                                                 let uu____7449 =
                                                   let res_t1 =
                                                     FStar_Syntax_Subst.compress
                                                       res_t in
                                                   let uu____7459 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       res_t1 env' in
                                                   match uu____7459 with
                                                   | (encoded_res_t, decls)
                                                       ->
                                                       let uu____7474 =
                                                         FStar_SMTEncoding_Term.mk_HasType
                                                           vapp encoded_res_t in
                                                       (encoded_res_t,
                                                         uu____7474, decls) in
                                                 (match uu____7449 with
                                                  | (encoded_res_t, ty_pred,
                                                     decls3) ->
                                                      let typingAx =
                                                        let uu____7489 =
                                                          let uu____7496 =
                                                            let uu____7497 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv in
                                                            let uu____7498 =
                                                              let uu____7509
                                                                =
                                                                FStar_SMTEncoding_Util.mkImp
                                                                  (guard,
                                                                    ty_pred) in
                                                              ([[vapp]],
                                                                vars1,
                                                                uu____7509) in
                                                            FStar_SMTEncoding_Term.mkForall
                                                              uu____7497
                                                              uu____7498 in
                                                          (uu____7496,
                                                            (FStar_Pervasives_Native.Some
                                                               "free var typing"),
                                                            (Prims.op_Hat
                                                               "typing_"
                                                               vname)) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____7489 in
                                                      let freshness =
                                                        let uu____7521 =
                                                          FStar_All.pipe_right
                                                            quals
                                                            (FStar_List.contains
                                                               FStar_Syntax_Syntax.New) in
                                                        if uu____7521
                                                        then
                                                          let uu____7526 =
                                                            let uu____7527 =
                                                              FStar_Syntax_Syntax.range_of_fv
                                                                fv in
                                                            let uu____7528 =
                                                              let uu____7539
                                                                =
                                                                FStar_All.pipe_right
                                                                  vars1
                                                                  (FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort) in
                                                              let uu____7546
                                                                =
                                                                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                                  () in
                                                              (vname,
                                                                uu____7539,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                uu____7546) in
                                                            FStar_SMTEncoding_Term.fresh_constructor
                                                              uu____7527
                                                              uu____7528 in
                                                          let uu____7549 =
                                                            let uu____7552 =
                                                              let uu____7553
                                                                =
                                                                FStar_Syntax_Syntax.range_of_fv
                                                                  fv in
                                                              pretype_axiom
                                                                uu____7553
                                                                env2 vapp
                                                                vars1 in
                                                            [uu____7552] in
                                                          uu____7526 ::
                                                            uu____7549
                                                        else [] in
                                                      let g =
                                                        let uu____7558 =
                                                          let uu____7561 =
                                                            let uu____7564 =
                                                              let uu____7567
                                                                =
                                                                let uu____7570
                                                                  =
                                                                  let uu____7573
                                                                    =
                                                                    mk_disc_proj_axioms
                                                                    guard
                                                                    encoded_res_t
                                                                    vapp
                                                                    vars1 in
                                                                  typingAx ::
                                                                    uu____7573 in
                                                                FStar_List.append
                                                                  freshness
                                                                  uu____7570 in
                                                              FStar_All.pipe_right
                                                                uu____7567
                                                                FStar_SMTEncoding_Term.mk_decls_trivial in
                                                            FStar_List.append
                                                              decls3
                                                              uu____7564 in
                                                          FStar_List.append
                                                            decls2 uu____7561 in
                                                        FStar_List.append
                                                          decls11 uu____7558 in
                                                      (g, env2)))))))))
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          (FStar_SMTEncoding_Env.fvar_binding *
            FStar_SMTEncoding_Term.decls_elt Prims.list *
            FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun x ->
      fun t ->
        fun t_norm ->
          let uu____7612 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____7612 with
          | FStar_Pervasives_Native.None ->
              let uu____7623 = encode_free_var false env x t t_norm [] in
              (match uu____7623 with
               | (decls, env1) ->
                   let fvb =
                     FStar_SMTEncoding_Env.lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (fvb, decls, env1))
          | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
let (encode_top_level_val :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun uninterpreted ->
    fun env ->
      fun lid ->
        fun t ->
          fun quals ->
            let tt = norm_before_encoding env t in
            let uu____7682 = encode_free_var uninterpreted env lid t tt quals in
            match uu____7682 with
            | (decls, env1) ->
                let uu____7693 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____7693
                then
                  let uu____7698 =
                    let uu____7699 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____7699 in
                  (uu____7698, env1)
                else (decls, env1)
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_elt Prims.list *
          FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun bindings ->
      fun quals ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____7753 ->
                fun lb ->
                  match uu____7753 with
                  | (decls, env1) ->
                      let uu____7773 =
                        let uu____7778 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____7778
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____7773 with
                       | (decls', env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____7797 = FStar_Syntax_Util.head_and_args t in
    match uu____7797 with
    | (hd, args) ->
        let uu____7840 =
          let uu____7841 = FStar_Syntax_Util.un_uinst hd in
          uu____7841.FStar_Syntax_Syntax.n in
        (match uu____7840 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____7845, c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             let uu____7868 = FStar_Ident.string_of_lid effect_name in
             FStar_Util.starts_with "FStar.Tactics" uu____7868
         | uu____7869 -> false)
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Let_rec_unencodeable -> true | uu____7875 -> false
let (copy_env : FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Env.env_t) =
  fun en ->
    let uu___495_7881 = en in
    let uu____7882 =
      FStar_Util.smap_copy en.FStar_SMTEncoding_Env.global_cache in
    {
      FStar_SMTEncoding_Env.bvar_bindings =
        (uu___495_7881.FStar_SMTEncoding_Env.bvar_bindings);
      FStar_SMTEncoding_Env.fvar_bindings =
        (uu___495_7881.FStar_SMTEncoding_Env.fvar_bindings);
      FStar_SMTEncoding_Env.depth =
        (uu___495_7881.FStar_SMTEncoding_Env.depth);
      FStar_SMTEncoding_Env.tcenv =
        (uu___495_7881.FStar_SMTEncoding_Env.tcenv);
      FStar_SMTEncoding_Env.warn = (uu___495_7881.FStar_SMTEncoding_Env.warn);
      FStar_SMTEncoding_Env.nolabels =
        (uu___495_7881.FStar_SMTEncoding_Env.nolabels);
      FStar_SMTEncoding_Env.use_zfuel_name =
        (uu___495_7881.FStar_SMTEncoding_Env.use_zfuel_name);
      FStar_SMTEncoding_Env.encode_non_total_function_typ =
        (uu___495_7881.FStar_SMTEncoding_Env.encode_non_total_function_typ);
      FStar_SMTEncoding_Env.current_module_name =
        (uu___495_7881.FStar_SMTEncoding_Env.current_module_name);
      FStar_SMTEncoding_Env.encoding_quantifier =
        (uu___495_7881.FStar_SMTEncoding_Env.encoding_quantifier);
      FStar_SMTEncoding_Env.global_cache = uu____7882
    }
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun uu____7910 ->
      fun quals ->
        match uu____7910 with
        | (is_rec, bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____8010 = FStar_Util.first_N nbinders formals in
              match uu____8010 with
              | (formals1, extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____8105 ->
                         fun uu____8106 ->
                           match (uu____8105, uu____8106) with
                           | ((formal, uu____8132), (binder, uu____8134)) ->
                               let uu____8155 =
                                 let uu____8162 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____8162) in
                               FStar_Syntax_Syntax.NT uu____8155) formals1
                      binders in
                  let extra_formals1 =
                    let uu____8176 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8217 ->
                              match uu____8217 with
                              | (x, i) ->
                                  let uu____8236 =
                                    let uu___521_8237 = x in
                                    let uu____8238 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___521_8237.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___521_8237.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____8238
                                    } in
                                  (uu____8236, i))) in
                    FStar_All.pipe_right uu____8176
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____8260 = FStar_Syntax_Subst.compress body in
                    let uu____8261 =
                      let uu____8262 =
                        FStar_Syntax_Util.args_of_binders extra_formals1 in
                      FStar_All.pipe_left FStar_Pervasives_Native.snd
                        uu____8262 in
                    FStar_Syntax_Syntax.extend_app_n uu____8260 uu____8261
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function t e =
              let tcenv =
                let uu___528_8309 = env.FStar_SMTEncoding_Env.tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___528_8309.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___528_8309.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___528_8309.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___528_8309.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___528_8309.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___528_8309.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___528_8309.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___528_8309.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___528_8309.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___528_8309.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___528_8309.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___528_8309.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___528_8309.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___528_8309.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___528_8309.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___528_8309.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___528_8309.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (uu___528_8309.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___528_8309.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___528_8309.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = true;
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___528_8309.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___528_8309.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___528_8309.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___528_8309.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___528_8309.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___528_8309.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___528_8309.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___528_8309.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___528_8309.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___528_8309.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___528_8309.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___528_8309.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___528_8309.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___528_8309.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___528_8309.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.try_solve_implicits_hook =
                    (uu___528_8309.FStar_TypeChecker_Env.try_solve_implicits_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___528_8309.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___528_8309.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___528_8309.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___528_8309.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___528_8309.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___528_8309.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.nbe =
                    (uu___528_8309.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___528_8309.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___528_8309.FStar_TypeChecker_Env.erasable_types_tab);
                  FStar_TypeChecker_Env.enable_defer_to_tac =
                    (uu___528_8309.FStar_TypeChecker_Env.enable_defer_to_tac)
                } in
              let subst_comp formals actuals comp =
                let subst =
                  FStar_List.map2
                    (fun uu____8380 ->
                       fun uu____8381 ->
                         match (uu____8380, uu____8381) with
                         | ((x, uu____8407), (b, uu____8409)) ->
                             let uu____8430 =
                               let uu____8437 =
                                 FStar_Syntax_Syntax.bv_to_name b in
                               (x, uu____8437) in
                             FStar_Syntax_Syntax.NT uu____8430) formals
                    actuals in
                FStar_Syntax_Subst.subst_comp subst comp in
              let rec arrow_formals_comp_norm norm t1 =
                let t2 =
                  let uu____8460 = FStar_Syntax_Subst.compress t1 in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____8460 in
                match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_arrow (formals, comp) ->
                    FStar_Syntax_Subst.open_comp formals comp
                | FStar_Syntax_Syntax.Tm_refine uu____8489 ->
                    let uu____8496 = FStar_Syntax_Util.unrefine t2 in
                    arrow_formals_comp_norm norm uu____8496
                | uu____8497 when Prims.op_Negation norm ->
                    let t_norm =
                      norm_with_steps
                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Exclude
                          FStar_TypeChecker_Env.Zeta;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.EraseUniverses] tcenv t2 in
                    arrow_formals_comp_norm true t_norm
                | uu____8499 ->
                    let uu____8500 = FStar_Syntax_Syntax.mk_Total t2 in
                    ([], uu____8500) in
              let aux t1 e1 =
                let uu____8542 = FStar_Syntax_Util.abs_formals e1 in
                match uu____8542 with
                | (binders, body, lopt) ->
                    let uu____8574 =
                      match binders with
                      | [] -> arrow_formals_comp_norm true t1
                      | uu____8589 -> arrow_formals_comp_norm false t1 in
                    (match uu____8574 with
                     | (formals, comp) ->
                         let nformals = FStar_List.length formals in
                         let nbinders = FStar_List.length binders in
                         let uu____8622 =
                           if nformals < nbinders
                           then
                             let uu____8655 =
                               FStar_Util.first_N nformals binders in
                             match uu____8655 with
                             | (bs0, rest) ->
                                 let body1 =
                                   FStar_Syntax_Util.abs rest body lopt in
                                 let uu____8735 = subst_comp formals bs0 comp in
                                 (bs0, body1, uu____8735)
                           else
                             if nformals > nbinders
                             then
                               (let uu____8763 =
                                  eta_expand binders formals body
                                    (FStar_Syntax_Util.comp_result comp) in
                                match uu____8763 with
                                | (binders1, body1) ->
                                    let uu____8810 =
                                      subst_comp formals binders1 comp in
                                    (binders1, body1, uu____8810))
                             else
                               (let uu____8822 =
                                  subst_comp formals binders comp in
                                (binders, body, uu____8822)) in
                         (match uu____8622 with
                          | (binders1, body1, comp1) ->
                              (binders1, body1, comp1))) in
              let uu____8882 = aux t e in
              match uu____8882 with
              | (binders, body, comp) ->
                  let uu____8928 =
                    let uu____8939 =
                      FStar_SMTEncoding_Util.is_smt_reifiable_comp tcenv comp in
                    if uu____8939
                    then
                      let comp1 =
                        FStar_TypeChecker_Env.reify_comp tcenv comp
                          FStar_Syntax_Syntax.U_unknown in
                      let body1 =
                        FStar_TypeChecker_Util.reify_body tcenv [] body in
                      let uu____8952 = aux comp1 body1 in
                      match uu____8952 with
                      | (more_binders, body2, comp2) ->
                          ((FStar_List.append binders more_binders), body2,
                            comp2)
                    else (binders, body, comp) in
                  (match uu____8928 with
                   | (binders1, body1, comp1) ->
                       let uu____9034 =
                         FStar_Syntax_Util.ascribe body1
                           ((FStar_Util.Inl
                               (FStar_Syntax_Util.comp_result comp1)),
                             FStar_Pervasives_Native.None) in
                       (binders1, uu____9034, comp1)) in
            (try
               (fun uu___598_9061 ->
                  match () with
                  | () ->
                      let uu____9068 =
                        FStar_All.pipe_right bindings
                          (FStar_Util.for_all
                             (fun lb ->
                                (FStar_Syntax_Util.is_lemma
                                   lb.FStar_Syntax_Syntax.lbtyp)
                                  || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
                      if uu____9068
                      then encode_top_level_vals env bindings quals
                      else
                        (let uu____9080 =
                           FStar_All.pipe_right bindings
                             (FStar_List.fold_left
                                (fun uu____9143 ->
                                   fun lb ->
                                     match uu____9143 with
                                     | (toks, typs, decls, env1) ->
                                         ((let uu____9198 =
                                             FStar_Syntax_Util.is_lemma
                                               lb.FStar_Syntax_Syntax.lbtyp in
                                           if uu____9198
                                           then
                                             FStar_Exn.raise
                                               Let_rec_unencodeable
                                           else ());
                                          (let t_norm =
                                             norm_before_encoding env1
                                               lb.FStar_Syntax_Syntax.lbtyp in
                                           let uu____9201 =
                                             let uu____9210 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname in
                                             declare_top_level_let env1
                                               uu____9210
                                               lb.FStar_Syntax_Syntax.lbtyp
                                               t_norm in
                                           match uu____9201 with
                                           | (tok, decl, env2) ->
                                               ((tok :: toks), (t_norm ::
                                                 typs), (decl :: decls),
                                                 env2)))) ([], [], [], env)) in
                         match uu____9080 with
                         | (toks, typs, decls, env1) ->
                             let toks_fvbs = FStar_List.rev toks in
                             let decls1 =
                               FStar_All.pipe_right (FStar_List.rev decls)
                                 FStar_List.flatten in
                             let env_decls = copy_env env1 in
                             let typs1 = FStar_List.rev typs in
                             let encode_non_rec_lbdef bindings1 typs2 toks1
                               env2 =
                               match (bindings1, typs2, toks1) with
                               | ({ FStar_Syntax_Syntax.lbname = lbn;
                                    FStar_Syntax_Syntax.lbunivs = uvs;
                                    FStar_Syntax_Syntax.lbtyp = uu____9351;
                                    FStar_Syntax_Syntax.lbeff = uu____9352;
                                    FStar_Syntax_Syntax.lbdef = e;
                                    FStar_Syntax_Syntax.lbattrs = uu____9354;
                                    FStar_Syntax_Syntax.lbpos = uu____9355;_}::[],
                                  t_norm::[], fvb::[]) ->
                                   let flid =
                                     fvb.FStar_SMTEncoding_Env.fvar_lid in
                                   let uu____9379 =
                                     let uu____9386 =
                                       FStar_TypeChecker_Env.open_universes_in
                                         env2.FStar_SMTEncoding_Env.tcenv uvs
                                         [e; t_norm] in
                                     match uu____9386 with
                                     | (tcenv', uu____9402, e_t) ->
                                         let uu____9408 =
                                           match e_t with
                                           | e1::t_norm1::[] -> (e1, t_norm1)
                                           | uu____9419 ->
                                               failwith "Impossible" in
                                         (match uu____9408 with
                                          | (e1, t_norm1) ->
                                              ((let uu___661_9435 = env2 in
                                                {
                                                  FStar_SMTEncoding_Env.bvar_bindings
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.bvar_bindings);
                                                  FStar_SMTEncoding_Env.fvar_bindings
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.fvar_bindings);
                                                  FStar_SMTEncoding_Env.depth
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.depth);
                                                  FStar_SMTEncoding_Env.tcenv
                                                    = tcenv';
                                                  FStar_SMTEncoding_Env.warn
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.warn);
                                                  FStar_SMTEncoding_Env.nolabels
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.nolabels);
                                                  FStar_SMTEncoding_Env.use_zfuel_name
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.use_zfuel_name);
                                                  FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                  FStar_SMTEncoding_Env.current_module_name
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.current_module_name);
                                                  FStar_SMTEncoding_Env.encoding_quantifier
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.encoding_quantifier);
                                                  FStar_SMTEncoding_Env.global_cache
                                                    =
                                                    (uu___661_9435.FStar_SMTEncoding_Env.global_cache)
                                                }), e1, t_norm1)) in
                                   (match uu____9379 with
                                    | (env', e1, t_norm1) ->
                                        let uu____9445 =
                                          destruct_bound_function t_norm1 e1 in
                                        (match uu____9445 with
                                         | (binders, body, t_body_comp) ->
                                             let t_body =
                                               FStar_Syntax_Util.comp_result
                                                 t_body_comp in
                                             ((let uu____9465 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env2.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____9465
                                               then
                                                 let uu____9466 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____9467 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 FStar_Util.print2
                                                   "Encoding let : binders=[%s], body=%s\n"
                                                   uu____9466 uu____9467
                                               else ());
                                              (let uu____9469 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____9469 with
                                               | (vars, _guards, env'1,
                                                  binder_decls, uu____9496)
                                                   ->
                                                   let uu____9509 =
                                                     if
                                                       fvb.FStar_SMTEncoding_Env.fvb_thunked
                                                         && (vars = [])
                                                     then
                                                       let dummy_var =
                                                         FStar_SMTEncoding_Term.mk_fv
                                                           ("@dummy",
                                                             FStar_SMTEncoding_Term.dummy_sort) in
                                                       let dummy_tm =
                                                         FStar_SMTEncoding_Term.mkFreeV
                                                           dummy_var
                                                           FStar_Range.dummyRange in
                                                       let app =
                                                         let uu____9523 =
                                                           FStar_Syntax_Util.range_of_lbname
                                                             lbn in
                                                         FStar_SMTEncoding_Term.mkApp
                                                           ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                             [dummy_tm])
                                                           uu____9523 in
                                                       ([dummy_var], app)
                                                     else
                                                       (let uu____9539 =
                                                          let uu____9540 =
                                                            FStar_Syntax_Util.range_of_lbname
                                                              lbn in
                                                          let uu____9541 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                            uu____9540 fvb
                                                            uu____9541 in
                                                        (vars, uu____9539)) in
                                                   (match uu____9509 with
                                                    | (vars1, app) ->
                                                        let uu____9552 =
                                                          let is_logical =
                                                            let uu____9564 =
                                                              let uu____9565
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t_body in
                                                              uu____9565.FStar_Syntax_Syntax.n in
                                                            match uu____9564
                                                            with
                                                            | FStar_Syntax_Syntax.Tm_fvar
                                                                fv when
                                                                FStar_Syntax_Syntax.fv_eq_lid
                                                                  fv
                                                                  FStar_Parser_Const.logical_lid
                                                                -> true
                                                            | uu____9569 ->
                                                                false in
                                                          let is_prims =
                                                            let uu____9571 =
                                                              let uu____9572
                                                                =
                                                                FStar_All.pipe_right
                                                                  lbn
                                                                  FStar_Util.right in
                                                              FStar_All.pipe_right
                                                                uu____9572
                                                                FStar_Syntax_Syntax.lid_of_fv in
                                                            FStar_All.pipe_right
                                                              uu____9571
                                                              (fun lid ->
                                                                 let uu____9580
                                                                   =
                                                                   let uu____9581
                                                                    =
                                                                    FStar_Ident.ns_of_lid
                                                                    lid in
                                                                   FStar_Ident.lid_of_ids
                                                                    uu____9581 in
                                                                 FStar_Ident.lid_equals
                                                                   uu____9580
                                                                   FStar_Parser_Const.prims_lid) in
                                                          let uu____9582 =
                                                            (Prims.op_Negation
                                                               is_prims)
                                                              &&
                                                              ((FStar_All.pipe_right
                                                                  quals
                                                                  (FStar_List.contains
                                                                    FStar_Syntax_Syntax.Logic))
                                                                 ||
                                                                 is_logical) in
                                                          if uu____9582
                                                          then
                                                            let uu____9595 =
                                                              FStar_SMTEncoding_Term.mk_Valid
                                                                app in
                                                            let uu____9596 =
                                                              FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                body env'1 in
                                                            (app, uu____9595,
                                                              uu____9596)
                                                          else
                                                            (let uu____9606 =
                                                               FStar_SMTEncoding_EncodeTerm.encode_term
                                                                 body env'1 in
                                                             (app, app,
                                                               uu____9606)) in
                                                        (match uu____9552
                                                         with
                                                         | (pat, app1,
                                                            (body1, decls2))
                                                             ->
                                                             let eqn =
                                                               let uu____9630
                                                                 =
                                                                 let uu____9637
                                                                   =
                                                                   let uu____9638
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                   let uu____9639
                                                                    =
                                                                    let uu____9650
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1) in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu____9650) in
                                                                   FStar_SMTEncoding_Term.mkForall
                                                                    uu____9638
                                                                    uu____9639 in
                                                                 let uu____9659
                                                                   =
                                                                   let uu____9660
                                                                    =
                                                                    let uu____9661
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    flid in
                                                                    FStar_Util.format1
                                                                    "Equation for %s"
                                                                    uu____9661 in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____9660 in
                                                                 (uu____9637,
                                                                   uu____9659,
                                                                   (Prims.op_Hat
                                                                    "equation_"
                                                                    fvb.FStar_SMTEncoding_Env.smt_id)) in
                                                               FStar_SMTEncoding_Util.mkAssume
                                                                 uu____9630 in
                                                             let uu____9662 =
                                                               let uu____9665
                                                                 =
                                                                 let uu____9668
                                                                   =
                                                                   let uu____9671
                                                                    =
                                                                    let uu____9674
                                                                    =
                                                                    let uu____9677
                                                                    =
                                                                    primitive_type_axioms
                                                                    env2.FStar_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStar_SMTEncoding_Env.smt_id
                                                                    app1 in
                                                                    eqn ::
                                                                    uu____9677 in
                                                                    FStar_All.pipe_right
                                                                    uu____9674
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                   FStar_List.append
                                                                    decls2
                                                                    uu____9671 in
                                                                 FStar_List.append
                                                                   binder_decls
                                                                   uu____9668 in
                                                               FStar_List.append
                                                                 decls1
                                                                 uu____9665 in
                                                             (uu____9662,
                                                               env2)))))))
                               | uu____9686 -> failwith "Impossible" in
                             let encode_rec_lbdefs bindings1 typs2 toks1 env2
                               =
                               let fuel =
                                 let uu____9745 =
                                   let uu____9750 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                       env2.FStar_SMTEncoding_Env.current_module_name
                                       "fuel" in
                                   (uu____9750,
                                     FStar_SMTEncoding_Term.Fuel_sort) in
                                 FStar_SMTEncoding_Term.mk_fv uu____9745 in
                               let fuel_tm =
                                 FStar_SMTEncoding_Util.mkFreeV fuel in
                               let env0 = env2 in
                               let uu____9753 =
                                 FStar_All.pipe_right toks1
                                   (FStar_List.fold_left
                                      (fun uu____9800 ->
                                         fun fvb ->
                                           match uu____9800 with
                                           | (gtoks, env3) ->
                                               let flid =
                                                 fvb.FStar_SMTEncoding_Env.fvar_lid in
                                               let g =
                                                 let uu____9846 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid "fuel_instrumented" in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9846 in
                                               let gtok =
                                                 let uu____9848 =
                                                   FStar_Ident.lid_add_suffix
                                                     flid
                                                     "fuel_instrumented_token" in
                                                 FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                                   uu____9848 in
                                               let env4 =
                                                 let uu____9850 =
                                                   let uu____9853 =
                                                     FStar_SMTEncoding_Util.mkApp
                                                       (g, [fuel_tm]) in
                                                   FStar_All.pipe_left
                                                     (fun uu____9858 ->
                                                        FStar_Pervasives_Native.Some
                                                          uu____9858)
                                                     uu____9853 in
                                                 FStar_SMTEncoding_Env.push_free_var
                                                   env3 flid
                                                   fvb.FStar_SMTEncoding_Env.smt_arity
                                                   gtok uu____9850 in
                                               (((fvb, g, gtok) :: gtoks),
                                                 env4)) ([], env2)) in
                               match uu____9753 with
                               | (gtoks, env3) ->
                                   let gtoks1 = FStar_List.rev gtoks in
                                   let encode_one_binding env01 uu____9958
                                     t_norm uu____9960 =
                                     match (uu____9958, uu____9960) with
                                     | ((fvb, g, gtok),
                                        { FStar_Syntax_Syntax.lbname = lbn;
                                          FStar_Syntax_Syntax.lbunivs = uvs;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____9986;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____9987;
                                          FStar_Syntax_Syntax.lbdef = e;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____9989;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____9990;_})
                                         ->
                                         let uu____10011 =
                                           let uu____10018 =
                                             FStar_TypeChecker_Env.open_universes_in
                                               env3.FStar_SMTEncoding_Env.tcenv
                                               uvs [e; t_norm] in
                                           match uu____10018 with
                                           | (tcenv', uu____10034, e_t) ->
                                               let uu____10040 =
                                                 match e_t with
                                                 | e1::t_norm1::[] ->
                                                     (e1, t_norm1)
                                                 | uu____10051 ->
                                                     failwith "Impossible" in
                                               (match uu____10040 with
                                                | (e1, t_norm1) ->
                                                    ((let uu___748_10067 =
                                                        env3 in
                                                      {
                                                        FStar_SMTEncoding_Env.bvar_bindings
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.bvar_bindings);
                                                        FStar_SMTEncoding_Env.fvar_bindings
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.fvar_bindings);
                                                        FStar_SMTEncoding_Env.depth
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.depth);
                                                        FStar_SMTEncoding_Env.tcenv
                                                          = tcenv';
                                                        FStar_SMTEncoding_Env.warn
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.warn);
                                                        FStar_SMTEncoding_Env.nolabels
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.nolabels);
                                                        FStar_SMTEncoding_Env.use_zfuel_name
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.use_zfuel_name);
                                                        FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                        FStar_SMTEncoding_Env.current_module_name
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.current_module_name);
                                                        FStar_SMTEncoding_Env.encoding_quantifier
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.encoding_quantifier);
                                                        FStar_SMTEncoding_Env.global_cache
                                                          =
                                                          (uu___748_10067.FStar_SMTEncoding_Env.global_cache)
                                                      }), e1, t_norm1)) in
                                         (match uu____10011 with
                                          | (env', e1, t_norm1) ->
                                              ((let uu____10080 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env01.FStar_SMTEncoding_Env.tcenv)
                                                    (FStar_Options.Other
                                                       "SMTEncoding") in
                                                if uu____10080
                                                then
                                                  let uu____10081 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lbn in
                                                  let uu____10082 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t_norm1 in
                                                  let uu____10083 =
                                                    FStar_Syntax_Print.term_to_string
                                                      e1 in
                                                  FStar_Util.print3
                                                    "Encoding let rec %s : %s = %s\n"
                                                    uu____10081 uu____10082
                                                    uu____10083
                                                else ());
                                               (let uu____10085 =
                                                  destruct_bound_function
                                                    t_norm1 e1 in
                                                match uu____10085 with
                                                | (binders, body, tres_comp)
                                                    ->
                                                    let curry =
                                                      fvb.FStar_SMTEncoding_Env.smt_arity
                                                        <>
                                                        (FStar_List.length
                                                           binders) in
                                                    let uu____10110 =
                                                      FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                        env3.FStar_SMTEncoding_Env.tcenv
                                                        tres_comp in
                                                    (match uu____10110 with
                                                     | (pre_opt, tres) ->
                                                         ((let uu____10132 =
                                                             FStar_All.pipe_left
                                                               (FStar_TypeChecker_Env.debug
                                                                  env01.FStar_SMTEncoding_Env.tcenv)
                                                               (FStar_Options.Other
                                                                  "SMTEncodingReify") in
                                                           if uu____10132
                                                           then
                                                             let uu____10133
                                                               =
                                                               FStar_Syntax_Print.lbname_to_string
                                                                 lbn in
                                                             let uu____10134
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " binders in
                                                             let uu____10135
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body in
                                                             let uu____10136
                                                               =
                                                               FStar_Syntax_Print.comp_to_string
                                                                 tres_comp in
                                                             FStar_Util.print4
                                                               "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                               uu____10133
                                                               uu____10134
                                                               uu____10135
                                                               uu____10136
                                                           else ());
                                                          (let uu____10138 =
                                                             FStar_SMTEncoding_EncodeTerm.encode_binders
                                                               FStar_Pervasives_Native.None
                                                               binders env' in
                                                           match uu____10138
                                                           with
                                                           | (vars, guards,
                                                              env'1,
                                                              binder_decls,
                                                              uu____10167) ->
                                                               let uu____10180
                                                                 =
                                                                 match pre_opt
                                                                 with
                                                                 | FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu____10193
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards in
                                                                    (uu____10193,
                                                                    [])
                                                                 | FStar_Pervasives_Native.Some
                                                                    pre ->
                                                                    let uu____10197
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_formula
                                                                    pre env'1 in
                                                                    (match uu____10197
                                                                    with
                                                                    | 
                                                                    (guard,
                                                                    decls0)
                                                                    ->
                                                                    let uu____10210
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    guards
                                                                    [guard]) in
                                                                    (uu____10210,
                                                                    decls0)) in
                                                               (match uu____10180
                                                                with
                                                                | (guard,
                                                                   guard_decls)
                                                                    ->
                                                                    let binder_decls1
                                                                    =
                                                                    FStar_List.append
                                                                    binder_decls
                                                                    guard_decls in
                                                                    let decl_g
                                                                    =
                                                                    let uu____10231
                                                                    =
                                                                    let uu____10242
                                                                    =
                                                                    let uu____10245
                                                                    =
                                                                    let uu____10248
                                                                    =
                                                                    let uu____10251
                                                                    =
                                                                    FStar_Util.first_N
                                                                    fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    vars in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu____10251 in
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_sort
                                                                    uu____10248 in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    uu____10245 in
                                                                    (g,
                                                                    uu____10242,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name")) in
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    uu____10231 in
                                                                    let env02
                                                                    =
                                                                    FStar_SMTEncoding_Env.push_zfuel_name
                                                                    env01
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid
                                                                    g in
                                                                    let decl_g_tok
                                                                    =
                                                                    FStar_SMTEncoding_Term.DeclFun
                                                                    (gtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Token for fuel-instrumented partial applications")) in
                                                                    let vars_tm
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let rng =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let app =
                                                                    let uu____10275
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    rng fvb
                                                                    uu____10275 in
                                                                    let mk_g_app
                                                                    args =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    rng
                                                                    (FStar_Util.Inl
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    g))
                                                                    (fvb.FStar_SMTEncoding_Env.smt_arity
                                                                    +
                                                                    Prims.int_one)
                                                                    args in
                                                                    let gsapp
                                                                    =
                                                                    let uu____10289
                                                                    =
                                                                    let uu____10292
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm]) in
                                                                    uu____10292
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu____10289 in
                                                                    let gmax
                                                                    =
                                                                    let uu____10296
                                                                    =
                                                                    let uu____10299
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    []) in
                                                                    uu____10299
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu____10296 in
                                                                    let uu____10302
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'1 in
                                                                    (match uu____10302
                                                                    with
                                                                    | 
                                                                    (body_tm,
                                                                    decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    let uu____10318
                                                                    =
                                                                    let uu____10325
                                                                    =
                                                                    let uu____10326
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____10327
                                                                    =
                                                                    let uu____10342
                                                                    =
                                                                    let uu____10343
                                                                    =
                                                                    let uu____10348
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                    (guard,
                                                                    uu____10348) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____10343 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10342) in
                                                                    FStar_SMTEncoding_Term.mkForall'
                                                                    uu____10326
                                                                    uu____10327 in
                                                                    let uu____10359
                                                                    =
                                                                    let uu____10360
                                                                    =
                                                                    let uu____10361
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    fvb.FStar_SMTEncoding_Env.fvar_lid in
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    uu____10361 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____10360 in
                                                                    (uu____10325,
                                                                    uu____10359,
                                                                    (Prims.op_Hat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10318 in
                                                                    let eqn_f
                                                                    =
                                                                    let uu____10363
                                                                    =
                                                                    let uu____10370
                                                                    =
                                                                    let uu____10371
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____10372
                                                                    =
                                                                    let uu____10383
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____10383) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10371
                                                                    uu____10372 in
                                                                    (uu____10370,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10363 in
                                                                    let eqn_g'
                                                                    =
                                                                    let uu____10393
                                                                    =
                                                                    let uu____10400
                                                                    =
                                                                    let uu____10401
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____10402
                                                                    =
                                                                    let uu____10413
                                                                    =
                                                                    let uu____10414
                                                                    =
                                                                    let uu____10419
                                                                    =
                                                                    let uu____10420
                                                                    =
                                                                    let uu____10423
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero in
                                                                    uu____10423
                                                                    ::
                                                                    vars_tm in
                                                                    mk_g_app
                                                                    uu____10420 in
                                                                    (gsapp,
                                                                    uu____10419) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____10414 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10413) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10401
                                                                    uu____10402 in
                                                                    (uu____10400,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.op_Hat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10393 in
                                                                    let uu____10432
                                                                    =
                                                                    let gapp
                                                                    =
                                                                    mk_g_app
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm) in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu____10444
                                                                    =
                                                                    let uu____10445
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____10445 in
                                                                    FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____10444
                                                                    (fuel ::
                                                                    vars) in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head
                                                                    =
                                                                    let uu____10448
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____10448 in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars in
                                                                    let guards1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____10456
                                                                    ->
                                                                    FStar_SMTEncoding_Util.mkTrue)
                                                                    vars1 in
                                                                    let uu____10457
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_comp
                                                                    tres_comp in
                                                                    FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head
                                                                    vars1
                                                                    guards1
                                                                    uu____10457 in
                                                                    let uu____10458
                                                                    =
                                                                    let uu____10465
                                                                    =
                                                                    let uu____10466
                                                                    =
                                                                    let uu____10471
                                                                    =
                                                                    let uu____10472
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____10473
                                                                    =
                                                                    let uu____10484
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10484) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10472
                                                                    uu____10473 in
                                                                    (uu____10471,
                                                                    tot_fun_axioms) in
                                                                    FStar_SMTEncoding_Util.mkAnd
                                                                    uu____10466 in
                                                                    (uu____10465,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.op_Hat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10458 in
                                                                    let uu____10493
                                                                    =
                                                                    let uu____10502
                                                                    =
                                                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres
                                                                    env'1
                                                                    gapp in
                                                                    match uu____10502
                                                                    with
                                                                    | 
                                                                    (g_typing,
                                                                    d3) ->
                                                                    let uu____10517
                                                                    =
                                                                    let uu____10520
                                                                    =
                                                                    let uu____10521
                                                                    =
                                                                    let uu____10528
                                                                    =
                                                                    let uu____10529
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn in
                                                                    let uu____10530
                                                                    =
                                                                    let uu____10541
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing) in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____10541) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____10529
                                                                    uu____10530 in
                                                                    (uu____10528,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.op_Hat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____10521 in
                                                                    [uu____10520] in
                                                                    (d3,
                                                                    uu____10517) in
                                                                    match uu____10493
                                                                    with
                                                                    | 
                                                                    (aux_decls,
                                                                    typing_corr)
                                                                    ->
                                                                    (aux_decls,
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])) in
                                                                    (match uu____10432
                                                                    with
                                                                    | 
                                                                    (aux_decls,
                                                                    g_typing)
                                                                    ->
                                                                    let uu____10594
                                                                    =
                                                                    let uu____10597
                                                                    =
                                                                    let uu____10600
                                                                    =
                                                                    let uu____10603
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    [decl_g;
                                                                    decl_g_tok]
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    uu____10603 in
                                                                    FStar_List.append
                                                                    decls2
                                                                    uu____10600 in
                                                                    FStar_List.append
                                                                    binder_decls1
                                                                    uu____10597 in
                                                                    let uu____10610
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing)
                                                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                                                    (uu____10594,
                                                                    uu____10610,
                                                                    env02)))))))))) in
                                   let uu____10615 =
                                     let uu____10628 =
                                       FStar_List.zip3 gtoks1 typs2 bindings1 in
                                     FStar_List.fold_left
                                       (fun uu____10685 ->
                                          fun uu____10686 ->
                                            match (uu____10685, uu____10686)
                                            with
                                            | ((decls2, eqns, env01),
                                               (gtok, ty, lb)) ->
                                                let uu____10801 =
                                                  encode_one_binding env01
                                                    gtok ty lb in
                                                (match uu____10801 with
                                                 | (decls', eqns', env02) ->
                                                     ((decls' :: decls2),
                                                       (FStar_List.append
                                                          eqns' eqns), env02)))
                                       ([decls1], [], env0) uu____10628 in
                                   (match uu____10615 with
                                    | (decls2, eqns, env01) ->
                                        let uu____10868 =
                                          let isDeclFun uu___1_10884 =
                                            match uu___1_10884 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____10885 -> true
                                            | uu____10896 -> false in
                                          let uu____10897 =
                                            FStar_All.pipe_right decls2
                                              FStar_List.flatten in
                                          FStar_All.pipe_right uu____10897
                                            (fun decls3 ->
                                               let uu____10927 =
                                                 FStar_List.fold_left
                                                   (fun uu____10958 ->
                                                      fun elt ->
                                                        match uu____10958
                                                        with
                                                        | (prefix_decls,
                                                           elts, rest) ->
                                                            let uu____10999 =
                                                              (FStar_All.pipe_right
                                                                 elt.FStar_SMTEncoding_Term.key
                                                                 FStar_Util.is_some)
                                                                &&
                                                                (FStar_List.existsb
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls) in
                                                            if uu____10999
                                                            then
                                                              (prefix_decls,
                                                                (FStar_List.append
                                                                   elts 
                                                                   [elt]),
                                                                rest)
                                                            else
                                                              (let uu____11021
                                                                 =
                                                                 FStar_List.partition
                                                                   isDeclFun
                                                                   elt.FStar_SMTEncoding_Term.decls in
                                                               match uu____11021
                                                               with
                                                               | (elt_decl_funs,
                                                                  elt_rest)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    prefix_decls
                                                                    elt_decl_funs),
                                                                    elts,
                                                                    (FStar_List.append
                                                                    rest
                                                                    [(
                                                                    let uu___846_11059
                                                                    = elt in
                                                                    {
                                                                    FStar_SMTEncoding_Term.sym_name
                                                                    =
                                                                    (uu___846_11059.FStar_SMTEncoding_Term.sym_name);
                                                                    FStar_SMTEncoding_Term.key
                                                                    =
                                                                    (uu___846_11059.FStar_SMTEncoding_Term.key);
                                                                    FStar_SMTEncoding_Term.decls
                                                                    =
                                                                    elt_rest;
                                                                    FStar_SMTEncoding_Term.a_names
                                                                    =
                                                                    (uu___846_11059.FStar_SMTEncoding_Term.a_names)
                                                                    })]))))
                                                   ([], [], []) decls3 in
                                               match uu____10927 with
                                               | (prefix_decls, elts, rest)
                                                   ->
                                                   let uu____11091 =
                                                     FStar_All.pipe_right
                                                       prefix_decls
                                                       FStar_SMTEncoding_Term.mk_decls_trivial in
                                                   (uu____11091, elts, rest)) in
                                        (match uu____10868 with
                                         | (prefix_decls, elts, rest) ->
                                             let eqns1 = FStar_List.rev eqns in
                                             ((FStar_List.append prefix_decls
                                                 (FStar_List.append elts
                                                    (FStar_List.append rest
                                                       eqns1))), env01))) in
                             let uu____11120 =
                               (FStar_All.pipe_right quals
                                  (FStar_Util.for_some
                                     (fun uu___2_11124 ->
                                        match uu___2_11124 with
                                        | FStar_Syntax_Syntax.HasMaskedEffect
                                            -> true
                                        | uu____11125 -> false)))
                                 ||
                                 (FStar_All.pipe_right typs1
                                    (FStar_Util.for_some
                                       (fun t ->
                                          let uu____11131 =
                                            (FStar_Syntax_Util.is_pure_or_ghost_function
                                               t)
                                              ||
                                              (FStar_SMTEncoding_Util.is_smt_reifiable_function
                                                 env1.FStar_SMTEncoding_Env.tcenv
                                                 t) in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____11131))) in
                             if uu____11120
                             then (decls1, env_decls)
                             else
                               (try
                                  (fun uu___863_11148 ->
                                     match () with
                                     | () ->
                                         if Prims.op_Negation is_rec
                                         then
                                           encode_non_rec_lbdef bindings
                                             typs1 toks_fvbs env1
                                         else
                                           encode_rec_lbdefs bindings typs1
                                             toks_fvbs env1) ()
                                with
                                | FStar_SMTEncoding_Env.Inner_let_rec names
                                    ->
                                    let plural =
                                      (FStar_List.length names) >
                                        Prims.int_one in
                                    let r =
                                      let uu____11187 = FStar_List.hd names in
                                      FStar_All.pipe_right uu____11187
                                        FStar_Pervasives_Native.snd in
                                    ((let uu____11201 =
                                        let uu____11204 =
                                          let uu____11205 =
                                            let uu____11206 =
                                              let uu____11207 =
                                                FStar_List.map
                                                  FStar_Pervasives_Native.fst
                                                  names in
                                              FStar_All.pipe_right
                                                uu____11207
                                                (FStar_String.concat ",") in
                                            FStar_Util.format3
                                              "Definitions of inner let-rec%s %s and %s enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types"
                                              (if plural then "s" else "")
                                              uu____11206
                                              (if plural
                                               then "their"
                                               else "its") in
                                          let uu____11218 =
                                            FStar_Errors.get_ctx () in
                                          (FStar_Errors.Warning_DefinitionNotTranslated,
                                            uu____11205, r, uu____11218) in
                                        [uu____11204] in
                                      FStar_TypeChecker_Err.add_errors
                                        env1.FStar_SMTEncoding_Env.tcenv
                                        uu____11201);
                                     (decls1, env_decls))))) ()
             with
             | Let_rec_unencodeable ->
                 let msg =
                   let uu____11237 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____11237
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.op_Hat "let rec unencodeable: Skipping: " msg) in
                 let uu____11249 =
                   FStar_All.pipe_right [decl]
                     FStar_SMTEncoding_Term.mk_decls_trivial in
                 (uu____11249, env))
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      let nm =
        let uu____11303 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____11303 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some l -> FStar_Ident.string_of_lid l in
      let uu____11307 = encode_sigelt' env se in
      match uu____11307 with
      | (g, env1) ->
          let g1 =
            match g with
            | [] ->
                ((let uu____11320 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         env1.FStar_SMTEncoding_Env.tcenv)
                      (FStar_Options.Other "SMTEncoding") in
                  if uu____11320
                  then FStar_Util.print1 "Skipped encoding of %s\n" nm
                  else ());
                 (let uu____11322 =
                    let uu____11325 =
                      let uu____11326 = FStar_Util.format1 "<Skipped %s/>" nm in
                      FStar_SMTEncoding_Term.Caption uu____11326 in
                    [uu____11325] in
                  FStar_All.pipe_right uu____11322
                    FStar_SMTEncoding_Term.mk_decls_trivial))
            | uu____11329 ->
                let uu____11330 =
                  let uu____11333 =
                    let uu____11336 =
                      let uu____11337 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____11337 in
                    [uu____11336] in
                  FStar_All.pipe_right uu____11333
                    FStar_SMTEncoding_Term.mk_decls_trivial in
                let uu____11342 =
                  let uu____11345 =
                    let uu____11348 =
                      let uu____11351 =
                        let uu____11352 =
                          FStar_Util.format1 "</end encoding %s>" nm in
                        FStar_SMTEncoding_Term.Caption uu____11352 in
                      [uu____11351] in
                    FStar_All.pipe_right uu____11348
                      FStar_SMTEncoding_Term.mk_decls_trivial in
                  FStar_List.append g uu____11345 in
                FStar_List.append uu____11330 uu____11342 in
          (g1, env1)
and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      (let uu____11364 =
         FStar_All.pipe_left
           (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____11364
       then
         let uu____11365 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____11365
       else ());
      (let is_opaque_to_smt t =
         let uu____11373 =
           let uu____11374 = FStar_Syntax_Subst.compress t in
           uu____11374.FStar_Syntax_Syntax.n in
         match uu____11373 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s, uu____11378)) -> s = "opaque_to_smt"
         | uu____11379 -> false in
       let is_uninterpreted_by_smt t =
         let uu____11386 =
           let uu____11387 = FStar_Syntax_Subst.compress t in
           uu____11387.FStar_Syntax_Syntax.n in
         match uu____11386 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
             (s, uu____11391)) -> s = "uninterpreted_by_smt"
         | uu____11392 -> false in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_splice uu____11397 ->
           failwith "impossible -- splice should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_fail uu____11408 ->
           failwith
             "impossible -- Sig_fail should have been removed by Tc.fs"
       | FStar_Syntax_Syntax.Sig_pragma uu____11423 -> ([], env)
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11424 -> ([], env)
       | FStar_Syntax_Syntax.Sig_sub_effect uu____11437 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____11438 -> ([], env)
       | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____11449 -> ([], env)
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           let uu____11459 =
             let uu____11460 =
               FStar_SMTEncoding_Util.is_smt_reifiable_effect
                 env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname in
             Prims.op_Negation uu____11460 in
           if uu____11459
           then ([], env)
           else
             (let close_effect_params tm =
                match ed.FStar_Syntax_Syntax.binders with
                | [] -> tm
                | uu____11486 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_abs
                         ((ed.FStar_Syntax_Syntax.binders), tm,
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))))
                      tm.FStar_Syntax_Syntax.pos in
              let encode_action env1 a =
                let action_defn =
                  let uu____11519 =
                    close_effect_params a.FStar_Syntax_Syntax.action_defn in
                  norm_before_encoding env1 uu____11519 in
                let uu____11520 =
                  FStar_Syntax_Util.arrow_formals_comp
                    a.FStar_Syntax_Syntax.action_typ in
                match uu____11520 with
                | (formals, uu____11532) ->
                    let arity = FStar_List.length formals in
                    let uu____11540 =
                      FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                        env1 a.FStar_Syntax_Syntax.action_name arity in
                    (match uu____11540 with
                     | (aname, atok, env2) ->
                         let uu____11556 =
                           FStar_SMTEncoding_EncodeTerm.encode_term
                             action_defn env2 in
                         (match uu____11556 with
                          | (tm, decls) ->
                              let a_decls =
                                let uu____11572 =
                                  let uu____11573 =
                                    let uu____11584 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____11604 ->
                                              FStar_SMTEncoding_Term.Term_sort)) in
                                    (aname, uu____11584,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (FStar_Pervasives_Native.Some "Action")) in
                                  FStar_SMTEncoding_Term.DeclFun uu____11573 in
                                [uu____11572;
                                FStar_SMTEncoding_Term.DeclFun
                                  (atok, [],
                                    FStar_SMTEncoding_Term.Term_sort,
                                    (FStar_Pervasives_Native.Some
                                       "Action token"))] in
                              let uu____11615 =
                                let aux uu____11661 uu____11662 =
                                  match (uu____11661, uu____11662) with
                                  | ((bv, uu____11706),
                                     (env3, acc_sorts, acc)) ->
                                      let uu____11738 =
                                        FStar_SMTEncoding_Env.gen_term_var
                                          env3 bv in
                                      (match uu____11738 with
                                       | (xxsym, xx, env4) ->
                                           let uu____11758 =
                                             let uu____11761 =
                                               FStar_SMTEncoding_Term.mk_fv
                                                 (xxsym,
                                                   FStar_SMTEncoding_Term.Term_sort) in
                                             uu____11761 :: acc_sorts in
                                           (env4, uu____11758, (xx :: acc))) in
                                FStar_List.fold_right aux formals
                                  (env2, [], []) in
                              (match uu____11615 with
                               | (uu____11792, xs_sorts, xs) ->
                                   let app =
                                     FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                   let a_eq =
                                     let uu____11807 =
                                       let uu____11814 =
                                         let uu____11815 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name in
                                         let uu____11816 =
                                           let uu____11827 =
                                             let uu____11828 =
                                               let uu____11833 =
                                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                   tm xs_sorts in
                                               (app, uu____11833) in
                                             FStar_SMTEncoding_Util.mkEq
                                               uu____11828 in
                                           ([[app]], xs_sorts, uu____11827) in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11815 uu____11816 in
                                       (uu____11814,
                                         (FStar_Pervasives_Native.Some
                                            "Action equality"),
                                         (Prims.op_Hat aname "_equality")) in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11807 in
                                   let tok_correspondence =
                                     let tok_term =
                                       let uu____11844 =
                                         FStar_SMTEncoding_Term.mk_fv
                                           (atok,
                                             FStar_SMTEncoding_Term.Term_sort) in
                                       FStar_All.pipe_left
                                         FStar_SMTEncoding_Util.mkFreeV
                                         uu____11844 in
                                     let tok_app =
                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                         tok_term xs_sorts in
                                     let uu____11846 =
                                       let uu____11853 =
                                         let uu____11854 =
                                           FStar_Ident.range_of_lid
                                             a.FStar_Syntax_Syntax.action_name in
                                         let uu____11855 =
                                           let uu____11866 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (tok_app, app) in
                                           ([[tok_app]], xs_sorts,
                                             uu____11866) in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11854 uu____11855 in
                                       (uu____11853,
                                         (FStar_Pervasives_Native.Some
                                            "Action token correspondence"),
                                         (Prims.op_Hat aname
                                            "_token_correspondence")) in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____11846 in
                                   let uu____11875 =
                                     let uu____11878 =
                                       FStar_All.pipe_right
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence])
                                         FStar_SMTEncoding_Term.mk_decls_trivial in
                                     FStar_List.append decls uu____11878 in
                                   (env2, uu____11875)))) in
              let uu____11887 =
                FStar_Util.fold_map encode_action env
                  ed.FStar_Syntax_Syntax.actions in
              match uu____11887 with
              | (env1, decls2) -> ((FStar_List.flatten decls2), env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11913, uu____11914)
           when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
           let uu____11915 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
               (Prims.of_int (4)) in
           (match uu____11915 with | (tname, ttok, env1) -> ([], env1))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11930, t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let will_encode_definition =
             let uu____11936 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___3_11940 ->
                       match uu___3_11940 with
                       | FStar_Syntax_Syntax.Assumption -> true
                       | FStar_Syntax_Syntax.Projector uu____11941 -> true
                       | FStar_Syntax_Syntax.Discriminator uu____11946 ->
                           true
                       | FStar_Syntax_Syntax.Irreducible -> true
                       | uu____11947 -> false)) in
             Prims.op_Negation uu____11936 in
           if will_encode_definition
           then ([], env)
           else
             (let fv =
                FStar_Syntax_Syntax.lid_as_fv lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              let uu____11954 =
                let uu____11959 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some is_uninterpreted_by_smt) in
                encode_top_level_val uu____11959 env fv t quals in
              match uu____11954 with
              | (decls, env1) ->
                  let tname = FStar_Ident.string_of_lid lid in
                  let tsym =
                    let uu____11970 =
                      FStar_SMTEncoding_Env.try_lookup_free_var env1 lid in
                    FStar_Option.get uu____11970 in
                  let uu____11973 =
                    let uu____11974 =
                      let uu____11977 =
                        primitive_type_axioms
                          env1.FStar_SMTEncoding_Env.tcenv lid tname tsym in
                      FStar_All.pipe_right uu____11977
                        FStar_SMTEncoding_Term.mk_decls_trivial in
                    FStar_List.append decls uu____11974 in
                  (uu____11973, env1))
       | FStar_Syntax_Syntax.Sig_assume (l, us, f) ->
           let uu____11987 = FStar_Syntax_Subst.open_univ_vars us f in
           (match uu____11987 with
            | (uvs, f1) ->
                let env1 =
                  let uu___1010_11999 = env in
                  let uu____12000 =
                    FStar_TypeChecker_Env.push_univ_vars
                      env.FStar_SMTEncoding_Env.tcenv uvs in
                  {
                    FStar_SMTEncoding_Env.bvar_bindings =
                      (uu___1010_11999.FStar_SMTEncoding_Env.bvar_bindings);
                    FStar_SMTEncoding_Env.fvar_bindings =
                      (uu___1010_11999.FStar_SMTEncoding_Env.fvar_bindings);
                    FStar_SMTEncoding_Env.depth =
                      (uu___1010_11999.FStar_SMTEncoding_Env.depth);
                    FStar_SMTEncoding_Env.tcenv = uu____12000;
                    FStar_SMTEncoding_Env.warn =
                      (uu___1010_11999.FStar_SMTEncoding_Env.warn);
                    FStar_SMTEncoding_Env.nolabels =
                      (uu___1010_11999.FStar_SMTEncoding_Env.nolabels);
                    FStar_SMTEncoding_Env.use_zfuel_name =
                      (uu___1010_11999.FStar_SMTEncoding_Env.use_zfuel_name);
                    FStar_SMTEncoding_Env.encode_non_total_function_typ =
                      (uu___1010_11999.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                    FStar_SMTEncoding_Env.current_module_name =
                      (uu___1010_11999.FStar_SMTEncoding_Env.current_module_name);
                    FStar_SMTEncoding_Env.encoding_quantifier =
                      (uu___1010_11999.FStar_SMTEncoding_Env.encoding_quantifier);
                    FStar_SMTEncoding_Env.global_cache =
                      (uu___1010_11999.FStar_SMTEncoding_Env.global_cache)
                  } in
                let f2 = norm_before_encoding env1 f1 in
                let uu____12002 =
                  FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1 in
                (match uu____12002 with
                 | (f3, decls) ->
                     let g =
                       let uu____12016 =
                         let uu____12019 =
                           let uu____12020 =
                             let uu____12027 =
                               let uu____12028 =
                                 let uu____12029 =
                                   FStar_Syntax_Print.lid_to_string l in
                                 FStar_Util.format1 "Assumption: %s"
                                   uu____12029 in
                               FStar_Pervasives_Native.Some uu____12028 in
                             let uu____12030 =
                               let uu____12031 =
                                 let uu____12032 =
                                   FStar_Ident.string_of_lid l in
                                 Prims.op_Hat "assumption_" uu____12032 in
                               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                 uu____12031 in
                             (f3, uu____12027, uu____12030) in
                           FStar_SMTEncoding_Util.mkAssume uu____12020 in
                         [uu____12019] in
                       FStar_All.pipe_right uu____12016
                         FStar_SMTEncoding_Term.mk_decls_trivial in
                     ((FStar_List.append decls g), env1)))
       | FStar_Syntax_Syntax.Sig_let (lbs, uu____12038) when
           (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
             ||
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                (FStar_Util.for_some is_opaque_to_smt))
           ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____12050 =
             FStar_Util.fold_map
               (fun env1 ->
                  fun lb ->
                    let lid =
                      let uu____12072 =
                        let uu____12075 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        uu____12075.FStar_Syntax_Syntax.fv_name in
                      uu____12072.FStar_Syntax_Syntax.v in
                    let uu____12076 =
                      let uu____12077 =
                        FStar_TypeChecker_Env.try_lookup_val_decl
                          env1.FStar_SMTEncoding_Env.tcenv lid in
                      FStar_All.pipe_left FStar_Option.isNone uu____12077 in
                    if uu____12076
                    then
                      let val_decl =
                        let uu___1027_12107 = se in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_declare_typ
                               (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                 (lb.FStar_Syntax_Syntax.lbtyp)));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1027_12107.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Irreducible ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1027_12107.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1027_12107.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___1027_12107.FStar_Syntax_Syntax.sigopts)
                        } in
                      let uu____12108 = encode_sigelt' env1 val_decl in
                      match uu____12108 with | (decls, env2) -> (env2, decls)
                    else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
           (match uu____12050 with
            | (env1, decls) -> ((FStar_List.flatten decls), env1))
       | FStar_Syntax_Syntax.Sig_let
           ((uu____12142,
             { FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
               FStar_Syntax_Syntax.lbunivs = uu____12144;
               FStar_Syntax_Syntax.lbtyp = uu____12145;
               FStar_Syntax_Syntax.lbeff = uu____12146;
               FStar_Syntax_Syntax.lbdef = uu____12147;
               FStar_Syntax_Syntax.lbattrs = uu____12148;
               FStar_Syntax_Syntax.lbpos = uu____12149;_}::[]),
            uu____12150)
           when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Parser_Const.b2t_lid
           ->
           let uu____12167 =
             FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
               (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               Prims.int_one in
           (match uu____12167 with
            | (tname, ttok, env1) ->
                let xx =
                  FStar_SMTEncoding_Term.mk_fv
                    ("x", FStar_SMTEncoding_Term.Term_sort) in
                let x = FStar_SMTEncoding_Util.mkFreeV xx in
                let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
                let valid_b2t_x =
                  FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
                let decls =
                  let uu____12192 =
                    let uu____12195 =
                      let uu____12196 =
                        let uu____12203 =
                          let uu____12204 =
                            FStar_Syntax_Syntax.range_of_fv b2t in
                          let uu____12205 =
                            let uu____12216 =
                              let uu____12217 =
                                let uu____12222 =
                                  FStar_SMTEncoding_Util.mkApp
                                    ((FStar_Pervasives_Native.snd
                                        FStar_SMTEncoding_Term.boxBoolFun),
                                      [x]) in
                                (valid_b2t_x, uu____12222) in
                              FStar_SMTEncoding_Util.mkEq uu____12217 in
                            ([[b2t_x]], [xx], uu____12216) in
                          FStar_SMTEncoding_Term.mkForall uu____12204
                            uu____12205 in
                        (uu____12203,
                          (FStar_Pervasives_Native.Some "b2t def"),
                          "b2t_def") in
                      FStar_SMTEncoding_Util.mkAssume uu____12196 in
                    [uu____12195] in
                  (FStar_SMTEncoding_Term.DeclFun
                     (tname, [FStar_SMTEncoding_Term.Term_sort],
                       FStar_SMTEncoding_Term.Term_sort,
                       FStar_Pervasives_Native.None))
                    :: uu____12192 in
                let uu____12247 =
                  FStar_All.pipe_right decls
                    FStar_SMTEncoding_Term.mk_decls_trivial in
                (uu____12247, env1))
       | FStar_Syntax_Syntax.Sig_let (uu____12250, uu____12251) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___4_12260 ->
                   match uu___4_12260 with
                   | FStar_Syntax_Syntax.Discriminator uu____12261 -> true
                   | uu____12262 -> false))
           ->
           ((let uu____12264 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____12264
             then
               let uu____12265 = FStar_Syntax_Print.sigelt_to_string_short se in
               FStar_Util.print1 "Not encoding discriminator '%s'\n"
                 uu____12265
             else ());
            ([], env))
       | FStar_Syntax_Syntax.Sig_let (uu____12267, lids) when
           (FStar_All.pipe_right lids
              (FStar_Util.for_some
                 (fun l ->
                    let uu____12278 =
                      let uu____12279 =
                        let uu____12280 = FStar_Ident.ns_of_lid l in
                        FStar_List.hd uu____12280 in
                      FStar_Ident.string_of_id uu____12279 in
                    uu____12278 = "Prims")))
             &&
             (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some
                   (fun uu___5_12286 ->
                      match uu___5_12286 with
                      | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                          -> true
                      | uu____12287 -> false)))
           ->
           ((let uu____12289 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____12289
             then
               let uu____12290 = FStar_Syntax_Print.sigelt_to_string_short se in
               FStar_Util.print1 "Not encoding unfold let from Prims '%s'\n"
                 uu____12290
             else ());
            ([], env))
       | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____12293) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___6_12304 ->
                   match uu___6_12304 with
                   | FStar_Syntax_Syntax.Projector uu____12305 -> true
                   | uu____12310 -> false))
           ->
           let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
           let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
           let uu____12313 = FStar_SMTEncoding_Env.try_lookup_free_var env l in
           (match uu____12313 with
            | FStar_Pervasives_Native.Some uu____12320 -> ([], env)
            | FStar_Pervasives_Native.None ->
                let se1 =
                  let uu___1096_12322 = se in
                  let uu____12323 = FStar_Ident.range_of_lid l in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_declare_typ
                         (l, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp)));
                    FStar_Syntax_Syntax.sigrng = uu____12323;
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1096_12322.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1096_12322.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1096_12322.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1096_12322.FStar_Syntax_Syntax.sigopts)
                  } in
                encode_sigelt env se1)
       | FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____12326) ->
           let bindings1 =
             FStar_List.map
               (fun lb ->
                  let def =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbdef in
                  let typ =
                    norm_before_encoding env lb.FStar_Syntax_Syntax.lbtyp in
                  let uu___1108_12345 = lb in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1108_12345.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1108_12345.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1108_12345.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = def;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1108_12345.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1108_12345.FStar_Syntax_Syntax.lbpos)
                  }) bindings in
           encode_top_level_let env (is_rec, bindings1)
             se.FStar_Syntax_Syntax.sigquals
       | FStar_Syntax_Syntax.Sig_bundle (ses, uu____12349) ->
           let uu____12358 = encode_sigelts env ses in
           (match uu____12358 with
            | (g, env1) ->
                let uu____12369 =
                  FStar_List.fold_left
                    (fun uu____12393 ->
                       fun elt ->
                         match uu____12393 with
                         | (g', inversions) ->
                             let uu____12421 =
                               FStar_All.pipe_right
                                 elt.FStar_SMTEncoding_Term.decls
                                 (FStar_List.partition
                                    (fun uu___7_12444 ->
                                       match uu___7_12444 with
                                       | FStar_SMTEncoding_Term.Assume
                                           {
                                             FStar_SMTEncoding_Term.assumption_term
                                               = uu____12445;
                                             FStar_SMTEncoding_Term.assumption_caption
                                               = FStar_Pervasives_Native.Some
                                               "inversion axiom";
                                             FStar_SMTEncoding_Term.assumption_name
                                               = uu____12446;
                                             FStar_SMTEncoding_Term.assumption_fact_ids
                                               = uu____12447;_}
                                           -> false
                                       | uu____12450 -> true)) in
                             (match uu____12421 with
                              | (elt_g', elt_inversions) ->
                                  ((FStar_List.append g'
                                      [(let uu___1134_12474 = elt in
                                        {
                                          FStar_SMTEncoding_Term.sym_name =
                                            (uu___1134_12474.FStar_SMTEncoding_Term.sym_name);
                                          FStar_SMTEncoding_Term.key =
                                            (uu___1134_12474.FStar_SMTEncoding_Term.key);
                                          FStar_SMTEncoding_Term.decls =
                                            elt_g';
                                          FStar_SMTEncoding_Term.a_names =
                                            (uu___1134_12474.FStar_SMTEncoding_Term.a_names)
                                        })]),
                                    (FStar_List.append inversions
                                       elt_inversions)))) ([], []) g in
                (match uu____12369 with
                 | (g', inversions) ->
                     let uu____12493 =
                       FStar_List.fold_left
                         (fun uu____12524 ->
                            fun elt ->
                              match uu____12524 with
                              | (decls, elts, rest) ->
                                  let uu____12565 =
                                    (FStar_All.pipe_right
                                       elt.FStar_SMTEncoding_Term.key
                                       FStar_Util.is_some)
                                      &&
                                      (FStar_List.existsb
                                         (fun uu___8_12570 ->
                                            match uu___8_12570 with
                                            | FStar_SMTEncoding_Term.DeclFun
                                                uu____12571 -> true
                                            | uu____12582 -> false)
                                         elt.FStar_SMTEncoding_Term.decls) in
                                  if uu____12565
                                  then
                                    (decls, (FStar_List.append elts [elt]),
                                      rest)
                                  else
                                    (let uu____12602 =
                                       FStar_All.pipe_right
                                         elt.FStar_SMTEncoding_Term.decls
                                         (FStar_List.partition
                                            (fun uu___9_12623 ->
                                               match uu___9_12623 with
                                               | FStar_SMTEncoding_Term.DeclFun
                                                   uu____12624 -> true
                                               | uu____12635 -> false)) in
                                     match uu____12602 with
                                     | (elt_decls, elt_rest) ->
                                         ((FStar_List.append decls elt_decls),
                                           elts,
                                           (FStar_List.append rest
                                              [(let uu___1156_12665 = elt in
                                                {
                                                  FStar_SMTEncoding_Term.sym_name
                                                    =
                                                    (uu___1156_12665.FStar_SMTEncoding_Term.sym_name);
                                                  FStar_SMTEncoding_Term.key
                                                    =
                                                    (uu___1156_12665.FStar_SMTEncoding_Term.key);
                                                  FStar_SMTEncoding_Term.decls
                                                    = elt_rest;
                                                  FStar_SMTEncoding_Term.a_names
                                                    =
                                                    (uu___1156_12665.FStar_SMTEncoding_Term.a_names)
                                                })])))) ([], [], []) g' in
                     (match uu____12493 with
                      | (decls, elts, rest) ->
                          let uu____12691 =
                            let uu____12692 =
                              FStar_All.pipe_right decls
                                FStar_SMTEncoding_Term.mk_decls_trivial in
                            let uu____12699 =
                              let uu____12702 =
                                let uu____12705 =
                                  FStar_All.pipe_right inversions
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append rest uu____12705 in
                              FStar_List.append elts uu____12702 in
                            FStar_List.append uu____12692 uu____12699 in
                          (uu____12691, env1))))
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (t, universe_names, tps, k, uu____12716, datas) ->
           let tcenv = env.FStar_SMTEncoding_Env.tcenv in
           let is_injective =
             let uu____12728 =
               FStar_Syntax_Subst.univ_var_opening universe_names in
             match uu____12728 with
             | (usubst, uvs) ->
                 let uu____12747 =
                   let uu____12754 =
                     FStar_TypeChecker_Env.push_univ_vars tcenv uvs in
                   let uu____12755 =
                     FStar_Syntax_Subst.subst_binders usubst tps in
                   let uu____12756 =
                     let uu____12757 =
                       FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                         usubst in
                     FStar_Syntax_Subst.subst uu____12757 k in
                   (uu____12754, uu____12755, uu____12756) in
                 (match uu____12747 with
                  | (env1, tps1, k1) ->
                      let uu____12769 = FStar_Syntax_Subst.open_term tps1 k1 in
                      (match uu____12769 with
                       | (tps2, k2) ->
                           let uu____12776 =
                             FStar_Syntax_Util.arrow_formals k2 in
                           (match uu____12776 with
                            | (uu____12783, k3) ->
                                let uu____12789 =
                                  FStar_TypeChecker_TcTerm.tc_binders env1
                                    tps2 in
                                (match uu____12789 with
                                 | (tps3, env_tps, uu____12800, us) ->
                                     let u_k =
                                       let uu____12803 =
                                         let uu____12804 =
                                           FStar_Syntax_Syntax.fvar t
                                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                                Prims.int_zero)
                                             FStar_Pervasives_Native.None in
                                         let uu____12805 =
                                           let uu____12806 =
                                             FStar_Syntax_Util.args_of_binders
                                               tps3 in
                                           FStar_Pervasives_Native.snd
                                             uu____12806 in
                                         let uu____12811 =
                                           FStar_Ident.range_of_lid t in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____12804 uu____12805
                                           uu____12811 in
                                       FStar_TypeChecker_TcTerm.level_of_type
                                         env_tps uu____12803 k3 in
                                     let rec universe_leq u v =
                                       match (u, v) with
                                       | (FStar_Syntax_Syntax.U_zero,
                                          uu____12823) -> true
                                       | (FStar_Syntax_Syntax.U_succ u0,
                                          FStar_Syntax_Syntax.U_succ v0) ->
                                           universe_leq u0 v0
                                       | (FStar_Syntax_Syntax.U_name u0,
                                          FStar_Syntax_Syntax.U_name v0) ->
                                           FStar_Ident.ident_equals u0 v0
                                       | (FStar_Syntax_Syntax.U_name
                                          uu____12828,
                                          FStar_Syntax_Syntax.U_succ v0) ->
                                           universe_leq u v0
                                       | (FStar_Syntax_Syntax.U_max us1,
                                          uu____12831) ->
                                           FStar_All.pipe_right us1
                                             (FStar_Util.for_all
                                                (fun u1 -> universe_leq u1 v))
                                       | (uu____12838,
                                          FStar_Syntax_Syntax.U_max vs) ->
                                           FStar_All.pipe_right vs
                                             (FStar_Util.for_some
                                                (universe_leq u))
                                       | (FStar_Syntax_Syntax.U_unknown,
                                          uu____12844) ->
                                           let uu____12845 =
                                             let uu____12846 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____12846 in
                                           failwith uu____12845
                                       | (uu____12847,
                                          FStar_Syntax_Syntax.U_unknown) ->
                                           let uu____12848 =
                                             let uu____12849 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____12849 in
                                           failwith uu____12848
                                       | (FStar_Syntax_Syntax.U_unif
                                          uu____12850, uu____12851) ->
                                           let uu____12862 =
                                             let uu____12863 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____12863 in
                                           failwith uu____12862
                                       | (uu____12864,
                                          FStar_Syntax_Syntax.U_unif
                                          uu____12865) ->
                                           let uu____12876 =
                                             let uu____12877 =
                                               FStar_Ident.string_of_lid t in
                                             FStar_Util.format1
                                               "Impossible: Unresolved or unknown universe in inductive type %s"
                                               uu____12877 in
                                           failwith uu____12876
                                       | uu____12878 -> false in
                                     let u_leq_u_k u =
                                       let uu____12889 =
                                         FStar_TypeChecker_Normalize.normalize_universe
                                           env_tps u in
                                       universe_leq uu____12889 u_k in
                                     let tp_ok tp u_tp =
                                       let t_tp =
                                         (FStar_Pervasives_Native.fst tp).FStar_Syntax_Syntax.sort in
                                       let uu____12906 = u_leq_u_k u_tp in
                                       if uu____12906
                                       then true
                                       else
                                         (let uu____12908 =
                                            FStar_Syntax_Util.arrow_formals
                                              t_tp in
                                          match uu____12908 with
                                          | (formals, uu____12916) ->
                                              let uu____12921 =
                                                FStar_TypeChecker_TcTerm.tc_binders
                                                  env_tps formals in
                                              (match uu____12921 with
                                               | (uu____12930, uu____12931,
                                                  uu____12932, u_formals) ->
                                                   FStar_Util.for_all
                                                     (fun u_formal ->
                                                        u_leq_u_k u_formal)
                                                     u_formals)) in
                                     FStar_List.forall2 tp_ok tps3 us)))) in
           ((let uu____12943 =
               FStar_All.pipe_left
                 (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv)
                 (FStar_Options.Other "SMTEncoding") in
             if uu____12943
             then
               let uu____12944 = FStar_Ident.string_of_lid t in
               FStar_Util.print2 "%s injectivity for %s\n"
                 (if is_injective then "YES" else "NO") uu____12944
             else ());
            (let quals = se.FStar_Syntax_Syntax.sigquals in
             let is_logical =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___10_12954 ->
                       match uu___10_12954 with
                       | FStar_Syntax_Syntax.Logic -> true
                       | FStar_Syntax_Syntax.Assumption -> true
                       | uu____12955 -> false)) in
             let constructor_or_logic_type_decl c =
               if is_logical
               then
                 let uu____12966 = c in
                 match uu____12966 with
                 | (name, args, uu____12971, uu____12972, uu____12973) ->
                     let uu____12978 =
                       let uu____12979 =
                         let uu____12990 =
                           FStar_All.pipe_right args
                             (FStar_List.map
                                (fun uu____13013 ->
                                   match uu____13013 with
                                   | (uu____13020, sort, uu____13022) -> sort)) in
                         (name, uu____12990,
                           FStar_SMTEncoding_Term.Term_sort,
                           FStar_Pervasives_Native.None) in
                       FStar_SMTEncoding_Term.DeclFun uu____12979 in
                     [uu____12978]
               else
                 (let uu____13026 = FStar_Ident.range_of_lid t in
                  FStar_SMTEncoding_Term.constructor_to_decl uu____13026 c) in
             let inversion_axioms tapp vars =
               let uu____13044 =
                 FStar_All.pipe_right datas
                   (FStar_Util.for_some
                      (fun l ->
                         let uu____13050 =
                           FStar_TypeChecker_Env.try_lookup_lid
                             env.FStar_SMTEncoding_Env.tcenv l in
                         FStar_All.pipe_right uu____13050 FStar_Option.isNone)) in
               if uu____13044
               then []
               else
                 (let uu____13082 =
                    FStar_SMTEncoding_Env.fresh_fvar
                      env.FStar_SMTEncoding_Env.current_module_name "x"
                      FStar_SMTEncoding_Term.Term_sort in
                  match uu____13082 with
                  | (xxsym, xx) ->
                      let uu____13091 =
                        FStar_All.pipe_right datas
                          (FStar_List.fold_left
                             (fun uu____13130 ->
                                fun l ->
                                  match uu____13130 with
                                  | (out, decls) ->
                                      let uu____13150 =
                                        FStar_TypeChecker_Env.lookup_datacon
                                          env.FStar_SMTEncoding_Env.tcenv l in
                                      (match uu____13150 with
                                       | (uu____13161, data_t) ->
                                           let uu____13163 =
                                             FStar_Syntax_Util.arrow_formals
                                               data_t in
                                           (match uu____13163 with
                                            | (args, res) ->
                                                let indices =
                                                  let uu____13183 =
                                                    let uu____13184 =
                                                      FStar_Syntax_Subst.compress
                                                        res in
                                                    uu____13184.FStar_Syntax_Syntax.n in
                                                  match uu____13183 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (uu____13187, indices)
                                                      -> indices
                                                  | uu____13213 -> [] in
                                                let env1 =
                                                  FStar_All.pipe_right args
                                                    (FStar_List.fold_left
                                                       (fun env1 ->
                                                          fun uu____13243 ->
                                                            match uu____13243
                                                            with
                                                            | (x,
                                                               uu____13251)
                                                                ->
                                                                let uu____13256
                                                                  =
                                                                  let uu____13257
                                                                    =
                                                                    let uu____13264
                                                                    =
                                                                    FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x in
                                                                    (uu____13264,
                                                                    [xx]) in
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    uu____13257 in
                                                                FStar_SMTEncoding_Env.push_term_var
                                                                  env1 x
                                                                  uu____13256)
                                                       env) in
                                                let uu____13267 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_args
                                                    indices env1 in
                                                (match uu____13267 with
                                                 | (indices1, decls') ->
                                                     (if
                                                        (FStar_List.length
                                                           indices1)
                                                          <>
                                                          (FStar_List.length
                                                             vars)
                                                      then
                                                        failwith "Impossible"
                                                      else ();
                                                      (let eqs =
                                                         if is_injective
                                                         then
                                                           FStar_List.map2
                                                             (fun v ->
                                                                fun a ->
                                                                  let uu____13298
                                                                    =
                                                                    let uu____13303
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    (uu____13303,
                                                                    a) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____13298)
                                                             vars indices1
                                                         else [] in
                                                       let uu____13305 =
                                                         let uu____13306 =
                                                           let uu____13311 =
                                                             let uu____13312
                                                               =
                                                               let uu____13317
                                                                 =
                                                                 FStar_SMTEncoding_Env.mk_data_tester
                                                                   env1 l xx in
                                                               let uu____13318
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   eqs
                                                                   FStar_SMTEncoding_Util.mk_and_l in
                                                               (uu____13317,
                                                                 uu____13318) in
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               uu____13312 in
                                                           (out, uu____13311) in
                                                         FStar_SMTEncoding_Util.mkOr
                                                           uu____13306 in
                                                       (uu____13305,
                                                         (FStar_List.append
                                                            decls decls'))))))))
                             (FStar_SMTEncoding_Util.mkFalse, [])) in
                      (match uu____13091 with
                       | (data_ax, decls) ->
                           let uu____13333 =
                             FStar_SMTEncoding_Env.fresh_fvar
                               env.FStar_SMTEncoding_Env.current_module_name
                               "f" FStar_SMTEncoding_Term.Fuel_sort in
                           (match uu____13333 with
                            | (ffsym, ff) ->
                                let fuel_guarded_inversion =
                                  let xx_has_type_sfuel =
                                    if
                                      (FStar_List.length datas) >
                                        Prims.int_one
                                    then
                                      let uu____13344 =
                                        FStar_SMTEncoding_Util.mkApp
                                          ("SFuel", [ff]) in
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        uu____13344 xx tapp
                                    else
                                      FStar_SMTEncoding_Term.mk_HasTypeFuel
                                        ff xx tapp in
                                  let uu____13348 =
                                    let uu____13355 =
                                      let uu____13356 =
                                        FStar_Ident.range_of_lid t in
                                      let uu____13357 =
                                        let uu____13368 =
                                          let uu____13369 =
                                            FStar_SMTEncoding_Term.mk_fv
                                              (ffsym,
                                                FStar_SMTEncoding_Term.Fuel_sort) in
                                          let uu____13370 =
                                            let uu____13373 =
                                              FStar_SMTEncoding_Term.mk_fv
                                                (xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort) in
                                            uu____13373 :: vars in
                                          FStar_SMTEncoding_Env.add_fuel
                                            uu____13369 uu____13370 in
                                        let uu____13374 =
                                          FStar_SMTEncoding_Util.mkImp
                                            (xx_has_type_sfuel, data_ax) in
                                        ([[xx_has_type_sfuel]], uu____13368,
                                          uu____13374) in
                                      FStar_SMTEncoding_Term.mkForall
                                        uu____13356 uu____13357 in
                                    let uu____13383 =
                                      let uu____13384 =
                                        let uu____13385 =
                                          FStar_Ident.string_of_lid t in
                                        Prims.op_Hat
                                          "fuel_guarded_inversion_"
                                          uu____13385 in
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                        uu____13384 in
                                    (uu____13355,
                                      (FStar_Pervasives_Native.Some
                                         "inversion axiom"), uu____13383) in
                                  FStar_SMTEncoding_Util.mkAssume uu____13348 in
                                let uu____13386 =
                                  FStar_All.pipe_right
                                    [fuel_guarded_inversion]
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append decls uu____13386))) in
             let uu____13393 =
               let k1 =
                 match tps with
                 | [] -> k
                 | uu____13407 ->
                     let uu____13408 =
                       let uu____13409 =
                         let uu____13424 = FStar_Syntax_Syntax.mk_Total k in
                         (tps, uu____13424) in
                       FStar_Syntax_Syntax.Tm_arrow uu____13409 in
                     FStar_Syntax_Syntax.mk uu____13408
                       k.FStar_Syntax_Syntax.pos in
               let k2 = norm_before_encoding env k1 in
               FStar_Syntax_Util.arrow_formals k2 in
             match uu____13393 with
             | (formals, res) ->
                 let uu____13448 =
                   FStar_SMTEncoding_EncodeTerm.encode_binders
                     FStar_Pervasives_Native.None formals env in
                 (match uu____13448 with
                  | (vars, guards, env', binder_decls, uu____13473) ->
                      let arity = FStar_List.length vars in
                      let uu____13487 =
                        FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                          env t arity in
                      (match uu____13487 with
                       | (tname, ttok, env1) ->
                           let ttok_tm =
                             FStar_SMTEncoding_Util.mkApp (ttok, []) in
                           let guard = FStar_SMTEncoding_Util.mk_and_l guards in
                           let tapp =
                             let uu____13506 =
                               let uu____13513 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars in
                               (tname, uu____13513) in
                             FStar_SMTEncoding_Util.mkApp uu____13506 in
                           let uu____13518 =
                             let tname_decl =
                               let uu____13528 =
                                 let uu____13529 =
                                   FStar_All.pipe_right vars
                                     (FStar_List.map
                                        (fun fv ->
                                           let uu____13546 =
                                             let uu____13547 =
                                               FStar_SMTEncoding_Term.fv_name
                                                 fv in
                                             Prims.op_Hat tname uu____13547 in
                                           let uu____13548 =
                                             FStar_SMTEncoding_Term.fv_sort
                                               fv in
                                           (uu____13546, uu____13548, false))) in
                                 let uu____13549 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                     () in
                                 (tname, uu____13529,
                                   FStar_SMTEncoding_Term.Term_sort,
                                   uu____13549, false) in
                               constructor_or_logic_type_decl uu____13528 in
                             let uu____13552 =
                               match vars with
                               | [] ->
                                   let uu____13565 =
                                     let uu____13566 =
                                       let uu____13569 =
                                         FStar_SMTEncoding_Util.mkApp
                                           (tname, []) in
                                       FStar_All.pipe_left
                                         (fun uu____13574 ->
                                            FStar_Pervasives_Native.Some
                                              uu____13574) uu____13569 in
                                     FStar_SMTEncoding_Env.push_free_var env1
                                       t arity tname uu____13566 in
                                   ([], uu____13565)
                               | uu____13577 ->
                                   let ttok_decl =
                                     FStar_SMTEncoding_Term.DeclFun
                                       (ttok, [],
                                         FStar_SMTEncoding_Term.Term_sort,
                                         (FStar_Pervasives_Native.Some
                                            "token")) in
                                   let ttok_fresh =
                                     let uu____13584 =
                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                         () in
                                     FStar_SMTEncoding_Term.fresh_token
                                       (ttok,
                                         FStar_SMTEncoding_Term.Term_sort)
                                       uu____13584 in
                                   let ttok_app =
                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                       ttok_tm vars in
                                   let pats = [[ttok_app]; [tapp]] in
                                   let name_tok_corr =
                                     let uu____13598 =
                                       let uu____13605 =
                                         let uu____13606 =
                                           FStar_Ident.range_of_lid t in
                                         let uu____13607 =
                                           let uu____13622 =
                                             FStar_SMTEncoding_Util.mkEq
                                               (ttok_app, tapp) in
                                           (pats,
                                             FStar_Pervasives_Native.None,
                                             vars, uu____13622) in
                                         FStar_SMTEncoding_Term.mkForall'
                                           uu____13606 uu____13607 in
                                       (uu____13605,
                                         (FStar_Pervasives_Native.Some
                                            "name-token correspondence"),
                                         (Prims.op_Hat
                                            "token_correspondence_" ttok)) in
                                     FStar_SMTEncoding_Util.mkAssume
                                       uu____13598 in
                                   ([ttok_decl; ttok_fresh; name_tok_corr],
                                     env1) in
                             match uu____13552 with
                             | (tok_decls, env2) ->
                                 let uu____13643 =
                                   FStar_Ident.lid_equals t
                                     FStar_Parser_Const.lex_t_lid in
                                 if uu____13643
                                 then (tok_decls, env2)
                                 else
                                   ((FStar_List.append tname_decl tok_decls),
                                     env2) in
                           (match uu____13518 with
                            | (decls, env2) ->
                                let kindingAx =
                                  let uu____13668 =
                                    FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                      FStar_Pervasives_Native.None res env'
                                      tapp in
                                  match uu____13668 with
                                  | (k1, decls1) ->
                                      let karr =
                                        if
                                          (FStar_List.length formals) >
                                            Prims.int_zero
                                        then
                                          let uu____13688 =
                                            let uu____13689 =
                                              let uu____13696 =
                                                let uu____13697 =
                                                  FStar_SMTEncoding_Term.mk_PreType
                                                    ttok_tm in
                                                FStar_SMTEncoding_Term.mk_tester
                                                  "Tm_arrow" uu____13697 in
                                              (uu____13696,
                                                (FStar_Pervasives_Native.Some
                                                   "kinding"),
                                                (Prims.op_Hat "pre_kinding_"
                                                   ttok)) in
                                            FStar_SMTEncoding_Util.mkAssume
                                              uu____13689 in
                                          [uu____13688]
                                        else [] in
                                      let rng = FStar_Ident.range_of_lid t in
                                      let tot_fun_axioms =
                                        let uu____13701 =
                                          FStar_List.map
                                            (fun uu____13705 ->
                                               FStar_SMTEncoding_Util.mkTrue)
                                            vars in
                                        FStar_SMTEncoding_EncodeTerm.isTotFun_axioms
                                          rng ttok_tm vars uu____13701 true in
                                      let uu____13706 =
                                        let uu____13709 =
                                          let uu____13712 =
                                            let uu____13715 =
                                              let uu____13716 =
                                                let uu____13723 =
                                                  let uu____13724 =
                                                    let uu____13729 =
                                                      let uu____13730 =
                                                        let uu____13741 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (guard, k1) in
                                                        ([[tapp]], vars,
                                                          uu____13741) in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        rng uu____13730 in
                                                    (tot_fun_axioms,
                                                      uu____13729) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13724 in
                                                (uu____13723,
                                                  FStar_Pervasives_Native.None,
                                                  (Prims.op_Hat "kinding_"
                                                     ttok)) in
                                              FStar_SMTEncoding_Util.mkAssume
                                                uu____13716 in
                                            [uu____13715] in
                                          FStar_List.append karr uu____13712 in
                                        FStar_All.pipe_right uu____13709
                                          FStar_SMTEncoding_Term.mk_decls_trivial in
                                      FStar_List.append decls1 uu____13706 in
                                let aux =
                                  let uu____13757 =
                                    let uu____13760 =
                                      inversion_axioms tapp vars in
                                    let uu____13763 =
                                      let uu____13766 =
                                        let uu____13769 =
                                          let uu____13770 =
                                            FStar_Ident.range_of_lid t in
                                          pretype_axiom uu____13770 env2 tapp
                                            vars in
                                        [uu____13769] in
                                      FStar_All.pipe_right uu____13766
                                        FStar_SMTEncoding_Term.mk_decls_trivial in
                                    FStar_List.append uu____13760 uu____13763 in
                                  FStar_List.append kindingAx uu____13757 in
                                let g =
                                  let uu____13778 =
                                    FStar_All.pipe_right decls
                                      FStar_SMTEncoding_Term.mk_decls_trivial in
                                  FStar_List.append uu____13778
                                    (FStar_List.append binder_decls aux) in
                                (g, env2))))))
       | FStar_Syntax_Syntax.Sig_datacon
           (d, uu____13786, uu____13787, uu____13788, uu____13789,
            uu____13790)
           when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
           ([], env)
       | FStar_Syntax_Syntax.Sig_datacon
           (d, uu____13796, t, uu____13798, n_tps, uu____13800) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let t1 = norm_before_encoding env t in
           let uu____13809 = FStar_Syntax_Util.arrow_formals t1 in
           (match uu____13809 with
            | (formals, t_res) ->
                let arity = FStar_List.length formals in
                let uu____13833 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env d arity in
                (match uu____13833 with
                 | (ddconstrsym, ddtok, env1) ->
                     let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
                     let uu____13850 =
                       FStar_SMTEncoding_Env.fresh_fvar
                         env1.FStar_SMTEncoding_Env.current_module_name "f"
                         FStar_SMTEncoding_Term.Fuel_sort in
                     (match uu____13850 with
                      | (fuel_var, fuel_tm) ->
                          let s_fuel_tm =
                            FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                          let uu____13864 =
                            FStar_SMTEncoding_EncodeTerm.encode_binders
                              (FStar_Pervasives_Native.Some fuel_tm) formals
                              env1 in
                          (match uu____13864 with
                           | (vars, guards, env', binder_decls, names) ->
                               let fields =
                                 FStar_All.pipe_right names
                                   (FStar_List.mapi
                                      (fun n ->
                                         fun x ->
                                           let projectible = true in
                                           let uu____13934 =
                                             FStar_SMTEncoding_Env.mk_term_projector_name
                                               d x in
                                           (uu____13934,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             projectible))) in
                               let datacons =
                                 let uu____13938 =
                                   let uu____13939 =
                                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                       () in
                                   (ddconstrsym, fields,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     uu____13939, true) in
                                 let uu____13942 =
                                   let uu____13949 =
                                     FStar_Ident.range_of_lid d in
                                   FStar_SMTEncoding_Term.constructor_to_decl
                                     uu____13949 in
                                 FStar_All.pipe_right uu____13938 uu____13942 in
                               let app =
                                 FStar_SMTEncoding_EncodeTerm.mk_Apply
                                   ddtok_tm vars in
                               let guard =
                                 FStar_SMTEncoding_Util.mk_and_l guards in
                               let xvars =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars in
                               let dapp =
                                 FStar_SMTEncoding_Util.mkApp
                                   (ddconstrsym, xvars) in
                               let uu____13960 =
                                 FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                   FStar_Pervasives_Native.None t1 env1
                                   ddtok_tm in
                               (match uu____13960 with
                                | (tok_typing, decls3) ->
                                    let tok_typing1 =
                                      match fields with
                                      | uu____13972::uu____13973 ->
                                          let ff =
                                            FStar_SMTEncoding_Term.mk_fv
                                              ("ty",
                                                FStar_SMTEncoding_Term.Term_sort) in
                                          let f =
                                            FStar_SMTEncoding_Util.mkFreeV ff in
                                          let vtok_app_l =
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              ddtok_tm [ff] in
                                          let vtok_app_r =
                                            let uu____14010 =
                                              let uu____14011 =
                                                FStar_SMTEncoding_Term.mk_fv
                                                  (ddtok,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              [uu____14011] in
                                            FStar_SMTEncoding_EncodeTerm.mk_Apply
                                              f uu____14010 in
                                          let uu____14030 =
                                            FStar_Ident.range_of_lid d in
                                          let uu____14031 =
                                            let uu____14042 =
                                              FStar_SMTEncoding_Term.mk_NoHoist
                                                f tok_typing in
                                            ([[vtok_app_l]; [vtok_app_r]],
                                              [ff], uu____14042) in
                                          FStar_SMTEncoding_Term.mkForall
                                            uu____14030 uu____14031
                                      | uu____14065 -> tok_typing in
                                    let uu____14074 =
                                      FStar_SMTEncoding_EncodeTerm.encode_binders
                                        (FStar_Pervasives_Native.Some fuel_tm)
                                        formals env1 in
                                    (match uu____14074 with
                                     | (vars', guards', env'', decls_formals,
                                        uu____14099) ->
                                         let uu____14112 =
                                           let xvars1 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars' in
                                           let dapp1 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (ddconstrsym, xvars1) in
                                           FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                             (FStar_Pervasives_Native.Some
                                                fuel_tm) t_res env'' dapp1 in
                                         (match uu____14112 with
                                          | (ty_pred', decls_pred) ->
                                              let guard' =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards' in
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu____14141 ->
                                                    let uu____14142 =
                                                      let uu____14143 =
                                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                          () in
                                                      FStar_SMTEncoding_Term.fresh_token
                                                        (ddtok,
                                                          FStar_SMTEncoding_Term.Term_sort)
                                                        uu____14143 in
                                                    [uu____14142] in
                                              let encode_elim uu____14157 =
                                                let uu____14158 =
                                                  FStar_Syntax_Util.head_and_args
                                                    t_res in
                                                match uu____14158 with
                                                | (head, args) ->
                                                    let uu____14209 =
                                                      let uu____14210 =
                                                        FStar_Syntax_Subst.compress
                                                          head in
                                                      uu____14210.FStar_Syntax_Syntax.n in
                                                    (match uu____14209 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____14222;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____14223;_},
                                                          uu____14224)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name in
                                                         let uu____14230 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env' in
                                                         (match uu____14230
                                                          with
                                                          | (encoded_args,
                                                             arg_decls) ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                  | uu____14287
                                                                    ->
                                                                    let uu____14288
                                                                    =
                                                                    let uu____14293
                                                                    =
                                                                    let uu____14294
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14294 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14293) in
                                                                    FStar_Errors.raise_error
                                                                    uu____14288
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____14312
                                                                    =
                                                                    let uu____14313
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14313 in
                                                                    if
                                                                    uu____14312
                                                                    then
                                                                    let uu____14330
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14330]
                                                                    else [])) in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1 in
                                                              let uu____14332
                                                                =
                                                                let uu____14345
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14401
                                                                    ->
                                                                    fun
                                                                    uu____14402
                                                                    ->
                                                                    match 
                                                                    (uu____14401,
                                                                    uu____14402)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____14507
                                                                    =
                                                                    let uu____14514
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14514 in
                                                                    (match uu____14507
                                                                    with
                                                                    | 
                                                                    (uu____14527,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14535
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____14535
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14539
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14539
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                  (env', [],
                                                                    [],
                                                                    Prims.int_zero)
                                                                  uu____14345 in
                                                              (match uu____14332
                                                               with
                                                               | (uu____14556,
                                                                  arg_vars,
                                                                  elim_eqns_or_guards,
                                                                  uu____14559)
                                                                   ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1 in
                                                                   let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                   let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                   let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                   let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                   let typing_inversion
                                                                    =
                                                                    let uu____14583
                                                                    =
                                                                    let uu____14590
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____14592
                                                                    =
                                                                    let uu____14603
                                                                    =
                                                                    let uu____14604
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14604
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14605
                                                                    =
                                                                    let uu____14606
                                                                    =
                                                                    let uu____14611
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14611) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14606 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14603,
                                                                    uu____14605) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14591
                                                                    uu____14592 in
                                                                    (uu____14590,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14583 in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____14622
                                                                    =
                                                                    let uu____14623
                                                                    =
                                                                    let uu____14628
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid in
                                                                    (uu____14628,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____14623 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____14622 in
                                                                    let prec
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____14652
                                                                    =
                                                                    let uu____14653
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____14653
                                                                    dapp1 in
                                                                    [uu____14652]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14632
                                                                    FStar_List.flatten in
                                                                    let uu____14660
                                                                    =
                                                                    let uu____14667
                                                                    =
                                                                    let uu____14668
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____14669
                                                                    =
                                                                    let uu____14680
                                                                    =
                                                                    let uu____14681
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____14681
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14682
                                                                    =
                                                                    let uu____14683
                                                                    =
                                                                    let uu____14688
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14688) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14683 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14680,
                                                                    uu____14682) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____14668
                                                                    uu____14669 in
                                                                    (uu____14667,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14660 in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStar_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStar_Syntax_Syntax.fv_name in
                                                         let uu____14703 =
                                                           FStar_SMTEncoding_EncodeTerm.encode_args
                                                             args env' in
                                                         (match uu____14703
                                                          with
                                                          | (encoded_args,
                                                             arg_decls) ->
                                                              let guards_for_parameter
                                                                orig_arg arg
                                                                xv =
                                                                let fv1 =
                                                                  match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                  with
                                                                  | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                  | uu____14760
                                                                    ->
                                                                    let uu____14761
                                                                    =
                                                                    let uu____14766
                                                                    =
                                                                    let uu____14767
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14767 in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____14766) in
                                                                    FStar_Errors.raise_error
                                                                    uu____14761
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                                let guards1 =
                                                                  FStar_All.pipe_right
                                                                    guards
                                                                    (
                                                                    FStar_List.collect
                                                                    (fun g ->
                                                                    let uu____14785
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14786 in
                                                                    if
                                                                    uu____14785
                                                                    then
                                                                    let uu____14803
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14803]
                                                                    else [])) in
                                                                FStar_SMTEncoding_Util.mk_and_l
                                                                  guards1 in
                                                              let uu____14805
                                                                =
                                                                let uu____14818
                                                                  =
                                                                  FStar_List.zip
                                                                    args
                                                                    encoded_args in
                                                                FStar_List.fold_left
                                                                  (fun
                                                                    uu____14874
                                                                    ->
                                                                    fun
                                                                    uu____14875
                                                                    ->
                                                                    match 
                                                                    (uu____14874,
                                                                    uu____14875)
                                                                    with
                                                                    | 
                                                                    ((env2,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu____14980
                                                                    =
                                                                    let uu____14987
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____14987 in
                                                                    (match uu____14980
                                                                    with
                                                                    | 
                                                                    (uu____15000,
                                                                    xv, env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15008
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15008
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15012
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15012
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                  (env', [],
                                                                    [],
                                                                    Prims.int_zero)
                                                                  uu____14818 in
                                                              (match uu____14805
                                                               with
                                                               | (uu____15029,
                                                                  arg_vars,
                                                                  elim_eqns_or_guards,
                                                                  uu____15032)
                                                                   ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                   let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    encoded_head_fvb
                                                                    arg_vars1 in
                                                                   let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                   let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                   let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                   let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                   let typing_inversion
                                                                    =
                                                                    let uu____15056
                                                                    =
                                                                    let uu____15063
                                                                    =
                                                                    let uu____15064
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____15065
                                                                    =
                                                                    let uu____15076
                                                                    =
                                                                    let uu____15077
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15077
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15078
                                                                    =
                                                                    let uu____15079
                                                                    =
                                                                    let uu____15084
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15084) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15079 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15076,
                                                                    uu____15078) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15064
                                                                    uu____15065 in
                                                                    (uu____15063,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.op_Hat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15056 in
                                                                   let subterm_ordering
                                                                    =
                                                                    let lex_t
                                                                    =
                                                                    let uu____15095
                                                                    =
                                                                    let uu____15096
                                                                    =
                                                                    let uu____15101
                                                                    =
                                                                    FStar_Ident.string_of_lid
                                                                    FStar_Parser_Const.lex_t_lid in
                                                                    (uu____15101,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    uu____15096 in
                                                                    FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____15095 in
                                                                    let prec
                                                                    =
                                                                    let uu____15105
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i ->
                                                                    fun v ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____15125
                                                                    =
                                                                    let uu____15126
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t
                                                                    lex_t
                                                                    uu____15126
                                                                    dapp1 in
                                                                    [uu____15125]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15105
                                                                    FStar_List.flatten in
                                                                    let uu____15133
                                                                    =
                                                                    let uu____15140
                                                                    =
                                                                    let uu____15141
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____15142
                                                                    =
                                                                    let uu____15153
                                                                    =
                                                                    let uu____15154
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15154
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15155
                                                                    =
                                                                    let uu____15156
                                                                    =
                                                                    let uu____15161
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15161) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15156 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15153,
                                                                    uu____15155) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15141
                                                                    uu____15142 in
                                                                    (uu____15140,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.op_Hat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15133 in
                                                                   (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                     | uu____15174 ->
                                                         ((let uu____15176 =
                                                             let uu____15181
                                                               =
                                                               let uu____15182
                                                                 =
                                                                 FStar_Syntax_Print.lid_to_string
                                                                   d in
                                                               let uu____15183
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   head in
                                                               FStar_Util.format2
                                                                 "Constructor %s builds an unexpected type %s\n"
                                                                 uu____15182
                                                                 uu____15183 in
                                                             (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                               uu____15181) in
                                                           FStar_Errors.log_issue
                                                             se.FStar_Syntax_Syntax.sigrng
                                                             uu____15176);
                                                          ([], []))) in
                                              let uu____15188 =
                                                encode_elim () in
                                              (match uu____15188 with
                                               | (decls2, elim) ->
                                                   let g =
                                                     let uu____15214 =
                                                       let uu____15217 =
                                                         let uu____15220 =
                                                           let uu____15223 =
                                                             let uu____15226
                                                               =
                                                               let uu____15229
                                                                 =
                                                                 let uu____15232
                                                                   =
                                                                   let uu____15233
                                                                    =
                                                                    let uu____15244
                                                                    =
                                                                    let uu____15245
                                                                    =
                                                                    let uu____15246
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15246 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____15245 in
                                                                    (ddtok,
                                                                    [],
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    uu____15244) in
                                                                   FStar_SMTEncoding_Term.DeclFun
                                                                    uu____15233 in
                                                                 [uu____15232] in
                                                               FStar_List.append
                                                                 uu____15229
                                                                 proxy_fresh in
                                                             FStar_All.pipe_right
                                                               uu____15226
                                                               FStar_SMTEncoding_Term.mk_decls_trivial in
                                                           let uu____15253 =
                                                             let uu____15256
                                                               =
                                                               let uu____15259
                                                                 =
                                                                 let uu____15262
                                                                   =
                                                                   let uu____15265
                                                                    =
                                                                    let uu____15268
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.op_Hat
                                                                    "typing_tok_"
                                                                    ddtok)) in
                                                                    let uu____15269
                                                                    =
                                                                    let uu____15272
                                                                    =
                                                                    let uu____15273
                                                                    =
                                                                    let uu____15280
                                                                    =
                                                                    let uu____15281
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____15282
                                                                    =
                                                                    let uu____15293
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15293) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15281
                                                                    uu____15282 in
                                                                    (uu____15280,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.op_Hat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15273 in
                                                                    let uu____15302
                                                                    =
                                                                    let uu____15305
                                                                    =
                                                                    let uu____15306
                                                                    =
                                                                    let uu____15313
                                                                    =
                                                                    let uu____15314
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d in
                                                                    let uu____15315
                                                                    =
                                                                    let uu____15326
                                                                    =
                                                                    let uu____15327
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort) in
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    uu____15327
                                                                    vars' in
                                                                    let uu____15328
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15326,
                                                                    uu____15328) in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____15314
                                                                    uu____15315 in
                                                                    (uu____15313,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.op_Hat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15306 in
                                                                    [uu____15305] in
                                                                    uu____15272
                                                                    ::
                                                                    uu____15302 in
                                                                    uu____15268
                                                                    ::
                                                                    uu____15269 in
                                                                   FStar_List.append
                                                                    uu____15265
                                                                    elim in
                                                                 FStar_All.pipe_right
                                                                   uu____15262
                                                                   FStar_SMTEncoding_Term.mk_decls_trivial in
                                                               FStar_List.append
                                                                 decls_pred
                                                                 uu____15259 in
                                                             FStar_List.append
                                                               decls_formals
                                                               uu____15256 in
                                                           FStar_List.append
                                                             uu____15223
                                                             uu____15253 in
                                                         FStar_List.append
                                                           decls3 uu____15220 in
                                                       FStar_List.append
                                                         decls2 uu____15217 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____15214 in
                                                   let uu____15341 =
                                                     let uu____15342 =
                                                       FStar_All.pipe_right
                                                         datacons
                                                         FStar_SMTEncoding_Term.mk_decls_trivial in
                                                     FStar_List.append
                                                       uu____15342 g in
                                                   (uu____15341, env1))))))))))
and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun ses ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15376 ->
              fun se ->
                match uu____15376 with
                | (g, env1) ->
                    let uu____15396 = encode_sigelt env1 se in
                    (match uu____15396 with
                     | (g', env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun bindings ->
      let encode_binding b uu____15461 =
        match uu____15461 with
        | (i, decls, env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____15493 ->
                 ((i + Prims.int_one), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   norm_before_encoding env1 x.FStar_Syntax_Syntax.sort in
                 ((let uu____15499 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15499
                   then
                     let uu____15500 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15501 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15502 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15500 uu____15501 uu____15502
                   else ());
                  (let uu____15504 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1 in
                   match uu____15504 with
                   | (t, decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15520 =
                         let uu____15527 =
                           let uu____15528 =
                             let uu____15529 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.op_Hat uu____15529
                               (Prims.op_Hat "_" (Prims.string_of_int i)) in
                           Prims.op_Hat "x_" uu____15528 in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____15527 in
                       (match uu____15520 with
                        | (xxsym, xx, env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____15543 = FStar_Options.log_queries () in
                              if uu____15543
                              then
                                let uu____15544 =
                                  let uu____15545 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15546 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15547 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15545 uu____15546 uu____15547 in
                                FStar_Pervasives_Native.Some uu____15544
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.op_Hat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              let uu____15554 =
                                FStar_All.pipe_right
                                  [FStar_SMTEncoding_Term.DeclFun
                                     (xxsym, [],
                                       FStar_SMTEncoding_Term.Term_sort,
                                       caption)]
                                  FStar_SMTEncoding_Term.mk_decls_trivial in
                              let uu____15563 =
                                let uu____15566 =
                                  FStar_All.pipe_right [ax]
                                    FStar_SMTEncoding_Term.mk_decls_trivial in
                                FStar_List.append decls' uu____15566 in
                              FStar_List.append uu____15554 uu____15563 in
                            ((i + Prims.int_one),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x, (uu____15576, t)) ->
                 let t_norm = norm_before_encoding env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____15590 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____15590 with
                  | (g, env') ->
                      ((i + Prims.int_one), (FStar_List.append decls g),
                        env'))) in
      let uu____15607 =
        FStar_List.fold_right encode_binding bindings
          (Prims.int_zero, [], env) in
      match uu____15607 with | (uu____15630, decls, env1) -> (decls, env1)
let (encode_labels :
  FStar_SMTEncoding_Term.error_label Prims.list ->
    (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl
      Prims.list))
  =
  fun labs ->
    let prefix =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____15678 ->
              match uu____15678 with
              | (l, uu____15686, uu____15687) ->
                  let uu____15688 =
                    let uu____15699 = FStar_SMTEncoding_Term.fv_name l in
                    (uu____15699, [], FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None) in
                  FStar_SMTEncoding_Term.DeclFun uu____15688)) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____15727 ->
              match uu____15727 with
              | (l, uu____15737, uu____15738) ->
                  let uu____15739 =
                    let uu____15740 = FStar_SMTEncoding_Term.fv_name l in
                    FStar_All.pipe_left
                      (fun uu____15741 ->
                         FStar_SMTEncoding_Term.Echo uu____15741) uu____15740 in
                  let uu____15742 =
                    let uu____15745 =
                      let uu____15746 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____15746 in
                    [uu____15745] in
                  uu____15739 :: uu____15742)) in
    (prefix, suffix)
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    let uu____15762 =
      let uu____15765 =
        let uu____15766 = FStar_Util.psmap_empty () in
        let uu____15781 =
          let uu____15790 = FStar_Util.psmap_empty () in (uu____15790, []) in
        let uu____15797 =
          let uu____15798 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15798 FStar_Ident.string_of_lid in
        let uu____15799 = FStar_Util.smap_create (Prims.of_int (100)) in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____15766;
          FStar_SMTEncoding_Env.fvar_bindings = uu____15781;
          FStar_SMTEncoding_Env.depth = Prims.int_zero;
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____15797;
          FStar_SMTEncoding_Env.encoding_quantifier = false;
          FStar_SMTEncoding_Env.global_cache = uu____15799
        } in
      [uu____15765] in
    FStar_ST.op_Colon_Equals last_env uu____15762
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn ->
    fun tcenv ->
      let uu____15822 = FStar_ST.op_Bang last_env in
      match uu____15822 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15836 ->
          let uu___1580_15839 = e in
          let uu____15840 = FStar_Ident.string_of_lid cmn in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___1580_15839.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___1580_15839.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___1580_15839.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___1580_15839.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.nolabels =
              (uu___1580_15839.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___1580_15839.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___1580_15839.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____15840;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___1580_15839.FStar_SMTEncoding_Env.encoding_quantifier);
            FStar_SMTEncoding_Env.global_cache =
              (uu___1580_15839.FStar_SMTEncoding_Env.global_cache)
          }
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env ->
    let uu____15846 = FStar_ST.op_Bang last_env in
    match uu____15846 with
    | [] -> failwith "Empty env stack"
    | uu____15859::tl -> FStar_ST.op_Colon_Equals last_env (env :: tl)
let (push_env : unit -> unit) =
  fun uu____15877 ->
    let uu____15878 = FStar_ST.op_Bang last_env in
    match uu____15878 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let top = copy_env hd in
        FStar_ST.op_Colon_Equals last_env (top :: hd :: tl)
let (pop_env : unit -> unit) =
  fun uu____15910 ->
    let uu____15911 = FStar_ST.op_Bang last_env in
    match uu____15911 with
    | [] -> failwith "Popping an empty stack"
    | uu____15924::tl -> FStar_ST.op_Colon_Equals last_env tl
let (snapshot_env : unit -> (Prims.int * unit)) =
  fun uu____15946 -> FStar_Common.snapshot push_env last_env ()
let (rollback_env : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_env last_env depth
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let (snapshot :
  Prims.string -> (FStar_TypeChecker_Env.solver_depth_t * unit)) =
  fun msg ->
    FStar_Util.atomically
      (fun uu____15989 ->
         let uu____15990 = snapshot_env () in
         match uu____15990 with
         | (env_depth, ()) ->
             let uu____16006 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot () in
             (match uu____16006 with
              | (varops_depth, ()) ->
                  let uu____16022 = FStar_SMTEncoding_Z3.snapshot msg in
                  (match uu____16022 with
                   | (z3_depth, ()) ->
                       ((env_depth, varops_depth, z3_depth), ()))))
let (rollback :
  Prims.string ->
    FStar_TypeChecker_Env.solver_depth_t FStar_Pervasives_Native.option ->
      unit)
  =
  fun msg ->
    fun depth ->
      FStar_Util.atomically
        (fun uu____16065 ->
           let uu____16066 =
             match depth with
             | FStar_Pervasives_Native.Some (s1, s2, s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None) in
           match uu____16066 with
           | (env_depth, varops_depth, z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
let (push : Prims.string -> unit) =
  fun msg -> let uu____16128 = snapshot msg in ()
let (pop : Prims.string -> unit) =
  fun msg -> rollback msg FStar_Pervasives_Native.None
let (open_fact_db_tags :
  FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  = fun env -> []
let (place_decl_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env ->
    fun fact_db_ids ->
      fun d ->
        match (fact_db_ids, d) with
        | (uu____16169::uu____16170, FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___1641_16178 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___1641_16178.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___1641_16178.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___1641_16178.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16179 -> d
let (place_decl_elt_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_elt)
  =
  fun env ->
    fun fact_db_ids ->
      fun elt ->
        let uu___1647_16205 = elt in
        let uu____16206 =
          FStar_All.pipe_right elt.FStar_SMTEncoding_Term.decls
            (FStar_List.map (place_decl_in_fact_dbs env fact_db_ids)) in
        {
          FStar_SMTEncoding_Term.sym_name =
            (uu___1647_16205.FStar_SMTEncoding_Term.sym_name);
          FStar_SMTEncoding_Term.key =
            (uu___1647_16205.FStar_SMTEncoding_Term.key);
          FStar_SMTEncoding_Term.decls = uu____16206;
          FStar_SMTEncoding_Term.a_names =
            (uu___1647_16205.FStar_SMTEncoding_Term.a_names)
        }
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env ->
    fun lid ->
      let uu____16225 =
        let uu____16228 =
          let uu____16229 =
            let uu____16230 = FStar_Ident.ns_of_lid lid in
            FStar_Ident.lid_of_ids uu____16230 in
          FStar_SMTEncoding_Term.Namespace uu____16229 in
        let uu____16231 = open_fact_db_tags env in uu____16228 :: uu____16231 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16225
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_elt Prims.list *
        FStar_SMTEncoding_Env.env_t))
  =
  fun env ->
    fun se ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____16257 = encode_sigelt env se in
      match uu____16257 with
      | (g, env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_elt_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let (recover_caching_and_update_env :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t)
  =
  fun env ->
    fun decls ->
      FStar_All.pipe_right decls
        (FStar_List.collect
           (fun elt ->
              if
                elt.FStar_SMTEncoding_Term.key = FStar_Pervasives_Native.None
              then [elt]
              else
                (let uu____16298 =
                   let uu____16301 =
                     FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                       FStar_Util.must in
                   FStar_Util.smap_try_find
                     env.FStar_SMTEncoding_Env.global_cache uu____16301 in
                 match uu____16298 with
                 | FStar_Pervasives_Native.Some cache_elt ->
                     FStar_All.pipe_right
                       [FStar_SMTEncoding_Term.RetainAssumptions
                          (cache_elt.FStar_SMTEncoding_Term.a_names)]
                       FStar_SMTEncoding_Term.mk_decls_trivial
                 | FStar_Pervasives_Native.None ->
                     ((let uu____16312 =
                         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key
                           FStar_Util.must in
                       FStar_Util.smap_add
                         env.FStar_SMTEncoding_Env.global_cache uu____16312
                         elt);
                      [elt]))))
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv ->
    fun se ->
      let caption decls =
        let uu____16337 = FStar_Options.log_queries () in
        if uu____16337
        then
          let uu____16340 =
            let uu____16341 =
              let uu____16342 =
                let uu____16343 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16343 (FStar_String.concat ", ") in
              Prims.op_Hat "encoding sigelt " uu____16342 in
            FStar_SMTEncoding_Term.Caption uu____16341 in
          uu____16340 :: decls
        else decls in
      (let uu____16354 =
         FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
       if uu____16354
       then
         let uu____16355 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____16355
       else ());
      (let env =
         let uu____16358 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____16358 tcenv in
       let uu____16359 = encode_top_level_facts env se in
       match uu____16359 with
       | (decls, env1) ->
           (set_env env1;
            (let uu____16373 =
               let uu____16376 =
                 let uu____16379 =
                   FStar_All.pipe_right decls
                     (recover_caching_and_update_env env1) in
                 FStar_All.pipe_right uu____16379
                   FStar_SMTEncoding_Term.decls_list_of in
               caption uu____16376 in
             FStar_SMTEncoding_Z3.giveZ3 uu____16373)))
let (give_decls_to_z3_and_set_env :
  FStar_SMTEncoding_Env.env_t ->
    Prims.string -> FStar_SMTEncoding_Term.decls_t -> unit)
  =
  fun env ->
    fun name ->
      fun decls ->
        let caption decls1 =
          let uu____16409 = FStar_Options.log_queries () in
          if uu____16409
          then
            let msg = Prims.op_Hat "Externals for " name in
            [FStar_SMTEncoding_Term.Module
               (name,
                 (FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                    decls1)
                    [FStar_SMTEncoding_Term.Caption (Prims.op_Hat "End " msg)]))]
          else [FStar_SMTEncoding_Term.Module (name, decls1)] in
        set_env
          (let uu___1685_16421 = env in
           {
             FStar_SMTEncoding_Env.bvar_bindings =
               (uu___1685_16421.FStar_SMTEncoding_Env.bvar_bindings);
             FStar_SMTEncoding_Env.fvar_bindings =
               (uu___1685_16421.FStar_SMTEncoding_Env.fvar_bindings);
             FStar_SMTEncoding_Env.depth =
               (uu___1685_16421.FStar_SMTEncoding_Env.depth);
             FStar_SMTEncoding_Env.tcenv =
               (uu___1685_16421.FStar_SMTEncoding_Env.tcenv);
             FStar_SMTEncoding_Env.warn = true;
             FStar_SMTEncoding_Env.nolabels =
               (uu___1685_16421.FStar_SMTEncoding_Env.nolabels);
             FStar_SMTEncoding_Env.use_zfuel_name =
               (uu___1685_16421.FStar_SMTEncoding_Env.use_zfuel_name);
             FStar_SMTEncoding_Env.encode_non_total_function_typ =
               (uu___1685_16421.FStar_SMTEncoding_Env.encode_non_total_function_typ);
             FStar_SMTEncoding_Env.current_module_name =
               (uu___1685_16421.FStar_SMTEncoding_Env.current_module_name);
             FStar_SMTEncoding_Env.encoding_quantifier =
               (uu___1685_16421.FStar_SMTEncoding_Env.encoding_quantifier);
             FStar_SMTEncoding_Env.global_cache =
               (uu___1685_16421.FStar_SMTEncoding_Env.global_cache)
           });
        (let z3_decls =
           let uu____16425 =
             let uu____16428 =
               FStar_All.pipe_right decls
                 (recover_caching_and_update_env env) in
             FStar_All.pipe_right uu____16428
               FStar_SMTEncoding_Term.decls_list_of in
           caption uu____16425 in
         FStar_SMTEncoding_Z3.giveZ3 z3_decls)
let (encode_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list))
  =
  fun tcenv ->
    fun modul ->
      let uu____16447 = (FStar_Options.lax ()) && (FStar_Options.ml_ish ()) in
      if uu____16447
      then ([], [])
      else
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____16477 ->
             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.reset_fresh
               ();
             (let name =
                let uu____16480 =
                  FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
                FStar_Util.format2 "%s %s"
                  (if modul.FStar_Syntax_Syntax.is_interface
                   then "interface"
                   else "module") uu____16480 in
              (let uu____16483 =
                 FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
               if uu____16483
               then
                 let uu____16484 =
                   FStar_All.pipe_right
                     (FStar_List.length
                        modul.FStar_Syntax_Syntax.declarations)
                     Prims.string_of_int in
                 FStar_Util.print2
                   "+++++++++++Encoding externals for %s ... %s declarations\n"
                   name uu____16484
               else ());
              (let env =
                 let uu____16487 =
                   get_env modul.FStar_Syntax_Syntax.name tcenv in
                 FStar_All.pipe_right uu____16487
                   FStar_SMTEncoding_Env.reset_current_module_fvbs in
               let encode_signature env1 ses =
                 FStar_All.pipe_right ses
                   (FStar_List.fold_left
                      (fun uu____16526 ->
                         fun se ->
                           match uu____16526 with
                           | (g, env2) ->
                               let uu____16546 =
                                 encode_top_level_facts env2 se in
                               (match uu____16546 with
                                | (g', env3) ->
                                    ((FStar_List.append g g'), env3)))
                      ([], env1)) in
               let uu____16569 =
                 encode_signature
                   (let uu___1709_16578 = env in
                    {
                      FStar_SMTEncoding_Env.bvar_bindings =
                        (uu___1709_16578.FStar_SMTEncoding_Env.bvar_bindings);
                      FStar_SMTEncoding_Env.fvar_bindings =
                        (uu___1709_16578.FStar_SMTEncoding_Env.fvar_bindings);
                      FStar_SMTEncoding_Env.depth =
                        (uu___1709_16578.FStar_SMTEncoding_Env.depth);
                      FStar_SMTEncoding_Env.tcenv =
                        (uu___1709_16578.FStar_SMTEncoding_Env.tcenv);
                      FStar_SMTEncoding_Env.warn = false;
                      FStar_SMTEncoding_Env.nolabels =
                        (uu___1709_16578.FStar_SMTEncoding_Env.nolabels);
                      FStar_SMTEncoding_Env.use_zfuel_name =
                        (uu___1709_16578.FStar_SMTEncoding_Env.use_zfuel_name);
                      FStar_SMTEncoding_Env.encode_non_total_function_typ =
                        (uu___1709_16578.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                      FStar_SMTEncoding_Env.current_module_name =
                        (uu___1709_16578.FStar_SMTEncoding_Env.current_module_name);
                      FStar_SMTEncoding_Env.encoding_quantifier =
                        (uu___1709_16578.FStar_SMTEncoding_Env.encoding_quantifier);
                      FStar_SMTEncoding_Env.global_cache =
                        (uu___1709_16578.FStar_SMTEncoding_Env.global_cache)
                    }) modul.FStar_Syntax_Syntax.declarations in
               match uu____16569 with
               | (decls, env1) ->
                   (give_decls_to_z3_and_set_env env1 name decls;
                    (let uu____16595 =
                       FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                     if uu____16595
                     then
                       FStar_Util.print1 "Done encoding externals for %s\n"
                         name
                     else ());
                    (let uu____16597 =
                       FStar_All.pipe_right env1
                         FStar_SMTEncoding_Env.get_current_module_fvbs in
                     (decls, uu____16597))))))
let (encode_modul_from_cache :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
        Prims.list) -> unit)
  =
  fun tcenv ->
    fun tcmod ->
      fun uu____16626 ->
        match uu____16626 with
        | (decls, fvbs) ->
            let uu____16639 =
              (FStar_Options.lax ()) && (FStar_Options.ml_ish ()) in
            if uu____16639
            then ()
            else
              (let name =
                 let uu____16642 =
                   FStar_Ident.string_of_lid tcmod.FStar_Syntax_Syntax.name in
                 FStar_Util.format2 "%s %s"
                   (if tcmod.FStar_Syntax_Syntax.is_interface
                    then "interface"
                    else "module") uu____16642 in
               (let uu____16645 =
                  FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                if uu____16645
                then
                  let uu____16646 =
                    FStar_All.pipe_right (FStar_List.length decls)
                      Prims.string_of_int in
                  FStar_Util.print2
                    "+++++++++++Encoding externals from cache for %s ... %s decls\n"
                    name uu____16646
                else ());
               (let env =
                  let uu____16649 =
                    get_env tcmod.FStar_Syntax_Syntax.name tcenv in
                  FStar_All.pipe_right uu____16649
                    FStar_SMTEncoding_Env.reset_current_module_fvbs in
                let env1 =
                  let uu____16651 = FStar_All.pipe_right fvbs FStar_List.rev in
                  FStar_All.pipe_right uu____16651
                    (FStar_List.fold_left
                       (fun env1 ->
                          fun fvb ->
                            FStar_SMTEncoding_Env.add_fvar_binding_to_env fvb
                              env1) env) in
                give_decls_to_z3_and_set_env env1 name decls;
                (let uu____16665 =
                   FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium in
                 if uu____16665
                 then
                   FStar_Util.print1
                     "Done encoding externals from cache for %s\n" name
                 else ())))
let (encode_query :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_ErrorReporting.label Prims.list *
          FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl
          Prims.list))
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        FStar_Errors.with_ctx "While encoding a query"
          (fun uu____16757 ->
             (let uu____16759 =
                let uu____16760 = FStar_TypeChecker_Env.current_module tcenv in
                FStar_Ident.string_of_lid uu____16760 in
              FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
                uu____16759);
             (let env =
                let uu____16762 = FStar_TypeChecker_Env.current_module tcenv in
                get_env uu____16762 tcenv in
              let uu____16763 =
                let rec aux bindings =
                  match bindings with
                  | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                      let uu____16800 = aux rest in
                      (match uu____16800 with
                       | (out, rest1) ->
                           let t =
                             let uu____16828 =
                               FStar_Syntax_Util.destruct_typ_as_formula
                                 x.FStar_Syntax_Syntax.sort in
                             match uu____16828 with
                             | FStar_Pervasives_Native.Some uu____16831 ->
                                 let uu____16832 =
                                   FStar_Syntax_Syntax.new_bv
                                     FStar_Pervasives_Native.None
                                     FStar_Syntax_Syntax.t_unit in
                                 FStar_Syntax_Util.refine uu____16832
                                   x.FStar_Syntax_Syntax.sort
                             | uu____16833 -> x.FStar_Syntax_Syntax.sort in
                           let t1 =
                             norm_with_steps
                               [FStar_TypeChecker_Env.Eager_unfolding;
                               FStar_TypeChecker_Env.Beta;
                               FStar_TypeChecker_Env.Simplify;
                               FStar_TypeChecker_Env.Primops;
                               FStar_TypeChecker_Env.EraseUniverses]
                               env.FStar_SMTEncoding_Env.tcenv t in
                           let uu____16837 =
                             let uu____16840 =
                               FStar_Syntax_Syntax.mk_binder
                                 (let uu___1753_16843 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1753_16843.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1753_16843.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }) in
                             uu____16840 :: out in
                           (uu____16837, rest1))
                  | uu____16848 -> ([], bindings) in
                let uu____16855 = aux tcenv.FStar_TypeChecker_Env.gamma in
                match uu____16855 with
                | (closing, bindings) ->
                    let uu____16880 =
                      FStar_Syntax_Util.close_forall_no_univs
                        (FStar_List.rev closing) q in
                    (uu____16880, bindings) in
              match uu____16763 with
              | (q1, bindings) ->
                  let uu____16901 = encode_env_bindings env bindings in
                  (match uu____16901 with
                   | (env_decls, env1) ->
                       ((let uu____16921 =
                           ((FStar_TypeChecker_Env.debug tcenv
                               FStar_Options.Medium)
                              ||
                              (FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug tcenv)
                                 (FStar_Options.Other "SMTEncoding")))
                             ||
                             (FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug tcenv)
                                (FStar_Options.Other "SMTQuery")) in
                         if uu____16921
                         then
                           let uu____16922 =
                             FStar_Syntax_Print.term_to_string q1 in
                           FStar_Util.print1 "Encoding query formula {: %s\n"
                             uu____16922
                         else ());
                        (let uu____16924 =
                           FStar_Util.record_time
                             (fun uu____16938 ->
                                FStar_SMTEncoding_EncodeTerm.encode_formula
                                  q1 env1) in
                         match uu____16924 with
                         | ((phi, qdecls), ms) ->
                             let uu____16958 =
                               let uu____16963 =
                                 FStar_TypeChecker_Env.get_range tcenv in
                               FStar_SMTEncoding_ErrorReporting.label_goals
                                 use_env_msg uu____16963 phi in
                             (match uu____16958 with
                              | (labels, phi1) ->
                                  let uu____16978 = encode_labels labels in
                                  (match uu____16978 with
                                   | (label_prefix, label_suffix) ->
                                       let caption =
                                         let uu____17012 =
                                           FStar_Options.log_queries () in
                                         if uu____17012
                                         then
                                           let uu____17015 =
                                             let uu____17016 =
                                               let uu____17017 =
                                                 FStar_Syntax_Print.term_to_string
                                                   q1 in
                                               Prims.op_Hat
                                                 "Encoding query formula : "
                                                 uu____17017 in
                                             FStar_SMTEncoding_Term.Caption
                                               uu____17016 in
                                           [uu____17015]
                                         else [] in
                                       let query_prelude =
                                         let uu____17022 =
                                           let uu____17023 =
                                             let uu____17024 =
                                               let uu____17027 =
                                                 FStar_All.pipe_right
                                                   label_prefix
                                                   FStar_SMTEncoding_Term.mk_decls_trivial in
                                               let uu____17034 =
                                                 let uu____17037 =
                                                   FStar_All.pipe_right
                                                     caption
                                                     FStar_SMTEncoding_Term.mk_decls_trivial in
                                                 FStar_List.append qdecls
                                                   uu____17037 in
                                               FStar_List.append uu____17027
                                                 uu____17034 in
                                             FStar_List.append env_decls
                                               uu____17024 in
                                           FStar_All.pipe_right uu____17023
                                             (recover_caching_and_update_env
                                                env1) in
                                         FStar_All.pipe_right uu____17022
                                           FStar_SMTEncoding_Term.decls_list_of in
                                       let qry =
                                         let uu____17047 =
                                           let uu____17054 =
                                             FStar_SMTEncoding_Util.mkNot
                                               phi1 in
                                           let uu____17055 =
                                             FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                               "@query" in
                                           (uu____17054,
                                             (FStar_Pervasives_Native.Some
                                                "query"), uu____17055) in
                                         FStar_SMTEncoding_Util.mkAssume
                                           uu____17047 in
                                       let suffix =
                                         FStar_List.append
                                           [FStar_SMTEncoding_Term.Echo
                                              "<labels>"]
                                           (FStar_List.append label_suffix
                                              [FStar_SMTEncoding_Term.Echo
                                                 "</labels>";
                                              FStar_SMTEncoding_Term.Echo
                                                "Done!"]) in
                                       ((let uu____17060 =
                                           ((FStar_TypeChecker_Env.debug
                                               tcenv FStar_Options.Medium)
                                              ||
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    tcenv)
                                                 (FStar_Options.Other
                                                    "SMTEncoding")))
                                             ||
                                             (FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   tcenv)
                                                (FStar_Options.Other
                                                   "SMTQuery")) in
                                         if uu____17060
                                         then
                                           FStar_Util.print_string
                                             "} Done encoding\n"
                                         else ());
                                        (let uu____17063 =
                                           (((FStar_TypeChecker_Env.debug
                                                tcenv FStar_Options.Medium)
                                               ||
                                               (FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     tcenv)
                                                  (FStar_Options.Other
                                                     "SMTEncoding")))
                                              ||
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    tcenv)
                                                 (FStar_Options.Other
                                                    "SMTQuery")))
                                             ||
                                             (FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   tcenv)
                                                (FStar_Options.Other "Time")) in
                                         if uu____17063
                                         then
                                           FStar_Util.print1
                                             "Encoding took %sms\n"
                                             (Prims.string_of_int ms)
                                         else ());
                                        (query_prelude, labels, qry, suffix)))))))))