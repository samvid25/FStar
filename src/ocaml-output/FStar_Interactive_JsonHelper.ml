open Prims
type assoct = (Prims.string * FStar_Util.json) Prims.list
let (try_assoc :
  Prims.string -> assoct -> FStar_Util.json FStar_Pervasives_Native.option) =
  fun key ->
    fun d ->
      let uu____47 =
        FStar_Util.try_find
          (fun uu____61 -> match uu____61 with | (k, uu____67) -> k = key) d in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____47
exception MissingKey of Prims.string 
let (uu___is_MissingKey : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MissingKey uu____82 -> true | uu____83 -> false
let (__proj__MissingKey__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | MissingKey uu____89 -> uu____89
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidQuery uu____100 -> true
    | uu____101 -> false
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidQuery uu____107 -> uu____107
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnexpectedJsonType uu____122 -> true
    | uu____127 -> false
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee ->
    match projectee with | UnexpectedJsonType uu____141 -> uu____141
exception MalformedHeader 
let (uu___is_MalformedHeader : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MalformedHeader -> true | uu____151 -> false
exception InputExhausted 
let (uu___is_InputExhausted : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InputExhausted -> true | uu____157 -> false
let (assoc : Prims.string -> assoct -> FStar_Util.json) =
  fun key ->
    fun a ->
      let uu____168 = try_assoc key a in
      match uu____168 with
      | FStar_Pervasives_Native.Some v -> v
      | FStar_Pervasives_Native.None ->
          let uu____172 =
            let uu____173 = FStar_Util.format1 "Missing key [%s]" key in
            MissingKey uu____173 in
          FStar_Exn.raise uu____172
let (write_json : FStar_Util.json -> unit) =
  fun js ->
    (let uu____180 = FStar_Util.string_of_json js in
     FStar_Util.print_raw uu____180);
    FStar_Util.print_raw "\n"
let (write_jsonrpc : FStar_Util.json -> unit) =
  fun js ->
    let js_str = FStar_Util.string_of_json js in
    let len = FStar_Util.string_of_int (FStar_String.length js_str) in
    let uu____188 =
      FStar_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str in
    FStar_Util.print_raw uu____188
let js_fail : 'a . Prims.string -> FStar_Util.json -> 'a =
  fun expected ->
    fun got -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___0_213 ->
    match uu___0_213 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___1_223 ->
    match uu___1_223 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'a . (FStar_Util.json -> 'a) -> FStar_Util.json -> 'a Prims.list =
  fun k ->
    fun uu___2_247 ->
      match uu___2_247 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let (js_assoc : FStar_Util.json -> assoct) =
  fun uu___3_263 ->
    match uu___3_263 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_str_int : FStar_Util.json -> Prims.int) =
  fun uu___4_279 ->
    match uu___4_279 with
    | FStar_Util.JsonInt i -> i
    | FStar_Util.JsonStr s -> FStar_Util.int_of_string s
    | other -> js_fail "string or int" other
let (arg : Prims.string -> assoct -> FStar_Util.json) =
  fun k ->
    fun r ->
      let uu____293 =
        let uu____294 = assoc "params" r in
        FStar_All.pipe_right uu____294 js_assoc in
      assoc k uu____293
let (uri_to_path : Prims.string -> Prims.string) =
  fun u ->
    let uu____300 =
      let uu____301 =
        FStar_Util.substring u (Prims.of_int (9)) (Prims.of_int (3)) in
      uu____301 = "%3A" in
    if uu____300
    then
      let uu____302 = FStar_Util.substring u (Prims.of_int (8)) Prims.int_one in
      let uu____303 = FStar_Util.substring_from u (Prims.of_int (12)) in
      FStar_Util.format2 "%s:%s" uu____302 uu____303
    else FStar_Util.substring_from u (Prims.of_int (7))
let (path_to_uri : Prims.string -> Prims.string) =
  fun u ->
    let uu____310 =
      let uu____311 = FStar_Util.char_at u Prims.int_one in uu____311 = 58 in
    if uu____310
    then
      let rest =
        let uu____313 = FStar_Util.substring_from u (Prims.of_int (2)) in
        FStar_Util.replace_char uu____313 92 47 in
      let uu____314 = FStar_Util.substring u Prims.int_zero Prims.int_one in
      FStar_Util.format2 "file:///%s%3A%s" uu____314 rest
    else FStar_Util.format1 "file://%s" u
type completion_context =
  {
  trigger_kind: Prims.int ;
  trigger_char: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkcompletion_context__item__trigger_kind :
  completion_context -> Prims.int) =
  fun projectee ->
    match projectee with | { trigger_kind; trigger_char;_} -> trigger_kind
let (__proj__Mkcompletion_context__item__trigger_char :
  completion_context -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { trigger_kind; trigger_char;_} -> trigger_char
let (js_compl_context : FStar_Util.json -> completion_context) =
  fun uu___5_357 ->
    match uu___5_357 with
    | FStar_Util.JsonAssoc a ->
        let uu____365 =
          let uu____366 = assoc "triggerKind" a in
          FStar_All.pipe_right uu____366 js_int in
        let uu____367 =
          let uu____370 = try_assoc "triggerChar" a in
          FStar_All.pipe_right uu____370 (FStar_Util.map_option js_str) in
        { trigger_kind = uu____365; trigger_char = uu____367 }
    | other -> js_fail "dictionary" other
type txdoc_item =
  {
  fname: Prims.string ;
  langId: Prims.string ;
  version: Prims.int ;
  text: Prims.string }
let (__proj__Mktxdoc_item__item__fname : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> fname
let (__proj__Mktxdoc_item__item__langId : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> langId
let (__proj__Mktxdoc_item__item__version : txdoc_item -> Prims.int) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> version
let (__proj__Mktxdoc_item__item__text : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> text
let (js_txdoc_item : FStar_Util.json -> txdoc_item) =
  fun uu___6_441 ->
    match uu___6_441 with
    | FStar_Util.JsonAssoc a ->
        let arg1 k = assoc k a in
        let uu____455 =
          let uu____456 =
            let uu____457 = arg1 "uri" in
            FStar_All.pipe_right uu____457 js_str in
          uri_to_path uu____456 in
        let uu____458 =
          let uu____459 = arg1 "languageId" in
          FStar_All.pipe_right uu____459 js_str in
        let uu____460 =
          let uu____461 = arg1 "version" in
          FStar_All.pipe_right uu____461 js_int in
        let uu____462 =
          let uu____463 = arg1 "text" in
          FStar_All.pipe_right uu____463 js_str in
        {
          fname = uu____455;
          langId = uu____458;
          version = uu____460;
          text = uu____462
        }
    | other -> js_fail "dictionary" other
type txdoc_pos = {
  path: Prims.string ;
  line: Prims.int ;
  col: Prims.int }
let (__proj__Mktxdoc_pos__item__path : txdoc_pos -> Prims.string) =
  fun projectee -> match projectee with | { path; line; col;_} -> path
let (__proj__Mktxdoc_pos__item__line : txdoc_pos -> Prims.int) =
  fun projectee -> match projectee with | { path; line; col;_} -> line
let (__proj__Mktxdoc_pos__item__col : txdoc_pos -> Prims.int) =
  fun projectee -> match projectee with | { path; line; col;_} -> col
let (js_txdoc_id : assoct -> Prims.string) =
  fun r ->
    let uu____515 =
      let uu____516 =
        let uu____517 =
          let uu____518 = arg "textDocument" r in
          FStar_All.pipe_right uu____518 js_assoc in
        assoc "uri" uu____517 in
      FStar_All.pipe_right uu____516 js_str in
    uri_to_path uu____515
let (js_txdoc_pos : assoct -> txdoc_pos) =
  fun r ->
    let pos =
      let uu____531 = arg "position" r in
      FStar_All.pipe_right uu____531 js_assoc in
    let uu____532 = js_txdoc_id r in
    let uu____533 =
      let uu____534 = assoc "line" pos in
      FStar_All.pipe_right uu____534 js_int in
    let uu____535 =
      let uu____536 = assoc "character" pos in
      FStar_All.pipe_right uu____536 js_int in
    { path = uu____532; line = uu____533; col = uu____535 }
type workspace_folder = {
  wk_uri: Prims.string ;
  wk_name: Prims.string }
let (__proj__Mkworkspace_folder__item__wk_uri :
  workspace_folder -> Prims.string) =
  fun projectee -> match projectee with | { wk_uri; wk_name;_} -> wk_uri
let (__proj__Mkworkspace_folder__item__wk_name :
  workspace_folder -> Prims.string) =
  fun projectee -> match projectee with | { wk_uri; wk_name;_} -> wk_name
type wsch_event = {
  added: workspace_folder ;
  removed: workspace_folder }
let (__proj__Mkwsch_event__item__added : wsch_event -> workspace_folder) =
  fun projectee -> match projectee with | { added; removed;_} -> added
let (__proj__Mkwsch_event__item__removed : wsch_event -> workspace_folder) =
  fun projectee -> match projectee with | { added; removed;_} -> removed
let (js_wsch_event : FStar_Util.json -> wsch_event) =
  fun uu___7_592 ->
    match uu___7_592 with
    | FStar_Util.JsonAssoc a ->
        let added' =
          let uu____601 = assoc "added" a in
          FStar_All.pipe_right uu____601 js_assoc in
        let removed' =
          let uu____603 = assoc "removed" a in
          FStar_All.pipe_right uu____603 js_assoc in
        let uu____604 =
          let uu____605 =
            let uu____606 = assoc "uri" added' in
            FStar_All.pipe_right uu____606 js_str in
          let uu____607 =
            let uu____608 = assoc "name" added' in
            FStar_All.pipe_right uu____608 js_str in
          { wk_uri = uu____605; wk_name = uu____607 } in
        let uu____609 =
          let uu____610 =
            let uu____611 = assoc "uri" removed' in
            FStar_All.pipe_right uu____611 js_str in
          let uu____612 =
            let uu____613 = assoc "name" removed' in
            FStar_All.pipe_right uu____613 js_str in
          { wk_uri = uu____610; wk_name = uu____612 } in
        { added = uu____604; removed = uu____609 }
    | other -> js_fail "dictionary" other
let (js_contentch : FStar_Util.json -> Prims.string) =
  fun uu___8_622 ->
    match uu___8_622 with
    | FStar_Util.JsonList l ->
        let uu____626 =
          FStar_List.map
            (fun uu____632 ->
               match uu____632 with
               | FStar_Util.JsonAssoc a ->
                   let uu____640 = assoc "text" a in
                   FStar_All.pipe_right uu____640 js_str) l in
        FStar_List.hd uu____626
    | other -> js_fail "dictionary" other
type rng =
  {
  rng_start: (Prims.int * Prims.int) ;
  rng_end: (Prims.int * Prims.int) }
let (__proj__Mkrng__item__rng_start : rng -> (Prims.int * Prims.int)) =
  fun projectee ->
    match projectee with | { rng_start; rng_end;_} -> rng_start
let (__proj__Mkrng__item__rng_end : rng -> (Prims.int * Prims.int)) =
  fun projectee -> match projectee with | { rng_start; rng_end;_} -> rng_end
let (js_rng : FStar_Util.json -> rng) =
  fun uu___9_710 ->
    match uu___9_710 with
    | FStar_Util.JsonAssoc a ->
        let st = assoc "start" a in
        let fin = assoc "end" a in
        let l = assoc "line" in
        let c = assoc "character" in
        let uu____730 =
          let uu____735 =
            let uu____736 =
              let uu____737 = FStar_All.pipe_right st js_assoc in l uu____737 in
            FStar_All.pipe_right uu____736 js_int in
          let uu____738 =
            let uu____739 =
              let uu____740 = FStar_All.pipe_right st js_assoc in c uu____740 in
            FStar_All.pipe_right uu____739 js_int in
          (uu____735, uu____738) in
        let uu____741 =
          let uu____746 =
            let uu____747 =
              let uu____748 = FStar_All.pipe_right fin js_assoc in
              l uu____748 in
            FStar_All.pipe_right uu____747 js_int in
          let uu____749 =
            let uu____750 =
              let uu____751 = FStar_All.pipe_right st js_assoc in c uu____751 in
            FStar_All.pipe_right uu____750 js_int in
          (uu____746, uu____749) in
        { rng_start = uu____730; rng_end = uu____741 }
    | other -> js_fail "dictionary" other
type lquery =
  | Initialize of (Prims.int * Prims.string) 
  | Initialized 
  | Shutdown 
  | Exit 
  | Cancel of Prims.int 
  | FolderChange of wsch_event 
  | ChangeConfig 
  | ChangeWatch 
  | Symbol of Prims.string 
  | ExecCommand of Prims.string 
  | DidOpen of txdoc_item 
  | DidChange of (Prims.string * Prims.string) 
  | WillSave of Prims.string 
  | WillSaveWait of Prims.string 
  | DidSave of (Prims.string * Prims.string) 
  | DidClose of Prims.string 
  | Completion of (txdoc_pos * completion_context) 
  | Resolve 
  | Hover of txdoc_pos 
  | SignatureHelp of txdoc_pos 
  | Declaration of txdoc_pos 
  | Definition of txdoc_pos 
  | TypeDefinition of txdoc_pos 
  | Implementation of txdoc_pos 
  | References 
  | DocumentHighlight of txdoc_pos 
  | DocumentSymbol 
  | CodeAction 
  | CodeLens 
  | CodeLensResolve 
  | DocumentLink 
  | DocumentLinkResolve 
  | DocumentColor 
  | ColorPresentation 
  | Formatting 
  | RangeFormatting 
  | TypeFormatting 
  | Rename 
  | PrepareRename of txdoc_pos 
  | FoldingRange 
  | BadProtocolMsg of Prims.string 
let (uu___is_Initialize : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialize _0 -> true | uu____884 -> false
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee -> match projectee with | Initialize _0 -> _0
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialized -> true | uu____908 -> false
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Shutdown -> true | uu____914 -> false
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____920 -> false
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Cancel _0 -> true | uu____927 -> false
let (__proj__Cancel__item___0 : lquery -> Prims.int) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FolderChange _0 -> true | uu____940 -> false
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee -> match projectee with | FolderChange _0 -> _0
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeConfig -> true | uu____952 -> false
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeWatch -> true | uu____958 -> false
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Symbol _0 -> true | uu____965 -> false
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Symbol _0 -> _0
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ExecCommand _0 -> true | uu____978 -> false
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | ExecCommand _0 -> _0
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidOpen _0 -> true | uu____991 -> false
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee -> match projectee with | DidOpen _0 -> _0
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidChange _0 -> true | uu____1008 -> false
let (__proj__DidChange__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidChange _0 -> _0
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSave _0 -> true | uu____1033 -> false
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSave _0 -> _0
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSaveWait _0 -> true | uu____1046 -> false
let (__proj__WillSaveWait__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSaveWait _0 -> _0
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidSave _0 -> true | uu____1063 -> false
let (__proj__DidSave__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidSave _0 -> _0
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidClose _0 -> true | uu____1088 -> false
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidClose _0 -> _0
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Completion _0 -> true | uu____1105 -> false
let (__proj__Completion__item___0 :
  lquery -> (txdoc_pos * completion_context)) =
  fun projectee -> match projectee with | Completion _0 -> _0
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Resolve -> true | uu____1129 -> false
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Hover _0 -> true | uu____1136 -> false
let (__proj__Hover__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Hover _0 -> _0
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | SignatureHelp _0 -> true | uu____1149 -> false
let (__proj__SignatureHelp__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | SignatureHelp _0 -> _0
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Declaration _0 -> true | uu____1162 -> false
let (__proj__Declaration__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Declaration _0 -> _0
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Definition _0 -> true | uu____1175 -> false
let (__proj__Definition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Definition _0 -> _0
let (uu___is_TypeDefinition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeDefinition _0 -> true | uu____1188 -> false
let (__proj__TypeDefinition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | TypeDefinition _0 -> _0
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Implementation _0 -> true | uu____1201 -> false
let (__proj__Implementation__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Implementation _0 -> _0
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | References -> true | uu____1213 -> false
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentHighlight _0 -> true | uu____1220 -> false
let (__proj__DocumentHighlight__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | DocumentHighlight _0 -> _0
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentSymbol -> true | uu____1232 -> false
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeAction -> true | uu____1238 -> false
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLens -> true | uu____1244 -> false
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLensResolve -> true | uu____1250 -> false
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLink -> true | uu____1256 -> false
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLinkResolve -> true | uu____1262 -> false
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentColor -> true | uu____1268 -> false
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ColorPresentation -> true | uu____1274 -> false
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Formatting -> true | uu____1280 -> false
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeFormatting -> true | uu____1286 -> false
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeFormatting -> true | uu____1292 -> false
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Rename -> true | uu____1298 -> false
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | PrepareRename _0 -> true | uu____1305 -> false
let (__proj__PrepareRename__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | PrepareRename _0 -> _0
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FoldingRange -> true | uu____1317 -> false
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | BadProtocolMsg _0 -> true | uu____1324 -> false
let (__proj__BadProtocolMsg__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | BadProtocolMsg _0 -> _0
type lsp_query =
  {
  query_id: Prims.int FStar_Pervasives_Native.option ;
  q: lquery }
let (__proj__Mklsp_query__item__query_id :
  lsp_query -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { query_id; q;_} -> query_id
let (__proj__Mklsp_query__item__q : lsp_query -> lquery) =
  fun projectee -> match projectee with | { query_id; q;_} -> q
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type timed_fname = {
  tf_fname: Prims.string ;
  tf_modtime: FStar_Util.time }
let (__proj__Mktimed_fname__item__tf_fname : timed_fname -> Prims.string) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_fname
let (__proj__Mktimed_fname__item__tf_modtime :
  timed_fname -> FStar_Util.time) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_modtime
type repl_task =
  | LDInterleaved of (timed_fname * timed_fname) 
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of FStar_Parser_ParseIt.input_frag 
  | Noop 
let (uu___is_LDInterleaved : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDInterleaved _0 -> true | uu____1429 -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu____1454 -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____1467 -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu____1480 -> false
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu____1492 -> false
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_fname: Prims.string ;
  repl_deps_stack: (repl_depth_t * (repl_task * repl_state)) Prims.list ;
  repl_curmod: optmod_t ;
  repl_env: FStar_TypeChecker_Env.env ;
  repl_stdin: FStar_Util.stream_reader ;
  repl_names: FStar_Interactive_CompletionTable.table }
and grepl_state =
  {
  grepl_repls: repl_state FStar_Util.psmap ;
  grepl_stdin: FStar_Util.stream_reader }
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_line
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_column
let (__proj__Mkrepl_state__item__repl_fname : repl_state -> Prims.string) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_fname
let (__proj__Mkrepl_state__item__repl_deps_stack :
  repl_state -> (repl_depth_t * (repl_task * repl_state)) Prims.list) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_deps_stack
let (__proj__Mkrepl_state__item__repl_curmod : repl_state -> optmod_t) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_curmod
let (__proj__Mkrepl_state__item__repl_env :
  repl_state -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_env
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Util.stream_reader) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_stdin
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_names
let (__proj__Mkgrepl_state__item__grepl_repls :
  grepl_state -> repl_state FStar_Util.psmap) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_repls
let (__proj__Mkgrepl_state__item__grepl_stdin :
  grepl_state -> FStar_Util.stream_reader) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_stdin
type repl_stack_entry_t = (repl_depth_t * (repl_task * repl_state))
type repl_stack_t = (repl_depth_t * (repl_task * repl_state)) Prims.list
type error_code =
  | ParseError 
  | InvalidRequest 
  | MethodNotFound 
  | InvalidParams 
  | InternalError 
  | ServerErrorStart 
  | ServerErrorEnd 
  | ServerNotInitialized 
  | UnknownErrorCode 
  | RequestCancelled 
  | ContentModified 
let (uu___is_ParseError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ParseError -> true | uu____1804 -> false
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidRequest -> true | uu____1810 -> false
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | MethodNotFound -> true | uu____1816 -> false
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidParams -> true | uu____1822 -> false
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalError -> true | uu____1828 -> false
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorStart -> true | uu____1834 -> false
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorEnd -> true | uu____1840 -> false
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerNotInitialized -> true | uu____1846 -> false
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | UnknownErrorCode -> true | uu____1852 -> false
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | RequestCancelled -> true | uu____1858 -> false
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ContentModified -> true | uu____1864 -> false
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___10_1872 ->
    match uu___10_1872 with
    | ParseError -> ~- (Prims.of_int (32700))
    | InvalidRequest -> ~- (Prims.of_int (32600))
    | MethodNotFound -> ~- (Prims.of_int (32601))
    | InvalidParams -> ~- (Prims.of_int (32602))
    | InternalError -> ~- (Prims.of_int (32603))
    | ServerErrorStart -> ~- (Prims.of_int (32099))
    | ServerErrorEnd -> ~- (Prims.of_int (32000))
    | ServerNotInitialized -> ~- (Prims.of_int (32002))
    | UnknownErrorCode -> ~- (Prims.of_int (32001))
    | RequestCancelled -> ~- (Prims.of_int (32800))
    | ContentModified -> ~- (Prims.of_int (32801))
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___11_1877 ->
    match uu___11_1877 with
    | FStar_Util.JsonNull -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1881 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1881
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1883 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1886 -> "dictionary (...)"
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStar_Util.json -> lsp_query)
  =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____1912 =
          let uu____1913 =
            let uu____1914 = json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1914 in
          BadProtocolMsg uu____1913 in
        { query_id = qid; q = uu____1912 }
let (resultResponse :
  FStar_Util.json -> assoct FStar_Pervasives_Native.option) =
  fun r -> FStar_Pervasives_Native.Some [("result", r)]
let (errorResponse :
  FStar_Util.json -> assoct FStar_Pervasives_Native.option) =
  fun r -> FStar_Pervasives_Native.Some [("error", r)]
let (nullResponse : assoct FStar_Pervasives_Native.option) =
  resultResponse FStar_Util.JsonNull
let (json_of_response :
  Prims.int FStar_Pervasives_Native.option -> assoct -> FStar_Util.json) =
  fun qid ->
    fun response ->
      match qid with
      | FStar_Pervasives_Native.Some i ->
          FStar_Util.JsonAssoc
            (FStar_List.append
               [("jsonrpc", (FStar_Util.JsonStr "2.0"));
               ("id", (FStar_Util.JsonInt i))] response)
      | FStar_Pervasives_Native.None ->
          FStar_Util.JsonAssoc
            (FStar_List.append [("jsonrpc", (FStar_Util.JsonStr "2.0"))]
               response)
let (js_resperr : error_code -> Prims.string -> FStar_Util.json) =
  fun err ->
    fun msg ->
      let uu____2006 =
        let uu____2013 =
          let uu____2018 =
            let uu____2019 = errorcode_to_int err in
            FStar_Util.JsonInt uu____2019 in
          ("code", uu____2018) in
        [uu____2013; ("message", (FStar_Util.JsonStr msg))] in
      FStar_Util.JsonAssoc uu____2006
let (wrap_content_szerr : Prims.string -> lsp_query) =
  fun m ->
    { query_id = FStar_Pervasives_Native.None; q = (BadProtocolMsg m) }
let (js_servcap : FStar_Util.json) =
  FStar_Util.JsonAssoc
    [("capabilities",
       (FStar_Util.JsonAssoc
          [("textDocumentSync",
             (FStar_Util.JsonAssoc
                [("openClose", (FStar_Util.JsonBool true));
                ("change", (FStar_Util.JsonInt Prims.int_one));
                ("willSave", (FStar_Util.JsonBool false));
                ("willSaveWaitUntil", (FStar_Util.JsonBool false));
                ("save",
                  (FStar_Util.JsonAssoc
                     [("includeText", (FStar_Util.JsonBool true))]))]));
          ("hoverProvider", (FStar_Util.JsonBool true));
          ("completionProvider", (FStar_Util.JsonAssoc []));
          ("signatureHelpProvider", (FStar_Util.JsonAssoc []));
          ("definitionProvider", (FStar_Util.JsonBool true));
          ("typeDefinitionProvider", (FStar_Util.JsonBool false));
          ("implementationProvider", (FStar_Util.JsonBool false));
          ("referencesProvider", (FStar_Util.JsonBool false));
          ("documentSymbolProvider", (FStar_Util.JsonBool false));
          ("workspaceSymbolProvider", (FStar_Util.JsonBool false));
          ("codeActionProvider", (FStar_Util.JsonBool false))]))]
let (js_pos : FStar_Range.pos -> FStar_Util.json) =
  fun p ->
    let uu____2138 =
      let uu____2145 =
        let uu____2150 =
          let uu____2151 =
            let uu____2152 = FStar_Range.line_of_pos p in
            uu____2152 - Prims.int_one in
          FStar_Util.JsonInt uu____2151 in
        ("line", uu____2150) in
      let uu____2153 =
        let uu____2160 =
          let uu____2165 =
            let uu____2166 = FStar_Range.col_of_pos p in
            FStar_Util.JsonInt uu____2166 in
          ("character", uu____2165) in
        [uu____2160] in
      uu____2145 :: uu____2153 in
    FStar_Util.JsonAssoc uu____2138
let (js_range : FStar_Range.range -> FStar_Util.json) =
  fun r ->
    let uu____2184 =
      let uu____2191 =
        let uu____2196 =
          let uu____2197 = FStar_Range.start_of_range r in js_pos uu____2197 in
        ("start", uu____2196) in
      let uu____2198 =
        let uu____2205 =
          let uu____2210 =
            let uu____2211 = FStar_Range.end_of_range r in js_pos uu____2211 in
          ("end", uu____2210) in
        [uu____2205] in
      uu____2191 :: uu____2198 in
    FStar_Util.JsonAssoc uu____2184
let (js_dummyrange : FStar_Util.json) =
  FStar_Util.JsonAssoc
    [("start",
       (FStar_Util.JsonAssoc
          [("line", (FStar_Util.JsonInt Prims.int_zero));
          ("character", (FStar_Util.JsonInt Prims.int_zero));
          ("end",
            (FStar_Util.JsonAssoc
               [("line", (FStar_Util.JsonInt Prims.int_zero));
               ("character", (FStar_Util.JsonInt Prims.int_zero))]))]))]
let (js_loclink : FStar_Range.range -> FStar_Util.json) =
  fun r ->
    let s = js_range r in
    let uu____2266 =
      let uu____2269 =
        let uu____2270 =
          let uu____2277 =
            let uu____2282 =
              let uu____2283 =
                let uu____2284 = FStar_Range.file_of_range r in
                path_to_uri uu____2284 in
              FStar_Util.JsonStr uu____2283 in
            ("targetUri", uu____2282) in
          [uu____2277; ("targetRange", s); ("targetSelectionRange", s)] in
        FStar_Util.JsonAssoc uu____2270 in
      [uu____2269] in
    FStar_Util.JsonList uu____2266
let (pos_munge : txdoc_pos -> (Prims.string * Prims.int * Prims.int)) =
  fun pos -> ((pos.path), (pos.line + Prims.int_one), (pos.col))
let (js_diag :
  Prims.string ->
    Prims.string ->
      FStar_Range.range FStar_Pervasives_Native.option -> assoct)
  =
  fun fname ->
    fun msg ->
      fun r ->
        let r' =
          match r with
          | FStar_Pervasives_Native.Some r1 -> js_range r1
          | FStar_Pervasives_Native.None -> js_dummyrange in
        let ds =
          ("diagnostics",
            (FStar_Util.JsonList
               [FStar_Util.JsonAssoc
                  [("range", r'); ("message", (FStar_Util.JsonStr msg))]])) in
        let uu____2350 =
          let uu____2357 =
            let uu____2362 =
              let uu____2363 =
                let uu____2370 =
                  let uu____2375 =
                    let uu____2376 = path_to_uri fname in
                    FStar_Util.JsonStr uu____2376 in
                  ("uri", uu____2375) in
                [uu____2370; ds] in
              FStar_Util.JsonAssoc uu____2363 in
            ("params", uu____2362) in
          [uu____2357] in
        ("method", (FStar_Util.JsonStr "textDocument/publishDiagnostics")) ::
          uu____2350
let (js_diag_clear : Prims.string -> assoct) =
  fun fname ->
    let uu____2406 =
      let uu____2413 =
        let uu____2418 =
          let uu____2419 =
            let uu____2426 =
              let uu____2431 =
                let uu____2432 = path_to_uri fname in
                FStar_Util.JsonStr uu____2432 in
              ("uri", uu____2431) in
            [uu____2426; ("diagnostics", (FStar_Util.JsonList []))] in
          FStar_Util.JsonAssoc uu____2419 in
        ("params", uu____2418) in
      [uu____2413] in
    ("method", (FStar_Util.JsonStr "textDocument/publishDiagnostics")) ::
      uu____2406