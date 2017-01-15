
open Prims

let intern_string : Prims.string  ->  Prims.string = (

let strings = (FStar_Util.smap_create (Prims.parse_int "100"))
in (fun s -> (

let uu____6 = (FStar_Util.smap_try_find strings s)
in (match (uu____6) with
| Some (res) -> begin
res
end
| None -> begin
((FStar_Util.smap_add strings s s);
s;
)
end))))


let default_string_finish = (fun endm b s -> FStar_Parser_Parse.STRING (s))


let call_string_finish = (fun fin buf endm b -> (let _0_359 = (FStar_Bytes.close buf)
in (fin endm b _0_359)))


let add_string : FStar_Bytes.bytebuf  ->  Prims.string  ->  Prims.unit = (fun buf x -> (let _0_360 = (FStar_Bytes.string_as_unicode_bytes x)
in (FStar_Bytes.emit_bytes buf _0_360)))


let add_int_char : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> ((FStar_Bytes.emit_int_as_byte buf (c mod (Prims.parse_int "256")));
(FStar_Bytes.emit_int_as_byte buf (c / (Prims.parse_int "256")));
))


let add_unichar : FStar_Bytes.bytebuf  ->  Prims.int  ->  Prims.unit = (fun buf c -> (add_int_char buf c))


let add_byte_char : FStar_Bytes.bytebuf  ->  FStar_BaseTypes.char  ->  Prims.unit = (fun buf c -> (add_int_char buf ((FStar_Util.int_of_char c) mod (Prims.parse_int "256"))))


let stringbuf_as_bytes : FStar_Bytes.bytebuf  ->  FStar_Bytes.bytes = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (let _0_362 = (let _0_361 = (FStar_Bytes.length bytes)
in (_0_361 / (Prims.parse_int "2")))
in (FStar_Bytes.make (fun i -> (FStar_Bytes.get bytes (FStar_Mul.op_Star i (Prims.parse_int "2")))) _0_362))))


let stringbuf_is_bytes : FStar_Bytes.bytebuf  ->  Prims.bool = (fun buf -> (

let bytes = (FStar_Bytes.close buf)
in (

let ok = (FStar_Util.mk_ref true)
in ((let _0_366 = (let _0_364 = (let _0_363 = (FStar_Bytes.length bytes)
in (_0_363 / (Prims.parse_int "2")))
in (_0_364 - (Prims.parse_int "1")))
in (FStar_Util.for_range (Prims.parse_int "0") _0_366 (fun i -> (

let uu____109 = (let _0_365 = (FStar_Bytes.get bytes ((FStar_Mul.op_Star i (Prims.parse_int "2")) + (Prims.parse_int "1")))
in (_0_365 <> (Prims.parse_int "0")))
in (match (uu____109) with
| true -> begin
(FStar_ST.write ok false)
end
| uu____112 -> begin
()
end)))));
(FStar_ST.read ok);
))))


let trigraph : FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char  ->  FStar_BaseTypes.char = (fun c1 c2 c3 -> (

let digit = (fun c -> ((FStar_Util.int_of_char c) - (FStar_Util.int_of_char '0')))
in (FStar_Util.char_of_int (((FStar_Mul.op_Star (digit c1) (Prims.parse_int "100")) + (FStar_Mul.op_Star (digit c2) (Prims.parse_int "10"))) + (digit c3)))))


let digit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9')))) with
| true -> begin
((FStar_Util.int_of_char d) - (FStar_Util.int_of_char '0'))
end
| uu____132 -> begin
(failwith "digit")
end)))


let hexdigit : FStar_BaseTypes.char  ->  Prims.int = (fun d -> (

let dd = (FStar_Util.int_of_char d)
in (match (((dd >= (FStar_Util.int_of_char '0')) && (dd <= (FStar_Util.int_of_char '9')))) with
| true -> begin
(digit d)
end
| uu____137 -> begin
(match (((dd >= (FStar_Util.int_of_char 'a')) && (dd <= (FStar_Util.int_of_char 'f')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'a')) + (Prims.parse_int "10"))
end
| uu____138 -> begin
(match (((dd >= (FStar_Util.int_of_char 'A')) && (dd <= (FStar_Util.int_of_char 'F')))) with
| true -> begin
((dd - (FStar_Util.int_of_char 'A')) + (Prims.parse_int "10"))
end
| uu____139 -> begin
(failwith "hexdigit")
end)
end)
end)))


let unicodegraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "4"))) with
| true -> begin
(failwith "unicodegraph")
end
| uu____145 -> begin
(FStar_Util.uint16_of_int (let _0_375 = (let _0_373 = (let _0_370 = (let _0_367 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "0")))
in (FStar_Mul.op_Star _0_367 (Prims.parse_int "4096")))
in (let _0_369 = (let _0_368 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "1")))
in (FStar_Mul.op_Star _0_368 (Prims.parse_int "256")))
in (_0_370 + _0_369)))
in (let _0_372 = (let _0_371 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "2")))
in (FStar_Mul.op_Star _0_371 (Prims.parse_int "16")))
in (_0_373 + _0_372)))
in (let _0_374 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "3")))
in (_0_375 + _0_374))))
end))


let hexgraph_short : Prims.string  ->  FStar_BaseTypes.uint16 = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "2"))) with
| true -> begin
(failwith "hexgraph")
end
| uu____151 -> begin
(FStar_Util.uint16_of_int (let _0_378 = (let _0_376 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "0")))
in (FStar_Mul.op_Star _0_376 (Prims.parse_int "16")))
in (let _0_377 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "1")))
in (_0_378 + _0_377))))
end))


let unicodegraph_long : Prims.string  ->  (FStar_BaseTypes.uint16 Prims.option * FStar_BaseTypes.uint16) = (fun s -> (match (((FStar_String.length s) <> (Prims.parse_int "8"))) with
| true -> begin
(failwith "unicodegraph_long")
end
| uu____166 -> begin
(

let high = (let _0_387 = (let _0_385 = (let _0_382 = (let _0_379 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "0")))
in (FStar_Mul.op_Star _0_379 (Prims.parse_int "4096")))
in (let _0_381 = (let _0_380 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "1")))
in (FStar_Mul.op_Star _0_380 (Prims.parse_int "256")))
in (_0_382 + _0_381)))
in (let _0_384 = (let _0_383 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "2")))
in (FStar_Mul.op_Star _0_383 (Prims.parse_int "16")))
in (_0_385 + _0_384)))
in (let _0_386 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "3")))
in (_0_387 + _0_386)))
in (

let low = (let _0_396 = (let _0_394 = (let _0_391 = (let _0_388 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "4")))
in (FStar_Mul.op_Star _0_388 (Prims.parse_int "4096")))
in (let _0_390 = (let _0_389 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "5")))
in (FStar_Mul.op_Star _0_389 (Prims.parse_int "256")))
in (_0_391 + _0_390)))
in (let _0_393 = (let _0_392 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "6")))
in (FStar_Mul.op_Star _0_392 (Prims.parse_int "16")))
in (_0_394 + _0_393)))
in (let _0_395 = (hexdigit (FStar_Util.char_at s (Prims.parse_int "7")))
in (_0_396 + _0_395)))
in (match ((high = (Prims.parse_int "0"))) with
| true -> begin
((None), ((FStar_Util.uint16_of_int low)))
end
| uu____173 -> begin
((Some ((FStar_Util.uint16_of_int ((Prims.parse_int "0xD800") + (((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + (low - (Prims.parse_int "0x10000"))) / (Prims.parse_int "0x400")))))), ((FStar_Util.uint16_of_int ((Prims.parse_int "0xDF30") + (((FStar_Mul.op_Star high (Prims.parse_int "0x10000")) + (low - (Prims.parse_int "0x10000"))) mod (Prims.parse_int "0x400"))))))
end)))
end))


let escape : FStar_Char.char  ->  FStar_Char.char = (fun c -> (match (c) with
| '\\' -> begin
'\\'
end
| '\'' -> begin
'\''
end
| 'n' -> begin
'\n'
end
| 't' -> begin
'\t'
end
| 'b' -> begin
'\b'
end
| 'r' -> begin
'\r'
end
| c -> begin
c
end))

type compatibilityMode =
| ALWAYS
| FSHARP


let uu___is_ALWAYS : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ALWAYS -> begin
true
end
| uu____182 -> begin
false
end))


let uu___is_FSHARP : compatibilityMode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FSHARP -> begin
true
end
| uu____186 -> begin
false
end))


let keywords : (compatibilityMode * Prims.string * FStar_Parser_Parse.token) Prims.list = (((ALWAYS), ("abstract"), (FStar_Parser_Parse.ABSTRACT)))::(((ALWAYS), ("attributes"), (FStar_Parser_Parse.ATTRIBUTES)))::(((ALWAYS), ("noeq"), (FStar_Parser_Parse.NOEQUALITY)))::(((ALWAYS), ("unopteq"), (FStar_Parser_Parse.UNOPTEQUALITY)))::(((ALWAYS), ("and"), (FStar_Parser_Parse.AND)))::(((ALWAYS), ("assert"), (FStar_Parser_Parse.ASSERT)))::(((ALWAYS), ("assume"), (FStar_Parser_Parse.ASSUME)))::(((ALWAYS), ("begin"), (FStar_Parser_Parse.BEGIN)))::(((FSHARP), ("default"), (FStar_Parser_Parse.DEFAULT)))::(((ALWAYS), ("effect"), (FStar_Parser_Parse.EFFECT)))::(((ALWAYS), ("effect_actions"), (FStar_Parser_Parse.ACTIONS)))::(((ALWAYS), ("else"), (FStar_Parser_Parse.ELSE)))::(((ALWAYS), ("end"), (FStar_Parser_Parse.END)))::(((ALWAYS), ("ensures"), (FStar_Parser_Parse.ENSURES)))::(((ALWAYS), ("exception"), (FStar_Parser_Parse.EXCEPTION)))::(((ALWAYS), ("exists"), (FStar_Parser_Parse.EXISTS)))::(((ALWAYS), ("false"), (FStar_Parser_Parse.FALSE)))::(((ALWAYS), ("False"), (FStar_Parser_Parse.L_FALSE)))::(((ALWAYS), ("forall"), (FStar_Parser_Parse.FORALL)))::(((ALWAYS), ("fun"), (FStar_Parser_Parse.FUN)))::(((ALWAYS), ("function"), (FStar_Parser_Parse.FUNCTION)))::(((ALWAYS), ("if"), (FStar_Parser_Parse.IF)))::(((ALWAYS), ("kind"), (FStar_Parser_Parse.KIND)))::(((ALWAYS), ("in"), (FStar_Parser_Parse.IN)))::(((ALWAYS), ("include"), (FStar_Parser_Parse.INCLUDE)))::(((ALWAYS), ("inline"), (FStar_Parser_Parse.INLINE)))::(((ALWAYS), ("inline_for_extraction"), (FStar_Parser_Parse.INLINE_FOR_EXTRACTION)))::(((ALWAYS), ("irreducible"), (FStar_Parser_Parse.IRREDUCIBLE)))::(((ALWAYS), ("let"), (FStar_Parser_Parse.LET (false))))::(((ALWAYS), ("logic"), (FStar_Parser_Parse.LOGIC)))::(((ALWAYS), ("match"), (FStar_Parser_Parse.MATCH)))::(((ALWAYS), ("module"), (FStar_Parser_Parse.MODULE)))::(((ALWAYS), ("mutable"), (FStar_Parser_Parse.MUTABLE)))::(((ALWAYS), ("new"), (FStar_Parser_Parse.NEW)))::(((ALWAYS), ("new_effect"), (FStar_Parser_Parse.NEW_EFFECT)))::(((ALWAYS), ("new_effect_for_free"), (FStar_Parser_Parse.NEW_EFFECT_FOR_FREE)))::(((ALWAYS), ("noextract"), (FStar_Parser_Parse.NOEXTRACT)))::(((ALWAYS), ("of"), (FStar_Parser_Parse.OF)))::(((ALWAYS), ("open"), (FStar_Parser_Parse.OPEN)))::(((ALWAYS), ("opaque"), (FStar_Parser_Parse.OPAQUE)))::(((ALWAYS), ("private"), (FStar_Parser_Parse.PRIVATE)))::(((ALWAYS), ("rec"), (FStar_Parser_Parse.REC)))::(((ALWAYS), ("reifiable"), (FStar_Parser_Parse.REIFIABLE)))::(((ALWAYS), ("reify"), (FStar_Parser_Parse.REIFY)))::(((ALWAYS), ("reflectable"), (FStar_Parser_Parse.REFLECTABLE)))::(((ALWAYS), ("requires"), (FStar_Parser_Parse.REQUIRES)))::(((ALWAYS), ("sub_effect"), (FStar_Parser_Parse.SUB_EFFECT)))::(((ALWAYS), ("then"), (FStar_Parser_Parse.THEN)))::(((ALWAYS), ("total"), (FStar_Parser_Parse.TOTAL)))::(((ALWAYS), ("true"), (FStar_Parser_Parse.TRUE)))::(((ALWAYS), ("True"), (FStar_Parser_Parse.L_TRUE)))::(((ALWAYS), ("try"), (FStar_Parser_Parse.TRY)))::(((ALWAYS), ("type"), (FStar_Parser_Parse.TYPE)))::(((ALWAYS), ("unfold"), (FStar_Parser_Parse.UNFOLD)))::(((ALWAYS), ("unfoldable"), (FStar_Parser_Parse.UNFOLDABLE)))::(((ALWAYS), ("val"), (FStar_Parser_Parse.VAL)))::(((ALWAYS), ("when"), (FStar_Parser_Parse.WHEN)))::(((ALWAYS), ("with"), (FStar_Parser_Parse.WITH)))::(((ALWAYS), ("_"), (FStar_Parser_Parse.UNDERSCORE)))::[]


let stringKeywords : Prims.string Prims.list = (FStar_List.map (fun uu____375 -> (match (uu____375) with
| (uu____379, w, uu____381) -> begin
w
end)) keywords)


let unreserve_words : Prims.string Prims.list = (FStar_List.choose (fun uu____386 -> (match (uu____386) with
| (mode, keyword, uu____393) -> begin
(match ((mode = FSHARP)) with
| true -> begin
Some (keyword)
end
| uu____395 -> begin
None
end)
end)) keywords)


let kwd_table : FStar_Parser_Parse.token FStar_Util.smap = (

let tab = (FStar_Util.smap_create (Prims.parse_int "1000"))
in ((FStar_List.iter (fun uu____403 -> (match (uu____403) with
| (mode, keyword, token) -> begin
(FStar_Util.smap_add tab keyword token)
end)) keywords);
tab;
))


let kwd : Prims.string  ->  FStar_Parser_Parse.token Prims.option = (fun s -> (FStar_Util.smap_try_find kwd_table s))

type lexargs =
{getSourceDirectory : Prims.unit  ->  Prims.string; contents : Prims.string}


let mkLexargs = (fun uu____447 -> (match (uu____447) with
| (srcdir, filename, contents) -> begin
{getSourceDirectory = srcdir; contents = contents}
end))


let kwd_or_id : lexargs  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Parser_Parse.token = (fun args r s -> (

let uu____469 = (kwd s)
in (match (uu____469) with
| Some (v) -> begin
v
end
| None -> begin
(match (s) with
| "__SOURCE_DIRECTORY__" -> begin
FStar_Parser_Parse.STRING ((FStar_Bytes.string_as_unicode_bytes (args.getSourceDirectory ())))
end
| "__SOURCE_FILE__" -> begin
FStar_Parser_Parse.STRING ((FStar_Bytes.string_as_unicode_bytes (FStar_Range.file_of_range r)))
end
| "__LINE__" -> begin
FStar_Parser_Parse.INT ((let _0_398 = (let _0_397 = (FStar_Range.line_of_pos (FStar_Range.start_of_range r))
in (FStar_All.pipe_left FStar_Util.string_of_int _0_397))
in ((_0_398), (false))))
end
| uu____472 -> begin
(match ((FStar_Util.starts_with s FStar_Ident.reserved_prefix)) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat FStar_Ident.reserved_prefix " is a reserved prefix for an identifier")), (r)))))
end
| uu____473 -> begin
FStar_Parser_Parse.IDENT ((intern_string s))
end)
end)
end)))




