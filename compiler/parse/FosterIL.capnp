@ 0x90d7c63df4155b81;

using Cxx = import "/capnp/c++.capnp";
$Cxx.namespace("foster::be");

annotation optional   @ 0xfdd8d84c51405f88 (field) : Void;
# package foster.bepb;


struct Type {
  enum Tag {
    named      @ 0;
    ptr        @ 1;
    procty     @ 2;
    carray     @ 3;
    primint    @ 4;
    float64    @ 5;
    array      @ 6;
    datatype   @ 7;
    tyconapp   @ 8;
    struct     @ 9;
    float32    @ 10;
  }

  tag   @ 0 : Tag;

  # LLVM_NAMED, TYPE_VARIABLE
  name         @ 1 : Text $optional;
  procty       @ 2 : ProcType $optional;
  typeparts    @ 3 : List(Type); # repeated
  carraysize   @ 4 : List(UInt64); # optional
  ctor         @ 5 : List(PbDataCtor); # repeated
}

struct PbDataCtor {
  name   @ 0 : Text;
  type   @ 1 : List(Type); # repeated
}

struct ProcType {
  argtypes            @ 0 : List(Type); # repeated
  rettype             @ 1 : Type;
  callingconvention   @ 2 : Text $optional;

  #repeated string annot_key = 3;
  #repeated string annot_val = 4;
}

struct Block {
  blockid    @ 0 : Text;
  phis       @ 1 : List(TermVar); # repeated
  middle     @ 2 : List(BlockMiddle); # repeated
  last       @ 3 : Terminator;
  numpreds   @ 4 : List(Int32); # optional
}

struct BlockMiddle {
  letval       @ 0 : LetVal $optional;
  rebind       @ 1 : RebindId $optional;
  tuplestore   @ 2 : TupleStore $optional;
}

struct RebindId {
  fromid   @ 0 : Text;
  tovar    @ 1 : TermVar;
}

struct TupleStore {
  storedvars     @ 0 : List(TermVar); # repeated
  storage        @ 1 : TermVar;
  storageindir   @ 2 : Bool;
}

struct LetVal {
  letvalid   @ 0 : Text;
  letexpr    @ 1 : Letable;
}

struct Letable {
  enum Tag {
    ilint             @  0;
    ilbool            @  1;
    iltext            @  2;
    ilunit            @  3;
    ilfloat           @  4;
    iloccurrence      @  5;
    ilcall            @  6;
    ilcallprimop      @  7;
    ilbytearray       @  8;
    iltyapp           @  9;
    ilkillprocess     @ 10;
    ilderef           @ 11;
    ilstore           @ 12;
    ilif              @ 13;
    ilallocate        @ 14;
    ilarrayread       @ 15;
    ilarraypoke       @ 16;
    ilarraylength     @ 17;
    ilarrayliteral    @ 18;
    ilnamedtypedecl   @ 19;
    ilunboxedtuple    @ 20;
    ilglobalappctor   @ 21;
    ilfieldidxopen    @ 22;
    ilfieldidxclosed  @ 23;
  }
  parts   @ 0 : List(TermVar); # repeated
  tag     @ 1 : Tag;
  type    @ 2 : Type $optional;

  names   @ 3 : List(Text); # repeated
  intlit  @ 4 : IntLit $optional;
  dval    @ 5 : List(Float64); # optional

  boolvalue     @ 6 : List(Bool); # optional
  bytesvalue    @ 7 : Data $optional;
  stringvalue   @ 8 : Text $optional;

  allocinfo   @  9 : PbAllocInfo $optional;
  callinfo    @ 10 : PbCallInfo $optional;
  callasm     @ 11 : PbCallAsm $optional;

  occ          @ 12 : PbOccurrence $optional;
  primopname   @ 13 : Text $optional;
  primopsize   @ 14 : List(Int64); # optional
  ctorinfo     @ 15 : PbCtorInfo $optional;
  arraylit     @ 16 : PbArrayLiteral $optional;
  sourceloc    @ 17 : SourceLocation $optional;
}

struct SourceLocation {
  line @ 0 : Int32;
  col  @ 1 : Int32;
  file @ 2 : Text;
}

struct PbCallInfo {
  coroprim   @ 0 : PbCoroPrim $optional;

  callmaytriggergc   @ 1 : Bool;
  callisatailcall    @ 2 : Bool;
  callconv           @ 3 : Text;
}

struct PbCallAsm {
  hassideeffects   @ 0 : Bool;
  asmcontents      @ 1 : Text;
  constraints      @ 2 : Text;
  asmproctype      @ 3 : ProcType;
}

struct PbArrayLiteral {
  elemtype  @ 1 : Type;
  entries   @ 0 : List(PbArrayEntry); # repeated
}

struct PbArrayEntry {
  var   @ 0 : TermVar $optional;
  lit   @ 1 : Letable $optional;
}

struct Terminator {
  enum Tag {
    blockretval     @ 0;
    blockretvoid    @ 1;
    blockbr         @ 2;
    blockcase       @ 3;
  }
  tag     @ 0 : Tag;
  var     @ 1 : TermVar $optional;  # BLOCK_RET, BLOCK_CASE
  block   @ 2 : Text $optional;  # BLOCK_BR
  scase   @ 3 : PbSwitch $optional;  # BLOCK_CASE
  args    @ 4 : List(TermVar);  # BLOCK_BR # repeated
}

struct TermVar {
  enum Tag {
    ilvar             @ 0;
    ilglobalsymbol    @ 1;
  }
  tag    @ 0 : Tag;
  name   @ 1 : Text;
  typ    @ 2 : Type $optional;
}

struct PbAllocInfo {
  enum MemRegion {
    memregionstack         @ 0;
    memregionglobalheap    @ 1;
    memregionglobaldata    @ 2;
  }
  memregion   @ 0 : MemRegion;
  type        @ 1 : Type;
  ctorrepr    @ 2 : PbCtorRepr $optional;
  arraysize   @ 3 : TermVar $optional;
  allocsite   @ 4 : Text;
  typename    @ 5 : Text;
  zeroinit    @ 6 : Bool;
}

struct Proc {
  enum Linkage {
    internal   @ 0;
    external   @ 1;
  }
  proctype   @ 0 : ProcType;
  inargs     @ 1 : List(Text); # repeated
  name       @ 2 : Text;
  blocks     @ 3 : List(Block); # repeated
  lines      @ 4 : Text $optional;
  linkage    @ 5 : Linkage;
}

struct IntLit {
  hexnat    @ 0 : Text;
  tysize    @ 1 : Int32;
  negate    @ 2 : Bool;
}

struct PbCoroPrim {
  enum Tag {
    ilcoroinvoke   @ 0;
    ilcorocreate   @ 1;
    ilcoroyield    @ 2;
    ilcoroparent   @ 3;
    ilcoroisdead   @ 4;
  }
  tag       @ 0 : Tag;
  rettype   @ 1 : Type;
  argtype   @ 2 : Type;
}

struct PbSwitch {
  ctors     @ 0 : List(PbCtorId); # repeated
  blocks    @ 1 : List(Text); # repeated
  defCase   @ 2 : Text $optional;
  var       @ 3 : TermVar;
  ctorby    @ 4 : Text $optional;
}

struct PbCtorInfo {
  ctorid         @ 0 : PbCtorId;
  ctorstructty   @ 1 : Type $optional;
}

struct PbCtorId {
  ctortypename   @ 0 : Text;
  ctorctorname   @ 1 : Text;
  ctorrepr       @ 2 : PbCtorRepr;
}

struct PbCtorRepr {
  enum Tag {
    crdefault       @ 0;
    crnullary       @ 1;
    crtransparent   @ 2;
    crvalue         @ 3;
  }
  tag           @ 0 : Tag;
  ctorreprtag   @ 1 : List(Int64); # optional
  isboxed       @ 2 : List(Bool); # optional
}

struct PbOccurrence {
  scrutinee   @ 0 : TermVar;
  occoffset   @ 1 : List(Int32); # repeated
  occctors    @ 2 : List(PbCtorInfo); # repeated
}

struct Decl {
  name   @ 0 : Text;
  type   @ 1 : Type;
  isForeign @ 2 : Bool;
}

struct CtorApp {
  info  @ 0 : PbCtorInfo;
  vars  @ 1 : List(TermVar);
}

struct PbToplevelItem {
  name         @ 1 : Text;
  arr          @ 0 : PbArrayLiteral $optional;
  lit          @ 2 : Letable $optional;
}

struct Module {
  modulename       @ 0 : Text;
  procs            @ 1 : List(Proc); # repeated
  externvaldecls   @ 2 : List(Decl); # repeated
  typdecls         @ 3 : List(Decl); # repeated
  modlines         @ 4 : List(Text); # repeated

  items            @ 5 : List(PbToplevelItem); # repeated
}

