def gen(name, cases):
    return """
  cb_parse_%s cbor = case cbor of
%s
    _ -> error $ "cb_parse_%s failed"
""" % (name, '\n'.join(["    " + gencase(name, case) for case in cases]), name)

def parseitems(name, items):
    return  name + " " + ' '.join("(cb_parse_%s %s)" % (item, item) for item in items)

def gencase(name, case):
    tag, items = case
    return "CBOR_Array [tok, _, cbr, CBOR_Array [%s]] | tok `tm` tok_%s-> %s" % (', '.join(items), tag, parseitems(name, items))

stuff = [
    ("ToplevelItem", [("DECL", ["x", "t"]),
                      ("DEFN", ["x", "atom"]),
                      ("DATATYPE", ["tyformal", "tyformal", "data_ctor"]) ] ),

    ("DataCtor", [("OF", ["dctor", "tatom"] )] ),

    ("x", [("TERMNAME", ["name"] )] ),
    ("xid", [("TERMNAME", ["nameunq"] )] ),
    ("name", [("QNAME", ["id", "name"] )] ),
    ("ctor", [("CTOR", ["x"] )] ),

    ("k", [ ("KIND_TYPE", [] ),
            ("KIND_BOXED", [] ) ] ),

    ("idbinding", [("BINDING", ["xid", "e"] )] ),
    ("pbinding", [("BINDING", ["patbind", "e"] )] ),
    ("patbind", [ ("WILDCARD", [] ),
                  ("TUPLE", ["p"] ) ] ),

    ("phrase", [ ("PHRASE", [] ),
                 ("PRIMAPP", ["nopr", "tyapp", "lvalue"] ) ] ),

    ("lvalue", [("LVALUE", ["atom", "suffix"] )] ),

    ("tyapp", [ ("VAL_TYPE_APP", [] ) ] ),
    ("pmatch", [ ("CASE", ["p", "e", "stmts"] ),
                 ("CASE", ["p", "stmts"] )] ),

    ("suffix", [ ("DEREF", [] ),
                 ("SUBSCRIPT", ["e"] ),
                 ("VAL_APP", [] )] ),

    ("atom", [   ("CASE", ["e", "pmatch"] ),
                 ("COMPILES", ["e"] ),
                 ("LETS",   ["binding", "stmts"] ),
                 ("LETREC", ["binding", "stmts"] ),
                 ("TUPLE", [] ),
                 ("TUPLE", ["e"] ),
                 ("IFEXPR", ["e", "stmts", "stmts"] ),
                 ("TYANNOT", ["e", "t"] ),
                 ("VAL_ABS", ["formal", "tyformal", "stmts"] ),
                 ] ),

    ("patom", [  ("WILDCARD", [] ),
                 ("TUPLE", ["p"] ),
                 ] ),

    ("lit", [  ("BOOL", [] ),
                 ] ),

    ("binding", [  ("BINDING", ["x", "e"] ), ] ),

    ("formal", [  ("FORMAL", ["xid", "t"] ), ] ),
    ("tyformal", [  ("TYPEVAR_DECL", ["aid", "k"] ), ] ),
    ("tyformalr", [ ("TYPEVAR_DECL", ["aid", "k"] ), ] ),

    ("t", [ ("REFINED", ["xid", "tp", "e"] ), ] ),

    ("tp", [ ("TYPE_ATOM",    ["tatom"] ),
             ("TYPE_TYP_APP", ["tatom", "tatom"] ),
             ("FORALL_TYPE", ["tyformalr", "t"] ),] ),

    ("tatom", [ ("TYPE_PLACEHOLDER",    ["a"] ),
             ("TUPLE", ["tatom", "tatom"] ),
             ("FUNC_TYPE", ["tuple", "tannots"] ),] ),

    ("tannots", [ ("BINDING", ["binding"] ), ] ),
    ("num", [ ("LIT_NUM", [] ), ] ),
    ("str", [ ("STRING", [] ), ] ),
    ]
for gd in stuff:
    print( gen(*gd) )

