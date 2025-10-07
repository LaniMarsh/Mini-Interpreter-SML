val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",{body=[],decls=[],params=[]}),
                 ("g",{body=[],decls=[],params=[]})],
     stmts=[ST_PRINT
              {exp=EXP_BINARY {lft=EXP_ID "f",opr=BOP_EQ,rht=EXP_ID "f"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT
              {exp=EXP_BINARY {lft=EXP_ID "f",opr=BOP_EQ,rht=EXP_ID "g"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT
              {exp=EXP_BINARY
                     {lft=EXP_ANON {body=[],decls=[],params=[]},opr=BOP_EQ,
                      rht=EXP_ANON {body=[],decls=[],params=[]}}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
