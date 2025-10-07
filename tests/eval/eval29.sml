val prog =
  PROGRAM
    {decls=["f"],func_decls=[],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f",
                      rhs=EXP_ANON
                            {body=[ST_PRINT
                                     {exp=EXP_BINARY
                                            {lft=EXP_ID "a",opr=BOP_PLUS,
                                             rht=EXP_ID "b"}},
                                   ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                             params=["a","b"]}}},
            ST_EXP {exp=EXP_CALL {args=[EXP_NUM 1,EXP_NUM 2],func=EXP_ID "f"}}]}
  : program
;
