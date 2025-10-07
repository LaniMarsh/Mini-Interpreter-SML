val prog =
  PROGRAM
    {decls=["f"],func_decls=[],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f",
                      rhs=EXP_ANON
                            {body=[ST_PRINT {exp=EXP_NUM 1},
                                   ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                             params=[]}}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f"}}]} : program
;
