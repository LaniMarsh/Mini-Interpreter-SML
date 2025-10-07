val prog =
  PROGRAM
    {decls=["a","f"],func_decls=[],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "a",rhs=EXP_NUM 7}},
            ST_EXP
              {exp=EXP_CALL
                     {args=[EXP_NUM 2],
                      func=EXP_ANON
                             {body=[ST_PRINT {exp=EXP_ID "a"},
                                    ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                              params=["a"]}}},ST_PRINT {exp=EXP_ID "a"},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
