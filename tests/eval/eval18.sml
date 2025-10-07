val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_RETURN
                           {exp=SOME
                                  (EXP_BINARY
                                     {lft=EXP_ID "a",opr=BOP_PLUS,
                                      rht=EXP_ID "b"})}],decls=[],
                   params=["a","b"]})],
     stmts=[ST_PRINT
              {exp=EXP_CALL {args=[EXP_NUM 1,EXP_NUM 2],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT
              {exp=EXP_CALL {args=[EXP_NUM 3,EXP_NUM 4],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT
              {exp=EXP_CALL
                     {args=[EXP_NUM 3,
                            EXP_CALL
                              {args=[EXP_NUM 3,EXP_NUM 4],func=EXP_ID "f"}],
                      func=EXP_ID "f"}},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
