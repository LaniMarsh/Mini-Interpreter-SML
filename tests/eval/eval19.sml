val prog =
  PROGRAM
    {decls=["x"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "x",
                                   rhs=EXP_BINARY
                                         {lft=EXP_ID "x",opr=BOP_PLUS,
                                          rht=EXP_NUM 1}}},
                         ST_RETURN
                           {exp=SOME
                                  (EXP_BINARY
                                     {lft=EXP_ID "a",opr=BOP_PLUS,
                                      rht=EXP_ID "b"})}],decls=[],
                   params=["a","b"]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "x",rhs=EXP_NUM 0}},
            ST_PRINT {exp=EXP_ID "x"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT
              {exp=EXP_CALL {args=[EXP_NUM 1,EXP_NUM 2],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_STRING "\n"},ST_PRINT {exp=EXP_ID "x"},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT
              {exp=EXP_CALL {args=[EXP_NUM 2,EXP_NUM 3],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_STRING "\n"},ST_PRINT {exp=EXP_ID "x"},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT
              {exp=EXP_CALL
                     {args=[EXP_NUM 2,
                            EXP_CALL
                              {args=[EXP_NUM 3,EXP_NUM 4],func=EXP_ID "f"}],
                      func=EXP_ID "f"}},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_ID "x"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
