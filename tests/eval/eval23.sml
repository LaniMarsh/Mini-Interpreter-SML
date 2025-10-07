val prog =
  PROGRAM
    {decls=[],
     func_decls=[("foo",
                  {body=[ST_RETURN {exp=SOME (EXP_NUM 2)}],decls=[],params=[]}),
                 ("bar",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "x",
                                   rhs=EXP_BINARY
                                         {lft=EXP_CALL
                                                {args=[],func=EXP_ID "foo"},
                                          opr=BOP_PLUS,rht=EXP_NUM 1}}},
                         ST_PRINT {exp=EXP_ID "x"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_RETURN
                           {exp=SOME
                                  (EXP_BINARY
                                     {lft=EXP_BINARY
                                            {lft=EXP_CALL
                                                   {args=[],func=EXP_ID "foo"},
                                             opr=BOP_TIMES,rht=EXP_ID "x"},
                                      opr=BOP_PLUS,
                                      rht=EXP_CALL {args=[],func=EXP_ID "foo"}})}],
                   decls=["x"],params=[]})],
     stmts=[ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "bar"}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
