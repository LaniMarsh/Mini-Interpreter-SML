val prog =
  PROGRAM
    {decls=[],
     func_decls=[("foo",
                  {body=[ST_RETURN {exp=SOME (EXP_NUM 2)}],decls=[],params=[]}),
                 ("bar",
                  {body=[ST_RETURN
                           {exp=SOME
                                  (EXP_BINARY
                                     {lft=EXP_CALL {args=[],func=EXP_ID "foo"},
                                      opr=BOP_PLUS,rht=EXP_NUM 1})}],decls=[],
                   params=[]})],
     stmts=[ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "bar"}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
