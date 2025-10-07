val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_RETURN
                           {exp=SOME
                                  (EXP_BINARY
                                     {lft=EXP_NUM 1,opr=BOP_PLUS,
                                      rht=EXP_BOOL true})}],decls=[],
                   params=[]})],
     stmts=[ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "f"}}]} : program
;
