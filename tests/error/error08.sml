val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_RETURN {exp=SOME (EXP_BOOL false)}],decls=[],
                   params=[]})],
     stmts=[ST_PRINT
              {exp=EXP_BINARY
                     {lft=EXP_CALL {args=[],func=EXP_ID "f"},opr=BOP_PLUS,
                      rht=EXP_NUM 1}}]} : program
;
