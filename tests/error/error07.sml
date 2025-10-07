val prog =
  PROGRAM
    {decls=[],func_decls=[("f",{body=[],decls=[],params=[]})],
     stmts=[ST_PRINT
              {exp=EXP_BINARY
                     {lft=EXP_NUM 1,opr=BOP_PLUS,
                      rht=EXP_CALL {args=[],func=EXP_ID "f"}}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
