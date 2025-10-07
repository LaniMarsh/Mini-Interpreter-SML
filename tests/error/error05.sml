val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_IF
                           {el=NONE,guard=EXP_NUM 3,
                            th=ST_BLOCK
                                 {stmts=[ST_PRINT {exp=EXP_NUM 1},
                                         ST_PRINT {exp=EXP_STRING "\n"}]}}],
                   decls=[],params=[]})],
     stmts=[ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f"}}]} : program
;
