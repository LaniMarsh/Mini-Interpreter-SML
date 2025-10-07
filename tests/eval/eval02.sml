val prog =
  PROGRAM
    {decls=["y"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "y",rhs=EXP_NUM 100}}],
                   decls=[],params=[]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "y",rhs=EXP_NUM 9}},
            ST_PRINT {exp=EXP_ID "y"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_ID "y"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
