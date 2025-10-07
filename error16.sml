val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_PRINT {exp=EXP_ID "a"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_PRINT {exp=EXP_ID "b"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                   params=["a","b"]})],
     stmts=[ST_EXP
              {exp=EXP_CALL
                     {args=[EXP_NUM 1,EXP_NUM 2,EXP_NUM 3],func=EXP_ID "f"}}]}
  : program
;
