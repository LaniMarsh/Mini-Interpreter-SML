val prog =
  PROGRAM
    {decls=[],
     func_decls=[("foo",
                  {body=[ST_PRINT {exp=EXP_NUM 1},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_RETURN {exp=SOME (EXP_NUM 2)},
                         ST_PRINT {exp=EXP_NUM 3},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=[],params=[]})],
     stmts=[ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "foo"}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
