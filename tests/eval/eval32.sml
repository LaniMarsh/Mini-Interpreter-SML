val prog =
  PROGRAM
    {decls=["a","b","c"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "b",rhs=EXP_NUM 100}},
                         ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "c",rhs=EXP_NUM 200}},
                         ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "a",
                                   rhs=EXP_CALL {args=[],func=EXP_ID "g"}}}],
                   decls=["b","c"],params=["g"]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "b",rhs=EXP_NUM 1}},
            ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "c",rhs=EXP_NUM 2}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "a",
                      rhs=EXP_CALL
                            {args=[EXP_ANON
                                     {body=[ST_PRINT {exp=EXP_ID "b"},
                                            ST_PRINT {exp=EXP_STRING "\n"},
                                            ST_PRINT {exp=EXP_ID "c"},
                                            ST_PRINT {exp=EXP_STRING "\n"}],
                                      decls=[],params=[]}],func=EXP_ID "f"}}}]}
  : program
;
