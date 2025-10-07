val prog =
  PROGRAM
    {decls=["a"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "a",rhs=EXP_STRING "in f\n"}},
                         ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "h",
                                   rhs=EXP_ANON
                                         {body=[ST_EXP
                                                  {exp=EXP_ASSIGN
                                                         {lhs=EXP_ID "a",
                                                          rhs=EXP_STRING
                                                                "in h\n"}},
                                                ST_EXP
                                                  {exp=EXP_CALL
                                                         {args=[],
                                                          func=EXP_ID "g"}},
                                                ST_PRINT {exp=EXP_ID "a"}],
                                          decls=["a"],params=[]}}},
                         ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "g",
                                   rhs=EXP_ANON
                                         {body=[ST_EXP
                                                  {exp=EXP_ASSIGN
                                                         {lhs=EXP_ID "a",
                                                          rhs=EXP_STRING
                                                                "in g\n"}},
                                                ST_PRINT {exp=EXP_ID "a"}],
                                          decls=["a"],params=[]}}},
                         ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "h"}},
                         ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "g"}},
                         ST_PRINT {exp=EXP_ID "a"}],decls=["a","h","g"],
                   params=[]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "a",rhs=EXP_STRING "global\n"}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_ID "a"}]} : program
;
