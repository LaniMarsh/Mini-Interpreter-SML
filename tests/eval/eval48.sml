val prog =
  PROGRAM
    {decls=["f","g","a","b","c"],
     func_decls=[("factory",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "f",
                                   rhs=EXP_ANON
                                         {body=[ST_EXP
                                                  {exp=EXP_ASSIGN
                                                         {lhs=EXP_ID "x",
                                                          rhs=EXP_BINARY
                                                                {lft=EXP_ID
                                                                       "x",
                                                                 opr=BOP_PLUS,
                                                                 rht=EXP_ID
                                                                       "dx"}}},
                                                ST_RETURN
                                                  {exp=SOME (EXP_ID "x")}],
                                          decls=[],params=["dx"]}}},
                         ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "g",
                                   rhs=EXP_ANON
                                         {body=[ST_EXP
                                                  {exp=EXP_ASSIGN
                                                         {lhs=EXP_ID "x",
                                                          rhs=EXP_BINARY
                                                                {lft=EXP_ID
                                                                       "x",
                                                                 opr=BOP_MINUS,
                                                                 rht=EXP_ID
                                                                       "dx"}}},
                                                ST_RETURN
                                                  {exp=SOME (EXP_ID "x")}],
                                          decls=[],params=["dx"]}}}],decls=[],
                   params=["x"]})],
     stmts=[ST_EXP {exp=EXP_CALL {args=[EXP_NUM 2],func=EXP_ID "factory"}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "a",
                      rhs=EXP_CALL {args=[EXP_NUM 10],func=EXP_ID "f"}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "b",
                      rhs=EXP_CALL {args=[EXP_NUM 3],func=EXP_ID "f"}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "c",
                      rhs=EXP_CALL {args=[EXP_NUM 5],func=EXP_ID "g"}}},
            ST_PRINT {exp=EXP_ID "a"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_ID "b"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_ID "c"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
