val prog =
  PROGRAM
    {decls=["h","fact"],
     func_decls=[("z",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "g",
                                   rhs=EXP_ANON
                                         {body=[ST_RETURN
                                                  {exp=SOME
                                                         (EXP_CALL
                                                            {args=[EXP_ANON
                                                                     {body=[ST_RETURN
                                                                              {exp=SOME
                                                                                     (EXP_CALL
                                                                                        {args=[EXP_ID
                                                                                                 "y"],
                                                                                         func=EXP_CALL
                                                                                                {args=[EXP_ID
                                                                                                         "x"],
                                                                                                 func=EXP_ID
                                                                                                        "x"}})}],
                                                                      decls=[],
                                                                      params=["y"]}],
                                                             func=EXP_ID "f"})}],
                                          decls=[],params=["x"]}}},
                         ST_RETURN
                           {exp=SOME
                                  (EXP_CALL
                                     {args=[EXP_ID "g"],func=EXP_ID "g"})}],
                   decls=["g"],params=["f"]})],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "fact",
                      rhs=EXP_ANON
                            {body=[ST_RETURN
                                     {exp=SOME
                                            (EXP_ANON
                                               {body=[ST_IF
                                                        {el=SOME
                                                              (ST_BLOCK
                                                                 {stmts=[ST_RETURN
                                                                           {exp=SOME
                                                                                  (EXP_BINARY
                                                                                     {lft=EXP_ID
                                                                                            "x",
                                                                                      opr=BOP_TIMES,
                                                                                      rht=EXP_CALL
                                                                                            {args=[EXP_BINARY
                                                                                                     {lft=EXP_ID
                                                                                                            "x",
                                                                                                      opr=BOP_MINUS,
                                                                                                      rht=EXP_NUM
                                                                                                            1}],
                                                                                             func=EXP_ID
                                                                                                    "funcArg"}})}]}),
                                                         guard=EXP_BINARY
                                                                 {lft=EXP_ID
                                                                        "x",
                                                                  opr=BOP_EQ,
                                                                  rht=EXP_NUM
                                                                        0},
                                                         th=ST_BLOCK
                                                              {stmts=[ST_RETURN
                                                                        {exp=SOME
                                                                               (EXP_NUM
                                                                                  1)}]}}],
                                                decls=[],params=["x"]})}],
                             decls=[],params=["funcArg"]}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "h",
                      rhs=EXP_CALL {args=[EXP_ID "fact"],func=EXP_ID "z"}}},
            ST_PRINT {exp=EXP_CALL {args=[EXP_NUM 6],func=EXP_ID "h"}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
