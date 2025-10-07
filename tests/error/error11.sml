val prog =
  PROGRAM
    {decls=["f"],
     func_decls=[("g",
                  {body=[ST_IF
                           {el=SOME
                                 (ST_BLOCK
                                    {stmts=[ST_RETURN
                                              {exp=SOME (EXP_BOOL true)}]}),
                            guard=EXP_ID "x",
                            th=ST_BLOCK
                                 {stmts=[ST_RETURN
                                           {exp=SOME
                                                  (EXP_ANON
                                                     {body=[ST_RETURN
                                                              {exp=SOME
                                                                     (EXP_BINARY
                                                                        {lft=EXP_ID
                                                                               "x",
                                                                         opr=BOP_PLUS,
                                                                         rht=EXP_NUM
                                                                               1})}],
                                                      decls=[],params=["x"]})}]}}],
                   decls=[],params=["x"]})],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f",
                      rhs=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "g"}}},
            ST_PRINT {exp=EXP_ID "f"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f",
                      rhs=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "g"}}},
            ST_PRINT {exp=EXP_ID "f"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_EXP {exp=EXP_CALL {args=[EXP_NUM 2],func=EXP_ID "f"}}]}
  : program
;
