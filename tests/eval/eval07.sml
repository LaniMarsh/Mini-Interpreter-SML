val prog =
  PROGRAM
    {decls=["result"],
     func_decls=[("fact",
                  {body=[ST_IF
                           {el=SOME
                                 (ST_BLOCK
                                    {stmts=[ST_EXP
                                              {exp=EXP_CALL
                                                     {args=[EXP_BINARY
                                                              {lft=EXP_ID "n",
                                                               opr=BOP_MINUS,
                                                               rht=EXP_NUM 1}],
                                                      func=EXP_ID "fact"}},
                                            ST_EXP
                                              {exp=EXP_ASSIGN
                                                     {lhs=EXP_ID "result",
                                                      rhs=EXP_BINARY
                                                            {lft=EXP_ID "n",
                                                             opr=BOP_TIMES,
                                                             rht=EXP_ID
                                                                   "result"}}}]}),
                            guard=EXP_BINARY
                                    {lft=EXP_ID "n",opr=BOP_LE,rht=EXP_NUM 0},
                            th=ST_BLOCK
                                 {stmts=[ST_EXP
                                           {exp=EXP_ASSIGN
                                                  {lhs=EXP_ID "result",
                                                   rhs=EXP_NUM 1}}]}}],
                   decls=[],params=["n"]})],
     stmts=[ST_EXP {exp=EXP_CALL {args=[EXP_NUM 5],func=EXP_ID "fact"}},
            ST_PRINT {exp=EXP_ID "result"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
