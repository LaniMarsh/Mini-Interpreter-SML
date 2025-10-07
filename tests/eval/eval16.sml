val prog =
  PROGRAM
    {decls=[],
     func_decls=[("fact",
                  {body=[ST_IF
                           {el=SOME
                                 (ST_BLOCK
                                    {stmts=[ST_RETURN
                                              {exp=SOME
                                                     (EXP_BINARY
                                                        {lft=EXP_ID "n",
                                                         opr=BOP_TIMES,
                                                         rht=EXP_CALL
                                                               {args=[EXP_BINARY
                                                                        {lft=EXP_ID
                                                                               "n",
                                                                         opr=BOP_MINUS,
                                                                         rht=EXP_NUM
                                                                               1}],
                                                                func=EXP_ID
                                                                       "fact"}})}]}),
                            guard=EXP_BINARY
                                    {lft=EXP_ID "n",opr=BOP_LE,rht=EXP_NUM 0},
                            th=ST_BLOCK
                                 {stmts=[ST_RETURN {exp=SOME (EXP_NUM 1)}]}}],
                   decls=[],params=["n"]})],
     stmts=[ST_PRINT {exp=EXP_CALL {args=[EXP_NUM 5],func=EXP_ID "fact"}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
