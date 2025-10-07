val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_WHILE
                           {body=ST_BLOCK
                                   {stmts=[ST_PRINT {exp=EXP_ID "n"},
                                           ST_PRINT {exp=EXP_STRING "\n"},
                                           ST_IF
                                             {el=NONE,
                                              guard=EXP_BINARY
                                                      {lft=EXP_ID "n",
                                                       opr=BOP_LE,
                                                       rht=EXP_NUM 5},
                                              th=ST_BLOCK
                                                   {stmts=[ST_RETURN
                                                             {exp=NONE}]}},
                                           ST_EXP
                                             {exp=EXP_ASSIGN
                                                    {lhs=EXP_ID "n",
                                                     rhs=EXP_BINARY
                                                           {lft=EXP_ID "n",
                                                            opr=BOP_MINUS,
                                                            rht=EXP_NUM 1}}}]},
                            guard=EXP_BINARY
                                    {lft=EXP_ID "n",opr=BOP_GT,rht=EXP_NUM 0}}],
                   decls=[],params=["n"]})],
     stmts=[ST_PRINT {exp=EXP_CALL {args=[EXP_NUM 3],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[EXP_NUM 10],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
