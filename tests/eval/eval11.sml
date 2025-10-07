val prog =
  PROGRAM
    {decls=["i","x"],
     func_decls=[("f",
                  {body=[ST_WHILE
                           {body=ST_BLOCK
                                   {stmts=[ST_EXP
                                             {exp=EXP_CALL
                                                    {args=[EXP_ID "i"],
                                                     func=EXP_ID "g"}},
                                           ST_EXP
                                             {exp=EXP_ASSIGN
                                                    {lhs=EXP_ID "i",
                                                     rhs=EXP_BINARY
                                                           {lft=EXP_ID "i",
                                                            opr=BOP_MINUS,
                                                            rht=EXP_NUM 1}}}]},
                            guard=EXP_BINARY
                                    {lft=EXP_ID "i",opr=BOP_GT,rht=EXP_NUM 0}}],
                   decls=[],params=["i"]}),
                 ("g",
                  {body=[ST_PRINT
                           {exp=EXP_BINARY
                                  {lft=EXP_ID "j",opr=BOP_TIMES,rht=EXP_NUM 2}},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "i",
                                   rhs=EXP_BINARY
                                         {lft=EXP_ID "i",opr=BOP_MINUS,
                                          rht=EXP_NUM 1}}}],decls=[],
                   params=["j"]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "i",rhs=EXP_NUM 20}},
            ST_WHILE
              {body=ST_BLOCK
                      {stmts=[ST_PRINT {exp=EXP_ID "i"},
                              ST_PRINT {exp=EXP_STRING "\n"},
                              ST_EXP
                                {exp=EXP_CALL
                                       {args=[EXP_ID "i"],func=EXP_ID "f"}},
                              ST_PRINT {exp=EXP_ID "i"},
                              ST_PRINT {exp=EXP_STRING "\n"},
                              ST_EXP
                                {exp=EXP_ASSIGN
                                       {lhs=EXP_ID "i",
                                        rhs=EXP_BINARY
                                              {lft=EXP_ID "i",opr=BOP_MINUS,
                                               rht=EXP_NUM 1}}}]},
               guard=EXP_BINARY {lft=EXP_ID "i",opr=BOP_GT,rht=EXP_NUM 0}},
            ST_PRINT {exp=EXP_ID "i"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
