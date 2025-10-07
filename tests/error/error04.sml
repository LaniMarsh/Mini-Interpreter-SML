val prog =
  PROGRAM
    {decls=["i","j"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "i",rhs=EXP_NUM 3}},
                         ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "j",rhs=EXP_NUM 4}},
                         ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "i",
                                   rhs=EXP_BINARY
                                         {lft=EXP_ID "j",opr=BOP_GT,
                                          rht=EXP_BOOL false}}}],decls=[],
                   params=[]})],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "i",rhs=EXP_CALL {args=[],func=EXP_ID "f"}}}]}
  : program
;
