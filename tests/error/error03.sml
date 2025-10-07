val prog =
  PROGRAM
    {decls=["x"],func_decls=[("j",{body=[],decls=[],params=["b"]})],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "x",
                      rhs=EXP_CALL
                            {args=[EXP_BINARY
                                     {lft=EXP_BOOL true,opr=BOP_GT,
                                      rht=EXP_NUM 3}],func=EXP_ID "j"}}}]}
  : program
;
