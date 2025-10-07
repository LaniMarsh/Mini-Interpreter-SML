val prog =
  PROGRAM
    {decls=["i"],func_decls=[],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "i",
                      rhs=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "i"}}}]}
  : program
;
