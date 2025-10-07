val prog =
  PROGRAM
    {decls=["y"],
     func_decls=[("f",
                  {body=[ST_PRINT
                           {exp=EXP_BINARY
                                  {lft=EXP_ID "a",opr=BOP_PLUS,rht=EXP_ID "y"}},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                   params=["a"]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "y",rhs=EXP_NUM 9}},
            ST_PRINT {exp=EXP_NUM 0},ST_PRINT {exp=EXP_STRING "\n"},
            ST_EXP {exp=EXP_CALL {args=[EXP_NUM 1],func=EXP_ID "f"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_NUM 2],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_NUM 3},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
