val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_CALL
                                  {args=[EXP_BINARY
                                           {lft=EXP_NUM 14,opr=BOP_TIMES,
                                            rht=EXP_NUM 2}],func=EXP_ID "g"}},
                         ST_PRINT {exp=EXP_ID "i"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                   params=["i"]}),
                 ("g",
                  {body=[ST_PRINT {exp=EXP_ID "i"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "i",rhs=EXP_NUM 17}},
                         ST_PRINT {exp=EXP_NUM 3},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                   params=["i"]})],
     stmts=[ST_EXP {exp=EXP_CALL {args=[EXP_NUM 7],func=EXP_ID "f"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_NUM 8],func=EXP_ID "g"}}]}
  : program
;
