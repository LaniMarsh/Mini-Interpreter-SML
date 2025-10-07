val prog =
  PROGRAM
    {decls=[],
     func_decls=[("f",
                  {body=[ST_IF
                           {el=SOME
                                 (ST_BLOCK
                                    {stmts=[ST_PRINT {exp=EXP_ID "i"},
                                            ST_PRINT {exp=EXP_STRING "\n"},
                                            ST_EXP
                                              {exp=EXP_CALL
                                                     {args=[EXP_BINARY
                                                              {lft=EXP_ID "i",
                                                               opr=BOP_MINUS,
                                                               rht=EXP_NUM 1}],
                                                      func=EXP_ID "f"}}]}),
                            guard=EXP_BINARY
                                    {lft=EXP_ID "i",opr=BOP_LE,rht=EXP_NUM 0},
                            th=ST_BLOCK
                                 {stmts=[ST_PRINT {exp=EXP_NUM 99},
                                         ST_PRINT {exp=EXP_STRING "\n"}]}}],
                   decls=[],params=["i"]})],
     stmts=[ST_EXP {exp=EXP_CALL {args=[EXP_NUM 3],func=EXP_ID "f"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_NUM 2],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_NUM 1},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
