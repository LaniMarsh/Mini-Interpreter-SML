val prog =
  PROGRAM
    {decls=["b","c"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "b",rhs=EXP_NUM 100}},
                         ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "c",rhs=EXP_NUM 200}},
                         ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "g"}},
                         ST_PRINT {exp=EXP_ID "b"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_PRINT {exp=EXP_ID "c"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=["b","c"],
                   params=["g"]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "b",rhs=EXP_NUM 1}},
            ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "c",rhs=EXP_NUM 2}},
            ST_EXP
              {exp=EXP_CALL
                     {args=[EXP_ANON
                              {body=[ST_EXP
                                       {exp=EXP_ASSIGN
                                              {lhs=EXP_ID "b",rhs=EXP_NUM 99}},
                                     ST_EXP
                                       {exp=EXP_ASSIGN
                                              {lhs=EXP_ID "c",rhs=EXP_NUM 21}}],
                               decls=[],params=[]}],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_ID "b"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_ID "c"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
