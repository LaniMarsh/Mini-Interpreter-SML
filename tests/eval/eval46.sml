val prog =
  PROGRAM
    {decls=["i"],
     func_decls=[("g",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "i",rhs=EXP_ID "n"}},
                         ST_PRINT {exp=EXP_ID "i"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                   params=["n"]}),
                 ("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "i",rhs=EXP_NUM 2}},
                         ST_PRINT {exp=EXP_ID "i"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_EXP
                           {exp=EXP_CALL {args=[EXP_NUM 8],func=EXP_ID "g"}},
                         ST_PRINT {exp=EXP_ID "i"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=["i"],
                   params=["n"]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "i",rhs=EXP_NUM 3}},
            ST_PRINT {exp=EXP_ID "i"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_EXP {exp=EXP_CALL {args=[EXP_NUM 2],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_ID "i"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
