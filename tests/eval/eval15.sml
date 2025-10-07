val prog =
  PROGRAM
    {decls=["a","b","g","d"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "a",
                                   rhs=EXP_ASSIGN
                                         {lhs=EXP_ID "b",rhs=EXP_ID "g"}}},
                         ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "d",rhs=EXP_NUM 9}},
                         ST_PRINT {exp=EXP_ID "a"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_PRINT {exp=EXP_ID "b"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_PRINT {exp=EXP_ID "g"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_PRINT {exp=EXP_ID "d"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=["a","c","d"],
                   params=[]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "g",rhs=EXP_NUM 4}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_ID "a"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_ID "b"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_ID "g"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_ID "d"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
