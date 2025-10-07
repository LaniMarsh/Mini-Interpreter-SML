val prog =
  PROGRAM
    {decls=["a","b"],
     func_decls=[("f",
                  {body=[ST_PRINT {exp=EXP_ID "a"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_EXP
                           {exp=EXP_ASSIGN
                                  {lhs=EXP_ID "a",
                                   rhs=EXP_BINARY
                                         {lft=EXP_ID "a",opr=BOP_MINUS,
                                          rht=EXP_NUM 7}}},
                         ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "b",rhs=EXP_BOOL false}},
                         ST_PRINT {exp=EXP_ID "a"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_PRINT {exp=EXP_ID "b"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=[],
                   params=["a","b"]})],
     stmts=[ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "a",rhs=EXP_NUM 28}},
            ST_EXP {exp=EXP_ASSIGN {lhs=EXP_ID "b",rhs=EXP_BOOL true}},
            ST_PRINT {exp=EXP_ID "a"},ST_PRINT {exp=EXP_STRING " "},
            ST_PRINT {exp=EXP_ID "b"},ST_PRINT {exp=EXP_STRING "\n"},
            ST_EXP
              {exp=EXP_CALL {args=[EXP_ID "a",EXP_ID "b"],func=EXP_ID "f"}},
            ST_PRINT {exp=EXP_ID "a"},ST_PRINT {exp=EXP_STRING " "},
            ST_PRINT {exp=EXP_ID "b"},ST_PRINT {exp=EXP_STRING "\n"}]}
  : program
;
