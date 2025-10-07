val prog =
  PROGRAM
    {decls=["g","h"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "a",rhs=EXP_NUM 0}},
                         ST_RETURN
                           {exp=SOME
                                  (EXP_ANON
                                     {body=[ST_EXP
                                              {exp=EXP_ASSIGN
                                                     {lhs=EXP_ID "a",
                                                      rhs=EXP_BINARY
                                                            {lft=EXP_ID "a",
                                                             opr=BOP_PLUS,
                                                             rht=EXP_NUM 1}}},
                                            ST_RETURN {exp=SOME (EXP_ID "a")}],
                                      decls=[],params=[]})}],decls=["a"],
                   params=[]})],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "g",rhs=EXP_CALL {args=[],func=EXP_ID "f"}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "h",rhs=EXP_CALL {args=[],func=EXP_ID "f"}}},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "g"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "g"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "g"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "h"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "h"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "h"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "g"}},
            ST_PRINT {exp=EXP_STRING "\n"},
            ST_PRINT {exp=EXP_CALL {args=[],func=EXP_ID "h"}},
            ST_PRINT {exp=EXP_STRING "\n"}]} : program
;
