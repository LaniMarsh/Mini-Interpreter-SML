val prog =
  PROGRAM
    {decls=[],
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
                   params=["g"]}),
                 ("h",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "b",rhs=EXP_NUM 1}},
                         ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "c",rhs=EXP_NUM 2}},
                         ST_EXP
                           {exp=EXP_CALL
                                  {args=[EXP_ANON
                                           {body=[ST_EXP
                                                    {exp=EXP_ASSIGN
                                                           {lhs=EXP_ID "b",
                                                            rhs=EXP_BINARY
                                                                  {lft=EXP_ID
                                                                         "b",
                                                                   opr=BOP_TIMES,
                                                                   rht=EXP_NUM
                                                                         2}}},
                                                  ST_EXP
                                                    {exp=EXP_ASSIGN
                                                           {lhs=EXP_ID "c",
                                                            rhs=EXP_BINARY
                                                                  {lft=EXP_ID
                                                                         "c",
                                                                   opr=BOP_PLUS,
                                                                   rht=EXP_NUM
                                                                         7}}}],
                                            decls=[],params=[]}],
                                   func=EXP_ID "f"}},
                         ST_PRINT {exp=EXP_ID "b"},
                         ST_PRINT {exp=EXP_STRING "\n"},
                         ST_PRINT {exp=EXP_ID "c"},
                         ST_PRINT {exp=EXP_STRING "\n"}],decls=["b","c"],
                   params=[]})],
     stmts=[ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "h"}}]} : program
;
