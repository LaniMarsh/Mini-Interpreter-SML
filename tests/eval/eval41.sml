val prog =
  PROGRAM
    {decls=["f1","f2","f3","f4","f5"],
     func_decls=[("f",
                  {body=[ST_EXP
                           {exp=EXP_ASSIGN {lhs=EXP_ID "a",rhs=EXP_NUM 1}},
                         ST_RETURN
                           {exp=SOME
                                  (EXP_ANON
                                     {body=[ST_EXP
                                              {exp=EXP_ASSIGN
                                                     {lhs=EXP_ID "b",
                                                      rhs=EXP_NUM 2}},
                                            ST_IF
                                              {el=SOME
                                                    (ST_BLOCK
                                                       {stmts=[ST_PRINT
                                                                 {exp=EXP_ID
                                                                        "a"},
                                                               ST_PRINT
                                                                 {exp=EXP_STRING
                                                                        "\n"}]}),
                                               guard=EXP_ID "x",
                                               th=ST_BLOCK
                                                    {stmts=[ST_EXP
                                                              {exp=EXP_ASSIGN
                                                                     {lhs=EXP_ID
                                                                            "a",
                                                                      rhs=EXP_BINARY
                                                                            {lft=EXP_ID
                                                                                   "a",
                                                                             opr=BOP_PLUS,
                                                                             rht=EXP_NUM
                                                                                   1}}}]}},
                                            ST_RETURN
                                              {exp=SOME
                                                     (EXP_ANON
                                                        {body=[ST_EXP
                                                                 {exp=EXP_ASSIGN
                                                                        {lhs=EXP_ID
                                                                               "c",
                                                                         rhs=EXP_NUM
                                                                               3}},
                                                               ST_IF
                                                                 {el=SOME
                                                                       (ST_BLOCK
                                                                          {stmts=[ST_PRINT
                                                                                    {exp=EXP_ID
                                                                                           "b"},
                                                                                  ST_PRINT
                                                                                    {exp=EXP_STRING
                                                                                           "\n"}]}),
                                                                  guard=EXP_ID
                                                                          "y",
                                                                  th=ST_BLOCK
                                                                       {stmts=[ST_EXP
                                                                                 {exp=EXP_ASSIGN
                                                                                        {lhs=EXP_ID
                                                                                               "b",
                                                                                         rhs=EXP_BINARY
                                                                                               {lft=EXP_ID
                                                                                                      "b",
                                                                                                opr=BOP_PLUS,
                                                                                                rht=EXP_NUM
                                                                                                      1}}}]}},
                                                               ST_RETURN
                                                                 {exp=SOME
                                                                        (EXP_ANON
                                                                           {body=[ST_EXP
                                                                                    {exp=EXP_ASSIGN
                                                                                           {lhs=EXP_ID
                                                                                                  "b",
                                                                                            rhs=EXP_NUM
                                                                                                  100}},
                                                                                  ST_IF
                                                                                    {el=SOME
                                                                                          (ST_BLOCK
                                                                                             {stmts=[ST_PRINT
                                                                                                       {exp=EXP_ID
                                                                                                              "c"},
                                                                                                     ST_PRINT
                                                                                                       {exp=EXP_STRING
                                                                                                              "\n"}]}),
                                                                                     guard=EXP_ID
                                                                                             "z",
                                                                                     th=ST_BLOCK
                                                                                          {stmts=[ST_EXP
                                                                                                    {exp=EXP_ASSIGN
                                                                                                           {lhs=EXP_ID
                                                                                                                  "c",
                                                                                                            rhs=EXP_BINARY
                                                                                                                  {lft=EXP_ID
                                                                                                                         "c",
                                                                                                                   opr=BOP_PLUS,
                                                                                                                   rht=EXP_NUM
                                                                                                                         1}}}]}},
                                                                                  ST_RETURN
                                                                                    {exp=SOME
                                                                                           (EXP_ANON
                                                                                              {body=[ST_EXP
                                                                                                       {exp=EXP_ASSIGN
                                                                                                              {lhs=EXP_ID
                                                                                                                     "a",
                                                                                                               rhs=EXP_BINARY
                                                                                                                     {lft=EXP_ID
                                                                                                                            "a",
                                                                                                                      opr=BOP_PLUS,
                                                                                                                      rht=EXP_NUM
                                                                                                                            1}}},
                                                                                                     ST_EXP
                                                                                                       {exp=EXP_ASSIGN
                                                                                                              {lhs=EXP_ID
                                                                                                                     "b",
                                                                                                               rhs=EXP_BINARY
                                                                                                                     {lft=EXP_ID
                                                                                                                            "b",
                                                                                                                      opr=BOP_PLUS,
                                                                                                                      rht=EXP_NUM
                                                                                                                            1}}},
                                                                                                     ST_EXP
                                                                                                       {exp=EXP_ASSIGN
                                                                                                              {lhs=EXP_ID
                                                                                                                     "c",
                                                                                                               rhs=EXP_BINARY
                                                                                                                     {lft=EXP_ID
                                                                                                                            "c",
                                                                                                                      opr=BOP_PLUS,
                                                                                                                      rht=EXP_NUM
                                                                                                                            1}}},
                                                                                                     ST_RETURN
                                                                                                       {exp=SOME
                                                                                                              (EXP_ANON
                                                                                                                 {body=[ST_PRINT
                                                                                                                          {exp=EXP_ID
                                                                                                                                 "a"},
                                                                                                                        ST_PRINT
                                                                                                                          {exp=EXP_STRING
                                                                                                                                 "\n"},
                                                                                                                        ST_PRINT
                                                                                                                          {exp=EXP_ID
                                                                                                                                 "b"},
                                                                                                                        ST_PRINT
                                                                                                                          {exp=EXP_STRING
                                                                                                                                 "\n"},
                                                                                                                        ST_PRINT
                                                                                                                          {exp=EXP_ID
                                                                                                                                 "c"},
                                                                                                                        ST_PRINT
                                                                                                                          {exp=EXP_STRING
                                                                                                                                 "\n"}],
                                                                                                                  decls=[],
                                                                                                                  params=[]})}],
                                                                                               decls=[],
                                                                                               params=[]})}],
                                                                            decls=["b"],
                                                                            params=["z"]})}],
                                                         decls=["c"],
                                                         params=["y"]})}],
                                      decls=["b"],params=["x"]})}],
                   decls=["a"],params=[]})],
     stmts=[ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f1",rhs=EXP_CALL {args=[],func=EXP_ID "f"}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f2",
                      rhs=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f1"}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f3",
                      rhs=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f2"}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f4",
                      rhs=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f3"}}},
            ST_EXP
              {exp=EXP_ASSIGN
                     {lhs=EXP_ID "f5",rhs=EXP_CALL {args=[],func=EXP_ID "f4"}}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f5"}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f4"}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f4"}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f4"}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f5"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f1"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f2"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f3"}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f5"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "f1"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "f2"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "f3"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "f1"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "f2"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL true],func=EXP_ID "f3"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f1"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f2"}},
            ST_EXP {exp=EXP_CALL {args=[EXP_BOOL false],func=EXP_ID "f3"}},
            ST_EXP {exp=EXP_CALL {args=[],func=EXP_ID "f5"}}]} : program
;
