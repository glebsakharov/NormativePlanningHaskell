

# LTLf and Finite Automata in Norm-Guided Planning

This ReadMe is here to explain the current state of the integration of temporal planning into Fast Downward via the fastdownward library from Hackage. Fast Downward is a classical domain indepenedent planner written in C++. fastdownward is a Domain Specific Language for defining planning problems, converting them into a format Fast Downward recognises and solving them in Fast Downward. But fastdownward is written in Haskell. It is essentially a wrapper to Fast Downward.

# A classical planning problem in fastdownward: Gripper

# Temporal Planning planning problem

# LTLf to Deterministic Finite Automaton

# Testing and Debugging the LTLf to DFA translation

``` haskell
instance Arbitrary Atom where 
	arbitrary = oneof [
			Atom <$> (pure "safety"),
			Atom <$> (pure "taskCompletion")
		]

data FormulaClass = Simple | Linear | Balanced | Complex

ltlfGenWithClass :: Int -> FormulaClass -> Gen LTLf
ltlfGenWithClass 0 _ = oneof [pure TrueF, pure FalseF, Prop <$> arbitrary]
ltlfGenWithClass n Simple = frequency [
    (5, Prop <$> arbitrary),
    (2, Not <$> (ltlfGenWithClass (n-1) Simple)),
    (1, Next <$> (ltlfGenWithClass (n-1) Simple))
  ]
ltlfGenWithClass n Linear = frequency [
    (3, Prop <$> arbitrary),
    (2, Not <$> (ltlfGenWithClass (n-1) Linear)),
    (1, Until <$> (ltlfGenWithClass (n-1) Linear) <*> (ltlfGenWithClass 0 Linear))
    
  ]
ltlfGenWithClass n Complex = 
    ltlfGenWithClass n Simple


smallLTLf2 :: Gen LTLf
smallLTLf2 = sized $ \n -> 
    frequency [
        (5, ltlfGenWithClass (min n 2) Simple),
        (4, ltlfGenWithClass (min n 2) Linear),
        (1, ltlfGenWithClass (min n 2) Complex)
    ]
```


