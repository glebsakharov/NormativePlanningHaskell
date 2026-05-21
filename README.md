

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

instance Arbitrary LTLf where 
	arbitrary = sized ltlfGen 
		where 
			ltlfGen :: Int -> Gen LTLf
			ltlfGen 0 = oneof [
					pure TrueF,
					pure FalseF,
					Prop <$> arbitrary
				]
			ltlfGen n = frequency [
					(1, pure TrueF),
					(1, pure FalseF),
					(2, Prop <$> arbitrary),
					(2, Not <$> ltlfGen (n-1)),
					(2, And <$> ltlfGen(n-1) <*> ltlfGen(n-1)),
					(2, Or <$> ltlfGen(n-1) <*> ltlfGen(n-1)),
					(1, Next <$> ltlfGen(n-1)),
					(1, Until <$> ltlfGen(n-1) <*> ltlfGen(n-1)),
					(1, Release <$> ltlfGen(n-1) <*> ltlfGen(n-1))
				]

smallLTLf1 :: Gen LTLf 
smallLTLf1 = resize 3 arbitrary
```


