import Data.List

--------------------
-- Definitions
--------------------


type NFTA = ([String], [String], [String], [([String], [String])])	-- (Q, F, Qf, delta)
type DFTA = ([String], [String], [String], [([String], [String])])

type G = (String, [String], [String], [(String, [String])])		-- (S, N, F, R)




--------------------
-- Examples
--------------------


-- example automata 

f = ["g", "f", "a", "h"] -- list of symbols
q = ["Qa", "Qg", "Qf", "Qh"] -- list of states
q' = []
qf =["Qf"] --final states

-- arity function for f
arityF :: String -> Int
arityF "h" = 3
arityF "f" = 2
arityF "g" = 1
arityF "a" = 0
arityF _ = 1

arityF' :: String -> Int
arityF' "a" = 2
arityF' "g" = -1
arityF' "f" = 0
arityF' _ = 1

-- list of transition rules
deltaF :: [([String], [String])]
deltaF = [(["a"], ["Qa", "a"]), (["g", "Qa", ""], ["Qg", "g", ""]), (["f", "Qa", "", "Qa", ""], ["Qf", "f", "", ""]), (["h", "Qa", "", "Qa", "", "Qa"], ["Qh", "h", "", "", ""])]

deltaF' = [([], [])]

deltaF_nondet = [(["a"], ["Qg", "a"]), (["g", "Qg", ""], ["Qg", "g", ""]), (["f", "Qg", "", "Qa", ""], ["Qf", "f", "", ""]), (["h", "Qa", "", "Qf", "", "Qg", ""], ["Qh", "h", "", "", ""])] ++ deltaF


--
deltaF1 :: [([String], [String])]
deltaF1 = [(["a"], ["Qa", "a"]), (["g", "Qa", "x"], ["Qg", "g", "x"]), (["g", "Qg", "x"], ["Qg", "g", "x"]), (["f", "Qg", "x", "Qg", "y"], ["Qf", "f", "x", "y"])] -- example 1.1.1
deltaF2 = [(["a"], ["Qa", "a"]), (["a"], ["Qg", "a"]), (["g", "Qg", ""], ["Qg", "a", ""]), (["g", "Qa", "x"], ["Qg", "a", "x"]), (["g", "Qg", "x"], ["Qg", "g", "x"]), (["f", "Qg", "x", "Qg", "y"], ["Qf", "f", "x", "y"])] -- example 1.1.1 + additional transitions to test nondetDeltaTree

nftaTest = (q, f, qf, deltaF2)
dftaTest = (q, f, qf, deltaF1)

dfta1 = (q, f, qf, deltaF)
nfta1 = (q, f, qf, deltaF_nondet)

f_det = f
q_det = ["Q", "Qg","Qf"]
qf_det = ["Qf"]
delta_det = [(["a"], ["Q"]), (["g", "Q"], ["Q"]), (["g", "Q"], ["Qg"]), (["g", "Qg"], ["Qf"]), (["f", "Q", "Q"], ["Q"])]

nftaDet = (q_det, f_det, qf_det, delta_det)



-- example (propositional logic)
s = "Prop"
n = ["Prop", "Rel"]
n2 = ["Prop", "Rel", "Rel2"]
grammar_f = ["true", "false", "not", "and", "or"]
prodRules = [("Prop", ["true"]), ("Prop", ["false"]), ("Prop", ["Rel"]), ("Rel", ["not", "Prop"]), ("Rel", ["and", "Prop", "Prop"]), ("Rel", ["or", "Prop", "Prop"])]
prodRules2 = [("Prop", ["true"]), ("Prop", ["false"]), ("Prop", ["Rel"]), ("Rel", ["not", "true"]), ("Rel", ["not", "false"]), ("Rel", ["and", "true", "Rel2"]), ("Rel2", ["not", "true"]), ("Rel2", ["not", "false"])]
prodRules3 = [("Prop", ["true"]), ("Prop", ["false"]), ("Prop", ["Rel"]), ("Rel2", ["not", "true"]), ("Rel2", ["not", "false"]), ("Rel2", ["and", "true", "Rel"])]

g1 = (s, n, grammar_f, prodRules)
gTest2 = (s, n2, grammar_f, prodRules2)
gTest3 = (s, n2, grammar_f, prodRules3)




--------------------
-- Generic Tree Languages
--------------------


-- generic tree automata

-- symbols: "fx_y" with x = arity, y = counter
-- generates a list of symbols with 
-- generateSymbols :: amount -> maxArity -> f
generateSymbols :: Int -> Int -> [String]
generateSymbols 0 _ = []
generateSymbols n maxArity = ["f" ++ (show ar) ++ "_" ++ (show m) | ar <- [0..maxArity], m <- [1..n]]


-- the arity function for generated symbols
generateArity :: String -> Int
generateArity ('f':xs) = read (generateArity' xs) :: Int
	where	generateArity' xs
			| null xs = []
			| (head xs) == '_' = []
			| otherwise = [head xs] ++ generateArity' (tail xs)
generateArity _ = 1	--default case for states


--states: "qa:fx_y" with a = counter, "fx_y" = state
-- generates states given a list of symbols
-- generateStates :: amount -> f -> q
generateStates :: Int -> [String] -> [String]
generateStates 0 _ = []
generateStates _ [] = []
generateStates n f = ["q" ++ (show m) ++ ":" ++ symbol | m <- [1..n], symbol <- f]


-- generate final states by defining some generated states to be final
-- generateFinalStates :: amount -> arityList -> q -> qf
generateFinalStates :: Int -> [String] -> [String]
generateFinalStates 0 _ = []
generateFinalStates n q = generateFinalStates' n (separateByArity q 0)
	where	generateFinalStates' n qList
			| null qList = []
			| otherwise = take n (head qList) ++ generateFinalStates' n (tail qList)
		separateByArity q ar
			| null q = []
			| ar > maximum (arityList q stateArity) = []
			| otherwise = [x | x <- q, (stateArity x) == ar] : separateByArity q (ar+1)	-- ++
			
			
-- generate delta rules given states and symbols
-- generateDelta :: q -> f -> arity -> deltaRules
generateDelta :: [String] -> [String] -> (String -> Int) -> [([String], [String])]
generateDelta [] _ _ = []
generateDelta _ [] _ = []
generateDelta q f arity = removeDuplicates $ generateDelta' f
	where	generateDelta' editedF
			| null editedF = []
			| otherwise = generateRule (head editedF) (arity (head editedF)) ++ (generateDelta' (tail editedF))
		generateRule symbol ar
			| ar == 0 = [([symbol], [state, symbol]) | state <- q, symbolState symbol state]
			| ar == 1 = [([symbol, subtreeState, ""], [state, symbol, subtreeSymbol]) | state <- q, subtreeState <- q, subtreeSymbol <- f, symbolState symbol state, symbolState subtreeSymbol subtreeState]
			| ar >= 2 = [([symbol] ++ (intersperse "" (subtreeStates) ++ [""]), [state, symbol] ++ (replicate ar "")) | state <- q, subtreeStates <- (allSubtreeStates ar), symbolState symbol state]
		allSubtreeStates ar = [take ar states | states <- take 1 (permutations q)]

		
-- add redundant states and transitions to generated automaton, in order to test reduction algorithm
-- generateDeltaRedundant :: NFTA -> NFTA
generateDeltaRedundant :: NFTA -> NFTA
generateDeltaRedundant (q, f, qf, deltaRules) = (q_reducible, f, qf_reducible, deltaRules_reducible)
	where	q_reducible = q ++ ["q" ++ (show n) ++ "_reducible" | n <- [1..(maximum (arityList q stateArity))]]
		qf_reducible = qf `intersect` q_reducible
		deltaRules_reducible = deltaRules ++ [([symbol, state], ["Q_unreachable"]) | symbol <- f, state <- (q_reducible \\ q), generateArity symbol > 0]



-- auxiliary functions		
		
stateArity :: String -> Int
stateArity xs = read (stateArity' xs False) :: Int
	where	stateArity' xs isNumber
			| null xs = []
			| (head xs) == 'f' = stateArity' (tail xs) True
			| (head xs) == '_' = []
			| isNumber = (head xs) : stateArity' (tail xs) isNumber
			| otherwise = stateArity' (tail xs) isNumber


symbolState :: String -> String -> Bool
symbolState symbol state
	| head state == 'f' = state == symbol
	| otherwise = symbolState symbol (tail state)
	
	
eq' :: Eq a => [a] -> [a] -> Bool
eq' xs ys 
	| null xs = True
	| null ys = True
	| otherwise = (head xs) `elem` ys && eq' (tail xs) ys


-- test functions for algorithms

testRed :: Int -> Int -> Int -> Bool
testRed sym maxArity sta = eq nfta (red nftaR generateArity)
	where	nfta = (q, f, [], deltaRules)
		nftaR = generateDeltaRedundant nfta
		eq (q, f, qf, d) (qr, fr, qfr, dr) = (eq' q qr) && (eq' d dr)
		q = generateStates sta f
		f = generateSymbols sym maxArity
		deltaRules = generateDelta q f generateArity


--testDet :: Int -> Int -> Int -> Bool
testDet sym maxArity sta = correct nftaDet nfta
	where	nfta = (q, f, [], deltaRules)
		nftaDet = det nfta generateArity
		correct ((qd, fd, qfd, deltad), dict) (q, f, qf, delta) = (eq' (pseudoLookup dict)  (correctQ q f)) && correctDelta deltad f q	-- !!
		correctQ q f
			| null f = [q]
			| otherwise = ([state | state <- q, symbolState (head f) state]) : (correctQ q (tail f))
		correctDelta deltad f q
			| null f = True
			| generateArity (head f) == 0 = True
			| otherwise = (uniqueDelta (map (\x -> (fst x) `intersect` q) [deltaRule | deltaRule <- deltad, (head (fst (deltaRule))) == (head f)])) && (correctDelta deltad (tail f) q)
		uniqueDelta deltaStateList = deltaStateList == deltaStateList\\(removeDuplicates deltaStateList)
		pseudoLookup dict = [snd entry | entry <- dict]
		q = generateStates sta f
		f = generateSymbols sym maxArity
		deltaRules = generateDelta q f generateArity



-- was used for bugfixing

--writeRed sym maxArity sta = red nftaR generateArity
--	where	nftaR = generateDeltaRedundant nfta
--		nfta = (q, f, [], deltaRules)
--		q = generateStates sta f
--		f = generateSymbols sym maxArity
--		deltaRules = generateDelta q f generateArity

--writeGen sym maxArity sta = (q, f, [], deltaRules)
--	where	q = generateStates sta f
--		f = generateSymbols sym maxArity
--		deltaRules = generateDelta q f generateArity

--genF = generateSymbols 1 2
--genQ = generateStates 1 genF
--genQf = []
--genDelta = generateDelta genQ genF generateArity
--genNfta = (genQ, genF, genQf, genDelta)
--redNfta = generateDeltaRedundant genNfta



-- generic tree grammars

-- generates grammar with x terminals and x*y nonterminals, with 'depth' y (y steps from axiom to tree)
-- generateGrammar :: amountTerminals -> maxArity -> derivationDepth -> grammar
generateGrammar :: Int -> Int -> Int -> G
generateGrammar amountTerminals maxArity depth = (axiom, nonterminals, terminals, prodRules)
	where	axiom = "S"
		nonterminals = (axiom) : ["T" ++ (show n) | n <- [1..amountTerminals]] ++ ["N" ++ (show d) ++ "_" ++ (show n) | n <- [1..amountTerminals*maxArity], d <- [1..depth]]
		terminals = generateSymbols amountTerminals maxArity
		prodRules = [(var, [symbol]) | var <- nonterminals, symbol <- terminals, (head var) == 'T', symbol == terminals!!((read (tail var) :: Int)-1), generateArity symbol == 0] ++ [(axiom, [symbol] ++ subtrees) | symbol <- terminals, subtrees <- (subtreeList symbol 0), generateArity symbol > 0] ++ inbetweenRules 1
		inbetweenRules d
			| d > depth = []
			| otherwise = [(var, [symbol] ++ subtrees) | var <- nonterminals, symbol <- terminals, (head var) == 'N', isDepth (tail var) (show d), subtrees <- (subtreeList symbol d), generateArity symbol > 0] ++ inbetweenRules (d+1)
		isDepth var d
			| (head var) == '_' = True
			| otherwise = (head var) == (head d) && isDepth (tail var) (tail d)
		subtreeList symbol d
			| depth < 1 && d == 0 = foldr (++) [] $ map permutations $ filter (\x -> (length x) == (generateArity symbol)) $ powerSet ((filter (\x -> (head x) == 'T')) (nonterminals\\["S"]))
			| d == depth = foldr (++) [] $ map permutations $ filter (\x -> (length x) == (generateArity symbol)) $ powerSet ((filter (\x -> (head x) == 'T' || (((head x) == 'N' && isDepth (tail x) (show d))))) (nonterminals\\["S"]))
			| otherwise = foldr (++) [] $ map permutations $ filter (\x -> (length x) == (generateArity symbol)) $ powerSet ((filter (\x -> (head x) == 'N' && [head (tail x)] == show (d+1))) (nonterminals\\["S"]))


-- add redundant nonterminals and production rules, in order to test reduction algorithm
-- generateRedundant :: grammar -> grammar
generateRRedundant :: G -> G
generateRRedundant (s, n, f, r) = (s, n_reducible, f, r_reducible)
	where 	n_reducible = n ++ unprod ++ unreach
		unreach = ["Unreachable" ++ (show n) | n <- [1..((length n) `div` 2)]]
		unprod = ["Unproductive" ++ (show n) | n <- [1..((length n) `div` 2)]]
		r_reducible = r ++ [(ur, []) | ur <- unreach] ++ [(nonterminal, [up]) | nonterminal <- (take (length unprod) n\\unprod), up <- unprod]


testRedG :: Int -> Int -> Int -> Bool
testRedG terminals maxArity depth = eq grammar grammarR
	where	grammar = generateGrammar terminals maxArity depth
		grammarR = generateRRedundant grammar
		eq (s, n, f, r) (sr, nr, fr, rr) = (eq' n nr) && (eq' f fr) && (eq' r rr)




--------------------
-- alternative representation
--------------------


data Tree = FNode String [Tree] | QNode String [Tree] | Epsilon deriving (Show, Eq)


-- treeToTerm :: tree -> term
treeToTerm :: Tree -> [String]
treeToTerm Epsilon = []
treeToTerm (FNode s []) = [s]
treeToTerm (QNode s []) = [s]
treeToTerm (FNode s xs) = (s) : treeToTerm' xs	-- ++
	where	treeToTerm' xs
			| null xs = []
			| otherwise = treeToTerm (head xs) ++ treeToTerm' (tail xs)
treeToTerm (QNode s xs) = (s) : treeToTerm' xs	-- ++
	where	treeToTerm' xs
			| null xs = []
			| otherwise = treeToTerm (head xs) ++ treeToTerm' (tail xs)


-- termToTree :: term -> f -> arity -> tree
termToTree :: [String] -> [String] -> (String -> Int)-> Tree
termToTree [] _ _ = Epsilon
termToTree (symbol:term) f arity
	| symbol `elem` f = FNode symbol (treeList (symbol:term) arity)
	| otherwise = QNode symbol (treeList (symbol:term) arity)
	where	treeList tree arity
			| null tree = []
			| otherwise = [termToTree subterm f arity | subterm <- (filter (\x -> not (null x)) (branches tree (subtreeHeads tree arity)))]
		branches tree subtreeHeadList
			| null subtreeHeadList = []
			| (length subtreeHeadList) < 2 = [treeSection tree (head subtreeHeadList) (length tree)] 
			| otherwise = (treeSection tree (head subtreeHeadList) (head (tail subtreeHeadList))) : branches tree (tail subtreeHeadList)
		treeSection tree index1 index2
			| null tree = []
			| index1 == index2 = []
			| otherwise = (tree!!index1) : (treeSection tree (index1+1) index2)


termToTreeList :: [[String]] -> [String] -> (String -> Int) -> [Tree]
termToTreeList termList f arity
	| null termList = []
	| otherwise = (termToTree (head termList) f arity) : termToTreeList (tail termList) f arity



-- treeDelta :: tree -> dfta -> tree
treeDelta :: Tree -> DFTA -> (String -> Int) -> Tree
treeDelta tree (q, f, qf, deltaF) arity = termToTree (delta (treeToTerm tree) (q, f, qf, deltaF) arity) f arity

-- treeDeltaTree :: tree -> dfta -> tree
treeDeltaTree :: Tree -> DFTA -> (String -> Int) -> Tree
treeDeltaTree tree (q, f, qf, deltaF) arity = termToTree (deltaTree (treeToTerm tree) (q, f, qf, deltaF) arity) f arity

-- treeNondetDelta :: tree -> nfta -> [tree]
treeNondetDelta :: Tree -> NFTA -> (String -> Int) -> [Tree]
treeNondetDelta tree (q, f, qf, deltaF) arity = termToTreeList (nondetDelta (treeToTerm tree) (q, f, qf, deltaF) arity) f arity

-- treeNondetDelta :: tree -> nfta -> [tree]
treeNondetDeltaTree :: Tree -> NFTA -> (String -> Int) -> [Tree]
treeNondetDeltaTree tree (q, f, qf, deltaF) arity = termToTreeList (nondetDeltaTree (treeToTerm tree) (q, f, qf, deltaF) arity) f arity

-- treeProduction :: g -> depth -> arity -> [tree]
treeProduction :: G -> Int -> (String -> Int) -> [Tree]
treeProduction (s, n, f, r) depth arity = termToTreeList (production (s, n, f, r) depth) f arity




--------------------
-- Regular Tree Grammars
--------------------


-- apply one production rule
-- produce :: nonterminal -> production rule -> subtree
produce :: String -> (String, [String]) -> [String]
produce nonterminal prodRule 
	| nonterminal == (fst prodRule) = snd prodRule
	| otherwise = []


-- production rules
-- takes a grammar and a depth to which it applies production rules
-- production :: grammar -> depth of production -> termList
production :: G -> Int -> [[String]]
production (s, n, f, r) 0 = [[s]]
production (s, n, f, r) depth = production' (produceAll s r)
	where 	production' termList
			| null termList = []
			| otherwise =  repeat (depth-1) $ (produceSubTree (head termList) 0) ++ production' (tail termList)
		repeat depth termList
			| null termList = []
			| depth == 0 = termList
			| notDone (head termList) n = repeat (depth-1) $ (produceSubTree (head termList) 0) ++ repeat (depth) (tail termList)
			| notDoneList (tail termList) n = (head termList) : repeat (depth-1) (tail termList)	-- ++
			| otherwise = termList
		produceSubTree term index
			| null term = []
			| index >= (length term) = [term]
			| not ((term!!index) `elem` n) = produceSubTree term (index+1)
			| (term!!index) `elem` n = addPrev (prevTerm term index 0) (map (++ addRest term (index+1)) (produceAll (term!!index) r)) 0
			| otherwise = [term]
		addPrev term termList index
			| null term = termList
			| null termList = [term]
			| index >= (length termList) = []
			| otherwise = (term ++ (termList!!index)) : (addPrev term termList (index+1))
		prevTerm term index index2
			| null term = []
			| index <= index2 = []
			| otherwise = (term!!index2) : prevTerm term index (index2+1)
		addRest term index
			| null term = []
			| index >= (length term) = []
			| otherwise = (term!!index) : addRest term (index+1)
		produceAll f r = produceAll' f (filter (\x -> (fst x) == f) r)
		produceAll' f newR 
			| null newR = []
			| otherwise = (produce f (head newR)) : produceAll' f (tail newR)



-- auxiliary functions

-- clean production without unfinished terms
-- takes a grammar and a depth and applies production rules
-- then filters out all terms with non-terminals
-- productionClean :: grammar -> depth -> termList
productionClean :: G -> Int ->  [[String]]
productionClean (s, n, f, r) depth = filter (\x -> not (notDone x n)) (production (s, n, f, r) depth)

-- checks if all nonterminals have been eliminated
-- true if more production rules could be applied
-- notDone :: term -> non-terminals -> Bool
notDone :: [String] -> [String] -> Bool
notDone term n
	| null term = False
	| otherwise = (head term) `elem` n || notDone (tail term) n

notDoneList :: [[String]] -> [String] -> Bool
notDoneList termList n
	| null termList = False
	| otherwise = (notDone (head termList) n) || (notDoneList (tail termList) n)



-- reduction algorithm for regular tree grammars

-- reduction of grammars
-- takes a grammar and returns a reduced, but equivalent grammar
-- grammarRed :: grammar -> grammar
grammarRed :: G -> G
grammarRed (s, n, f, r) = (s, newN, f, newR)
	where	newN = filter (\x -> x `elem` reach n [s] 0) $ filter (\x -> prod x) n
		newR = filter (\x -> containsN' (snd x)) $ filter (\x -> containsN x) r
		prod nonterminal = prod' nonterminal r
		prod' nonterminal r
			| null r = False
			| otherwise = nonterminal == (fst (head r)) || prod' nonterminal (tail r)
		reach nonterminals reachables index
			| null nonterminals && index >= (length r) = reachables
			| null nonterminals = reach n reachables (index+1)	-- reach n reachables (index+1)?
			| otherwise = reach (tail nonterminals) (reach' (head nonterminals) r reachables) index
		reach' nonterminal r reachables		-- error?
			| null r = removeDuplicates reachables
			| ((nonterminal `elem` (snd (head r))) && ((fst (head r)) `elem` reachables)) = reach' nonterminal (tail r) $ removeDuplicates (reachables ++ [nonterminal])
			| otherwise = reach' nonterminal (tail r) reachables
		containsN prodRule = (fst prodRule) `elem` newN 
		containsN' product
			| null product = True
			| (head product) `elem` f = containsN' (tail product)
			| otherwise = (head product) `elem` newN && containsN' (tail product)




--------------------
-- Finite Tree Automata
--------------------


-- deterministic delta function
-- checks if the tree is equal to the left-hand side of a transition rule.
-- If yes, delta' applies transition rule
--
-- delta :: tree -> deltaRules -> arityFunction -> tree
delta :: [String] -> DFTA -> (String -> Int) -> [String]
delta tree (q, f, qf, deltaRules) arity
	| null tree = []
	| null deltaRules = tree
	| testEquals tree (fst (head deltaRules)) arity = delta' tree (head deltaRules) arity	
	| otherwise = delta tree (q, f, qf, (tail deltaRules)) arity
	where	delta' tree deltaRules arity
			| (arity (head tree)) == 0 = (snd deltaRules) ++ (tail tree) 						-- ["a"] 				-> [] ++ ["Qa", "a"]
			| (arity (head tree)) == 1 = ((snd deltaRules)!!0) : ((snd deltaRules)!!1) : (tail (tail tree)) 	-- ["g", "Qa", "a"] 			-> ["Qg"] ++ ["g"] ++ ["a"]
			| (arity (head tree)) >= 2 = ((snd deltaRules)!!0) : cutSubtreeHeads tree 0				-- ["f", "Qg" "g", "a", "Qg", "g", "a"]	-> ["Qf"] ++ ["f", "g", "a", "g", "a"]
		cutSubtreeHeads tree subtreeIndex -- removes all unwanted state-nodes
			| null tree = []
			| subtreeIndex >= (length (subtreeHeads tree arity)) = tree
			| otherwise = cutSubtreeHeads (cutString tree ((subtreeHeads tree arity)!!(subtreeIndex))) (subtreeIndex+1)


-- nondeterministic delta function
-- relies on deterministic delta
--
-- nondetDelta :: tree -> deltaRules arityFunction -> [tree]
nondetDelta :: [String] -> NFTA -> (String -> Int) -> [[String]]
nondetDelta tree (q, f, qf, deltaRules) arity
	| null tree = []
	| null deltaRules = []	-- not x as in deterministic delta
	| testEquals tree (fst (head deltaRules)) arity = nondetDelta tree (q, f, qf, (tail deltaRules)) arity ++ [delta tree (q, f, qf, deltaRules) arity] 	
	| otherwise = nondetDelta tree (q, f, qf, (tail deltaRules)) arity


-- deterministic case
-- returns the result of the reduction of a given tree with the rules of a given DFTA
-- deltaTree :: tree -> DFTA -> arityFunction -> tree
deltaTree :: [String] -> DFTA -> (String -> Int) -> [String]
deltaTree tree (q, f, qf, deltaF) arity = deltaTree' tree (q, f, qf, deltaF) arity 0
	where	deltaTree' tree (q, f, qf, deltaF) arity ar
			| null tree = tree
			| ar > maximum (arityList tree arity) = tree
			| ar <= maximum (arityList tree arity) = deltaTree' (deltaTreeArity tree (q, f, qf, deltaF) arity ar) (q, f, qf, deltaF) arity (ar+1)
		deltaTreeArity tree (q, f, qf, deltaF) arity ar
			| null tree = tree
			| (head tree) `elem` q = (head tree) : deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar
			| arity (head tree) < ar = (head tree) : (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)
			| (arity (head tree) == ar) && (ar == 0) = (delta [head tree] (q, f, qf, deltaF) arity) ++ (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)
			| (arity (head tree) == ar) && (ar > 0) = delta ((head tree) : (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)) (q, f, qf, deltaF) arity
			| arity (head tree) > ar = [head tree] ++ (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)


-- nondeterministic case
-- returns the result of the reduction of a given tree with the rules of a given NFTA
-- nondetDeltaTree :: tree -> NFTA -> arityFunction -> [tree]
nondetDeltaTree :: [String] -> NFTA -> (String -> Int) -> [[String]]
nondetDeltaTree [] _ _ = []
nondetDeltaTree tree (q, f, qf, deltaF) arity = nondetDeltaTree' [tree] 0
	where	nondetDeltaTree' treeList ar
			| ar > maximum (arityList tree arityF) = removeDuplicates treeList
			| otherwise = nondetDeltaTree' (filterEqLen (nondetDeltaTree'' treeList ar)) (ar+1)
		nondetDeltaTree'' treeList ar
			| null treeList = []
			| otherwise = nondetDeltaTreeArity (head treeList) ar ++ nondetDeltaTree'' (tail treeList) ar
		nondetDeltaTreeArity tree ar
			| null tree = []
			| (head tree) `elem` q = concatList [head tree] (nondetDeltaTreeArity (tail tree) ar)
			| arity (head tree) < ar = concatList [head tree] (nondetDeltaTreeArity (tail tree) ar)
			| arity (head tree) > ar = concatList [head tree] (nondetDeltaTreeArity (tail tree) ar)
			| arity (head tree) == ar = concatAll (nondetDelta (pseudoHead tree) (q, f, qf, deltaF) arity) (nondetDeltaTreeArity (pseudoTail tree) ar)
			| otherwise = []
		concatAll xs ys
			| null xs = []
			| null ys = xs
			| otherwise = [x ++ y | x <- xs, y <- ys]
		concatList x ys
			| null ys = [x]
			| otherwise = [x ++ y | y <- ys]
		pseudoHead tree
			| null tree = []
			| arity (head tree) == 0 = [head tree]
			| arity (head tree) == 1 = [head tree] ++ pseudoHead (tail tree)
			| (startPos tree) <= length tree = [tree!!x | x <- [0..((startPos tree)-1)]]
			| otherwise = tree
		pseudoTail tree
			| null tree = []
			| arity (head tree) == 0 = tail tree
			| arity (head tree) == 1 = pseudoTail (tail tree)
			| (startPos tree) < length tree = [tree!!x | x <- [(startPos tree)..((length tree)-1)]]
			| otherwise = []	
		startPos tree 
			| null tree = 0
			| arity (head tree) == 0 = 1
			| (last (subtreeHeads tree arity)) < (length tree) = (last (subtreeHeads tree arity)) + startPos [tree!!x | x <- [(last (subtreeHeads tree arity))..((length tree)-1)], x >= (last (subtreeHeads tree arity))]
			| otherwise = length tree
		filterEqLen xs = filter (\x -> (length x) == maximum (map length xs)) xs



-- auxiliary functions

-- to determine whether there is a transition rule for a given (sub)tree
-- testEquals :: tree -> transitionRule -> index -> arityFunction -> Bool
testEquals :: [String] -> [String] -> (String -> Int) -> Bool
testEquals tree deltaElem arity = testEquals' tree deltaElem arity 0
	where testEquals' tree deltaElem arity index
		| null tree = True
		| null deltaElem = True
		| (arity (head tree)) == (index-1) = True
		| index == 0 && index < length tree && index < length deltaElem = tree!!index == deltaElem!!index && testEquals' tree deltaElem arity (index+1)					-- compare first element
		| index == 1 && index < length tree && index < length deltaElem = tree!!index == deltaElem!!index && testEquals' tree deltaElem arity (index+1)					-- compare second element
		| index < length tree && index < length deltaElem = (tree!!((subtreeHeads tree arity)!!(index-1)) == deltaElem!!(index+(index-1))) && testEquals' tree deltaElem arity (index+1)	-- compare subtree heads, not entire list
		| otherwise = False


-- returns a tree with the element at position index removed
-- used for delta
-- cutString :: tree -> index -> tree
cutString:: [String] -> Int -> [String]
cutString [] _ = []
cutString tree index
	| index == 0 = tail tree
	| otherwise = (head tree) : cutString (tail tree) (index-1)


-- returns a list of indices of the heads of the subtrees of the input tree
-- uses arity function to keep track of the depth of the tree
-- subtreeHeads :: tree - arityFunction -> tree
subtreeHeads :: [String] -> (String -> Int) -> [Int]
subtreeHeads tree arity = subtreeHeads' tree 0 arity
	where 	subtreeHeads' tree elemIndex arity	-- elemIndex = index of subtreeHeads
			| tree == [] = []
			| arity (head tree) == 0 = []
			| arity (head tree) >= 1 = subtreeFind (tail tree) (elemIndex+1) arity 0 ((arity (head tree)))
		subtreeFind tree elemIndex arity ar subtreeNum	-- ar is used to keep track of the depth; increased if arity(head) >=1, decreased if arity(head) <= 0
			| tree == [] = []
			| subtreeNum == 0 = []
			| ar == 0 = (elemIndex) : subtreeFind (tail tree) (elemIndex+1) arity (arity(head tree)) (subtreeNum-1)
			| arity (head tree) == 0 = subtreeFind (tail tree) (elemIndex+1) arity (ar-1) subtreeNum
			| arity (head tree) >= 1 = subtreeFind (tail tree) (elemIndex+1) arity (ar + arity (head tree)-1) subtreeNum


-- returns a tree in similar form to the input tree, with the arity of each element instead of the elements themselves
-- arityList :: tree -> arityFunction -> [arity]
arityList :: [String] -> (String -> Int) -> [Int]
arityList [] _ = []
arityList tree arity = (arity (head tree)) : arityList (tail tree) arity


cleanup :: (Eq a) => [[a]] -> [[a]] -> [[a]]
cleanup list output
	| null list = output
	| null (head list) = cleanup (tail list) output
	| (head list) `elem` output = cleanup (tail list) output
	| otherwise = cleanup (tail list) (output ++ [head list])


-- to determine if NFTA accepts a tree
-- applies nondetDeltaTree and checks if head is in qf
-- isAccepted :: tree -> NFTA -> arityFunction -> Bool
isAccepted :: [String] -> NFTA -> (String -> Int) -> Bool
isAccepted tree (q, f, qf, deltaF) arity = isAccepted' (nondetDeltaTree tree (q, f, qf, deltaF) arity) qf
	where isAccepted' deltaTreeList qf
		| null deltaTreeList = False
		| head (head deltaTreeList) `elem` qf = True
		| otherwise = isAccepted' (tail deltaTreeList) qf


-- removes duplicates from a list
-- used for simplifying marked in the reduction algorithm red
-- removeDuplicates :: list -> list
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates [] = []
removeDuplicates (x:xs)
	| x `elem` xs = removeDuplicates xs
	| otherwise = (x) : removeDuplicates xs



-- reduction algorithm for tree automata

-- reduction algorithm for NFTAs
-- red :: NFTA -> arity -> NFTA
red :: NFTA -> (String -> Int) -> NFTA
red (q, f, qf, deltaRules) arity = (qr, f, qr `intersect` qf, deltaR)
	where 	qr = removeDuplicates $ reduceNFTA (q, f, qf, deltaRules) arity [] 0 f deltaRules
		deltaR = [transitionRules | transitionRules <- deltaRules, isInMarked transitionRules qr]
		reduceNFTA (q, f, qf, deltaRules) arity marked arityIndex editedF editedDelta
			| null f = []
			| editedF == [] = marked
			| arity (head editedF) == 0 = reduceNFTA (q, f, qf, deltaRules) arity (removeDuplicates (marked ++ [head (snd state) | state <- deltaRules, (head editedF) == (head (fst state))])) arityIndex (tail editedF) (editedDelta\\(containsMarked marked editedDelta))
			| arity (head editedF) >= 1 = reduceNFTA (q, f, qf, deltaRules) arity (removeDuplicates (marked ++ addToMarked (head editedF) arity marked deltaRules)) arityIndex (tail editedF) (editedDelta\\(containsMarked marked editedDelta))
			| otherwise = marked
		containsMarked marked editedDelta
			| null editedDelta = []
			| null marked = []
			| head (snd (head editedDelta)) `elem` marked = (head editedDelta) : containsMarked marked (tail editedDelta)
			| otherwise = containsMarked marked (tail editedDelta)
		addToMarked f' arity marked (deltaRule:deltaRules)
			| null deltaRules = []
			| isInMarked deltaRule marked = (head (snd deltaRule)) : addToMarked f' arity marked (deltaRules\\(containsMarked marked deltaRules))
			| otherwise = addToMarked f' arity marked deltaRules
		isInMarked deltaRule marked
			| null marked = False
			| arity (head (fst deltaRule)) == 0 = True
			| otherwise = (not (null (stateList deltaRule))) && (null $ (stateList deltaRule)\\marked)
		stateList deltaRule = [state | state <- (fst deltaRule), state `elem` q]



-- determinisation algorithm for tree automata

-- determinisation algorithm for NFTAs
-- takes an NFTA and arity function as input and returns a DFTA
-- det :: NFTA -> arityFunction -> DFTA
det :: NFTA -> (String -> Int) -> (DFTA, [(String, [String])])
det (q, f, qf, deltaRules) arity = (([newState | (newState, _) <- renamedStates], f, qdf, deltaRulesD), renamedStates)
	where	qd = [s | s <- existsDeltaRule f]
		renamedStates = renameStates qd
		qdf = [rename stateList renamedStates | stateList <- qd, stateList `intersect` qf /= []]
		deltaRulesD = removeDuplicates [((symbol) : [rename newState renamedStates | newState <- state], [rename s renamedStates]) | symbol <- f, (state, s) <- existsTransition [deltaElem | deltaElem <- deltaRules, symbol `elem` (fst deltaElem)] 0]
		existsDeltaRule f
			| null f = []
			| otherwise = cleanup2 $ (existsDeltaRule' [deltaElem | deltaElem <- deltaRules, (head f) `elem` (fst deltaElem)]) ++ existsDeltaRule (tail f)
		existsDeltaRule' deltaList  = [fstStates deltaList] ++ [sndStates deltaList]
		fstStates deltaList
			| null deltaList = []
			| otherwise = removeDuplicates $ [state | state <- q, state `elem` (fst (head deltaList))] ++ fstStates (tail deltaList)
		sndStates deltaList
			| null deltaList = []
			| otherwise = removeDuplicates $ [state | state <- q, state `elem` (snd (head deltaList))] ++ sndStates (tail deltaList)
		existsTransition deltaList1 index
			| index > (arity (head (fst (head deltaList1)))) = [([[show index]], [])]	--useless?
			| arity (head (fst (head deltaList1))) == 0 = [([], (head [(snd state) | state <- (head (groupTransitions deltaList1 deltaList1 index))]))]
			| arity (head (fst (head deltaList1))) == 1 = [statePair | statePair <- (statePairs (groupTransitions deltaList1 deltaList1 index)), (snd statePair) `elem` qd] ++ existsTransition deltaList1 (index+1)
			| arity (head (fst (head deltaList1))) >= 2 = [stateGroup | stateGroup <- (stateGroups (groupTransitions deltaList1 deltaList1 index)), (snd stateGroup) `elem` qd] ++ existsTransition deltaList1 (index+1)
			| otherwise = []
		groupTransitions deltaList1 deltaList2 index
			| index == 0 = [deltaList1]
			| null deltaList2 = []
			| otherwise = removeDuplicates $ [[deltaElem | deltaElem <- deltaList1, equalSubtreeHead deltaElem (head deltaList2) index 0]] ++ groupTransitions deltaList1 (tail deltaList2) index
		equalSubtreeHead deltaElem deltaListElem index counter
			| counter == index = True
			| counter == length (subtreeHeads (fst deltaElem) arity) || counter == length (subtreeHeads (fst deltaListElem)  arity) = True
			| otherwise = (fst deltaElem)!!((subtreeHeads (fst deltaElem) arity)!!counter) == (fst deltaListElem)!!((subtreeHeads (fst deltaListElem) arity)!!counter) && equalSubtreeHead deltaElem deltaListElem index (counter+1)
		statePairs deltaListList 
			| null deltaListList = []
			| otherwise = statePairs' deltaListList qd
		statePairs' deltaListList qd
			| null qd = []
			| otherwise = statePairs'' deltaListList (head qd) ++ statePairs' deltaListList (tail qd)
		statePairs'' deltaListList state
			| null deltaListList = []
			| otherwise = [([state], (removeDuplicates (statePairs''' deltaListList state)))]	-- ?
		statePairs''' deltaListList state
			| null deltaListList = []
			| otherwise = [states | states <- q, deltaElem <- (head deltaListList), states `elem` (snd deltaElem), isInDelta state deltaElem] ++ statePairs''' (tail deltaListList) state
		isInDelta state deltaElem
			| null state = False
			| otherwise = (head state) `elem` (fst deltaElem) || isInDelta (tail state) deltaElem
		stateGroups deltaListList 
			| null deltaListList = []
			| otherwise = stateGroups' deltaListList (stateList qd (arity (head (fst (head (head deltaListList))))))
		stateList qd ar = perm (filter (\x -> (length x) == ar) (powerSet qd)) ++ sameStates qd ar
		sameStates qd ar
			| null qd = []
			| otherwise = (sameStates' (head qd) ar) : sameStates (tail qd) ar
		sameStates' state 0 = []
		sameStates' state ar = (state) : sameStates' state (ar-1)
		perm stateLists
			| null stateLists = []
			| otherwise = (permutations (head stateLists)) ++ perm (tail stateLists)
		stateGroups' deltaListList qds
			| null qds = []
			| otherwise = stateGroups'' deltaListList (head qds) ++ stateGroups' deltaListList (tail qds)
		stateGroups'' deltaListList states
			| null deltaListList = []
			| otherwise = [(states, (removeDuplicates (stateGroups''' deltaListList states)))]
		stateGroups''' deltaListList qds
			| null deltaListList = []
			| otherwise = [s | s <- q, deltaElem <- (head deltaListList), s `elem` (snd deltaElem), isInDelta2 qds deltaElem] ++ stateGroups''' (tail deltaListList) qds
		isInDelta2 states deltaElem
			| null states = True
			| otherwise = isInDelta (head states) deltaElem && isInDelta2 (tail states) deltaElem



-- auxiliary functions

-- calculates the power set of a given list
powerSet :: [a] -> [[a]]
powerSet [] = [[]]
powerSet (x:xs) = [x:ps | ps <- powerSet xs] ++ powerSet xs


cleanup2 :: Eq a => [[a]] -> [[a]]
cleanup2 [] = []
cleanup2 xs = removeDuplicates $ cleanup2' xs
	where cleanup2' (x:xs)
		| null x = cleanup2 xs
		| otherwise = x : (cleanup2 xs)


-- renames states for determinisation
-- new statenames are of the form Qx with x an Int
-- renameStates :: stateList -> [(state, stateList)]
renameStates :: [[String]] -> [(String, [String])]
renameStates [] = []
renameStates qd = renameStates' qd 0
	where renameStates' qd index
		| null qd = []
		| otherwise = (("Q" ++ (show index), (head qd))) : renameStates' (tail qd) (index+1)


-- lookup function for renamed states
-- unlike lookup without Maybe
-- rename :: stateList -> [(state, stateList)] -> state
rename :: [String] -> [(String, [String])] -> String
rename [] _ = []
rename x [] = head x
rename state (x:xs)
	| head state `elem` (snd x) = fst x
	| otherwise = rename state xs





