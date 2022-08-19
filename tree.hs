import Data.List


-- example NFTA (taken from book)

-- syntactic sugar
type NFTA = ([String], [String], [String], [([String], [String])])	-- (Q, F, Qf, delta)
type DFTA a = ([a], [String], [a], [([String], [String])])	-- polymorphism necessary because of determinisation algorithm (sets of states instead of states). TODO: see if this can be simplified
type RankedAlphabet = ([String], String -> Int)


-- example automata (mostly similar to example 1.1.1 (p. 20) from book)
f :: [String]
q :: [String]
f = ["g", "f", "a"] -- list of symbols
q = ["Qa", "Qg", "Qf", "Qd"] -- list of states
q' = []
qf =["Qf"] --final states

-- arity function for f
arityF :: String -> Int
arityF "f" = 2
arityF "g" = 1
arityF "a" = 0
arityF _ = -1

-- list of transition rules
deltaF1 :: [([String], [String])]
deltaF1 = [(["a"], ["Qa", "a"]), (["g", "Qa", "x"], ["Qg", "g", "x"]), (["g", "Qg", "x"], ["Qg", "g", "x"]), (["f", "Qg", "x", "Qg", "y"], ["Qf", "f", "x", "y"])] -- example 1.1.1
deltaF2 = [(["a"], ["Qa", "a"]), (["a"], ["Qg", "a"]), (["g", "Qg", ""], ["Qg", "a", ""]), (["g", "Qa", "x"], ["Qg", "a", "x"]), (["g", "Qg", "x"], ["Qg", "g", "x"]), (["f", "Qg", "x", "Qg", "y"], ["Qf", "f", "x", "y"])] -- example 1.1.1 + additional transitions to test nondetDeltaTree

nftaTest = (q, f, qf, deltaF2)
dftaTest = (q, f, qf, deltaF1)

f_det = f
q_det = ["Q", "Qg","Qf"]
qf_det = ["Qf"]
delta_det = [(["a"], ["Q"]), (["g", "Q"], ["Q"]), (["g", "Q"], ["Qg"]), (["g", "Qg"], ["Qf"]), (["f", "Q", "Q"], ["Q"])]

nftaDet = (q_det, f_det, qf_det, delta_det)




-- regular tree grammars

type G = (String, [String], [String], [(String, [String])])	-- (S, N, F, R)

-- example (propositional logic)
s = "Prop"
n = ["Prop", "Rel"]
n2 = ["Prop", "Rel", "Rel2"]
grammar_f = ["true", "false", "not", "and", "or"]
prodRules = [("Prop", ["true"]), ("Prop", ["false"]), ("Prop", ["Rel"]), ("Rel", ["not", "Prop"]), ("Rel", ["and", "Prop", "Prop"]), ("Rel", ["or", "Prop", "Prop"])]
prodRules2 = [("Prop", ["true"]), ("Prop", ["false"]), ("Prop", ["Rel"]), ("Rel", ["not", "true"]), ("Rel", ["not", "false"]), ("Rel", ["and", "true", "Rel2"]), ("Rel2", ["not", "true"]), ("Rel2", ["not", "false"])]

gTest = (s, n, grammar_f, prodRules)
gTest2 = (s, n2, grammar_f, prodRules2)




-- apply one production rule
-- produce :: nonterminal -> production rule -> subtree
produce :: String -> (String, [String]) -> [String]
produce nonterminal prodRule 
	| nonterminal == (fst prodRule) = snd prodRule
	| otherwise = []


-- checks if all nonterminals have been eliminated
-- true if more production rules could be applied
-- notDone :: term -> non-terminals -> Bool
notDone :: [String] -> [String] -> Bool
notDone term n
	| null term = False
	| otherwise = (head term) `elem` n || notDone (tail term) n


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
			| notDoneYet (tail termList) = [head termList] ++ repeat (depth-1) (tail termList)
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
			| otherwise = [term ++ (termList!!index)] ++ (addPrev term termList (index+1))
		prevTerm term index index2
			| null term = []
			| index <= index2 = []
			| otherwise = [term!!index2] ++ prevTerm term index (index2+1)
		addRest term index
			| null term = []
			| index >= (length term) = []
			| otherwise = [term!!index] ++ addRest term (index+1)
		notDoneYet termList 
			| null termList = False
			| otherwise = notDone (head termList) n || notDoneYet (tail termList)
		produceAll f r = produceAll' f (filter (\x -> (fst x) == f) r)
		produceAll' f newR 
			| null newR = []
			| otherwise = [produce f (head newR)] ++ produceAll' f (tail newR)


-- clean production without unfinished terms
-- takes a grammar and a depth and applies production rules
-- then filters out all terms with non-terminals
-- productionClean :: grammar -> depth -> termList
productionClean :: G -> Int ->  [[String]]
productionClean (s, n, f, r) depth = filter (\x -> not (notDone x n)) (production (s, n, f, r) depth)



-- reduction of grammars
-- takes a grammar and returns a reduced, but equivalent grammar
-- grammarRed :: G -> G
grammarRed :: G -> G
grammarRed (s, n, f, r) = (s, newN, f, newR)
	where	newN = filter (\x -> x `elem` reach n [s] 0) $ filter (\x -> prod x) n
		newR = filter (\x -> containsN x) r
		prod nonterminal = prod' nonterminal r
		prod' nonterminal r
			| null r = False
			| otherwise = nonterminal == (fst (head r)) || prod' nonterminal (tail r)
		reach nonterminals reachables index	-- should work (probably (i hope))
			| null nonterminals && index >= (length n) = reachables
			| null nonterminals && not (index >= (length n)) = reach nonterminals reachables (index+1)
			| otherwise = reach (tail nonterminals) (reach' (head nonterminals) reachables 0) index
		reach' nonterminal reachables index	-- maybe one unnecessary loop through n
			| index >= (length n) = reachables
			| otherwise = reach' nonterminal (reach'' nonterminal r reachables) (index+1)
		reach'' nonterminal r reachables
			| null r = removeDuplicates reachables
			| (nonterminal `elem` (snd (head r)) && (fst (head r)) `elem` reachables) = reach'' nonterminal (tail r) $ removeDuplicates (reachables ++ [nonterminal])
			| otherwise = reach'' nonterminal (tail r) reachables
		containsN prodRule = ((fst prodRule) `elem` newN || (fst prodRule) `elem` f) && (containsN' (snd prodRule))
		containsN' product
			| null product = True
			| (head product) `elem` f = containsN' (tail product)
			| otherwise = (head product) `elem` newN && containsN' (tail product)






-- deterministic delta function
-- checks if the tree is equal to the left-hand side of a transition rule.
-- If yes, delta' applies transition rule
--
-- delta :: tree -> deltaRules -> arityFunction -> tree
-- TODO: take DFTA as input, instead of NFTA?
delta :: [String] -> NFTA -> (String -> Int) -> [String]
delta [] _ _ = []
delta tree (q, f, qf, deltaRules) arity
	| tree == [] = []
	| deltaRules == [] = tree
	| (head tree) `elem` q = delta tree (f, q, qf, (tail deltaRules)) arity --probably not necessary
	| (arity (head tree)) == 0 && testEquals tree (fst (head deltaRules)) 0 arity = delta' tree (head deltaRules) arity
	| testEquals tree (fst (head deltaRules)) 0 arity = delta' tree (head deltaRules) arity	
	| otherwise = delta tree (q, f, qf, (tail deltaRules)) arity
	where	delta' tree deltaRules arity
			| (arity (head tree)) == 0 = (snd deltaRules) ++ (tail tree) 							-- ["a"] 				-> [] ++ ["Qa", "a"]
			| (arity (head tree)) == 1 = [head (snd deltaRules)] ++ [head (tail (snd deltaRules))] ++ (tail (tail tree)) 	-- ["g", "Qa", "a"] 			-> ["Qg"] ++ ["g"] ++ ["a"]
			| (arity (head tree)) >= 2 = [head (snd deltaRules)] ++ cutSubtreeHeads tree 0					-- ["f", "Qg" "g", "a", "Qg", "g", "a"]	-> ["Qf"] ++ ["f", "g", "a", "g", "a"]
		cutSubtreeHeads tree subtreeIndex -- removes all unwanted state-nodes
			| tree == [] = []
			| subtreeIndex >= (length (subtreeHeads tree arity)) = tree
			| otherwise = cutSubtreeHeads (cutString tree ((subtreeHeads tree arity)!!(subtreeIndex))) (subtreeIndex+1)



-- to determine whether there is a transition rule for a given (sub)tree
-- testEquals :: tree -> trabsitionRule -> index -> arityFunction -> Bool
testEquals :: [String] -> [String] -> Int -> (String -> Int) -> Bool
testEquals tree deltaElem index arity
	| tree == [] = True
	| deltaElem == [] = True
	| (arity (head tree)) == (index-1) = True
	| index == 0 && index < length tree && index < length deltaElem = tree!!index == deltaElem!!index && testEquals tree deltaElem (index+1) arity					-- compare first element
	| index == 1 && index < length tree && index < length deltaElem = tree!!index == deltaElem!!index && testEquals tree deltaElem (index+1) arity					-- compare second element
	| index < length tree && index < length deltaElem = (tree!!((subtreeHeads tree arity)!!(index-1)) == deltaElem!!(index+(index-1))) && testEquals tree deltaElem (index+1) arity	-- compare subtree heads, not entire list
	| otherwise = False



-- nondeterministic delta function
-- relies on deterministic delta
--
-- nondetDelta :: tree -> deltaRules arityFunction -> [tree]
-- TODO: deterministic delta rules?
nondetDelta :: [String] -> NFTA -> (String -> Int) -> [[String]]
nondetDelta [] _ _ = []
nondetDelta tree (q, f, qf, deltaRules) arity
	| tree == [] = []
	| deltaRules == [] = []	-- not x as in deterministic delta
	| (arity (head tree)) == 0 && testEquals tree (fst (head deltaRules)) 0 arity = nondetDelta tree (q, f, qf, (tail deltaRules)) arity ++ [delta tree (q, f, qf, deltaRules) arity]	-- if transition rule is found, add reduced tree to the list and continue searching for transition rules
	| testEquals tree (fst (head deltaRules)) 0 arity = nondetDelta tree (q, f, qf, (tail deltaRules)) arity ++ [delta tree (q, f, qf, deltaRules) arity] 	
	| otherwise = nondetDelta tree (q, f, qf, (tail deltaRules)) arity



-- returns a tree with the element at position index removed
-- used for delta
-- cutString :: tree -> index -> tree
cutString:: [String] -> Int -> [String]
cutString [] _ = []
cutString tree index
	| index == 0 = tail tree
	| otherwise = [head tree] ++ cutString (tail tree) (index-1)



-- returns a list of indices of the heads of the subtrees of the input tree
-- uses arity function to keep track of the depth of the tree
-- subtreeHeads :: tree - arityFunction -> tree
subtreeHeads :: [String] -> (String -> Int) -> [Int]
subtreeHeads tree arity = subtreeHeads' tree 0 arity
	where 	subtreeHeads' tree elemIndex arity	-- elemIndex = index of subtreeHeads
			| tree == [] = []
			| arity (head tree) == 0 = []
			| arity (head tree) >= 1 = [elemIndex+1] ++ subtreeFind (tail tree) (elemIndex+1) arity ((arity (head tree))-1)
			| otherwise = [elemIndex+1] ++ subtreeFind (tail tree) (elemIndex+1) arity ((arity (head tree))-1)
		subtreeFind tree elemIndex arity ar	-- ar is used to keep track of the depth; increased if arity(head) >=1, decreased if arity(head) <= 0
			| tree == [] = []
			| ar == 0 = [elemIndex] ++ subtreeFind (tail tree) (elemIndex+1) arity (arity (head tree))
			| (head tree) `elem` q = subtreeFind (tail tree) (elemIndex+1) arity (ar) 
			| not ((head tree) `elem` q) && not ((head tree) `elem` f) = subtreeFind (tail tree) (elemIndex+1) arity (ar-1)
			| arity (head tree) == 0 = subtreeFind (tail tree) (elemIndex+1) arity (ar-1)
			| arity (head tree) >= 1 = subtreeFind (tail tree) (elemIndex+1) arity (ar + arity (head tree) - 1)



-- returns a tree in similar form to the input tree, with the arity of each element instead of the elements themselves
-- arityList :: tree -> arityFunction -> [arity]
arityList :: [String] -> (String -> Int) -> [Int]
arityList [] _ = []
arityList tree arity = [arity (head tree)] ++ arityList (tail tree) arity



-- deterministic case
-- returns the result of the reduction of a given tree with the rules of a given DFTA
-- deltaTree :: tree -> deltaRules -> arityFunction -> tree
deltaTree :: [String] -> DFTA String -> (String -> Int) -> [String]
deltaTree tree (q, f, qf, deltaF) arity = deltaTree' tree (q, f, qf, deltaF) arity 0
	where	deltaTree' tree (q, f, qf, deltaF) arity ar
			| ar > maximum (arityList tree arity) = tree
			| ar <= maximum (arityList tree arity) = deltaTree' (deltaTreeArity tree (q, f, qf, deltaF) arity ar) (q, f, qf, deltaF) arity (ar+1)
		deltaTreeArity tree (q, f, qf, deltaF) arity ar
			| tree == [] = tree
			| (head tree) `elem` q = [head tree] ++ deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar
			| arity (head tree) < ar = [head tree] ++ (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)
			| (arity (head tree) == ar) && (ar == 0) = (delta [head tree] (q, f, qf, deltaF) arity) ++ (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)
			| (arity (head tree) == ar) && (ar > 0) = delta ([head tree] ++ (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)) (q, f, qf, deltaF) arity
			| arity (head tree) > ar = [head tree] ++ (deltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar)



-- nondeterministic case
-- returns the result of all possible reductions of a given tree with the rules of a given NFTA
-- nondetDeltaTree :: tree -> deltaRules -> arity -> [tree]
nondetDeltaTree :: [String] -> NFTA -> (String -> Int) -> [[String]]	--f and q are implicit
nondetDeltaTree tree (q, f, qf, deltaF) arity = cleanup (nondetDeltaTree' [] tree (q, f, qf, deltaF) arity 0) [] 0 --nondetDeltaTree' [] tree deltaF 0
	where	cleanup list output index	-- for preventing [["Qa","a"],[],[],[],[]]
			| index == length (list)-1 = output
			| head (list) == [] = cleanup (tail list) output (index+1)
			| head (list) `elem` output = cleanup (tail list) output (index+1)
			| otherwise = cleanup (tail list) (output ++ [(head list)]) (index+1)
		nondetDeltaTree' newTree tree (q, f, qf, deltaF) arity index1
			| index1 > length deltaF = newTree
			| otherwise = nondetDeltaTree' (newTree ++ (nondetDeltaTree'' newTree tree (q, f, qf, deltaF) arity index1 0)) tree (q, f, qf, deltaF) arity (index1+1)
		nondetDeltaTree'' newTree tree (q, f, qf, deltaF) arity index1 index2
			| index2 > length deltaF = newTree
			| otherwise = nondetDeltaTree'' (newTree ++ [(nondetDeltaTree''' tree (q, f, qf, deltaF) arity index1 index2 0)]) tree (q, f, qf, deltaF) arity index1 (index2+1)
		nondetDeltaTree''' tree (q, f, qf, deltaF) arity index1 index2 ar
			| tree == [] = []
			| ar > maximum (arityList tree arity) = tree
			| ar <= maximum (arityList tree arity) = nondetDeltaTree''' (nondetDeltaTreeArity tree (q, f, qf, deltaF) arity ar index1 index2) (q, f, qf, deltaF) arity index1 index2 (ar+1)
		nondetDeltaTreeArity tree (q, f, qf, deltaF) arity ar index1 index2
			| tree == [] = tree
			| (head tree) `elem` q = [head tree] ++ nondetDeltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar index1 index2
			| arity (head tree) < ar = [head tree] ++ nondetDeltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar index1 index2
			| arity (head tree) == ar && ar == 0 && index1 < (length (nondetDelta tree (q, f, qf, deltaF) arity)) && ar <= index2 = (nondetDelta [head tree] (q, f, qf, deltaF) arity)!!index1 ++ nondetDeltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar index1 index2
			| arity (head tree) == ar && ar == 0 && index2 < (length (nondetDelta tree (q, f, qf, deltaF) arity)) && ar > index2 && index1 /= index2 = (nondetDelta [head tree] (q, f, qf, deltaF) arity)!!index2 ++ nondetDeltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar index1 index2
			| arity (head tree) == ar && ar > 0 && index1 < (length (nondetDelta tree (q, f, qf, deltaF) arity)) && ar <= index2 = (nondetDelta ([head tree] ++ (nondetDeltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar index1 index2)) (q, f, qf, deltaF) arity)!!index1
			| arity (head tree) == ar && ar > 0 && index2 < (length (nondetDelta tree (q, f, qf, deltaF) arity)) && ar > index2 && index1 /= index2 = (nondetDelta ([head tree] ++ (nondetDeltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar index1 index2)) (q, f, qf, deltaF) arity)!!index2
			| arity (head tree) > ar = [head tree] ++ nondetDeltaTreeArity (tail tree) (q, f, qf, deltaF) arity ar index1 index2
			| arity (head tree) == ar && ar == 0 && index1 >= (length (nondetDelta tree (q, f, qf, deltaF) arity)) = []
			| arity (head tree) == ar && ar > 0 && index1 >= (length (nondetDelta tree (q, f, qf, deltaF) arity)) = []
			| otherwise = []



-- to determine if NFTA accepts a tree
-- applies nondetDeltaTree and checks if head is in qf
-- isAccepted :: tree -> NFTA -> arityFunction -> Bool
isAccepted :: [String] -> NFTA -> (String -> Int) -> Bool
isAccepted tree (q, f, qf, deltaF) arity = isAccepted' (nondetDeltaTree tree (q, f, qf, deltaF) arity) qf
	where isAccepted' deltaTreeList qf
		| deltaTreeList == [] = False
		| head (head deltaTreeList) `elem` qf = True
		| otherwise = isAccepted' (tail deltaTreeList) qf



-- removes duplicates from a list
-- used for simplifying marked in the reduction algorithm red
-- removeDuplicates :: list -> list
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates [] = []
removeDuplicates (x:xs)
	| x `elem` xs = removeDuplicates xs
	| otherwise = [x] ++ removeDuplicates xs



-- reduction algorithm for NFTAs
-- may or may not workhaskell list minus
-- red :: NFTA -> arityFunction -> NFTA
red :: NFTA -> (String -> Int) -> NFTA
red (q, f, qf, deltaRules) arity = (qr, f, qr `intersect` qf, deltaR)
	where 	qr = removeDuplicates $ reduceNFTA (q, f, qf, deltaRules) arity [] (0) f
		deltaR = [transitionRules | transitionRules <- deltaRules, isInMarked [state | state <- (tail (fst (head deltaRules))), state `elem` q] qr]
		reduceNFTA (q, f, qf, deltaRules) arity marked arityIndex editedF
			| editedF == [] && (arityIndex > (maximum (arityList f arity))) = marked
			| editedF == [] && (arityIndex <= (maximum (arityList f arity))) = reduceNFTA (q, f, qf, deltaRules) arity marked (arityIndex + 1) f
			| arity (head editedF) == 0 = reduceNFTA (q, f, qf, deltaRules) arity  (marked ++ [state | (state:tail) <- nondetDelta [(head editedF)] (q, f, qf, deltaRules) arity]) arityIndex (tail editedF)
			| arity (head editedF) >= 1 = reduceNFTA (q, f, qf, deltaRules) arity (marked ++ addToMarked (head editedF) arity marked deltaRules) arityIndex (tail editedF)	
			| otherwise = marked --reduceNFTA (q, f, qf, deltaRules) arity (--TODO) arityIndex (tail f')
		addToMarked f' arity marked deltaRules
			| marked == [] = []
			| deltaRules == [] = marked
			| isInMarked [state | state <- (tail (fst (head deltaRules))), state `elem` q] marked = addToMarked f' arity ([head (snd (head deltaRules))] ++ marked) (tail deltaRules) -- where error starts
			| otherwise = [] -- ??
		isInMarked states marked
			| states == [] = True
			| marked == [] = False
			| otherwise = (head states) `elem` marked && isInMarked (tail states) marked



-- calculates the power set of a given list
powerSet :: [a] -> [[a]]
powerSet [] = [[]]
powerSet (x:xs) = [x:ps | ps <- powerSet xs] ++ powerSet xs


cleanup :: Eq a => [[a]] -> [[a]]
cleanup [] = []
cleanup xs = removeDuplicates $ cleanup' xs
	where cleanup' (x:xs)
		| null x = cleanup xs
		| otherwise = x:(cleanup xs)



-- determinisation algorithm for NFTAs
-- takes an NFTA and arity function as input and returns a DFTA
-- det :: NFTA -> arityFunction -> DFTA
det :: NFTA -> (String -> Int) -> DFTA [String]
det (q, f, qf, deltaRules) arity = (qd, f, qdf, deltaRulesD)
	where	qd = [s | s <- existsDeltaRule f]
		qdf = [stateList | stateList <- qd, stateList `intersect` qf /= []]
		deltaRulesD = removeDuplicates [([symbol ++ (show state) ++ ""], s) | symbol <- f, (state, s) <- existsTransition [deltaElem | deltaElem <- deltaRules, symbol `elem` (fst deltaElem)] 0] --[deltaElem | deltaElem <- deltaRules, symbol `elem` (fst deltaElem)]] --state <- qd, s <- qd, existsTransition [deltaElem | deltaElem <- deltaRules, symbol `elem` (fst deltaElem)] state s]
		existsDeltaRule f
			| null f = []
			| otherwise = cleanup $ (existsDeltaRule' [deltaElem | deltaElem <- deltaRules, (head f) `elem` (fst deltaElem)]) ++ existsDeltaRule (tail f)
		existsDeltaRule' deltaList  = [fstStates deltaList] ++ [sndStates deltaList]
		fstStates deltaList
			| null deltaList = []
			| otherwise = removeDuplicates $ [state | state <- q, state `elem` (fst (head deltaList))] ++ fstStates (tail deltaList)
		sndStates deltaList
			| null deltaList = []
			| otherwise = removeDuplicates $ [state | state <- q, state `elem` (snd (head deltaList))] ++ sndStates (tail deltaList)
		--existsTransition :: [([String], [String])] -> Int -> [([[String]], [String])]	-- delta det
		existsTransition deltaList1 index
			| index > (arityF (head (fst (head deltaList1)))) = []	--useless?
			| arityF (head (fst (head deltaList1))) == 0 = [([], (head [(snd state) | state <- (head (groupTransitions deltaList1 deltaList1 index))]))]
			| index > (arityF (head (fst (head deltaList1)))) = []
			| arityF (head (fst (head deltaList1))) == 1 = [statePair | statePair <- (statePairs (groupTransitions deltaList1 deltaList1 index)), (snd statePair) `elem` qd] ++ existsTransition deltaList1 (index+1)
			| otherwise = [stateGroup | stateGroup <- (stateGroups (groupTransitions deltaList1 deltaList1 index)), (snd stateGroup) `elem` qd] ++ existsTransition deltaList1 (index+1)
		--groupTransitions :: [([String], [String])] -> [([String], [String])] -> Int -> [[([String], [String])]]
		groupTransitions deltaList1 deltaList2 index
			| index == 0 = [deltaList1]
			| null deltaList2 = []
			| otherwise = removeDuplicates $ [[deltaElem | deltaElem <- deltaList1, equalSubtreeHead deltaElem (head deltaList2) index 0]] ++ groupTransitions deltaList1 (tail deltaList2) index
		--equalSubtreeHead :: ([String], [String]) -> ([String], [String]) -> Int -> Int -> Bool
		equalSubtreeHead deltaElem deltaListElem index counter
			| counter == index = True
			| otherwise = (fst deltaElem)!!((subtreeHeads (fst deltaElem) arity)!!counter) == (fst deltaListElem)!!((subtreeHeads (fst deltaListElem) arity)!!counter) && equalSubtreeHead deltaElem deltaListElem index (counter+1)
		--statePairs :: [[([String], [String])]] -> [([[String]], [String])]
		statePairs deltaListList 
			| null deltaListList = []
			| otherwise = statePairs' deltaListList qd
		--statePairs' :: [[([String], [String])]] -> [[String]] ->  [([[String]], [String])]
		statePairs' deltaListList qd
			| null qd = []
			| otherwise = statePairs'' deltaListList (head qd) ++ statePairs' deltaListList (tail qd)
		--statePairs'' :: [[([String], [String])]] -> [String] -> [([[String]], [String])]
		statePairs'' deltaListList state
			| null deltaListList = []
			| otherwise = [([state], (removeDuplicates (statePairs''' deltaListList state)))]
		--statePairs''' :: [[([String], [String])]] -> [String] -> [String]
		statePairs''' deltaListList state
			| null deltaListList = []
			| otherwise = [states | states <- q_det, deltaElem <- (head deltaListList), states `elem` (snd deltaElem), isInDelta state deltaElem] ++ statePairs''' (tail deltaListList) state
		--isInDelta :: [String] -> ([String], [String]) -> Bool
		isInDelta state deltaElem
			| null state = False
			| otherwise = (head state) `elem` (fst deltaElem) || isInDelta (tail state) deltaElem
		--stateGroups :: [[([String], [String])]] -> [([[String]], [String])]
		stateGroups deltaListList 
			| null deltaListList = []
			| otherwise = stateGroups' deltaListList (stateList qd (arity (head (fst (head (head deltaListList))))))
		--stateList :: [[String]] -> Int -> [[[String]]]
		stateList qd ar = perm (filter (\x -> (length x) == ar) (powerSet qd)) ++ sameStates qd ar
		--sameStates :: [[String]] -> Int -> [[[String]]]
		sameStates qd ar
			| null qd = []
			| otherwise = [sameStates' (head qd) ar] ++ sameStates (tail qd) ar
		--sameStates' :: [String] -> Int -> [[String]]
		sameStates' state 0 = []
		sameStates' state ar = [state] ++ sameStates' state (ar-1)
		--perm :: [[[String]]] -> [[[String]]]
		perm stateLists
			| null stateLists = []
			| otherwise = (permutations (head stateLists)) ++ perm (tail stateLists)
		--stateGroups' :: [[([String], [String])]] -> [[[String]]] -> [([[String]], [String])]
		stateGroups' deltaListList qds
			| null qds = []
			| otherwise = stateGroups'' deltaListList (head qds) ++ stateGroups' deltaListList (tail qds)
		--stateGroups'' :: [[([String], [String])]] -> [[String]] -> [([[String]], [String])]
		stateGroups'' deltaListList states
			| null deltaListList = []
			| otherwise = [(states, (removeDuplicates (stateGroups''' deltaListList states)))]
		--stateGroups''' :: [[([String], [String])]] -> [[String]] -> [String]
		stateGroups''' deltaListList qds
			| null deltaListList = []
			| otherwise = [s | s <- q_det, deltaElem <- (head deltaListList), s `elem` (snd deltaElem), isInDelta2 qds deltaElem] ++ stateGroups''' (tail deltaListList) qds
		--isInDelta2 :: [[String]] -> ([String], [String]) -> Bool
		isInDelta2 states deltaElem
			| null states = True
			| otherwise = isInDelta (head states) deltaElem && isInDelta2 (tail states) deltaElem
