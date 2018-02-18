Author: José-Paul Dominguez
Email : λfirst.last first.last@etu.upmc.fr José-Paul Dominguez

Problem solving with bounded model checking

| Preface

Two kind of cats are disposed on aligned pillows over a cold floor. Some are
black-colored and others are white-colored. All the cats want to go to their own
side of the pillow chain: the black cats want to go to the left pillows while
the white ones want to move to the right pillows. But there are few rules:

- pillows are too small to host more than one cat
- we are dealing with stubborn cats: black cats refuse to move to the right
  while white cats refuse to move to the left
- a cat can only hop to the next pillow or leap over a cat of the different
  color if the pillow after is free

| Introduction

Is there a solution to the problem given an initial configuration? The approach
presented in this document is to model the problem as a satisfiability formula
instead of writing an algorithm that moves cats over pillows. Then, the formula
will be fed to a SAT solver that will do the job. The latter will answer if yes
or no the formula satisfies, i.e. given an initial configuration of cats on
pillows, they can move to their own spot.

Using bounded model checking as a verification technique, the formula must be
generated for a given number of steps. Here, steps are cat hops. Finding the
number of cat hops until they reach their spot implies that the SAT solver will
first be called with a formula representing one possible move. If the SAT solver
yields "UNSAT", the number of possible moves need to be incremented: 2, 3, 4...
until the formula satisfies or never if a max bound is reached.

The initial configuration can be anything but a complex and interesting one is
where N white cats are on the left, N black cats are on the right and there is
just one free pillow separating them.

For example, given N = 2 the initial state would be:

W W _ B B

Where W denotes a white cat on a pillow, B denotes a black cat on a pillow and _
denotes a free pillow.

The final configuration is the same where black cats take the place of the white
cats and vice versa : B B _ W W

| Setup

This document is written in literate Haskell, *ghc* can compile it directly:

`ghc LeapCats.lhs` # which will generate a LeapCats binary

- Conversion to DIMACS CNF: bool2cnf
- SAT solver: minisat

The *shell.nix* file can be used with *nix-shell* in order to bootstrap a shell
with these programs.

The program can be run with:

`./LeapCats N`

where N denotes the number of white cats on the left and black cats on the
right.

| Few imports

Some functions defined later are already named in the Prelude, so let's hide
them:

> import Prelude hiding (not, and, or)

All of this will be needed in the end for the crappy IO:

> import System.Environment
> import System.Process hiding (runProcess)
> import System.IO
> import System.Exit
> import qualified Data.ByteString.Char8 as B
> import Data.Monoid ((<>))

| Data types

> data Proposition v = Variable v
>                    | Not (Proposition v)
>                    | And (Proposition v) (Proposition v)
>                    | Or (Proposition v) (Proposition v)

Using data constructors everytime to build a proposition would be annoying.
Defining functions and operators to build them is super convenient again.

> not = Not
> and = And
> or = Or
> pA `without` pB = pA `and` not pB
> pA `xor` pB = (pA `and` not pB) `or` (not pA `and` pB)
> pA `equals` pB = not $ pA `xor` pB
> ifThenElse cond stmt1 stmt2 = (cond `and` stmt1) `or` (not cond `and` stmt2)

Propositions are written in terms of cats and turns. Is there a white or a black
cat on a certain pillow at a given moment? Wich kind of cat the solver choose to
move at a given moment? These two type of informations are atomic propositions.

> data Atom = Cat Color Position Date
>           | Turn Color Date


There are white and black cats and a function that swaps colors will be helpful.

> data Color = White | Black

> switch White = Black
> switch Black = White

Moreover, the color is not sufficient in order to identify cats. They need to be
associated to a position at a given time.

> type Position = Integer
> type Date = Integer

Primitives functions that generate simple propositions about cats and turns will
be also useful.

> cat color on date = Variable $ Cat color on date
> white = cat White
> black = cat Black

> whiteOnly on date = (white on date) `without` (black on date)
> blackOnly on date = (black on date) `without` (white on date)

> otherCat color = cat (switch color)
> both on date = (white on date) `and` (black on date)
> free on date = not (white on date) `and` not (black on date)

> turn color date = Variable $ Turn color date
> whiteTurn = turn White
> blackTurn = turn Black

| Initial and final state

> genConf left right date n = foldr1 and [ left on date | on <- [0 .. n - 1] ]
>                       `and` free n date
>                       `and` foldr1 and [ right on date | on <- [n + 1 .. last] ]
>     where length = n * 2 + 1
>           last = length - 1

> firstConf = genConf whiteOnly blackOnly 0
> finalConf = flip $ genConf blackOnly whiteOnly

| Moves

White cats want to move to the right pillows (increasing numbers) while black
cats want to move to the left pillows (decreasing numbers).

> next White n = n + 1
> next Black n = n - 1

> prev White n = n - 1
> prev Black n = n + 1

The fact that there is a certain kind of cat in the future on a given pillow
depends on:

1. the SAT solver chose to move this kind of cat
2. - a cat of this kind couldn't move out of this pillow
or - a cat of this kind could move on this pollow

otherwise, the SAT solver needs to know the cat stayed here this turn.

> transition color on future = cat color on future `equals` p
>     where now = future - 1
>           p = ifThenElse (turn color now)
>                          (cantMoveOut color on now `or` canMoveIn color on now)
>                          (cat color on now)

There should be special cases for cat moves (think of the borders of the game).
But as it's a bit annoying to write, an alternative is to extend the pillow
chain (2 pillows on each side) and add sentinels on them so that cats never
reach them.

> cantMoveOut color from now = cantHopOut color from now
>                        `and` cantLeapOut color from now

> canMoveIn color to now = canHopIn color to now
>                     `or` canLeapIn color to now

> cantHopOut color from now = cat color from now `without` free to now
>     where to = next color from

> cantLeapOut color from now = cat color from now `without`
>     (otherCat color over now `and` free to now)
>     where over = next color from
>           to = next color over

> canHopIn color to now = cat color from now `and` free to now
>     where from = prev color to

> canLeapIn color to now = cat color from now
>                              `and` otherCat color over now
>                              `and` free to now
>     where over = prev color to
>           from = prev color over

> transitions length steps = foldr1 and [ transition color on future
>                                       | color <- [White, Black]
>                                       , on <- [0 .. length - 1]
>                                       , future <- [1 .. steps]
>                                       ]

| Constraints

The first thing to forbid is to have more than one cat on a pillow.

> checkPillow on now = not $ both on now
> checkPillows length steps = foldr1 and [ checkPillow on now
>                                        | on <- [0 .. length]
>                                        , now <- [0 .. steps]
>                                        ]

The second thing, is to authorize the SAT solver to do at most one move per
turn.

> checkMove now = not (whiteTurn now `and` blackTurn now)
> checkMoves steps = foldr1 and [ checkMove now | now <- [0 .. steps - 1] ]

At last, sentinels are put around the game for our little trick.

> sentinels length now = free (-2) now
>                  `and` blackOnly (-1) now
>                  `and` whiteOnly length now
>                  `and` free (length + 1) now
> checkBounds length steps = foldr1 and [ sentinels length now
>                                       | now <- [0 .. steps]
>                                       ]

> constraints length steps = checkPillows length steps
>                      `and` checkMoves steps
>                      `and` checkBounds length steps

| Putting everything together

> formula n steps = let length = 2 * n + 1
>                   in firstConf n
>                `and` transitions length steps
>                `and` constraints length steps
>                `and` finalConf n steps

| Text rendering

> instance Show Color where
>     show White = "w"
>     show Black = "b"

> instance Show Atom where
>     show (Cat color on date) = show color ++ "_"
>                             ++ show (on + 2) ++ "_"
>                             ++ show date
>     show (Turn color date) = "turn_"
>                            ++ show color ++ "_"
>                            ++ show date

> enclose = (++ ")") . ("(" ++)

> instance Show v => Show (Proposition v) where
>     show (Variable v) = show v
>     show (Not v) = "!" ++ show v
>     show (And pA pB) = enclose  $ show pA ++ " & " ++ show pB
>     show (Or pA pB) = enclose $ show pA ++ " | " ++ show pB

| Crappy IOs

> main :: IO ()
> main = do
>     args <- getArgs
>     hSetBuffering stdout NoBuffering
>     case args of
>       [ "0" ] -> error "invalid number of steps"
>       [ nStr ] -> let n = read nStr
>                    in solve n
>       _ -> error "invalid arguments"

> solve :: Integer -> IO ()
> solve n = solveWith n 1

> solveWith n steps = do
>     let p = formula n steps
>     putStr ("running with " ++ show steps ++ " steps... ")
>     (code, dimacs) <- prop2dimacs (B.pack . show $ p)
>     (code, output) <- runSATSolver dimacs
>     case code of
>       ExitFailure 10 -> putStrLn $ showResult n steps
>       ExitFailure 20 -> putStrLn "UNSAT" >> solveWith n (steps + 1)
>       _ -> error "something went wrong"


> showResult n steps = "SAT after " ++ show steps ++ " steps"

> gatherOutput :: ProcessHandle -> Handle -> IO (ExitCode, B.ByteString)
> gatherOutput hP hOut = gather mempty
>     where
>         gather acc = do
>             bs <- B.hGetNonBlocking hOut (64 * 1024)
>             let acc' = acc <> bs
>             s <- getProcessExitCode hP
>             case s of
>               Nothing -> gather acc'
>               Just ec -> do
>                 last <- B.hGetContents hOut
>                 return (ec, acc' <> last)

> runProcess :: FilePath -> B.ByteString -> IO (ExitCode, B.ByteString)
> runProcess name input = do
>     let spawn = createProcess (proc name []){
>         std_in = CreatePipe
>       , std_out = CreatePipe
>     }
>     (Just hIn, Just hOut, _, hProc) <- spawn
>     B.hPut hIn input 
>     (exitCode, output) <- gatherOutput hProc hOut
>     return (exitCode, output)

> prop2dimacs = runProcess "bool2cnf"
> runSATSolver = runProcess "minisat"
