(* ITP course 2020 - Homework 1
 * Karl Norrman, 2020-01-24
 *)

(*
 * Part 1 -- list functions
 *)

datatype 'a kList = kNil | kCons of 'a  * 'a kList


fun kLength kNil = 0
  | kLength (kCons (x, xs)) = 1 + kLength xs

val tst_kLength =
  kLength kNil = 0
    andalso
  kLength (kCons (2, kCons (1, kNil))) = 2
    andalso
  kLength (kCons ("abc", kCons ("def", kNil))) = 2


fun kRevAppend kNil ys = ys
  | kRevAppend (kCons (x, xs)) ys = kRevAppend xs (kCons (x, ys))

val tst_kRevAppend =
  kRevAppend kNil kNil = kNil
    andalso
  kRevAppend (kCons (1, kCons (2, kNil))) kNil = (kCons (2, kCons (1, kNil)))
    andalso
  kRevAppend kNil (kCons (1, kCons (2, kNil))) = (kCons (1, kCons (2, kNil)))
    andalso
  kRevAppend (kCons (1, kCons (2, kNil))) (kCons (3, kCons (4, kNil))) =
     (kCons (2, kCons (1, kCons (3, kCons (4, kNil)))))


fun kRev xs = kRevAppend xs kNil

val tst_kRev =
  kRev kNil = kNil  andalso
  kRev (kCons (1, kCons (2, kNil))) = kCons (2, kCons (1, kNil))


fun kAppend kNil ys = ys
  | kAppend (kCons (x, xs)) ys = kCons (x, kAppend xs ys)

val tst_kAppend =
  kAppend kNil kNil = kNil
    andalso
  kAppend kNil (kCons (1, kCons (2, kNil))) = kCons (1, kCons (2, kNil))
    andalso
  kAppend (kCons (1, kCons (2, kNil))) kNil = kCons (1, kCons (2, kNil))
    andalso
  kAppend (kCons (1, kCons (2, kNil))) (kCons (3, kCons (4, kNil))) =
    kCons (1, kCons (2, kCons (3, kCons (4, kNil))))


fun kExists p kNil = false
  | kExists p (kCons (x, xs)) = if p x then true else kExists p xs

val tst_kExists =
  kExists (fn x => true) kNil = false
    andalso
  kExists (fn x => false) kNil = false
    andalso
  kExists (fn x => x = 1) (kCons (1, kCons (2, kNil))) = true
    andalso
  kExists (fn x => x = 4) (kCons (1, kCons (2, kNil))) = false


fun replicate _ 0 = []
  | replicate x n = x::replicate x (n - 1)

val tst_replicate =
  replicate 1 0 = []  andalso
  replicate 1 3 = [1, 1, 1]


val tst_all =
  tst_kLength andalso
  tst_kRevAppend andalso
  tst_kRev andalso
  tst_kAppend andalso
  tst_kExists andalso
  tst_replicate



(* I had heard of the relation between revAppend, append and rev before, and
 * therefore rev is already implemented in this style.  I here give a version of
 * append that uses revAppend as well.
 *)
fun k2Append xs ys = kRevAppend (kRev xs) ys

val tst_k2Append =
  k2Append kNil kNil = kNil
    andalso
  k2Append kNil (kCons (1, kCons (2, kNil))) = kCons (1, kCons (2, kNil))
    andalso
  k2Append (kCons (1, kCons (2, kNil))) kNil = kCons (1, kCons (2, kNil))
    andalso
  k2Append (kCons (1, kCons (2, kNil))) (kCons (3, kCons (4, kNil))) =
    kCons (1, kCons (2, kCons (3, kCons (4, kNil))))


(*
 * Part 2 -- Making change
 *
 * Write a program that, given the coins and notes you have in your wallet,
 * lists all the possible ways to pay a certain amount.  Represent the coins
 * you have as a list of integers.  If a number occurs twice in this list, you
 * have two coins with this value.  The result should be returned in the form
 * of a list of lists. For simplicity, the output may contain duplicates.
 * The function should have the following signature:
 *
 * make_change : int list -> int -> int list list
 *)

fun appendToAll x [] : 'a list list = [] : 'a list list
  | appendToAll x (y::ys) = [x :: y] @ appendToAll x ys

val tst_appendToAll =
  appendToAll 1 [] = []
    andalso
  appendToAll 1 [[2], [3, 4]] = [[1, 2], [1, 3, 4]]


fun allCombs [] = [] : 'a list list
  | allCombs (x::xs) = [x] :: (appendToAll x (allCombs xs)) @ allCombs xs

val tst_allCombs =
  allCombs [] = []
    andalso
  allCombs [1] = [[1]]
    andalso
  allCombs [1, 2, 3] = [[1], [2], [1, 2], [2, 1]]


fun make_change coins amount =
  filter (fn xs => (foldl (op +) 0 xs) = amount) (allCombs coins)

val tst_make_change =
  make_change [] 1 = []
    andalso
  make_change [1] 1 = [[1]]
    andalso
  make_change [1] 2 = []
    andalso
  make_change [1, 2] 1 = [[1]]
    andalso
  make_change [1, 2] 4 = []
    andalso
  make_change [1, 2] 3 = [[1, 2]]
    andalso
  make_change [1, 2, 4] 3 = [[1, 2]]
    andalso
  make_change [1, 2, 1] 3 = [[1, 2], [2, 1]]
    andalso
  make_change [1, 2, 1, 2] 3 = [[1, 2], [1, 2], [2, 1], [1, 2]]


(* Some properties of make change (that should be true):
 *
 * fun sum xs = foldl (op +) 0 xs
 *
 * forall s coins amount.
 *      s in (make_change coins amount)  ==>  s <= sum coins
 *
 * forall coins amount.
 *      length (make_change coins amount) <= pow (2, (length coins))
 *)
