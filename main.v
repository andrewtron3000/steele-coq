
(* 

this is a treatment of the water holding histogram problem found in
https://www.youtube.com/watch?v=ftcIcn8AmSY

 *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Nat.
Require Import List.

Import ListNotations.

(* Let's first define the type of our histogram *)
Definition histogram := list nat.

Definition max_nat (x1 x2 : nat) : nat :=
  if (leb x1 x2) then x2 else x1.

Definition min_nat (x1 x2 : nat) : nat :=
  if (leb x1 x2) then x1 else x2.

(* define a low level utility function for the left to right sweep *)
Fixpoint left_to_right_sweep' (max : nat) (h : histogram) : list nat :=
  match h with
  | [] => []
  | x :: xs => (max_nat max x) :: (left_to_right_sweep' (max_nat max x) xs)
  end.

(* define the left to right sweep function that returns, for each
element of the histogram the highest bar starting from the left. *)
Definition left_to_right_sweep (h : histogram) : list nat :=
  left_to_right_sweep' 0 h.

(* define the right to left sweep function that returns, for each
element of the histogram the highest bar starting from the right *)
Definition right_to_left_sweep (h : histogram) : list nat :=
  rev (left_to_right_sweep (rev h)).

Compute left_to_right_sweep [1 ; 2; 1; 4; 2; 1].
Compute right_to_left_sweep [1 ; 2; 1; 4; 2; 1].

(* Next, define some utility functions like zip *)
Fixpoint zip (l1 l2 : list nat) : list (nat * nat) :=
  match l1 with
  | [] => []
  | x :: xs => match l2 with
               | [] => []
               | y :: ys => (x, y) :: zip xs ys
               end
  end.

Compute (zip [1; 2; 3; 4] [5; 6; 7; 8]).

(* define a low level utility function useful for computing the water
level *)
Fixpoint water_level' (levels : list (nat * nat)) : list nat :=
  match levels with
  | [] => []
  | (l, r) :: xs => (min_nat l r) :: water_level' xs
  end.

(* now compute the water level *)
Definition water_level (h : histogram) : list nat :=
  let lr := left_to_right_sweep h in
  let rr := right_to_left_sweep h in
  let lrs := zip lr rr in
  water_level' lrs.

(* Here is the example from the youtube video *)
Definition example := [2;6;3;5;2;8;1;4;2;2;5;3;5;7;4;1].

(* for a particular bar and water level, how much water is there *)
Definition how_much_water (bar_and_water : (nat * nat)) : nat :=
  match bar_and_water with
  | (bar, water) => if (leb bar water) then water - bar else 0
  end.

(* This function computes the total amount of water carried by a
histogram by just computing the amount of water carried by each bar.
*)
Definition amount_of_water (bars : histogram) : nat :=
  let water := water_level bars in
  let bars_and_water := zip bars water in
  fold_left add (map how_much_water bars_and_water) 0.

(* This should evaluate to 35. *)
Compute amount_of_water example.

(* Ok, now we'll work on the bitonic data structure representation.
This is the second development in the talk. *)

Definition height_width_list := list (nat * nat).

Fixpoint hw_list_eq (x y : height_width_list) : bool :=
  let lx := List.length x in
  let ly := List.length y in
  if (beq_nat lx ly)
  then match x with
       | (x1, x2) :: xs =>
         match y with
         | (y1, y2) :: ys => if (andb (beq_nat x1 y1) (beq_nat x2 y2)) 
                             then hw_list_eq xs ys
                             else false
         | [] => true
         end
       | [] => true
       end
  else false.

Compute hw_list_eq [(1, 2) ; (3, 4)] [(1, 2) ; (3, 4)].
Compute hw_list_eq [(1, 4) ; (3, 4)] [(1, 2) ; (3, 4)].
Compute hw_list_eq [(1, 2) ; (3, 4) ; (5, 6)] [(1, 2) ; (3, 4)].

(* Define the glob data structure as in the video *)
Record glob : Set := mkGlob {
                         left : height_width_list;
                         h : nat;
                         w : nat;
                         right : height_width_list;
                         water : nat }.

Definition initial_glob := mkGlob [] 0 0 [] 0.

Definition make_singleton_glob (h : nat) : glob :=
  mkGlob [] h 1 [] 0.

(* The width function calculates the width of a list of height width
pairs.  This is on the slide of utility functions. *)
Fixpoint width (hw : height_width_list) : nat :=
  match hw with
  | [] => 0
  | (h, w) :: xs => w + (width xs)
  end.

(* The fill function computes how much water can be held at a
particular water height for a set of height width pairs. *)
Fixpoint fill (hw : height_width_list) (water_height : nat) : nat :=
  match hw with
  | [] => 0
  | (h, w) :: xs => (w * (water_height - h)) + (fill xs water_height)
  end.

(* The function half is the "split" function that will divide a list
of height width pairs into two lists. *)
Definition half (l : height_width_list) : (height_width_list * height_width_list) :=
  let n := length l in
  (firstn (n / 2) l, skipn (n / 2) l).

Compute half [ (0, 1) ; (2, 3) ; (4, 5) ; (6, 7) ].

(* OK, now we are going to implement the three way split.  This is
defined in the video. *)
Fixpoint three_way_split (gas : nat) (x : height_width_list) (m : nat) : (height_width_list * option nat * height_width_list) :=
  match gas with
  | 0 => ([], None, [])
  | S g => match x with
           | [] => ([], None, [])
           | [ l ] => let (a, b) := l in
                      if (Nat.leb a m)
                      then ([l], None, [])
                      else if (Nat.ltb m a)
                           then ([], None, [l])
                           else ([], Some b, [])
           | l :: ls => let (y, z) := half x in
                        let (n, w) := hd (0, 0) z in
                        if (Nat.ltb m n)
                        then let '(p, q, r) := three_way_split g y m in
                             (p, q, r ++ z)
                        else let '(p, q, r) := three_way_split g z m in
                             (y ++ p, q, r)
           end
  end.

(* Next we define the oplus operator from the video. *)
Definition oplus (gas : nat) (x y : glob) : glob :=
  if (Nat.ltb (h x) (h y))
  then let '(lss, eql, gtr) := three_way_split gas (left y) (h x) in
       mkGlob ( (left x) ++ [(h x, (w x) + (width (right x)) + (width lss))] ++ gtr )
              (h y)
              (w y)
              (right y)
              ( (water x) + 
                (fill (right x) (h x)) +
                (fill lss (h x)) +
                (water y) )
  else if (Nat.ltb (h y) (h x))
       then let '(lss, eql, gtr) := three_way_split gas (right x) (h y) in
            mkGlob (left x)
                   (h x)
                   (w x) 
                   ( (right y) ++ [(h y, (width lss) + (width (left y)) + (w y))] ++ gtr )
                   ( (water x) + (fill lss (h y)) + (fill (left y) (h y)) + (water y) )
       else mkGlob (left x)
                   (h x)
                   ( (w x) + (width (right x)) + (width (left y)) + (w y) )
                   (right y)
                   ( (water x) + (fill (right x) (h x)) + (fill (left y) (h x)) + (water y) ).

(* And we define a notation for oplus *)
Notation "x @ y" :=
  (oplus 1000 x y)
    (at level 50,
     left associativity).

(* Now let's do some testing of the oplus.  First we need to generate
all of the initial globs *)

Definition globs_start (w : histogram) : list glob :=
  List.map make_singleton_glob w.

(* Create the starting list of singleton globs from the example from the video *)
Definition start : list glob :=
  globs_start example.

Compute start.

(* Now, for testing, break out every glob *)
Definition x1 : glob := List.hd initial_glob start.
Definition x2 : glob := List.nth 1 start initial_glob.
Definition x3 : glob := List.nth 2 start initial_glob.
Definition x4 : glob := List.nth 3 start initial_glob.
Definition x5 : glob := List.nth 4 start initial_glob.
Definition x6 : glob := List.nth 5 start initial_glob.
Definition x7 : glob := List.nth 6 start initial_glob.
Definition x8 : glob := List.nth 7 start initial_glob.
Definition x9 : glob := List.nth 8 start initial_glob.
Definition x10 : glob := List.nth 9 start initial_glob.
Definition x11 : glob := List.nth 10 start initial_glob.
Definition x12 : glob := List.nth 11 start initial_glob.
Definition x13 : glob := List.nth 12 start initial_glob.
Definition x14 : glob := List.nth 13 start initial_glob.
Definition x15 : glob := List.nth 14 start initial_glob.
Definition x16 : glob := List.nth 15 start initial_glob.

(* Now do some simple tests of the oplus operator *)
Compute (x1 @ x2).
Compute (x1 @ x2 @ x3 @ x4 @ x5).
Compute (x1 @ x2 @ x3 @ x4 @ x5 @ x6 @ x7 @ x8 @
         x9 @ x10 @ x11 @ x12 @ x13 @ x14 @ x15 @ x16).

(* Now testing the three-case bitonic glob slide.  Here is test #1. *)
Definition one_l : glob :=
  (make_singleton_glob 1) @ (make_singleton_glob 3) @ (make_singleton_glob 4) @ (make_singleton_glob 2).
 
Definition one_r : glob :=
  (make_singleton_glob 1) @ (make_singleton_glob 2) @ (make_singleton_glob 3) @ (make_singleton_glob 2).

Compute (one_l @ one_r).

(* Here is test #2 of the oplus operator *)
Definition two_l : glob :=
  (make_singleton_glob 1) @ (make_singleton_glob 2) @ (make_singleton_glob 3) @ (make_singleton_glob 2).
 
Definition two_r : glob :=
  (make_singleton_glob 1) @ (make_singleton_glob 4) @ (make_singleton_glob 5) @ (make_singleton_glob 2).

Compute (two_l @ two_r).

(* Here is test #3 of the oplus operator *)
Definition three_l : glob :=
  (make_singleton_glob 1) @ (make_singleton_glob 2) @ (make_singleton_glob 3) @ (make_singleton_glob 2).
 
Definition three_r : glob :=
  (make_singleton_glob 1) @ (make_singleton_glob 2) @ (make_singleton_glob 3) @ (make_singleton_glob 2).

Compute (three_l @ three_r).

(* OK, it looks like the glob stuff is working *)

(* Now let's try asking if the oplus operator is associative *)
Theorem oplus_assoc : forall (x y z : glob),
    x @ (y @ z) = (x @ y) @ z.
Proof.
  Admitted.

(* Now, let's work on the quickchick support *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From QuickChick Require Import QuickChick.

(* Do a quickchick that the simple sequential solution returns the
same amount of water as the oplus version. *)

Definition oplus_water (h : histogram) : nat :=
  let gs := globs_start h in
  let final := List.fold_left (oplus 1000) gs initial_glob in
  water final.

Definition equiv_solutions_p (h : histogram) : bool :=
  beq_nat (amount_of_water h) (oplus_water h).

QuickChick
  (forAll (vectorOf 32 (choose (0, 20))) equiv_solutions_p).

(* Now we know the oplus and simple sequential versions return
the same value. *)

(* Let's test the oplus to see if it associative *)

Definition glob_eq (x y : glob) : bool :=
  match x with
  | {| left := xleft; h := xh; w := xw; right := xright; water := xwater |} =>
    match y with
    | {| left := yleft; h := yh; w := yw; right := yright; water := ywater |} =>
      List.fold_left (andb) [ (hw_list_eq xleft yleft) ;
                                (beq_nat xh yh) ;
                                (beq_nat xw yw) ;
                                (hw_list_eq xright yright) ;
                                (beq_nat xwater ywater) ] true
    end
  end.

Definition oplus_assoc_p (globs : (glob * glob * glob)) : bool :=
  match globs with
  | (x, y, z) =>
    glob_eq (x @ (y @ z)) ((x @ y) @ z)
  end.

(* First, let's define useful generators.  This generator returns a
list of singleton globs *)
Definition genStartState : G (list glob) :=
  bindGen (vectorOf 8 (choose (0, 20)))
          (fun xs => returnGen (globs_start xs)).

(* This generator creates a glob *)
Definition genGlob : G glob :=
  bindGen genStartState
          (fun start => returnGen (fold_left (oplus 1000) start initial_glob)).

(* Now I want to derive a show function for globs *)
Derive Show for glob.
Print showglob.

(* TODO: work on shrinkers *)


(* OK, let's put together a check. *)
QuickChick
  (forAll
     (bindGen genGlob
              (fun x =>
                 bindGen genGlob
                         (fun y =>
                            bindGen genGlob (fun z => returnGen (x, y, z))))) oplus_assoc_p).

(* OK, now I have quickchicked two properties.  The first is that the
simple sequential version returns the same value as the oplus.  The
second is that oplus is associative. So I think it is OK to start
trying to prove that the oplus operator is associative.  *)



