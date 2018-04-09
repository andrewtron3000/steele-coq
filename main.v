
(* this is a treatment of the water holding histogram problem found in

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

Fixpoint left_to_right_sweep' (max : nat) (h : histogram) : list nat :=
  match h with
  | [] => []
  | x :: xs => (max_nat max x) :: (left_to_right_sweep' (max_nat max x) xs)
  end.

(* define the left to right sweep function that returns, for each
element of the histogram the highest bar starting from the left. *)
Fixpoint left_to_right_sweep (h : histogram) : list nat :=
  left_to_right_sweep' 0 h.

Compute left_to_right_sweep [1 ; 2; 1; 4; 2; 1].

(* define the right to left sweep function that returns, for each
element of the histogram the highest bar starting from the right *)
Fixpoint right_to_left_sweep (h : histogram) : list nat :=
  rev (left_to_right_sweep (rev h)).

Compute right_to_left_sweep [1 ; 2; 1; 4; 2; 1].

Fixpoint zip (l1 l2 : list nat) : list (nat * nat) :=
  match l1 with
  | [] => []
  | x :: xs => match l2 with
               | [] => []
               | y :: ys => (x, y) :: zip xs ys
               end
  end.

Compute (zip [1; 2; 3; 4] [5; 6; 7; 8]).

Fixpoint water_level' (levels : list (nat * nat)) : list nat :=
  match levels with
  | [] => []
  | (l, r) :: xs => (min_nat l r) :: water_level' xs
  end.

(* now compute the water level *)
Fixpoint water_level (h : histogram) : list nat :=
  let lr := left_to_right_sweep h in
  let rr := right_to_left_sweep h in
  let lrs := zip lr rr in
  water_level' lrs.

(* Here is the example from the youtube video *)
Definition example := [2;6;3;5;2;8;1;4;2;2;5;3;5;7;4;1].

Compute water_level example.

Definition how_much_water (bar_and_water : (nat * nat)) : nat :=
  match bar_and_water with
  | (bar, water) => if (leb bar water) then water - bar else 0
  end.

Fixpoint map (f : nat*nat -> nat) (ls : list (nat * nat)) : list nat :=
  match ls with
  | [] => []
  | x :: xs => (f x) :: map f xs
  end.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
  | [] => 0
  | x :: xs => x + sum(xs)
  end.

Definition amount_of_water (bars : histogram) : nat :=
  let water := water_level bars in
  let bars_and_water := zip bars water in
  sum (map how_much_water bars_and_water).

Compute amount_of_water example.

(* Ok, now we'll work on the bitonic data structure representation *)

Definition height_width_list := list (nat * nat).

Record glob : Set := mkGlob {
                         left : height_width_list;
                         h : nat;
                         w : nat;
                         right : height_width_list;
                         water : nat }.

Definition initial_glob := mkGlob [] 0 0 [] 0.

Definition make_singleton_glob (h : nat) : glob :=
  mkGlob [] h 1 [] 0.

Fixpoint width (hw : height_width_list) : nat :=
  match hw with
  | [] => 0
  | (h, w) :: xs => w + (width xs)
  end.

Fixpoint fill (hw : height_width_list) (water_height : nat) : nat :=
  match hw with
  | [] => 0
  | (h, w) :: xs => (w * (water_height - h)) + (fill xs water_height)
  end.

Search Nat.leb.

Definition half (l : height_width_list) : (height_width_list * height_width_list) :=
  let n := length l in
  (firstn (n / 2) l, skipn (n / 2) l).

Compute half [ (0, 1) ; (2, 3) ; (4, 5) ; (6, 7) ].

(* OK, now we are going to implement the three way split *)
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


Notation "x @ y" :=
  (oplus 1000 x y)
    (at level 50,
     left associativity).

(*
Notation "x # y" :=
  (oplus_debug 1000 x y)
    (at level 50,
     left associativity).
 *)

(* Now let's do some testing of the oplus *)

(* First we need to generate all of the initial globs *)

Definition globs_start (w : list nat) : list glob :=
  List.map make_singleton_glob w.

Definition start : list glob :=
  globs_start example.

Compute start.

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

Compute (x1, x2).

Compute (x1 @ x2).

Compute (x1 @ x2 @ x3 @ x4 @ x5).

(* = {| left := [(2, 1)]; h := 6; w := 1; 
        right := [(2, 1); (5, 2)]; water := 2 |}
     : glob *)

Compute (x1 @ x2 @ x3 @ x4 @ x5 @ x6 @ x7 @ x8 @
         x9 @ x10 @ x11 @ x12 @ x13 @ x14 @ x15 @ x16).
