import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_667

open PEqualNP.CircuitLowerBounds

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

def linesThrough (v : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun w => v ∈ line w)

lemma line_card (w : Fin 13) : (line w).card = 4 := by
  revert w
  decide

lemma line_inter_card (w1 w2 : Fin 13) (h : w1 ≠ w2) : (line w1 ∩ line w2).card = 1 := by
  revert w1 w2 h
  decide

lemma linesThrough_card (v : Fin 13) : (linesThrough v).card = 4 := by
  revert v
  decide

lemma linesThrough_inter_card (v1 v2 : Fin 13) (h : v1 ≠ v2) :
    (linesThrough v1 ∩ linesThrough v2).card = 1 := by
  revert v1 v2 h
  decide

def supCredit (k : ℕ) : ℕ :=
  match k with
  | 5 => 36
  | 6 => 36
  | 7 => 18
  | 8 => 18
  | 9 => 12
  | 10 => 9
  | 11 => 6
  | _ => 0

def credit (S : Finset (Fin 13)) (w : Fin 13) : ℕ :=
  if S ⊆ line w ∧ 2 ≤ S.card then 36
  else if line w ⊂ S then supCredit S.card
  else 0

lemma union2_card {α : Type} [DecidableEq α] (A B : Finset α)
    (hA : A.card = 4) (hB : B.card = 4) (hAB : (A ∩ B).card = 1) :
    (A ∪ B).card = 7 := by
  have h := Finset.card_union_add_card_inter A B
  omega

lemma union3_card {α : Type} [DecidableEq α] (A B C : Finset α)
    (hA : A.card = 4) (hB : B.card = 4) (hC : C.card = 4)
    (hAB : (A ∩ B).card = 1) (hAC : (A ∩ C).card = 1) (hBC : (B ∩ C).card = 1) :
    9 ≤ (A ∪ B ∪ C).card := by
  have h1 : (A ∪ B).card = 7 := union2_card A B hA hB hAB
  have h2 := Finset.card_union_add_card_inter (A ∪ B) C
  have h3 : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le (A ∩ C) (B ∩ C)
  omega

lemma union4_card {α : Type} [DecidableEq α] (A B C D : Finset α)
    (hA : A.card = 4) (hB : B.card = 4) (hC : C.card = 4) (hD : D.card = 4)
    (hAB : (A ∩ B).card = 1) (hAC : (A ∩ C).card = 1) (hAD : (A ∩ D).card = 1)
    (hBC : (B ∩ C).card = 1) (hBD : (B ∩ D).card = 1) (hCD : (C ∩ D).card = 1) :
    10 ≤ (A ∪ B ∪ C ∪ D).card := by
  have h3 : 9 ≤ (A ∪ B ∪ C).card := union3_card A B C hA hB hC hAB hAC hBC
  have h4 := Finset.card_union_add_card_inter (A ∪ B ∪ C) D
  have h5 : ((A ∪ B ∪ C) ∩ D).card ≤ (A ∩ D).card + (B ∩ D).card + (C ∩ D).card := by
    rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
    have h6 := Finset.card_union_le (A ∩ D ∪ B ∩ D) (C ∩ D)
    have h7 := Finset.card_union_le (A ∩ D) (B ∩ D)
    omega
  omega

lemma sub_line_unique (S : Finset (Fin 13)) (h2 : 2 ≤ S.card)
    (w1 w2 : Fin 13) (h1 : S ⊆ line w1) (h2' : S ⊆ line w2) : w1 = w2 := by
  by_contra hne
  have hsub : S ⊆ line w1 ∩ line w2 := Finset.subset_inter h1 h2'
  have hc := Finset.card_le_card hsub
  rw [line_inter_card w1 w2 hne] at hc
  omega

lemma lines_in_le_one (S : Finset (Fin 13)) (hS : S.card ≤ 6) :
    (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card ≤ 1 := by
  by_contra h
  have h2 : 1 < (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card := by omega
  obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp h2
  have h1 : line w1 ⊆ S := (Finset.mem_filter.mp hw1).2
  have h2' : line w2 ⊆ S := (Finset.mem_filter.mp hw2).2
  have hsub : line w1 ∪ line w2 ⊆ S := Finset.union_subset h1 h2'
  have hc := Finset.card_le_card hsub
  have hu := union2_card (line w1) (line w2) (line_card w1) (line_card w2)
    (line_inter_card w1 w2 hne)
  omega

lemma lines_in_le_two (S : Finset (Fin 13)) (hS : S.card ≤ 8) :
    (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card ≤ 2 := by
  by_contra h
  set T := Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)
  have h3 : 3 ≤ T.card := by omega
  obtain ⟨w1, hw1⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hcard1 : 2 ≤ (T.erase w1).card := by
    rw [Finset.card_erase_of_mem hw1]
    omega
  obtain ⟨w2, hw2e⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase w1).card)
  have h12 : w1 ≠ w2 := (Finset.mem_erase.mp hw2e).1.symm
  have hw2 : w2 ∈ T := (Finset.mem_erase.mp hw2e).2
  have hcard2 : 1 ≤ ((T.erase w1).erase w2).card := by
    rw [Finset.card_erase_of_mem hw2e]
    omega
  obtain ⟨w3, hw3e⟩ := Finset.card_pos.mp (by omega : 0 < ((T.erase w1).erase w2).card)
  have h23 : w2 ≠ w3 := (Finset.mem_erase.mp hw3e).1.symm
  have hw3e1 : w3 ∈ T.erase w1 := (Finset.mem_erase.mp hw3e).2
  have h13 : w1 ≠ w3 := (Finset.mem_erase.mp hw3e1).1.symm
  have hw3 : w3 ∈ T := (Finset.mem_erase.mp hw3e1).2
  have hsub : line w1 ∪ line w2 ∪ line w3 ⊆ S :=
    Finset.union_subset (Finset.union_subset (Finset.mem_filter.mp hw1).2
      (Finset.mem_filter.mp hw2).2) (Finset.mem_filter.mp hw3).2
  have hc := Finset.card_le_card hsub
  have hu := union3_card (line w1) (line w2) (line w3)
    (line_card w1) (line_card w2) (line_card w3)
    (line_inter_card w1 w2 h12) (line_inter_card w1 w3 h13) (line_inter_card w2 w3 h23)
  omega

lemma lines_in_le_three (S : Finset (Fin 13)) (hS : S.card ≤ 9) :
    (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card ≤ 3 := by
  by_contra h
  set T := Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)
  have h4 : 4 ≤ T.card := by omega
  obtain ⟨w1, hw1⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hc1 : 3 ≤ (T.erase w1).card := by rw [Finset.card_erase_of_mem hw1]; omega
  obtain ⟨w2, hw2e⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase w1).card)
  have h12 : w1 ≠ w2 := (Finset.mem_erase.mp hw2e).1.symm
  have hw2 : w2 ∈ T := (Finset.mem_erase.mp hw2e).2
  have hc2 : 2 ≤ ((T.erase w1).erase w2).card := by rw [Finset.card_erase_of_mem hw2e]; omega
  obtain ⟨w3, hw3e⟩ := Finset.card_pos.mp (by omega : 0 < ((T.erase w1).erase w2).card)
  have h23 : w2 ≠ w3 := (Finset.mem_erase.mp hw3e).1.symm
  have hw3e1 : w3 ∈ T.erase w1 := (Finset.mem_erase.mp hw3e).2
  have h13 : w1 ≠ w3 := (Finset.mem_erase.mp hw3e1).1.symm
  have hw3 : w3 ∈ T := (Finset.mem_erase.mp hw3e1).2
  have hc3 : 1 ≤ (((T.erase w1).erase w2).erase w3).card := by
    rw [Finset.card_erase_of_mem hw3e]; omega
  obtain ⟨w4, hw4e⟩ := Finset.card_pos.mp (by omega : 0 < (((T.erase w1).erase w2).erase w3).card)
  have h34 : w3 ≠ w4 := (Finset.mem_erase.mp hw4e).1.symm
  have hw4e2 : w4 ∈ (T.erase w1).erase w2 := (Finset.mem_erase.mp hw4e).2
  have h24 : w2 ≠ w4 := (Finset.mem_erase.mp hw4e2).1.symm
  have hw4e1 : w4 ∈ T.erase w1 := (Finset.mem_erase.mp hw4e2).2
  have h14 : w1 ≠ w4 := (Finset.mem_erase.mp hw4e1).1.symm
  have hw4 : w4 ∈ T := (Finset.mem_erase.mp hw4e1).2
  have hsub : line w1 ∪ line w2 ∪ line w3 ∪ line w4 ⊆ S :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset
      (Finset.mem_filter.mp hw1).2 (Finset.mem_filter.mp hw2).2)
      (Finset.mem_filter.mp hw3).2) (Finset.mem_filter.mp hw4).2
  have hc := Finset.card_le_card hsub
  have hu := union4_card (line w1) (line w2) (line w3) (line w4)
    (line_card w1) (line_card w2) (line_card w3) (line_card w4)
    (line_inter_card w1 w2 h12) (line_inter_card w1 w3 h13) (line_inter_card w1 w4 h14)
    (line_inter_card w2 w3 h23) (line_inter_card w2 w4 h24) (line_inter_card w3 w4 h34)
  omega

lemma lines_in_le_four (S : Finset (Fin 13)) (hS : S.card = 10) :
    (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card ≤ 4 := by
  set U := Finset.univ \ S
  have hU : U.card = 3 := by
    simp [U, Finset.card_sdiff, hS]
  obtain ⟨v1, hv1⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  have hc1 : 2 ≤ (U.erase v1).card := by rw [Finset.card_erase_of_mem hv1]; omega
  obtain ⟨v2, hv2e⟩ := Finset.card_pos.mp (by omega : 0 < (U.erase v1).card)
  have h12 : v1 ≠ v2 := (Finset.mem_erase.mp hv2e).1.symm
  have hv2 : v2 ∈ U := (Finset.mem_erase.mp hv2e).2
  have hc2 : 1 ≤ ((U.erase v1).erase v2).card := by rw [Finset.card_erase_of_mem hv2e]; omega
  obtain ⟨v3, hv3e⟩ := Finset.card_pos.mp (by omega : 0 < ((U.erase v1).erase v2).card)
  have h23 : v2 ≠ v3 := (Finset.mem_erase.mp hv3e).1.symm
  have hv3e1 : v3 ∈ U.erase v1 := (Finset.mem_erase.mp hv3e).2
  have h13 : v1 ≠ v3 := (Finset.mem_erase.mp hv3e1).1.symm
  have hv3 : v3 ∈ U := (Finset.mem_erase.mp hv3e1).2
  set T := Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)
  set K := linesThrough v1 ∪ linesThrough v2 ∪ linesThrough v3
  have hdisj : Disjoint T K := by
    rw [Finset.disjoint_left]
    intro w hwT hwK
    have hsub : line w ⊆ S := (Finset.mem_filter.mp hwT).2
    simp only [K, Finset.mem_union, linesThrough, Finset.mem_filter, Finset.mem_univ, true_and] at hwK
    rcases hwK with (h | h) | h
    · exact (Finset.mem_sdiff.mp hv1).2 (hsub h)
    · exact (Finset.mem_sdiff.mp hv2).2 (hsub h)
    · exact (Finset.mem_sdiff.mp hv3).2 (hsub h)
  have hK : 9 ≤ K.card := union3_card (linesThrough v1) (linesThrough v2) (linesThrough v3)
    (linesThrough_card v1) (linesThrough_card v2) (linesThrough_card v3)
    (linesThrough_inter_card v1 v2 h12) (linesThrough_inter_card v1 v3 h13)
    (linesThrough_inter_card v2 v3 h23)
  have htot : (T ∪ K).card ≤ 13 := by
    calc (T ∪ K).card ≤ (Finset.univ : Finset (Fin 13)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 13 := by simp
  rw [Finset.card_union_of_disjoint hdisj] at htot
  omega

lemma lines_in_le_six (S : Finset (Fin 13)) (hS : S.card = 11) :
    (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card ≤ 6 := by
  set U := Finset.univ \ S
  have hU : U.card = 2 := by
    simp [U, Finset.card_sdiff, hS]
  obtain ⟨v1, hv1, v2, hv2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
  set T := Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)
  set K := linesThrough v1 ∪ linesThrough v2
  have hdisj : Disjoint T K := by
    rw [Finset.disjoint_left]
    intro w hwT hwK
    have hsub : line w ⊆ S := (Finset.mem_filter.mp hwT).2
    simp only [K, Finset.mem_union, linesThrough, Finset.mem_filter, Finset.mem_univ, true_and] at hwK
    rcases hwK with h | h
    · exact (Finset.mem_sdiff.mp hv1).2 (hsub h)
    · exact (Finset.mem_sdiff.mp hv2).2 (hsub h)
  have hK : K.card = 7 := union2_card (linesThrough v1) (linesThrough v2)
    (linesThrough_card v1) (linesThrough_card v2) (linesThrough_inter_card v1 v2 h12)
  have htot : (T ∪ K).card ≤ 13 := by
    calc (T ∪ K).card ≤ (Finset.univ : Finset (Fin 13)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 13 := by simp
  rw [Finset.card_union_of_disjoint hdisj] at htot
  omega

lemma capacity (S : Finset (Fin 13)) : ∑ w : Fin 13, credit S w ≤ 36 := by
  by_cases hlt : S.card ≤ 1
  · have hz : ∀ w : Fin 13, credit S w = 0 := by
      intro w
      unfold credit
      have h1 : ¬ (S ⊆ line w ∧ 2 ≤ S.card) := by omega
      have h2 : ¬ (line w ⊂ S) := by
        intro hss
        have := Finset.card_lt_card hss
        rw [line_card w] at this
        omega
      simp [h1, h2]
    simp [hz]
  · by_cases hle4 : S.card ≤ 4
    · have h2 : 2 ≤ S.card := by omega
      have hnosup : ∀ w : Fin 13, ¬ (line w ⊂ S) := by
        intro w hss
        have := Finset.card_lt_card hss
        rw [line_card w] at this
        omega
      by_cases hex : ∃ w0 : Fin 13, S ⊆ line w0
      · rcases hex with ⟨w0, hw0⟩
        have hsum : ∑ w : Fin 13, credit S w = credit S w0 := by
          apply Finset.sum_eq_single w0
          · intro w _ hne
            unfold credit
            have hns : ¬ S ⊆ line w := fun hs => hne (sub_line_unique S h2 w w0 hs hw0)
            simp [hns, hnosup w]
          · intro h
            exact False.elim (h (Finset.mem_univ w0))
        rw [hsum]
        unfold credit
        simp [hw0, h2]
      · have hz : ∀ w : Fin 13, credit S w = 0 := by
          intro w
          unfold credit
          have hns : ¬ S ⊆ line w := fun hs => hex ⟨w, hs⟩
          simp [hns, hnosup w]
        simp [hz]
    · have hge5 : 5 ≤ S.card := by omega
      have hnosub : ∀ w : Fin 13, ¬ (S ⊆ line w ∧ 2 ≤ S.card) := by
        intro w h
        have := Finset.card_le_card h.1
        rw [line_card w] at this
        omega
      have hss_iff : ∀ w : Fin 13, line w ⊂ S ↔ line w ⊆ S := by
        intro w
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          intro hrev
          have := Finset.card_le_card hrev
          rw [line_card w] at this
          omega
      have hrew : ∑ w : Fin 13, credit S w =
          (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card * supCredit S.card := by
        calc
          ∑ w : Fin 13, credit S w
              = ∑ w : Fin 13, if line w ⊆ S then supCredit S.card else 0 := by
                apply Finset.sum_congr rfl
                intro w _
                unfold credit
                simp [hnosub w, hss_iff w]
          _ = ∑ w ∈ Finset.univ.filter (fun w : Fin 13 => line w ⊆ S), supCredit S.card := by
                rw [Finset.sum_filter]
          _ = (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card * supCredit S.card := by
                rw [Finset.sum_const, smul_eq_mul]
      rw [hrew]
      have hle13 : S.card ≤ 13 := by
        calc S.card ≤ (Finset.univ : Finset (Fin 13)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = 13 := by simp
      interval_cases hcard : S.card
      · have := lines_in_le_one S (by omega)
        simp only [supCredit]
        omega
      · have := lines_in_le_one S (by omega)
        simp only [supCredit]
        omega
      · have := lines_in_le_two S (by omega)
        simp only [supCredit]
        omega
      · have := lines_in_le_two S (by omega)
        simp only [supCredit]
        omega
      · have := lines_in_le_three S (by omega)
        simp only [supCredit]
        omega
      · have := lines_in_le_four S hcard
        simp only [supCredit]
        omega
      · have := lines_in_le_six S hcard
        simp only [supCredit]
        omega
      · simp [supCredit]
      · simp [supCredit]

def Mono2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def wiresFrom (gates : List Gate) (init : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init

def val (gates : List Gate) (x : Fin 13 → Bool) (k : ℕ) : Bool :=
  (wiresFrom gates (List.ofFn x)).getD k false

lemma wiresFrom_length (gates : List Gate) (init : List Bool) :
    (wiresFrom gates init).length = init.length + gates.length := by
  induction gates generalizing init with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    have hstep : wiresFrom (g :: gs) init =
        wiresFrom gs (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]) := rfl
    rw [hstep, ih]
    simp
    omega

lemma wiresFrom_append (g1 g2 : List Gate) (init : List Bool) :
    wiresFrom (g1 ++ g2) init = wiresFrom g2 (wiresFrom g1 init) := by
  simp [wiresFrom, List.foldl_append]

lemma getD_wiresFrom_lt (gates : List Gate) (init : List Bool) (k : ℕ) (hk : k < init.length) :
    (wiresFrom gates init).getD k false = init.getD k false := by
  induction gates generalizing init with
  | nil => rfl
  | cons g gs ih =>
    have hstep : wiresFrom (g :: gs) init =
        wiresFrom gs (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]) := rfl
    have hlt : k < (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]).length := by
      simp
      omega
    rw [hstep, ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma val_input (gates : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : k < 13) :
    val gates x k = x ⟨k, hk⟩ := by
  unfold val
  have hlen : k < (List.ofFn x).length := by rw [List.length_ofFn]; exact hk
  rw [getD_wiresFrom_lt gates (List.ofFn x) k hlen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hk, ↓reduceDIte, Option.getD_some]

lemma val_beyond (gates : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : 13 + gates.length ≤ k) :
    val gates x k = false := by
  unfold val
  have hlen : (wiresFrom gates (List.ofFn x)).length = 13 + gates.length := by
    rw [wiresFrom_length, List.length_ofFn]
  rw [List.getD_eq_default]
  omega

lemma split_gate (gates : List Gate) (p : ℕ) (hp : p < gates.length) :
    ∃ pre post : List Gate, gates = pre ++ gates[p] :: post ∧ pre.length = p := by
  refine ⟨gates.take p, gates.drop (p + 1), ?_, by simp [Nat.le_of_lt hp]⟩
  have h1 := List.take_append_drop p gates
  have h2 : gates.drop p = gates[p] :: gates.drop (p + 1) := List.drop_eq_getElem_cons hp
  rw [h2] at h1
  exact h1.symm

lemma val_gate (gates : List Gate) (x : Fin 13 → Bool) (p : ℕ) (hp : p < gates.length) :
    val gates x (13 + p) =
      (gates[p]).op.eval ((gates[p]).inputs.map (fun i => if i < 13 + p then val gates x i else false)) := by
  obtain ⟨pre, post, hsplit, hpre⟩ := split_gate gates p hp
  set g := gates[p]
  set w0 := wiresFrom pre (List.ofFn x)
  set v := g.op.eval (g.inputs.map fun i => w0.getD i false)
  have hwl : w0.length = 13 + p := by
    dsimp [w0]
    rw [wiresFrom_length, List.length_ofFn, hpre]
  have hfull : wiresFrom gates (List.ofFn x) = wiresFrom post (w0 ++ [v]) := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]
    rfl
  have hpre_val : ∀ i : ℕ, w0.getD i false =
      if i < 13 + p then val gates x i else false := by
    intro i
    by_cases hi : i < 13 + p
    · simp only [hi, ↓reduceIte]
      unfold val
      rw [hfull]
      have hi1 : i < (w0 ++ [v]).length := by
        rw [List.length_append, hwl]
        simp
        omega
      rw [getD_wiresFrom_lt post (w0 ++ [v]) i hi1]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega : i < w0.length)]
    · simp only [hi, ↓reduceIte]
      rw [List.getD_eq_default]
      omega
  have htop : val gates x (13 + p) = v := by
    unfold val
    rw [hfull]
    have hlt : 13 + p < (w0 ++ [v]).length := by
      rw [List.length_append, hwl]
      simp
    rw [getD_wiresFrom_lt post (w0 ++ [v]) (13 + p) hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ 13 + p),
      hwl, Nat.sub_self]
    rfl
  rw [htop]
  dsimp [v]
  congr 1
  apply List.map_congr_left
  intro i _
  exact hpre_val i

lemma val_mono (gates : List Gate) (hm : Mono2 gates) (x y : Fin 13 → Bool)
    (hxy : ∀ i : Fin 13, x i = true → y i = true) :
    ∀ k : ℕ, val gates x k = true → val gates y k = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkx
    by_cases hk13 : k < 13
    · rw [val_input gates x k hk13] at hkx
      rw [val_input gates y k hk13]
      exact hxy ⟨k, hk13⟩ hkx
    · by_cases hkl : k < 13 + gates.length
      · obtain ⟨p, rfl⟩ : ∃ p, k = 13 + p := ⟨k - 13, by omega⟩
        have hp : p < gates.length := by omega
        have hg := hm (gates[p]) (List.getElem_mem hp)
        rw [val_gate gates x p hp] at hkx
        rw [val_gate gates y p hp]
        have hstep : ∀ i ∈ (gates[p]).inputs,
            (if i < 13 + p then val gates x i else false) = true →
            (if i < 13 + p then val gates y i else false) = true := by
          intro i _ hi
          by_cases hil : i < 13 + p
          · simp only [hil, ↓reduceIte] at hi ⊢
            exact ih i hil hi
          · simp only [hil, ↓reduceIte] at hi
            cases hi
        rcases hg.1 with hop | hop
        · rw [hop] at hkx ⊢
          simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map] at hkx ⊢
          rintro b ⟨i, hi, rfl⟩
          exact hstep i hi (hkx _ ⟨i, hi, rfl⟩)
        · rw [hop] at hkx ⊢
          simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map] at hkx ⊢
          rcases hkx with ⟨b, ⟨i, hi, rfl⟩, hb⟩
          exact ⟨_, ⟨i, hi, rfl⟩, hstep i hi hb⟩
      · rw [val_beyond gates x k (by omega)] at hkx
        cases hkx

def e1 (v : Fin 13) : Fin 13 → Bool := fun i => decide (i = v)

def e2 (u v : Fin 13) : Fin 13 → Bool := fun i => decide (i = u ∨ i = v)

lemma e1_light (v : Fin 13) :
    ∀ i j k : Fin 13, e1 v i = true → e1 v j = true → e1 v k = true → i = j ∨ j = k ∨ i = k := by
  intro i j k hi hj _
  simp only [e1, decide_eq_true_eq] at hi hj
  exact Or.inl (hi.trans hj.symm)

lemma e2_light (u v : Fin 13) :
    ∀ i j k : Fin 13, e2 u v i = true → e2 u v j = true → e2 u v k = true →
      i = j ∨ j = k ∨ i = k := by
  intro i j k hi hj hk
  simp only [e2, decide_eq_true_eq] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> simp

def S1 (gates : List Gate) (k : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun v : Fin 13 => val gates (e1 v) k = true)

def N2 (gates : List Gate) (k : ℕ) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 < p.2 ∧ val gates (e2 p.1 p.2) k = false)

def pairSet (S : Finset (Fin 13)) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter (fun p : Fin 13 × Fin 13 => p.1 < p.2 ∧ p.1 ∉ S ∧ p.2 ∉ S)

lemma S1_input (gates : List Gate) (k : ℕ) (hk : k < 13) :
    S1 gates k = {⟨k, hk⟩} := by
  ext v
  simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [val_input gates (e1 v) k hk]
  simp [e1, eq_comm]

lemma S1_beyond (gates : List Gate) (k : ℕ) (hk : 13 + gates.length ≤ k) :
    S1 gates k = ∅ := by
  ext v
  simp [S1, val_beyond gates (e1 v) k hk]

lemma N2_sub_pairSet (gates : List Gate) (hm : Mono2 gates) (k : ℕ) :
    N2 gates k ⊆ pairSet (S1 gates k) := by
  intro p hp
  simp only [N2, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [pairSet, Finset.mem_filter, Finset.mem_univ, true_and, S1]
  refine ⟨hp.1, ?_, ?_⟩
  · intro h1
    have h2 := val_mono gates hm (e1 p.1) (e2 p.1 p.2) (by
      intro i hi
      simp only [e1, decide_eq_true_eq] at hi
      simp [e2, hi]) k h1
    rw [hp.2] at h2
    cases h2
  · intro h1
    have h2 := val_mono gates hm (e1 p.2) (e2 p.1 p.2) (by
      intro i hi
      simp only [e1, decide_eq_true_eq] at hi
      simp [e2, hi]) k h1
    rw [hp.2] at h2
    cases h2

lemma pairSet_card (S : Finset (Fin 13)) :
    (pairSet S).card = (13 - S.card) * (12 - S.card) / 2 := by
  set U := Finset.univ \ S
  have hU : U.card = 13 - S.card := by
    simp [U, Finset.card_sdiff]
  have hP_eq : pairSet S = (U ×ˢ U).filter (fun p => p.1 < p.2) := by
    ext p
    simp only [pairSet, U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_sdiff]
    tauto
  set P := (U ×ˢ U).filter (fun p => p.1 < p.2)
  set Q := (U ×ˢ U).filter (fun p => p.2 < p.1)
  set D := (U ×ˢ U).filter (fun p => p.1 = p.2)
  have hPQ : P.card = Q.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p1 _ p2 _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
  have hD : D.card = U.card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p1 hp1 p2 hp2 h
      have e1 := (Finset.mem_filter.mp hp1).2
      have e2 := (Finset.mem_filter.mp hp2).2
      exact Prod.ext h (e1.symm.trans (h.trans e2))
    · intro u hu
      exact ⟨(u, u), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hu⟩, rfl⟩, rfl⟩
  have hd1 : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have a := (Finset.mem_filter.mp h1).2
    have b := (Finset.mem_filter.mp h2).2
    exact lt_asymm a b
  have hd2 : Disjoint (P ∪ Q) D := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have e := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with h | h
    · exact ne_of_lt (Finset.mem_filter.mp h).2 e
    · exact ne_of_gt (Finset.mem_filter.mp h).2 e
  have hunion : P ∪ Q ∪ D = U ×ˢ U := by
    ext p
    simp only [P, Q, D, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
      · exact Or.inl (Or.inr ⟨hp, h⟩)
  have htot : P.card + Q.card + D.card = U.card * U.card := by
    rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2, hunion,
      Finset.card_product]
  rw [← hPQ, hD] at htot
  rw [hP_eq]
  have hS13 : S.card ≤ 13 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 13)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 13 := by simp
  rw [hU] at htot
  have hmul : 2 * P.card = (13 - S.card) * (12 - S.card) := by
    cases h : 13 - S.card with
    | zero =>
      rw [h] at htot
      omega
    | succ m =>
      have hm : 12 - S.card = m := by omega
      rw [h] at htot
      rw [hm]
      have hexp : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
      rw [hexp] at htot
      omega
  omega

lemma pairSet_line_card (w : Fin 13) : (pairSet (line w)).card = 36 := by
  rw [pairSet_card, line_card w]

lemma pairSet_le_supCredit (S : Finset (Fin 13)) (w : Fin 13) (hss : line w ⊂ S) :
    (pairSet S).card ≤ credit S w := by
  have hge5 : 5 ≤ S.card := by
    have := Finset.card_lt_card hss
    rw [line_card w] at this
    omega
  have hle13 : S.card ≤ 13 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 13)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 13 := by simp
  have hnosub : ¬ (S ⊆ line w ∧ 2 ≤ S.card) := by
    intro h
    have := Finset.card_le_card h.1
    rw [line_card w] at this
    omega
  unfold credit
  simp only [hnosub, hss, ↓reduceIte, pairSet_card]
  interval_cases S.card <;> decide

lemma gate_and_eval (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hop : (gates[p]).op = GateOp.and) (a b : ℕ) (hin : (gates[p]).inputs = [a, b])
    (ha : a < 13 + p) (hb : b < 13 + p) (x : Fin 13 → Bool) :
    val gates x (13 + p) = (val gates x a && val gates x b) := by
  rw [val_gate gates x p hp, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma gate_or_eval (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hop : (gates[p]).op = GateOp.or) (a b : ℕ) (hin : (gates[p]).inputs = [a, b])
    (ha : a < 13 + p) (hb : b < 13 + p) (x : Fin 13 → Bool) :
    val gates x (13 + p) = (val gates x a || val gates x b) := by
  rw [val_gate gates x p hp, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma gate_S1_and (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hop : (gates[p]).op = GateOp.and) (a b : ℕ) (hin : (gates[p]).inputs = [a, b])
    (ha : a < 13 + p) (hb : b < 13 + p) :
    S1 gates (13 + p) = S1 gates a ∩ S1 gates b := by
  ext v
  simp [S1, gate_and_eval gates p hp hop a b hin ha hb (e1 v)]

lemma gate_N2_and (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hop : (gates[p]).op = GateOp.and) (a b : ℕ) (hin : (gates[p]).inputs = [a, b])
    (ha : a < 13 + p) (hb : b < 13 + p) :
    N2 gates (13 + p) = N2 gates a ∪ N2 gates b := by
  ext q
  simp only [N2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    gate_and_eval gates p hp hop a b hin ha hb (e2 q.1 q.2), Bool.and_eq_false_iff]
  tauto

lemma gate_S1_or (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hop : (gates[p]).op = GateOp.or) (a b : ℕ) (hin : (gates[p]).inputs = [a, b])
    (ha : a < 13 + p) (hb : b < 13 + p) :
    S1 gates (13 + p) = S1 gates a ∪ S1 gates b := by
  ext v
  simp [S1, gate_or_eval gates p hp hop a b hin ha hb (e1 v)]

lemma gate_N2_or (gates : List Gate) (p : ℕ) (hp : p < gates.length)
    (hop : (gates[p]).op = GateOp.or) (a b : ℕ) (hin : (gates[p]).inputs = [a, b])
    (ha : a < 13 + p) (hb : b < 13 + p) :
    N2 gates (13 + p) = N2 gates a ∩ N2 gates b := by
  ext q
  simp only [N2, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    gate_or_eval gates p hp hop a b hin ha hb (e2 q.1 q.2), Bool.or_eq_false_iff]
  tauto

lemma and_clean_one_sub (gates : List Gate) (hm : Mono2 gates) (L : Finset (Fin 13))
    (p : ℕ) (hp : p < gates.length) (hop : (gates[p]).op = GateOp.and)
    (a b : ℕ) (hin : (gates[p]).inputs = [a, b]) (ha : a < 13 + p) (hb : b < 13 + p)
    (hsub : S1 gates (13 + p) ⊆ L) (hclean : pairSet L ⊆ N2 gates (13 + p)) :
    S1 gates a ⊆ L ∨ S1 gates b ⊆ L := by
  by_contra h
  push Not at h
  obtain ⟨u, hua, huL⟩ := Finset.not_subset.mp h.1
  obtain ⟨v, hvb, hvL⟩ := Finset.not_subset.mp h.2
  have huv : u ≠ v := by
    intro heq
    subst heq
    have hmem : u ∈ S1 gates (13 + p) := by
      rw [gate_S1_and gates p hp hop a b hin ha hb]
      exact Finset.mem_inter.mpr ⟨hua, hvb⟩
    exact huL (hsub hmem)
  have hua' : val gates (e1 u) a = true := (Finset.mem_filter.mp hua).2
  have hvb' : val gates (e1 v) b = true := (Finset.mem_filter.mp hvb).2
  rcases lt_or_gt_of_ne huv with hlt | hlt
  · have hmem : (u, v) ∈ N2 gates (13 + p) :=
      hclean (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, huL, hvL⟩)
    have hfalse : val gates (e2 u v) (13 + p) = false := (Finset.mem_filter.mp hmem).2.2
    have ha2 : val gates (e2 u v) a = true := val_mono gates hm (e1 u) (e2 u v) (by
      intro i hi; simp only [e1, decide_eq_true_eq] at hi; simp [e2, hi]) a hua'
    have hb2 : val gates (e2 u v) b = true := val_mono gates hm (e1 v) (e2 u v) (by
      intro i hi; simp only [e1, decide_eq_true_eq] at hi; simp [e2, hi]) b hvb'
    rw [gate_and_eval gates p hp hop a b hin ha hb (e2 u v), ha2, hb2] at hfalse
    cases hfalse
  · have hmem : (v, u) ∈ N2 gates (13 + p) :=
      hclean (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hvL, huL⟩)
    have hfalse : val gates (e2 v u) (13 + p) = false := (Finset.mem_filter.mp hmem).2.2
    have ha2 : val gates (e2 v u) a = true := val_mono gates hm (e1 u) (e2 v u) (by
      intro i hi; simp only [e1, decide_eq_true_eq] at hi; simp [e2, hi]) a hua'
    have hb2 : val gates (e2 v u) b = true := val_mono gates hm (e1 v) (e2 v u) (by
      intro i hi; simp only [e1, decide_eq_true_eq] at hi; simp [e2, hi]) b hvb'
    rw [gate_and_eval gates p hp hop a b hin ha hb (e2 v u), ha2, hb2] at hfalse
    cases hfalse

lemma gate_copy_or_binary (gates : List Gate) (hm : Mono2 gates) (p : ℕ) (hp : p < gates.length)
    (hne0 : (S1 gates (13 + p)).card ≠ 0) (hne13 : (S1 gates (13 + p)).card ≠ 13) :
    (∃ c < 13 + p, ∀ x : Fin 13 → Bool, val gates x (13 + p) = val gates x c) ∨
    (∃ a b : ℕ, (gates[p]).inputs = [a, b] ∧ a < 13 + p ∧ b < 13 + p) := by
  have hg := hm (gates[p]) (List.getElem_mem hp)
  cases hlen : (gates[p]).inputs with
  | nil =>
    exfalso
    rcases hg.1 with hop | hop
    · apply hne13
      have hall : S1 gates (13 + p) = Finset.univ := by
        ext v
        simp [S1, val_gate gates (e1 v) p hp, hop, hlen, GateOp.eval]
      rw [hall]
      simp
    · apply hne0
      have hemp : S1 gates (13 + p) = ∅ := by
        ext v
        simp [S1, val_gate gates (e1 v) p hp, hop, hlen, GateOp.eval]
      rw [hemp]
      simp
  | cons a rest =>
    cases rest with
    | nil =>
      by_cases ha : a < 13 + p
      · left
        refine ⟨a, ha, fun x => ?_⟩
        rw [val_gate gates x p hp, hlen]
        rcases hg.1 with hop | hop <;> simp [hop, GateOp.eval, ha]
      · exfalso
        apply hne0
        have hemp : S1 gates (13 + p) = ∅ := by
          ext v
          simp only [Finset.notMem_empty, iff_false, S1, Finset.mem_filter, Finset.mem_univ,
            true_and, val_gate gates (e1 v) p hp, hlen]
          rcases hg.1 with hop | hop <;> simp [hop, GateOp.eval, ha]
        rw [hemp]
        simp
    | cons b rest2 =>
      cases rest2 with
      | nil =>
        by_cases ha : a < 13 + p
        · by_cases hb : b < 13 + p
          · exact Or.inr ⟨a, b, rfl, ha, hb⟩
          · rcases hg.1 with hop | hop
            · exfalso
              apply hne0
              have hemp : S1 gates (13 + p) = ∅ := by
                ext v
                simp [S1, val_gate gates (e1 v) p hp, hop, hlen, ha, hb, GateOp.eval]
              rw [hemp]; simp
            · left
              refine ⟨a, ha, fun x => ?_⟩
              rw [val_gate gates x p hp, hop, hlen]
              simp [GateOp.eval, ha, hb]
        · rcases hg.1 with hop | hop
          · exfalso
            apply hne0
            have hemp : S1 gates (13 + p) = ∅ := by
              ext v
              simp [S1, val_gate gates (e1 v) p hp, hop, hlen, ha, GateOp.eval]
            rw [hemp]; simp
          · by_cases hb : b < 13 + p
            · left
              refine ⟨b, hb, fun x => ?_⟩
              rw [val_gate gates x p hp, hop, hlen]
              simp [GateOp.eval, ha, hb]
            · exfalso
              apply hne0
              have hemp : S1 gates (13 + p) = ∅ := by
                ext v
                simp [S1, val_gate gates (e1 v) p hp, hop, hlen, ha, hb, GateOp.eval]
              rw [hemp]; simp
      | cons _ _ =>
        exfalso
        have := hg.2
        rw [hlen] at this
        simp at this

lemma wire_ge_13_of_card (gates : List Gate) (k : ℕ) (h2 : 2 ≤ (S1 gates k).card) : 13 ≤ k := by
  by_contra h
  have hlt : k < 13 := by omega
  rw [S1_input gates k hlt, Finset.card_singleton] at h2
  omega

lemma exists_cover (gates : List Gate) (hm : Mono2 gates) (w : Fin 13)
    (pstar pa : Fin gates.length)
    (hnoSub : ∀ r : Fin gates.length, r ≠ pa → r ≠ pstar →
      ¬ (S1 gates (13 + r.val) ⊆ line w ∧ 2 ≤ (S1 gates (13 + r.val)).card))
    (hpa_and : (gates[pa.val]).op = GateOp.and)
    (hpstar_and : (gates[pstar.val]).op = GateOp.and) :
    ∀ k : ℕ, k ≤ 13 + pstar.val → line w ⊆ S1 gates k →
      ∃ O : Finset (Fin gates.length),
        (∀ r ∈ O, r ≠ pa ∧ r ≠ pstar ∧ line w ⊂ S1 gates (13 + r.val)) ∧
        pairSet (line w) ∩ N2 gates k ⊆
          O.biUnion (fun r => pairSet (line w) ∩ N2 gates (13 + r.val)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkle hsub
    have hcard4 : 4 ≤ (S1 gates k).card := by
      have := Finset.card_le_card hsub
      rw [line_card w] at this
      exact this
    have hk13 : 13 ≤ k := wire_ge_13_of_card gates k (by omega)
    obtain ⟨p, rfl⟩ : ∃ p, k = 13 + p := ⟨k - 13, by omega⟩
    have hp : p < gates.length := by omega
    have hg := hm (gates[p]) (List.getElem_mem hp)
    cases hlen : (gates[p]).inputs with
    | nil =>
      rcases hg.1 with hop | hop
      · refine ⟨∅, by simp, ?_⟩
        intro q hq
        exfalso
        have hfalse : val gates (e2 q.1 q.2) (13 + p) = false :=
          (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2.2
        rw [val_gate gates (e2 q.1 q.2) p hp, hop, hlen] at hfalse
        simp [GateOp.eval] at hfalse
      · exfalso
        have hemp : S1 gates (13 + p) = ∅ := by
          ext v
          simp [S1, val_gate gates (e1 v) p hp, hop, hlen, GateOp.eval]
        rw [hemp] at hcard4
        simp at hcard4
    | cons a rest =>
      cases rest with
      | nil =>
        by_cases ha : a < 13 + p
        · have heq : ∀ x : Fin 13 → Bool, val gates x (13 + p) = val gates x a := by
            intro x
            rw [val_gate gates x p hp, hlen]
            rcases hg.1 with hop | hop <;> simp [hop, GateOp.eval, ha]
          have hS : S1 gates a = S1 gates (13 + p) := by ext v; simp [S1, heq]
          have hN : N2 gates a = N2 gates (13 + p) := by ext q; simp [N2, heq]
          rw [← hS] at hsub
          rw [← hN]
          exact ih a ha (by omega) hsub
        · exfalso
          have hemp : S1 gates (13 + p) = ∅ := by
            ext v
            simp only [Finset.notMem_empty, iff_false, S1, Finset.mem_filter, Finset.mem_univ,
              true_and, val_gate gates (e1 v) p hp, hlen]
            rcases hg.1 with hop | hop <;> simp [hop, GateOp.eval, ha]
          rw [hemp] at hcard4
          simp at hcard4
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          rcases hg.1 with hop | hop
          · by_cases ha : a < 13 + p
            · by_cases hb : b < 13 + p
              · rw [gate_S1_and gates p hp hop a b hlen ha hb] at hsub
                rw [gate_N2_and gates p hp hop a b hlen ha hb]
                obtain ⟨Oa, hOa1, hOa2⟩ := ih a ha (by omega)
                  (Finset.Subset.trans hsub Finset.inter_subset_left)
                obtain ⟨Ob, hOb1, hOb2⟩ := ih b hb (by omega)
                  (Finset.Subset.trans hsub Finset.inter_subset_right)
                refine ⟨Oa ∪ Ob, ?_, ?_⟩
                · intro r hr
                  rcases Finset.mem_union.mp hr with hr | hr
                  · exact hOa1 r hr
                  · exact hOb1 r hr
                · intro q hq
                  rw [Finset.inter_union_distrib_left] at hq
                  rw [Finset.union_biUnion]
                  rcases Finset.mem_union.mp hq with hq | hq
                  · exact Finset.mem_union_left _ (hOa2 hq)
                  · exact Finset.mem_union_right _ (hOb2 hq)
              · exfalso
                have hemp : S1 gates (13 + p) = ∅ := by
                  ext v
                  simp [S1, val_gate gates (e1 v) p hp, hop, hlen, ha, hb, GateOp.eval]
                rw [hemp] at hcard4
                simp at hcard4
            · exfalso
              have hemp : S1 gates (13 + p) = ∅ := by
                ext v
                simp [S1, val_gate gates (e1 v) p hp, hop, hlen, ha, GateOp.eval]
              rw [hemp] at hcard4
              simp at hcard4
          · let r : Fin gates.length := ⟨p, hp⟩
            have hrpa : r ≠ pa := by
              intro e
              have hev : p = pa.val := congrArg Fin.val e
              have : (gates[p]).op = (gates[pa.val]).op := by
                simp only [hev]
              rw [hop, hpa_and] at this
              cases this
            have hrpstar : r ≠ pstar := by
              intro e
              have hev : p = pstar.val := congrArg Fin.val e
              have : (gates[p]).op = (gates[pstar.val]).op := by
                simp only [hev]
              rw [hop, hpstar_and] at this
              cases this
            have hss : line w ⊂ S1 gates (13 + r.val) := by
              refine ⟨hsub, ?_⟩
              intro hrev
              exact hnoSub r hrpa hrpstar ⟨hrev, by dsimp [r]; omega⟩
            refine ⟨{r}, ?_, ?_⟩
            · intro r' hr'
              rw [Finset.mem_singleton.mp hr']
              exact ⟨hrpa, hrpstar, hss⟩
            · simp [r]
        | cons _ _ =>
          exfalso
          have := hg.2
          rw [hlen] at this
          simp at this

lemma sum_three_gates (gates : List Gate) (w : Fin 13) (p1 p2 p3 : Fin gates.length)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hc1 : credit (S1 gates (13 + p1.val)) w = 36)
    (hc2 : credit (S1 gates (13 + p2.val)) w = 36)
    (hc3 : credit (S1 gates (13 + p3.val)) w = 36) :
    108 ≤ ∑ p : Fin gates.length, credit (S1 gates (13 + p.val)) w := by
  have hsub : ({p1, p2, p3} : Finset (Fin gates.length)) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset (f := fun p : Fin gates.length =>
    credit (S1 gates (13 + p.val)) w) hsub
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton, hc1, hc2, hc3] at hle
  omega

lemma credit_sub_line (S : Finset (Fin 13)) (w : Fin 13) (hsub : S ⊆ line w) (h2 : 2 ≤ S.card) :
    credit S w = 36 := by
  unfold credit
  simp [hsub, h2]

lemma line_credit_ge (gates : List Gate) (hm : Mono2 gates) (w : Fin 13)
    (outw : ℕ)
    (hvalid_out : S1 gates outw = line w ∧ pairSet (line w) ⊆ N2 gates outw) :
    108 ≤ ∑ p : Fin gates.length, credit (S1 gates (13 + p.val)) w := by
  classical
  have hex : ∃ p : ℕ, p < gates.length ∧
      S1 gates (13 + p) = line w ∧ pairSet (line w) ⊆ N2 gates (13 + p) := by
    have hcard : (S1 gates outw).card = 4 := by rw [hvalid_out.1, line_card w]
    have hge13 : 13 ≤ outw := wire_ge_13_of_card gates outw (by omega)
    have hlt : outw < 13 + gates.length := by
      by_contra h
      have hemp := S1_beyond gates outw (by omega)
      rw [hemp] at hcard
      simp at hcard
    exact ⟨outw - 13, by omega, by simpa [show 13 + (outw - 13) = outw by omega] using hvalid_out⟩
  let pstarNat := Nat.find hex
  have hpstar_spec := Nat.find_spec hex
  have hpstar_min : ∀ p' < pstarNat,
      ¬ (p' < gates.length ∧ S1 gates (13 + p') = line w ∧ pairSet (line w) ⊆ N2 gates (13 + p')) :=
    fun p' hp' => Nat.find_min hex hp'
  let pstar : Fin gates.length := ⟨pstarNat, hpstar_spec.1⟩
  have hSstar : S1 gates (13 + pstar.val) = line w := hpstar_spec.2.1
  have hNstar : pairSet (line w) ⊆ N2 gates (13 + pstar.val) := hpstar_spec.2.2
  have hcard_star : (S1 gates (13 + pstar.val)).card = 4 := by rw [hSstar, line_card w]
  have hc_star : credit (S1 gates (13 + pstar.val)) w = 36 :=
    credit_sub_line _ w (by rw [hSstar]) (by omega)
  rcases gate_copy_or_binary gates hm pstar.val pstar.isLt (by omega) (by omega) with
      ⟨c, hc_lt, hc_eq⟩ | ⟨a, b, hin, ha, hb⟩
  · exfalso
    have hSc : S1 gates c = line w := by
      rw [← hSstar]
      ext v; simp [S1, hc_eq]
    have hNc : N2 gates c = N2 gates (13 + pstar.val) := by
      ext q; simp [N2, hc_eq]
    have hc13 : 13 ≤ c := wire_ge_13_of_card gates c (by rw [hSc, line_card w]; omega)
    exact hpstar_min (c - 13) (by dsimp [pstar] at hc_lt; omega)
      ⟨by omega, by simpa [show 13 + (c - 13) = c by omega] using hSc,
        by simpa [show 13 + (c - 13) = c by omega, hNc] using hNstar⟩
  · have hg := hm (gates[pstar.val]) (List.getElem_mem pstar.isLt)
    rcases hg.1 with hop | hop
    · have hS_and : S1 gates (13 + pstar.val) = S1 gates a ∩ S1 gates b :=
        gate_S1_and gates pstar.val pstar.isLt hop a b hin ha hb
      have hsub_one : S1 gates a ⊆ line w ∨ S1 gates b ⊆ line w :=
        and_clean_one_sub gates hm (line w) pstar.val pstar.isLt hop a b hin ha hb
          (by rw [hSstar]) hNstar
      have hex_pa : ∃ pa : Fin gates.length, pa.val < pstar.val ∧
          S1 gates (13 + pa.val) = line w := by
        rcases hsub_one with hsubA | hsubB
        · have hSa : S1 gates a = line w := by
            apply Finset.Subset.antisymm hsubA
            rw [← hSstar, hS_and]
            exact Finset.inter_subset_left
          have ha13 : 13 ≤ a := wire_ge_13_of_card gates a (by rw [hSa, line_card w]; omega)
          exact ⟨⟨a - 13, by omega⟩, by dsimp; omega, by simpa [show 13 + (a - 13) = a by omega] using hSa⟩
        · have hSb : S1 gates b = line w := by
            apply Finset.Subset.antisymm hsubB
            rw [← hSstar, hS_and]
            exact Finset.inter_subset_right
          have hb13 : 13 ≤ b := wire_ge_13_of_card gates b (by rw [hSb, line_card w]; omega)
          exact ⟨⟨b - 13, by omega⟩, by dsimp; omega, by simpa [show 13 + (b - 13) = b by omega] using hSb⟩
      obtain ⟨pa, hpa_lt, hSpa⟩ := hex_pa
      have hpa_ne : pa ≠ pstar := fun e => by rw [e] at hpa_lt; omega
      have hc_pa : credit (S1 gates (13 + pa.val)) w = 36 :=
        credit_sub_line _ w (by rw [hSpa]) (by rw [hSpa, line_card w]; omega)
      by_cases hother : ∃ r : Fin gates.length, r ≠ pa ∧ r ≠ pstar ∧
          S1 gates (13 + r.val) ⊆ line w ∧ 2 ≤ (S1 gates (13 + r.val)).card
      · obtain ⟨r, hrpa, hrps, hrsub, hr2⟩ := hother
        exact sum_three_gates gates w r pa pstar hrpa hrps hpa_ne
          (credit_sub_line _ w hrsub hr2) hc_pa hc_star
      · have hnoSub : ∀ r : Fin gates.length, r ≠ pa → r ≠ pstar →
            ¬ (S1 gates (13 + r.val) ⊆ line w ∧ 2 ≤ (S1 gates (13 + r.val)).card) := by
          intro r hr1 hr2 h
          exact hother ⟨r, hr1, hr2, h.1, h.2⟩
        have hpa_and : (gates[pa.val]).op = GateOp.and := by
          have hcard_pa : (S1 gates (13 + pa.val)).card = 4 := by rw [hSpa, line_card w]
          rcases gate_copy_or_binary gates hm pa.val pa.isLt (by omega) (by omega) with
              ⟨c, hc_lt, hc_eq⟩ | ⟨ca, cb, hinc, hca, hcb⟩
          · exfalso
            have hSc : S1 gates c = line w := by
              rw [← hSpa]; ext v; simp [S1, hc_eq]
            have hc13 : 13 ≤ c := wire_ge_13_of_card gates c (by rw [hSc, line_card w]; omega)
            let r : Fin gates.length := ⟨c - 13, by omega⟩
            exact hnoSub r (by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega)
              (by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega)
              ⟨by simpa [r, show 13 + (c - 13) = c by omega] using hSc.subset,
               by simp [r, show 13 + (c - 13) = c by omega, hSc, line_card w]⟩
          · have hgpa := hm (gates[pa.val]) (List.getElem_mem pa.isLt)
            rcases hgpa.1 with hpaop | hpaop
            · exact hpaop
            · exfalso
              have hSor := gate_S1_or gates pa.val pa.isLt hpaop ca cb hinc hca hcb
              rw [hSpa] at hSor
              have hsum_card : 4 ≤ (S1 gates ca).card + (S1 gates cb).card := by
                have := Finset.card_union_le (S1 gates ca) (S1 gates cb)
                rw [← hSor, line_card w] at this
                exact this
              have hsubA : S1 gates ca ⊆ line w := by rw [hSor]; exact Finset.subset_union_left
              have hsubB : S1 gates cb ⊆ line w := by rw [hSor]; exact Finset.subset_union_right
              by_cases h2a : 2 ≤ (S1 gates ca).card
              · have hca13 : 13 ≤ ca := wire_ge_13_of_card gates ca h2a
                let r : Fin gates.length := ⟨ca - 13, by omega⟩
                exact hnoSub r (by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega)
                  (by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega)
                  ⟨by simpa [r, show 13 + (ca - 13) = ca by omega] using hsubA,
                   by simpa [r, show 13 + (ca - 13) = ca by omega] using h2a⟩
              · have h2b : 2 ≤ (S1 gates cb).card := by omega
                have hcb13 : 13 ≤ cb := wire_ge_13_of_card gates cb h2b
                let r : Fin gates.length := ⟨cb - 13, by omega⟩
                exact hnoSub r (by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega)
                  (by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega)
                  ⟨by simpa [r, show 13 + (cb - 13) = cb by omega] using hsubB,
                   by simpa [r, show 13 + (cb - 13) = cb by omega] using h2b⟩
        obtain ⟨O, hO1, hO2⟩ := exists_cover gates hm w pstar pa hnoSub hpa_and hop
          (13 + pstar.val) le_rfl (by rw [hSstar])
        have hcov : pairSet (line w) ⊆
            O.biUnion (fun r => pairSet (line w) ∩ N2 gates (13 + r.val)) := by
          have hrew : pairSet (line w) ⊆ pairSet (line w) ∩ N2 gates (13 + pstar.val) :=
            Finset.subset_inter (Finset.Subset.refl _) hNstar
          exact Finset.Subset.trans hrew hO2
        have h36 : 36 ≤ ∑ r ∈ O, credit (S1 gates (13 + r.val)) w := by
          calc
            36 = (pairSet (line w)).card := (pairSet_line_card w).symm
            _ ≤ (O.biUnion (fun r => pairSet (line w) ∩ N2 gates (13 + r.val))).card :=
                Finset.card_le_card hcov
            _ ≤ ∑ r ∈ O, (pairSet (line w) ∩ N2 gates (13 + r.val)).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ r ∈ O, credit (S1 gates (13 + r.val)) w := by
                apply Finset.sum_le_sum
                intro r hr
                have hle1 : (pairSet (line w) ∩ N2 gates (13 + r.val)).card ≤
                    (pairSet (S1 gates (13 + r.val))).card := by
                  apply Finset.card_le_card
                  exact Finset.Subset.trans Finset.inter_subset_right
                    (N2_sub_pairSet gates hm (13 + r.val))
                exact le_trans hle1 (pairSet_le_supCredit _ w (hO1 r hr).2.2)
        have hpa_notO : pa ∉ O := fun h => (hO1 pa h).1 rfl
        have hpstar_notO : pstar ∉ O := fun h => (hO1 pstar h).2.1 rfl
        have hsub_all : insert pa (insert pstar O) ⊆ Finset.univ := Finset.subset_univ _
        have hsum_le := Finset.sum_le_sum_of_subset (f := fun p : Fin gates.length =>
          credit (S1 gates (13 + p.val)) w) hsub_all
        rw [Finset.sum_insert (by simp [hpa_ne, hpa_notO]),
          Finset.sum_insert hpstar_notO, hc_pa, hc_star] at hsum_le
        omega
    · have hSor := gate_S1_or gates pstar.val pstar.isLt hop a b hin ha hb
      have hNor := gate_N2_or gates pstar.val pstar.isLt hop a b hin ha hb
      rw [hSstar] at hSor
      rw [hNor] at hNstar
      have hsubA : S1 gates a ⊆ line w := by rw [hSor]; exact Finset.subset_union_left
      have hsubB : S1 gates b ⊆ line w := by rw [hSor]; exact Finset.subset_union_right
      have hNA : pairSet (line w) ⊆ N2 gates a :=
        Finset.Subset.trans hNstar Finset.inter_subset_left
      have hNB : pairSet (line w) ⊆ N2 gates b :=
        Finset.Subset.trans hNstar Finset.inter_subset_right
      have hlt4A : (S1 gates a).card < 4 := by
        by_contra h
        have h4 : (S1 gates a).card = 4 := by
          have := Finset.card_le_card hsubA
          rw [line_card w] at this
          omega
        have hSa : S1 gates a = line w := Finset.eq_of_subset_of_card_le hsubA (by rw [line_card w, h4])
        have ha13 : 13 ≤ a := wire_ge_13_of_card gates a (by omega)
        exact hpstar_min (a - 13) (by dsimp [pstar] at ha; omega)
          ⟨by omega, by simpa [show 13 + (a - 13) = a by omega] using hSa,
            by simpa [show 13 + (a - 13) = a by omega] using hNA⟩
      have hlt4B : (S1 gates b).card < 4 := by
        by_contra h
        have h4 : (S1 gates b).card = 4 := by
          have := Finset.card_le_card hsubB
          rw [line_card w] at this
          omega
        have hSb : S1 gates b = line w := Finset.eq_of_subset_of_card_le hsubB (by rw [line_card w, h4])
        have hb13 : 13 ≤ b := wire_ge_13_of_card gates b (by omega)
        exact hpstar_min (b - 13) (by dsimp [pstar] at hb; omega)
          ⟨by omega, by simpa [show 13 + (b - 13) = b by omega] using hSb,
            by simpa [show 13 + (b - 13) = b by omega] using hNB⟩
      have hsum_card : 4 ≤ (S1 gates a).card + (S1 gates b).card := by
        have := Finset.card_union_le (S1 gates a) (S1 gates b)
        rw [← hSor, line_card w] at this
        exact this
      by_cases hboth2 : 2 ≤ (S1 gates a).card ∧ 2 ≤ (S1 gates b).card
      · have hab : a ≠ b := by
          intro e
          subst e
          rw [Finset.union_idempotent] at hSor
          have := congrArg Finset.card hSor
          rw [line_card w] at this
          omega
        have ha13 : 13 ≤ a := wire_ge_13_of_card gates a hboth2.1
        have hb13 : 13 ≤ b := wire_ge_13_of_card gates b hboth2.2
        let pa : Fin gates.length := ⟨a - 13, by omega⟩
        let pb : Fin gates.length := ⟨b - 13, by omega⟩
        have hpa_pb : pa ≠ pb := by intro e; have := congrArg Fin.val e; dsimp [pa, pb] at this; omega
        have hpa_ps : pa ≠ pstar := by intro e; have := congrArg Fin.val e; dsimp [pa] at this; omega
        have hpb_ps : pb ≠ pstar := by intro e; have := congrArg Fin.val e; dsimp [pb] at this; omega
        exact sum_three_gates gates w pa pb pstar hpa_pb hpa_ps hpb_ps
          (credit_sub_line _ w (by simpa [pa, show 13 + (a - 13) = a by omega] using hsubA)
            (by simpa [pa, show 13 + (a - 13) = a by omega] using hboth2.1))
          (credit_sub_line _ w (by simpa [pb, show 13 + (b - 13) = b by omega] using hsubB)
            (by simpa [pb, show 13 + (b - 13) = b by omega] using hboth2.2))
          hc_star
      · have hex3 : ∃ q : ℕ, q < pstar.val ∧ S1 gates (13 + q) ⊆ line w ∧
            (S1 gates (13 + q)).card = 3 ∧ pairSet (line w) ⊆ N2 gates (13 + q) := by
          by_cases h3a : (S1 gates a).card = 3
          · have ha13 : 13 ≤ a := wire_ge_13_of_card gates a (by omega)
            exact ⟨a - 13, by omega,
              by simpa [show 13 + (a - 13) = a by omega] using hsubA,
              by simpa [show 13 + (a - 13) = a by omega] using h3a,
              by simpa [show 13 + (a - 13) = a by omega] using hNA⟩
          · have h3b : (S1 gates b).card = 3 := by omega
            have hb13 : 13 ≤ b := wire_ge_13_of_card gates b (by omega)
            exact ⟨b - 13, by omega,
              by simpa [show 13 + (b - 13) = b by omega] using hsubB,
              by simpa [show 13 + (b - 13) = b by omega] using h3b,
              by simpa [show 13 + (b - 13) = b by omega] using hNB⟩
        let qNat := Nat.find hex3
        have hq_spec := Nat.find_spec hex3
        have hq_min : ∀ q' < qNat, ¬ (q' < pstar.val ∧ S1 gates (13 + q') ⊆ line w ∧
            (S1 gates (13 + q')).card = 3 ∧ pairSet (line w) ⊆ N2 gates (13 + q')) :=
          fun q' hq' => Nat.find_min hex3 hq'
        let q : Fin gates.length := ⟨qNat, by omega⟩
        have hq_lt : q.val < pstar.val := hq_spec.1
        have hq_sub : S1 gates (13 + q.val) ⊆ line w := hq_spec.2.1
        have hq_card : (S1 gates (13 + q.val)).card = 3 := hq_spec.2.2.1
        have hq_N : pairSet (line w) ⊆ N2 gates (13 + q.val) := hq_spec.2.2.2
        have hc_q : credit (S1 gates (13 + q.val)) w = 36 :=
          credit_sub_line _ w hq_sub (by omega)
        have hq_ne : q ≠ pstar := by intro e; rw [e] at hq_lt; omega
        rcases gate_copy_or_binary gates hm q.val q.isLt (by omega) (by omega) with
            ⟨c, hc_lt, hc_eq⟩ | ⟨ca, cb, hinc, hca, hcb⟩
        · exfalso
          have hSc : S1 gates c = S1 gates (13 + q.val) := by ext v; simp [S1, hc_eq]
          have hNc : N2 gates c = N2 gates (13 + q.val) := by ext p; simp [N2, hc_eq]
          have hc13 : 13 ≤ c := wire_ge_13_of_card gates c (by rw [hSc]; omega)
          exact hq_min (c - 13) (by dsimp [q] at hc_lt; omega)
            ⟨by omega, by simpa [show 13 + (c - 13) = c by omega, hSc] using hq_sub,
             by simpa [show 13 + (c - 13) = c by omega, hSc] using hq_card,
             by simpa [show 13 + (c - 13) = c by omega, hNc] using hq_N⟩
        · have hgq := hm (gates[q.val]) (List.getElem_mem q.isLt)
          rcases hgq.1 with hqop | hqop
          · have hSand := gate_S1_and gates q.val q.isLt hqop ca cb hinc hca hcb
            have hsub1 := and_clean_one_sub gates hm (line w) q.val q.isLt hqop ca cb hinc hca hcb
              hq_sub hq_N
            rcases hsub1 with hsubca | hsubcb
            · have hle : S1 gates (13 + q.val) ⊆ S1 gates ca := by
                rw [hSand]; exact Finset.inter_subset_left
              have hcard_ca : 3 ≤ (S1 gates ca).card := by
                have := Finset.card_le_card hle; omega
              have hca13 : 13 ≤ ca := wire_ge_13_of_card gates ca (by omega)
              let r : Fin gates.length := ⟨ca - 13, by omega⟩
              have hr_q : r ≠ q := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              have hr_ps : r ≠ pstar := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              exact sum_three_gates gates w r q pstar hr_q hr_ps hq_ne
                (credit_sub_line _ w (by simpa [r, show 13 + (ca - 13) = ca by omega] using hsubca)
                  (by simpa [r, show 13 + (ca - 13) = ca by omega] using (by omega : 2 ≤ (S1 gates ca).card)))
                hc_q hc_star
            · have hle : S1 gates (13 + q.val) ⊆ S1 gates cb := by
                rw [hSand]; exact Finset.inter_subset_right
              have hcard_cb : 3 ≤ (S1 gates cb).card := by
                have := Finset.card_le_card hle; omega
              have hcb13 : 13 ≤ cb := wire_ge_13_of_card gates cb (by omega)
              let r : Fin gates.length := ⟨cb - 13, by omega⟩
              have hr_q : r ≠ q := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              have hr_ps : r ≠ pstar := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              exact sum_three_gates gates w r q pstar hr_q hr_ps hq_ne
                (credit_sub_line _ w (by simpa [r, show 13 + (cb - 13) = cb by omega] using hsubcb)
                  (by simpa [r, show 13 + (cb - 13) = cb by omega] using (by omega : 2 ≤ (S1 gates cb).card)))
                hc_q hc_star
          · have hSorq := gate_S1_or gates q.val q.isLt hqop ca cb hinc hca hcb
            have hNorq := gate_N2_or gates q.val q.isLt hqop ca cb hinc hca hcb
            have hsubca : S1 gates ca ⊆ line w :=
              Finset.Subset.trans (by rw [hSorq]; exact Finset.subset_union_left) hq_sub
            have hsubcb : S1 gates cb ⊆ line w :=
              Finset.Subset.trans (by rw [hSorq]; exact Finset.subset_union_right) hq_sub
            have hNca : pairSet (line w) ⊆ N2 gates ca :=
              Finset.Subset.trans hq_N (by rw [hNorq]; exact Finset.inter_subset_left)
            have hNcb : pairSet (line w) ⊆ N2 gates cb :=
              Finset.Subset.trans hq_N (by rw [hNorq]; exact Finset.inter_subset_right)
            have hsum3 : 3 ≤ (S1 gates ca).card + (S1 gates cb).card := by
              have := Finset.card_union_le (S1 gates ca) (S1 gates cb)
              rw [← hSorq, hq_card] at this
              exact this
            by_cases h2a : 2 ≤ (S1 gates ca).card
            · have hca13 : 13 ≤ ca := wire_ge_13_of_card gates ca h2a
              let r : Fin gates.length := ⟨ca - 13, by omega⟩
              have hr_q : r ≠ q := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              have hr_ps : r ≠ pstar := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              exact sum_three_gates gates w r q pstar hr_q hr_ps hq_ne
                (credit_sub_line _ w (by simpa [r, show 13 + (ca - 13) = ca by omega] using hsubca)
                  (by simpa [r, show 13 + (ca - 13) = ca by omega] using h2a))
                hc_q hc_star
            · have h2b : 2 ≤ (S1 gates cb).card := by omega
              have hcb13 : 13 ≤ cb := wire_ge_13_of_card gates cb h2b
              let r : Fin gates.length := ⟨cb - 13, by omega⟩
              have hr_q : r ≠ q := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              have hr_ps : r ≠ pstar := by intro e; have := congrArg Fin.val e; dsimp [r] at this; omega
              exact sum_three_gates gates w r q pstar hr_q hr_ps hq_ne
                (credit_sub_line _ w (by simpa [r, show 13 + (cb - 13) = cb by omega] using hsubcb)
                  (by simpa [r, show 13 + (cb - 13) = cb by omega] using h2b))
                hc_q hc_star

end PEqualNP.Outside.L_meta_667

theorem PEqualNP.Outside.L_meta_667 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 13) (x : Fin 13 → Bool), (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) → 39 ≤ gates.length := by
  intro gates out hm hev
  have hline : ∀ w : Fin 13,
      108 ≤ ∑ p : Fin gates.length,
        PEqualNP.Outside.L_meta_667.credit
          (PEqualNP.Outside.L_meta_667.S1 gates (13 + p.val)) w := by
    intro w
    apply PEqualNP.Outside.L_meta_667.line_credit_ge gates hm w (out w)
    constructor
    · ext v
      simp only [PEqualNP.Outside.L_meta_667.S1, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hev w (PEqualNP.Outside.L_meta_667.e1 v) (PEqualNP.Outside.L_meta_667.e1_light v)
      change PEqualNP.Outside.L_meta_667.val gates (PEqualNP.Outside.L_meta_667.e1 v) (out w) =
        decide (∃ u ∈ PEqualNP.Outside.L_meta_667.line w,
          PEqualNP.Outside.L_meta_667.e1 v u = true) at h1
      rw [h1]
      simp [PEqualNP.Outside.L_meta_667.e1]
    · intro p hp
      simp only [PEqualNP.Outside.L_meta_667.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp
      simp only [PEqualNP.Outside.L_meta_667.N2, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hp.1, ?_⟩
      have h2 := hev w (PEqualNP.Outside.L_meta_667.e2 p.1 p.2)
        (PEqualNP.Outside.L_meta_667.e2_light p.1 p.2)
      change PEqualNP.Outside.L_meta_667.val gates (PEqualNP.Outside.L_meta_667.e2 p.1 p.2) (out w) =
        decide (∃ u ∈ PEqualNP.Outside.L_meta_667.line w,
          PEqualNP.Outside.L_meta_667.e2 p.1 p.2 u = true) at h2
      rw [h2]
      simp only [decide_eq_false_iff_not, not_exists, not_and, PEqualNP.Outside.L_meta_667.e2,
        decide_eq_true_eq]
      intro u hu hor
      rcases hor with rfl | rfl
      · exact hp.2.1 hu
      · exact hp.2.2 hu
  have hlow : 13 * 108 ≤
      ∑ w : Fin 13, ∑ p : Fin gates.length,
        PEqualNP.Outside.L_meta_667.credit
          (PEqualNP.Outside.L_meta_667.S1 gates (13 + p.val)) w := by
    calc
      13 * 108 = ∑ _w : Fin 13, 108 := by simp
      _ ≤ ∑ w : Fin 13, ∑ p : Fin gates.length,
            PEqualNP.Outside.L_meta_667.credit
              (PEqualNP.Outside.L_meta_667.S1 gates (13 + p.val)) w :=
          Finset.sum_le_sum (fun w _ => hline w)
  have hhigh :
      ∑ w : Fin 13, ∑ p : Fin gates.length,
        PEqualNP.Outside.L_meta_667.credit
          (PEqualNP.Outside.L_meta_667.S1 gates (13 + p.val)) w ≤
      gates.length * 36 := by
    rw [Finset.sum_comm]
    calc
      ∑ p : Fin gates.length, ∑ w : Fin 13,
          PEqualNP.Outside.L_meta_667.credit
            (PEqualNP.Outside.L_meta_667.S1 gates (13 + p.val)) w
          ≤ ∑ _p : Fin gates.length, 36 :=
          Finset.sum_le_sum (fun p _ =>
            PEqualNP.Outside.L_meta_667.capacity _)
      _ = gates.length * 36 := by simp
  omega
