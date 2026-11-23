import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Elim

namespace PEqualNP.Outside.L_meta_659

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers

def JointG (n k : ℕ) (G : Fin k → (Fin n → Bool) → Bool) (t : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ t ∧ ∃ o : Fin k → ℕ,
    ∀ (x : Fin n → Bool) (j : Fin k), (C.wires (List.ofFn x)).getD (o j) false = G j x

def JointFG (n k : ℕ) (f : (Fin n → Bool) → Bool)
    (G : Fin k → (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∃ (o1 : ℕ) (o : Fin k → ℕ),
    ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD o1 false = f x ∧
      ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x

def statFix (n : ℕ) (i : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun j : Fin n => if j = i then Stat.const b else Stat.wire j.val)

lemma statFix_length (n : ℕ) (i : Fin n) (b : Bool) : (statFix n i b).length = n := by
  simp [statFix]

lemma statFix_getD_lt (n : ℕ) (i : Fin n) (b : Bool) (j : ℕ) (hj : j < n) :
    (statFix n i b).getD j (Stat.const false) =
      if (⟨j, hj⟩ : Fin n) = i then Stat.const b else Stat.wire j := by
  simp [statFix, hj]

lemma statFix_getD_self (n : ℕ) (i : Fin n) (b : Bool) :
    (statFix n i b).getD i.val (Stat.const false) = Stat.const b := by
  rw [statFix_getD_lt n i b i.val i.isLt]
  simp

lemma inv_statFix (n : ℕ) (i : Fin n) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y i b)) (statFix n i b, []) := by
  refine ⟨by simp [statFix], ?_⟩
  intro j
  by_cases hj : j < n
  · rw [statFix_getD_lt n i b j hj]
    have hget : (List.ofFn (Function.update y i b)).getD j false =
        Function.update y i b ⟨j, hj⟩ := by
      simp [hj]
    rw [hget]
    by_cases hji : (⟨j, hj⟩ : Fin n) = i
    · rw [if_pos hji, hji]
      simp [Stat.Valid, Stat.val]
    · rw [if_neg hji]
      refine ⟨by simpa [Stat.Valid] using hj, ?_⟩
      simp [Stat.val, wiresFrom, hj, Function.update_of_ne hji]
  · have h1 : (statFix n i b).getD j (Stat.const false) = Stat.const false :=
      List.getD_eq_default _ _ (by rw [statFix_length]; omega)
    have h2 : (List.ofFn (Function.update y i b)).getD j false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [h1, h2]
    exact ⟨trivial, rfl⟩

lemma supp_noread_gen {n : ℕ} (i : Fin n) (gs : List Gate) :
    ∀ L : List (Finset (Fin n)),
      (∀ g ∈ gs, i.val ∉ g.inputs) →
      (∀ j : ℕ, j ≠ i.val → i ∉ L.getD j ∅) →
      ∀ j : ℕ, j ≠ i.val → i ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]
      exact h j hj

lemma supp_noread2 {n : ℕ} (i : Fin n) (w1 : ℕ) (gs : List Gate) :
    ∀ L : List (Finset (Fin n)),
      (∀ g ∈ gs, i.val ∉ g.inputs ∧ w1 ∉ g.inputs) →
      (∀ j : ℕ, j ≠ i.val → j ≠ w1 → i ∉ L.getD j ∅) →
      ∀ j : ℕ, j ≠ i.val → j ≠ w1 → i ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj1 hj2
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      have hg := hno g List.mem_cons_self
      exact h a (fun e => hg.1 (e ▸ ha)) (fun e => hg.2 (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]
      exact h j hj1 hj2

lemma inputSupps_noread_gen {n : ℕ} (i : Fin n) :
    ∀ j : ℕ, j ≠ i.val → i ∉ (inputSupps n).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n
  · rw [inputSupps_getD n j hlt, Finset.mem_singleton]
    intro e
    exact hj (congrArg Fin.val e).symm
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]
    simp

lemma suppsFrom_append {n : ℕ} (g1 g2 : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (g1 ++ g2) L = suppsFrom g2 (suppsFrom g1 L) := by
  simp [suppsFrom, List.foldl_append]

lemma elim_append (n : ℕ) (g1 g2 : List Gate) (acc : List Stat × List Gate) :
    elim n (g1 ++ g2) acc = elim n g2 (elim n g1 acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have hstep : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [hstep, ih]
    simp [elimStep]
    omega

lemma suppsFrom_len {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; simp [suppsFrom]
  | cons g gs ih =>
    intro L
    have hstep : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [hstep, ih]
    simp
    omega

lemma list_split_first {α : Type} (p : α → Prop) [DecidablePred p] (l : List α)
    (h : ∃ x ∈ l, p x) :
    ∃ pre x post, l = pre ++ x :: post ∧ p x ∧ ∀ y ∈ pre, ¬ p y := by
  induction l with
  | nil => rcases h with ⟨_, hmem, _⟩; simp at hmem
  | cons a t ih =>
    by_cases ha : p a
    · exact ⟨[], a, t, rfl, ha, by simp⟩
    · have ht : ∃ x ∈ t, p x := by
        rcases h with ⟨x, hx, hpx⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact False.elim (ha hpx)
        · exact ⟨x, hx, hpx⟩
      obtain ⟨pre, x, post, hsplit, hpx, hpre⟩ := ih ht
      refine ⟨a :: pre, x, post, by simp [hsplit], hpx, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ha
      · exact hpre y hy

lemma simplify_kill_bit (g : Gate) (hnok : NOk g) (k : ℕ) (hk : k ∈ g.inputs) :
    ∃ b : Bool, ∀ (m : ℕ) (st : List Stat), st.getD k (Stat.const false) = Stat.const b →
      (simplify g.op m (g.inputs.map fun a => st.getD a (Stat.const false))).1 = none ∧
      ∃ c : Bool, (simplify g.op m (g.inputs.map fun a => st.getD a (Stat.const false))).2 =
        Stat.const c := by
  rcases hnok.1.1 with hop | hop | hop
  · refine ⟨false, fun m st hst => ?_⟩
    have hlen := hnok.1.2
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · rw [hin] at hk; simp at hk
    · rw [hin] at hk
      have ha : k = a := by simpa using hk
      subst ha
      rw [hop]
      simp only [List.map_cons, List.map_nil, hst]
      exact ⟨rfl, false, rfl⟩
    · rw [hin] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [hop]
        simp only [List.map_cons, List.map_nil, hst, simplify]
        cases hb : st.getD b (Stat.const false) with
        | const d => exact ⟨rfl, false && d, rfl⟩
        | wire j => exact ⟨rfl, false, rfl⟩
      · rw [hop]
        simp only [List.map_cons, List.map_nil, hst, simplify]
        cases ha : st.getD a (Stat.const false) with
        | const d => exact ⟨rfl, d && false, rfl⟩
        | wire j => exact ⟨rfl, false, rfl⟩
    · rw [hin] at hlen; simp at hlen
  · refine ⟨true, fun m st hst => ?_⟩
    have hlen := hnok.1.2
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · rw [hin] at hk; simp at hk
    · rw [hin] at hk
      have ha : k = a := by simpa using hk
      subst ha
      rw [hop]
      simp only [List.map_cons, List.map_nil, hst]
      exact ⟨rfl, true, rfl⟩
    · rw [hin] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rw [hop]
        simp only [List.map_cons, List.map_nil, hst, simplify]
        cases hb : st.getD b (Stat.const false) with
        | const d => exact ⟨rfl, true || d, rfl⟩
        | wire j => exact ⟨rfl, true, rfl⟩
      · rw [hop]
        simp only [List.map_cons, List.map_nil, hst, simplify]
        cases ha : st.getD a (Stat.const false) with
        | const d => exact ⟨rfl, d || true, rfl⟩
        | wire j => exact ⟨rfl, true, rfl⟩
    · rw [hin] at hlen; simp at hlen
  · refine ⟨false, fun m st hst => ?_⟩
    have hlen := hnok.2 hop
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · rw [hin] at hk; simp at hk
    · rw [hin] at hk
      have ha : k = a := by simpa using hk
      subst ha
      rw [hop]
      simp only [List.map_cons, List.map_nil, hst]
      exact ⟨rfl, true, rfl⟩
    · rw [hin] at hlen; simp at hlen

lemma jointFG_elim_result (n k s d : ℕ) (f : (Fin n → Bool) → Bool)
    (G : Fin k → (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (gs : List Gate) (o1 : ℕ) (o : Fin k → ℕ)
    (hnok : ∀ g ∈ gs, NOk g)
    (hsz : gs.length ≤ s)
    (hev : ∀ x : Fin n → Bool,
      (wiresFrom gs (List.ofFn x)).getD o1 false = f x ∧
      ∀ j : Fin k, (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x)
    (hf_nc : ∃ x y : Fin n → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (hG_nc : ∀ j : Fin k, ∃ x y : Fin n → Bool, G j x ≠ G j y)
    (hG_indep : ∀ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i b) = G j x)
    (hsave : (elim n gs (statFix n i b, [])).2.length + d ≤ gs.length) :
    d ≤ s ∧ JointFG n k (fun x => f (Function.update x i b)) G (s - d) := by
  set acc := elim n gs (statFix n i b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Function.update y i b))) acc := fun y =>
    inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_statFix n i b y)
  have hval1 : ∀ y : Fin n → Bool,
      (acc.1.getD o1 (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) =
        f (Function.update y i b) := by
    intro y
    rw [((hinv y).2 o1).2, (hev (Function.update y i b)).1]
  have hvalG : ∀ (j : Fin k) (y : Fin n → Bool),
      (acc.1.getD (o j) (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = G j y := by
    intro j y
    rw [((hinv y).2 (o j)).2, (hev (Function.update y i b)).2 j, hG_indep j y]
  have ho1_wire : ∃ w1 : ℕ, acc.1.getD o1 (Stat.const false) = Stat.wire w1 := by
    cases hst : acc.1.getD o1 (Stat.const false) with
    | const c =>
      exfalso
      obtain ⟨x, y, hxy⟩ := hf_nc
      apply hxy
      rw [← hval1 x, ← hval1 y, hst]
      rfl
    | wire w1 => exact ⟨w1, rfl⟩
  have hoG_wire : ∀ j : Fin k, ∃ wj : ℕ, acc.1.getD (o j) (Stat.const false) = Stat.wire wj := by
    intro j
    cases hst : acc.1.getD (o j) (Stat.const false) with
    | const c =>
      exfalso
      obtain ⟨x, y, hxy⟩ := hG_nc j
      apply hxy
      rw [← hvalG j x, ← hvalG j y, hst]
      rfl
    | wire wj => exact ⟨wj, rfl⟩
  obtain ⟨w1, hw1⟩ := ho1_wire
  choose o' ho' using hoG_wire
  refine ⟨by omega, ⟨⟨acc.2, w1⟩, elim_ok n gs _ (by simp), by show acc.2.length ≤ s - d; omega,
    w1, o', ?_⟩⟩
  intro y
  constructor
  · have h := hval1 y
    rw [hw1] at h
    exact h
  · intro j
    have h := hvalG j y
    rw [ho' j] at h
    exact h

lemma one_gate_multi (n k s : ℕ) (f : (Fin n → Bool) → Bool)
    (G : Fin k → (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (hf_nc : ∃ x y : Fin n → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (hG_nc : ∀ j : Fin k, ∃ x y : Fin n → Bool, G j x ≠ G j y)
    (hG_indep : ∀ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i b) = G j x)
    (hJ : JointFG n k f G s) :
    1 ≤ s ∧ JointFG n k (fun x => f (Function.update x i b)) G (s - 1) := by
  obtain ⟨C, ok, hsz, o1, o, hev⟩ := hJ
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin n → Bool,
      (wiresFrom gs (List.ofFn x)).getD o1 false = f x ∧
      ∀ j : Fin k, (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact hev x
  have hlen_gs : gs.length ≤ s := by
    have : gs.length = C.gates.length := by simp [hgs]
    have hsz' : C.gates.length ≤ s := hsz
    omega
  have hread : ∃ g ∈ gs, i.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    have ho1_ne : o1 ≠ i.val := by
      intro e
      obtain ⟨x, y, hxy⟩ := hf_nc
      apply hxy
      rw [← (hevg (Function.update x i b)).1, ← (hevg (Function.update y i b)).1, e]
      have hget : ∀ z : Fin n → Bool,
          (wiresFrom gs (List.ofFn z)).getD i.val false = z i := by
        intro z
        rw [getD_wiresFrom gs (List.ofFn z) i.val (by simp)]
        simp
      rw [hget, hget]
      simp
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hns := supp_noread_gen i gs (inputSupps n) hno (inputSupps_noread_gen i) o1 ho1_ne
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x gs _ _ _
      (agree_inputs _ _)).2.2 o1 (by
        intro u hu
        have : u ≠ i := fun e => hns (e ▸ hu)
        simp [Function.update_of_ne this])
    rw [← (hevg _).1, ← (hevg _).1]
    exact hag
  have hsave : (elim n gs (statFix n i b, [])).2.length + 1 ≤ gs.length := by
    have h := elim_len_lt n i.val gs (statFix n i b, []) hnok
      (by rw [statFix_length]; exact i.isLt)
      ⟨b, statFix_getD_self n i b⟩ hread
    simpa using h
  exact jointFG_elim_result n k s 1 f G i b gs o1 o hnok hlen_gs hevg hf_nc hG_nc hG_indep hsave

lemma two_gates_multi (n k s : ℕ) (f : (Fin n → Bool) → Bool)
    (G : Fin k → (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (hf_nc : ∀ b : Bool, ∃ x y : Fin n → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (hG_nc : ∀ j : Fin k, ∃ x y : Fin n → Bool, G j x ≠ G j y)
    (hG_indep : ∀ (j : Fin k) (b : Bool) (x : Fin n → Bool), G j (Function.update x i b) = G j x)
    (hJ : JointFG n k f G s) :
    ∃ b : Bool, 2 ≤ s ∧ JointFG n k (fun x => f (Function.update x i b)) G (s - 2) := by
  classical
  obtain ⟨C, ok, hsz, o1, o, hev⟩ := hJ
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin n → Bool,
      (wiresFrom gs (List.ofFn x)).getD o1 false = f x ∧
      ∀ j : Fin k, (wiresFrom gs (List.ofFn x)).getD (o j) false = G j x := by
    intro x
    rw [hgs, wiresFrom_norm]
    exact hev x
  have hlen_gs : gs.length ≤ s := by
    have : gs.length = C.gates.length := by simp [hgs]
    have hsz' : C.gates.length ≤ s := hsz
    omega
  have ho1_ne : o1 ≠ i.val := by
    intro e
    obtain ⟨x, y, hxy⟩ := hf_nc false
    apply hxy
    rw [← (hevg (Function.update x i false)).1, ← (hevg (Function.update y i false)).1, e]
    have hget : ∀ z : Fin n → Bool,
        (wiresFrom gs (List.ofFn z)).getD i.val false = z i := by
      intro z
      rw [getD_wiresFrom gs (List.ofFn z) i.val (by simp)]
      simp
    rw [hget, hget]
    simp
  have hread : ∃ g ∈ gs, i.val ∈ g.inputs := by
    by_contra hno
    push Not at hno
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hns := supp_noread_gen i gs (inputSupps n) hno (inputSupps_noread_gen i) o1 ho1_ne
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x gs _ _ _
      (agree_inputs _ _)).2.2 o1 (by
        intro u hu
        have : u ≠ i := fun e => hns (e ▸ hu)
        simp [Function.update_of_ne this])
    rw [← (hevg _).1, ← (hevg _).1]
    exact hag
  obtain ⟨pre, g1, post, hsplit, hg1_in, hpre_no⟩ :=
    list_split_first (fun g : Gate => i.val ∈ g.inputs) gs hread
  have hnok_g1 : NOk g1 := hnok g1 (by rw [hsplit]; simp)
  have hnok_post : ∀ g ∈ post, NOk g := fun g hg =>
    hnok g (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  obtain ⟨b, hb_kill⟩ := simplify_kill_bit g1 hnok_g1 i.val hg1_in
  refine ⟨b, ?_⟩
  set acc0 : List Stat × List Gate := (statFix n i b, [])
  set acc1 := elim n pre acc0
  set acc2 := elimStep n acc1 g1
  have hacc1_len : acc1.1.length = n + pre.length := by
    dsimp [acc1, acc0]
    rw [elim_fst_len, statFix_length]
  have hacc1_i : acc1.1.getD i.val (Stat.const false) = Stat.const b := by
    dsimp [acc1, acc0]
    rw [elim_getD n i.val _ pre _ (by rw [statFix_length]; exact i.isLt)]
    exact statFix_getD_self n i b
  obtain ⟨hnone1, c1, hc1⟩ := hb_kill (n + acc1.2.length) acc1.1 hacc1_i
  have hacc2_2 : acc2.2.length = acc1.2.length := by
    show (acc1.2 ++ (simplify g1.op (n + acc1.2.length)
      (g1.inputs.map fun a => acc1.1.getD a (Stat.const false))).1.toList).length = _
    rw [hnone1]
    simp
  have hacc1_2_le : acc1.2.length ≤ pre.length := by
    have := elim_len n pre acc0
    simpa [acc1, acc0] using this
  have hacc2_len : acc2.1.length = n + pre.length + 1 := by
    simp [acc2, elimStep, hacc1_len]
  have hacc2_i : acc2.1.getD i.val (Stat.const false) = Stat.const b := by
    simp only [acc2, elimStep]
    rw [getD_snoc_ne _ _ _ _ (by omega)]
    exact hacc1_i
  have hacc2_w1 : acc2.1.getD (n + pre.length) (Stat.const false) = Stat.const c1 := by
    simp only [acc2, elimStep]
    rw [getD_snoc_len _ _ _ _ hacc1_len]
    exact hc1
  have hsplit_elim : elim n gs acc0 = elim n post acc2 := by
    rw [hsplit, elim_append]
    rfl
  have hsave : (elim n gs acc0).2.length + 2 ≤ gs.length := by
    by_cases hpost_i : ∃ g ∈ post, i.val ∈ g.inputs
    · have hlt := elim_len_lt n i.val post acc2 hnok_post (by omega) ⟨b, hacc2_i⟩ hpost_i
      rw [hsplit_elim]
      have hglen : gs.length = pre.length + 1 + post.length := by
        rw [hsplit]; simp; omega
      omega
    · by_cases hpost_w1 : ∃ g ∈ post, (n + pre.length) ∈ g.inputs
      · have hlt := elim_len_lt n (n + pre.length) post acc2 hnok_post (by omega)
          ⟨c1, hacc2_w1⟩ hpost_w1
        rw [hsplit_elim]
        have hglen : gs.length = pre.length + 1 + post.length := by
          rw [hsplit]; simp; omega
        omega
      · exfalso
        push Not at hpost_i hpost_w1
        have ho1_ne_w1 : o1 ≠ n + pre.length := by
          intro e
          have hst_w1 : (elim n gs acc0).1.getD (n + pre.length) (Stat.const false) = Stat.const c1 := by
            rw [hsplit_elim, elim_getD n (n + pre.length) _ post acc2 (by omega)]
            exact hacc2_w1
          have hinv := fun y : Fin n → Bool =>
            inv_elim n (List.ofFn y) (by simp) gs _ _ (fun g hg => (hnok g hg).1)
              (inv_statFix n i b y)
          obtain ⟨x, y, hxy⟩ := hf_nc b
          apply hxy
          have hx1 := ((hinv x).2 o1).2
          have hy1 := ((hinv y).2 o1).2
          rw [(hevg (Function.update x i b)).1] at hx1
          rw [(hevg (Function.update y i b)).1] at hy1
          rw [e, hst_w1] at hx1 hy1
          exact hx1.symm.trans hy1
        set L1 := suppsFrom pre (inputSupps n)
        have hL1_len : L1.length = n + pre.length := by
          dsimp [L1]
          rw [suppsFrom_len]
          simp [inputSupps]
        have hL1_no : ∀ j : ℕ, j ≠ i.val → i ∉ L1.getD j ∅ :=
          supp_noread_gen i pre (inputSupps n) hpre_no (inputSupps_noread_gen i)
        set L2 := L1 ++ [gateSupp L1 g1]
        have hL2_no : ∀ j : ℕ, j ≠ i.val → j ≠ n + pre.length → i ∉ L2.getD j ∅ := by
          intro j hj1 hj2
          dsimp [L2]
          rw [getD_snoc_ne _ _ _ _ (by omega)]
          exact hL1_no j hj1
        have hns : i ∉ (suppsFrom gs (inputSupps n)).getD o1 ∅ := by
          rw [hsplit, suppsFrom_append]
          have hstep : suppsFrom (g1 :: post) L1 = suppsFrom post L2 := rfl
          rw [hstep]
          exact supp_noread2 i (n + pre.length) post L2
            (fun g hg => ⟨hpost_i g hg, hpost_w1 g hg⟩) hL2_no o1 ho1_ne ho1_ne_w1
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hag := (agree_wiresFrom (Function.update x i (!x i)) x gs _ _ _
          (agree_inputs _ _)).2.2 o1 (by
            intro u hu
            have : u ≠ i := fun e => hns (e ▸ hu)
            simp [Function.update_of_ne this])
        rw [← (hevg _).1, ← (hevg _).1]
        exact hag
  exact jointFG_elim_result n k s 2 f G i b gs o1 o hnok hlen_gs hevg
    (hf_nc b) hG_nc (fun j x => hG_indep j b x) hsave

noncomputable def fKA {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)
    (Classical.propDecidable _)

lemma fKA_eq_true {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    fKA K A x = true ↔
      (∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true := by
  unfold fKA
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

def delV {n : ℕ} (K : SimpleGraph (Fin n)) (X : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := K.Adj u v ∧ u ∉ X ∧ v ∉ X
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun u h => K.loopless.irrefl u h.1⟩

lemma delV_le {n : ℕ} (K : SimpleGraph (Fin n)) (X : Finset (Fin n)) : delV K X ≤ K :=
  fun _ _ h => h.1

lemma delV_acyclic {n : ℕ} (K : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (hcyc : ∀ (v : Fin n) (c : K.Walk v v), ¬ c.IsCycle) :
    ∀ (v : Fin n) (c : (delV K X).Walk v v), ¬ c.IsCycle := by
  intro v c hc
  exact hcyc v (c.mapLe (delV_le K X)) (hc.mapLe (delV_le K X))

lemma delV_edgeSet_sub {n : ℕ} (K : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    (delV K X).edgeSet ⊆ K.edgeSet :=
  SimpleGraph.edgeSet_mono (delV_le K X)

lemma edgeSet_finite {n : ℕ} (K : SimpleGraph (Fin n)) : K.edgeSet.Finite :=
  Set.toFinite _

lemma delV_leaf_edgeSet {n : ℕ} (K : SimpleGraph (Fin n)) (l p : Fin n)
    (hlp : K.Adj l p) (hleaf : ∀ w, K.Adj l w → w = p) :
    K.edgeSet = insert s(l, p) (delV K {l}).edgeSet ∧ s(l, p) ∉ (delV K {l}).edgeSet := by
  constructor
  · ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeSet, Set.mem_insert_iff, Sym2.eq_iff, delV,
        Finset.mem_singleton]
      constructor
      · intro huv
        by_cases hul : u = l
        · subst hul
          left
          exact Or.inl ⟨rfl, hleaf v huv⟩
        · by_cases hvl : v = l
          · subst hvl
            left
            exact Or.inr ⟨hleaf u huv.symm, rfl⟩
          · exact Or.inr ⟨huv, hul, hvl⟩
      · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨huv, _, _⟩)
        · exact hlp
        · exact hlp.symm
        · exact huv
  · simp [SimpleGraph.mem_edgeSet, delV]

lemma delV_leaf_ncard {n : ℕ} (K : SimpleGraph (Fin n)) (l p : Fin n)
    (hlp : K.Adj l p) (hleaf : ∀ w, K.Adj l w → w = p) :
    K.edgeSet.ncard = (delV K {l}).edgeSet.ncard + 1 := by
  obtain ⟨heq, hnot⟩ := delV_leaf_edgeSet K l p hlp hleaf
  rw [heq, Set.ncard_insert_of_notMem hnot (edgeSet_finite _)]

lemma delV_leaf2_ncard {n : ℕ} (K : SimpleGraph (Fin n)) (l p q : Fin n)
    (hlp : K.Adj l p) (hleaf : ∀ w, K.Adj l w → w = p)
    (hp : ∀ w, K.Adj p w → w = l ∨ w = q) :
    K.edgeSet.ncard ≤ (delV K ({l, p} : Finset (Fin n))).edgeSet.ncard + 2 ∧
    (delV K ({l, p} : Finset (Fin n))).edgeSet.ncard < K.edgeSet.ncard := by
  have hsub : K.edgeSet ⊆ insert s(l, p) (insert s(p, q) (delV K {l, p}).edgeSet) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeSet] at he
      simp only [Set.mem_insert_iff, Sym2.eq_iff, SimpleGraph.mem_edgeSet, delV,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      by_cases hul : u = l
      · subst hul; exact Or.inl (Or.inl ⟨rfl, hleaf v he⟩)
      · by_cases hvl : v = l
        · subst hvl; exact Or.inl (Or.inr ⟨hleaf u he.symm, rfl⟩)
        · by_cases hup : u = p
          · subst hup
            rcases hp v he with rfl | rfl
            · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
            · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
          · by_cases hvp : v = p
            · subst hvp
              rcases hp u he.symm with rfl | rfl
              · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
              · exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))
            · exact Or.inr (Or.inr ⟨he, ⟨hul, hup⟩, ⟨hvl, hvp⟩⟩)
  have h1 : K.edgeSet.ncard ≤
      (insert s(l, p) (insert s(p, q) (delV K {l, p}).edgeSet)).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : (insert s(l, p) (insert s(p, q) (delV K {l, p}).edgeSet)).ncard ≤
      (insert s(p, q) (delV K {l, p}).edgeSet).ncard + 1 := Set.ncard_insert_le _ _
  have h3 : (insert s(p, q) (delV K {l, p}).edgeSet).ncard ≤
      (delV K {l, p}).edgeSet.ncard + 1 := Set.ncard_insert_le _ _
  have hlt : (delV K {l, p}).edgeSet.ncard < K.edgeSet.ncard := by
    have hss : (delV K {l, p}).edgeSet ⊂ K.edgeSet := by
      refine ⟨delV_edgeSet_sub K {l, p}, ?_⟩
      intro hrev
      have hmem : s(l, p) ∈ (delV K {l, p}).edgeSet := hrev hlp
      simp [SimpleGraph.mem_edgeSet, delV] at hmem
    exact Set.ncard_lt_ncard hss (edgeSet_finite _)
  exact ⟨by omega, hlt⟩

lemma res_false_leaf {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l : Fin n)
    (hlA : l ∉ A) (x : Fin n → Bool) :
    fKA K A (Function.update x l false) = fKA (delV K {l}) A x := by
  apply Bool.eq_iff_iff.mpr
  rw [fKA_eq_true, fKA_eq_true]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hu, hv⟩)
    · left
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      rw [Function.update_of_ne hal] at hxa
      exact ⟨a, ha, hxa⟩
    · right
      have hul : u ≠ l := by intro e; subst e; simp at hu
      have hvl : v ≠ l := by intro e; subst e; simp at hv
      rw [Function.update_of_ne hul] at hu
      rw [Function.update_of_ne hvl] at hv
      exact ⟨u, v, ⟨huv, by simpa using hul, by simpa using hvl⟩, hu, hv⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨u, v, ⟨huv, hul, hvl⟩, hu, hv⟩)
    · left
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
    · right
      simp only [Finset.mem_singleton] at hul hvl
      exact ⟨u, v, huv, by rwa [Function.update_of_ne hul], by rwa [Function.update_of_ne hvl]⟩

lemma res_true_leaf {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hlp : K.Adj l p) (hleaf : ∀ w, K.Adj l w → w = p) (x : Fin n → Bool) :
    fKA K A (Function.update x l true) = fKA (delV K {l, p}) (insert p A) x := by
  apply Bool.eq_iff_iff.mpr
  rw [fKA_eq_true, fKA_eq_true]
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hu, hv⟩)
    · left
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      rw [Function.update_of_ne hal] at hxa
      exact ⟨a, Finset.mem_insert_of_mem ha, hxa⟩
    · by_cases hup : u = p
      · rw [hup] at hu
        left
        have hpl : p ≠ l := hlp.ne.symm
        rw [Function.update_of_ne hpl] at hu
        exact ⟨p, Finset.mem_insert_self p A, hu⟩
      · by_cases hvp : v = p
        · rw [hvp] at hv
          left
          have hpl : p ≠ l := hlp.ne.symm
          rw [Function.update_of_ne hpl] at hv
          exact ⟨p, Finset.mem_insert_self p A, hv⟩
        · have hul : u ≠ l := fun e => hvp (hleaf v (e ▸ huv))
          have hvl : v ≠ l := fun e => hup (hleaf u (e ▸ huv.symm))
          rw [Function.update_of_ne hul] at hu
          rw [Function.update_of_ne hvl] at hv
          exact Or.inr ⟨u, v, ⟨huv, by simp [hul, hup], by simp [hvl, hvp]⟩, hu, hv⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨u, v, ⟨huv, huX, hvX⟩, hu, hv⟩)
    · rcases Finset.mem_insert.mp ha with hap | haA
      · right
        rw [hap] at hxa
        have hpl : p ≠ l := hlp.ne.symm
        exact ⟨l, p, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · left
        have hal : a ≠ l := fun e => hlA (e ▸ haA)
        exact ⟨a, haA, by rwa [Function.update_of_ne hal]⟩
    · right
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huX hvX
      exact ⟨u, v, huv, by rwa [Function.update_of_ne huX.1], by rwa [Function.update_of_ne hvX.1]⟩

lemma res_false_free {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (haA : a ∈ A) (ha_iso : ∀ w : Fin n, ¬ K.Adj a w) (x : Fin n → Bool) :
    fKA K A (Function.update x a false) = fKA K (A.erase a) x := by
  apply Bool.eq_iff_iff.mpr
  rw [fKA_eq_true, fKA_eq_true]
  constructor
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hu, hv⟩)
    · have hba : b ≠ a := by intro e; subst e; simp at hxb
      rw [Function.update_of_ne hba] at hxb
      exact Or.inl ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, hxb⟩
    · have hua : u ≠ a := fun e => ha_iso v (e ▸ huv)
      have hva : v ≠ a := fun e => ha_iso u (e ▸ huv.symm)
      rw [Function.update_of_ne hua] at hu
      rw [Function.update_of_ne hva] at hv
      exact Or.inr ⟨u, v, huv, hu, hv⟩
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hu, hv⟩)
    · obtain ⟨hba, hbA⟩ := Finset.mem_erase.mp hb
      exact Or.inl ⟨b, hbA, by rwa [Function.update_of_ne hba]⟩
    · have hua : u ≠ a := fun e => ha_iso v (e ▸ huv)
      have hva : v ≠ a := fun e => ha_iso u (e ▸ huv.symm)
      exact Or.inr ⟨u, v, huv, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩

lemma fKA_nc {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) :
    ∃ x y : Fin n → Bool, fKA K A x ≠ fKA K A y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h0 : fKA K A (fun _ => false) = false := by
    rw [Bool.eq_false_iff, ne_eq, fKA_eq_true]
    simp
  have h1 : fKA K A (fun _ => true) = true := by
    rw [fKA_eq_true]
    rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨u, v, huv, rfl, rfl⟩
  rw [h0, h1]
  decide

lemma fKA_dep_free {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, fKA K A (Function.update x a (!x a)) ≠ fKA K A x := by
  refine ⟨fun _ => false, ?_⟩
  have h0 : fKA K A (fun _ => false) = false := by
    rw [Bool.eq_false_iff, ne_eq, fKA_eq_true]; simp
  have h1 : fKA K A (Function.update (fun _ => false) a true) = true := by
    rw [fKA_eq_true]
    exact Or.inl ⟨a, ha, by simp⟩
  simp [h0, h1]

lemma fKA_dep_edge {n : ℕ} (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlp : K.Adj l p) (hpA : p ∉ A) :
    ∃ x : Fin n → Bool, fKA K A (Function.update x l (!x l)) ≠ fKA K A x := by
  let x : Fin n → Bool := fun i => decide (i = p)
  have hxl : x l = false := by simp [x, hlp.ne]
  have h0 : fKA K A x = false := by
    rw [Bool.eq_false_iff, ne_eq, fKA_eq_true]
    rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hu, hv⟩)
    · simp only [x, decide_eq_true_eq] at hxa
      exact hpA (hxa ▸ ha)
    · simp only [x, decide_eq_true_eq] at hu hv
      subst hu; subst hv
      exact K.loopless.irrefl _ huv
  have h1 : fKA K A (Function.update x l (!x l)) = true := by
    rw [hxl, fKA_eq_true]
    exact Or.inr ⟨l, p, hlp, by simp, by simp [x, hlp.ne.symm]⟩
  exact ⟨x, by rw [h0, h1]; decide⟩

lemma cov_swap {n : ℕ} (K : SimpleGraph (Fin n)) (l p l' : Fin n)
    (hl'l : l' ≠ l) (hpl' : K.Adj p l') (hleaf : ∀ w, K.Adj l w → w = p)
    (hleaf' : ∀ w, K.Adj l' w → w = p)
    (T' : Finset (Fin n)) (hT' : ∀ u v : Fin n, (delV K {l}).Adj u v → u ∈ T' ∨ v ∈ T') :
    ∃ T : Finset (Fin n), (∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ T'.card := by
  have hpl'0 : (delV K {l}).Adj p l' := by
    refine ⟨hpl', ?_, ?_⟩
    · simp only [Finset.mem_singleton]
      intro e
      subst e
      exact hl'l (hleaf l' hpl')
    · simpa using hl'l
  rcases hT' p l' hpl'0 with hpT | hl'T
  · refine ⟨T', ?_, le_rfl⟩
    intro u v huv
    by_cases hul : u = l
    · subst hul; rw [hleaf v huv]; exact Or.inr hpT
    · by_cases hvl : v = l
      · subst hvl; rw [hleaf u huv.symm]; exact Or.inl hpT
      · exact hT' u v ⟨huv, by simpa using hul, by simpa using hvl⟩
  · refine ⟨insert p (T'.erase l'), ?_, ?_⟩
    · intro u v huv
      by_cases hul : u = l
      · subst hul; rw [hleaf v huv]; exact Or.inr (Finset.mem_insert_self p _)
      · by_cases hvl : v = l
        · subst hvl; rw [hleaf u huv.symm]; exact Or.inl (Finset.mem_insert_self p _)
        · by_cases hul' : u = l'
          · subst hul'; rw [hleaf' v huv]; exact Or.inr (Finset.mem_insert_self p _)
          · by_cases hvl' : v = l'
            · subst hvl'; rw [hleaf' u huv.symm]; exact Or.inl (Finset.mem_insert_self p _)
            · rcases hT' u v ⟨huv, by simpa using hul, by simpa using hvl⟩ with hu | hv
              · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hul', hu⟩))
              · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvl', hv⟩))
    · have h1 := Finset.card_insert_le p (T'.erase l')
      have h2 := Finset.card_erase_of_mem hl'T
      have h3 : 1 ≤ T'.card := Finset.card_pos.mpr ⟨l', hl'T⟩
      omega

lemma walk_of_chain {n : ℕ} (K : SimpleGraph (Fin n)) :
    ∀ (a : Fin n) (l : List (Fin n)), List.IsChain K.Adj (a :: l) →
      ∃ b : Fin n, b = (a :: l).getLast (by simp) ∧
        ∃ p : K.Walk a b, p.support = a :: l := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _
    exact ⟨a, rfl, SimpleGraph.Walk.nil, rfl⟩
  | cons x xs ih =>
    intro hch
    rw [List.isChain_cons_cons] at hch
    obtain ⟨b, hb, p, hsupp⟩ := ih x hch.2
    refine ⟨b, by simpa using hb, SimpleGraph.Walk.cons hch.1 p, ?_⟩
    simp [hsupp]

lemma isChain_append_left {α : Type} {R : α → α → Prop} :
    ∀ (l1 l2 : List α), List.IsChain R (l1 ++ l2) → List.IsChain R l1 := by
  intro l1 l2
  induction l1 with
  | nil => intro _; exact List.IsChain.nil
  | cons a t ih =>
    cases t with
    | nil => intro _; exact List.IsChain.singleton a
    | cons b t' =>
      intro h
      rw [List.cons_append, List.cons_append, List.isChain_cons_cons] at h
      exact List.isChain_cons_cons.mpr ⟨h.1, ih h.2⟩

lemma no_chord_in_tree {n : ℕ} (K : SimpleGraph (Fin n))
    (hcyc : ∀ (v : Fin n) (c : K.Walk v v), ¬ c.IsCycle)
    (u p : Fin n) (rest : List (Fin n))
    (hch : List.IsChain K.Adj (u :: p :: rest))
    (hnod : (u :: p :: rest).Nodup)
    (w : Fin n) (huw : K.Adj u w) (hw : w ∈ rest) : False := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hw
  have hfull : u :: p :: rest = (u :: p :: pre ++ [w]) ++ post := by
    rw [hsplit]
    simp
  have hch_sub : List.IsChain K.Adj (u :: p :: pre ++ [w]) := by
    rw [hfull] at hch
    exact isChain_append_left (u :: p :: pre ++ [w]) post hch
  have hnod_sub : (u :: p :: pre ++ [w]).Nodup := by
    rw [hfull] at hnod
    exact hnod.sublist (List.sublist_append_left _ _)
  obtain ⟨b, hb, q, hsupp⟩ := walk_of_chain K u (p :: pre ++ [w]) hch_sub
  have hbw : b = w := by
    rw [hb]
    have hlist : u :: (p :: pre ++ [w]) = (u :: p :: pre) ++ [w] := rfl
    simp only [hlist, List.getLast_append_singleton]
  subst hbw
  let c : K.Walk b b := SimpleGraph.Walk.cons huw.symm q
  have hctail : c.support.tail = u :: p :: pre ++ [b] := by
    simp [c, hsupp]
  have hclen : 3 ≤ c.length := by
    have hs : c.support.length = c.length + 1 := c.length_support
    have hst : c.support.length = (u :: p :: pre ++ [b]).length + 1 := by
      simp [c, hsupp]
    simp at hst
    omega
  have hc_trail : c.IsTrail := by
    have hq_path : q.IsPath := by
      rw [SimpleGraph.Walk.isPath_def, hsupp]
      exact hnod_sub
    have hnod_cons : (u :: (p :: (pre ++ [b]))).Nodup := hnod_sub
    rw [SimpleGraph.Walk.isTrail_def]
    simp only [c, SimpleGraph.Walk.edges_cons, List.nodup_cons]
    refine ⟨?_, hq_path.isTrail.edges_nodup⟩
    intro hmem
    have hlen_q : 2 ≤ q.length := by
      have hs := q.length_support
      rw [hsupp] at hs
      simp at hs
      omega
    cases hq : q with
    | nil => rw [hq] at hlen_q; simp at hlen_q
    | cons hadj1 q1 =>
      rename_i v1
      have hv1 : v1 = p := by
        have := congrArg (fun l => l[1]?) hsupp
        rw [hq] at this
        simpa using this
      subst v1
      rw [hq, SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
      rcases hmem with heq | hmem1
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact K.loopless.irrefl b (h1 ▸ huw)
        · have : p ∈ pre ++ [b] := by rw [← h1]; simp
          rw [List.nodup_cons, List.nodup_cons] at hnod_cons
          exact hnod_cons.2.1 this
      · have hwu : u ∈ q1.support :=
          SimpleGraph.Walk.snd_mem_support_of_mem_edges q1 hmem1
        have hq1_supp : q1.support = p :: (pre ++ [b]) := by
          have := congrArg List.tail hsupp
          rw [hq] at this
          simpa using this
        rw [hq1_supp] at hwu
        rw [List.nodup_cons] at hnod_cons
        exact hnod_cons.1 hwu
  have hcyc_c : c.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨hc_trail, ?_, by rw [hctail]; exact hnod_sub⟩
    intro hnil
    rw [hnil] at hclen
    simp at hclen
  exact hcyc b c hcyc_c

lemma good_leaf_avoiding {n : ℕ} (K : SimpleGraph (Fin n)) (bad : Fin n → Prop)
    (hcyc : ∀ (v : Fin n) (c : K.Walk v v), ¬ c.IsCycle)
    (hbad : ∀ i i' : Fin n, (∃ w, K.Adj i w) → (∃ w, K.Adj i' w) → bad i → bad i' → i = i')
    (hE : ∃ u v : Fin n, K.Adj u v) :
    ∃ l p : Fin n, ¬ bad l ∧ K.Adj l p ∧ (∀ w, K.Adj l w → w = p) ∧
      ((∃ q, ∀ w, K.Adj p w → w = l ∨ w = q) ∨
       (∃ l', l' ≠ l ∧ K.Adj p l' ∧ ∀ w, K.Adj l' w → w = p)) := by
  classical
  have hroot : ∃ r : Fin n, (∃ w, K.Adj r w) ∧ ∀ u : Fin n, (∃ w, K.Adj u w) → u ≠ r → ¬ bad u := by
    by_cases hb : ∃ v0 : Fin n, (∃ w, K.Adj v0 w) ∧ bad v0
    · obtain ⟨v0, hv0e, hv0b⟩ := hb
      exact ⟨v0, hv0e, fun u hue hur hub => hur (hbad u v0 hue hv0e hub hv0b)⟩
    · obtain ⟨a, b, hab⟩ := hE
      exact ⟨a, ⟨b, hab⟩, fun u hue _ hub => hb ⟨u, hue, hub⟩⟩
  obtain ⟨r, ⟨w0, hrw0⟩, hr_avoid⟩ := hroot
  let GoodPath (L : List (Fin n)) : Prop :=
    2 ≤ L.length ∧ L.Nodup ∧ List.IsChain K.Adj L ∧ L.getLast? = some r
  have hex_len : ∃ d : ℕ, ∃ L : List (Fin n), GoodPath L ∧ L.length = d :=
    ⟨2, [w0, r], ⟨le_rfl, by simp [hrw0.ne.symm], by simp [hrw0.symm], rfl⟩, rfl⟩
  have hbound : ∀ L : List (Fin n), GoodPath L → L.length ≤ n := by
    intro L hL
    have hcard := L.toFinset_card_of_nodup hL.2.1
    calc L.length = L.toFinset.card := hcard.symm
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := Fintype.card_fin n
  have hex_max : ∃ L : List (Fin n), GoodPath L ∧ ∀ L' : List (Fin n), GoodPath L' → L'.length ≤ L.length := by
    let S : Finset ℕ := (Finset.range (n + 1)).filter (fun d => ∃ L : List (Fin n), GoodPath L ∧ L.length = d)
    have hS : S.Nonempty := by
      refine ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, [w0, r], ?_, rfl⟩⟩
      · have := hbound [w0, r] ⟨le_rfl, by simp [hrw0.ne.symm], by simp [hrw0.symm], rfl⟩
        simp at this
        omega
      · exact ⟨le_rfl, by simp [hrw0.ne.symm], by simp [hrw0.symm], rfl⟩
    obtain ⟨d, hdS, hdmax⟩ := Finset.exists_max_image S id hS
    obtain ⟨L, hL, hLlen⟩ := (Finset.mem_filter.mp hdS).2
    refine ⟨L, hL, fun L' hL' => ?_⟩
    have hmem : L'.length ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := hbound L' hL'; omega), L', hL', rfl⟩
    have := hdmax L'.length hmem
    simpa [hLlen] using this
  have leaf_of_max : ∀ (u p : Fin n) (rest : List (Fin n)),
      GoodPath (u :: p :: rest) →
      (∀ L' : List (Fin n), GoodPath L' → L'.length ≤ (u :: p :: rest).length) →
      ∀ w : Fin n, K.Adj u w → w = p := by
    intro u p rest hG hmax w huw
    by_contra hwp
    have hch := hG.2.2.1
    have hnod := hG.2.1
    have hwu : w ≠ u := huw.ne.symm
    by_cases hwrest : w ∈ rest
    · exact no_chord_in_tree K hcyc u p rest hch hnod w huw hwrest
    · have hw_not : w ∉ u :: p :: rest := by
        simp [hwu, hwp, hwrest]
      have hG' : GoodPath (w :: u :: p :: rest) := by
        refine ⟨by simp, List.nodup_cons.mpr ⟨hw_not, hnod⟩,
          List.isChain_cons_cons.mpr ⟨huw.symm, hch⟩, ?_⟩
        simpa using hG.2.2.2
      have := hmax (w :: u :: p :: rest) hG'
      simp at this
  obtain ⟨L, hL, hmax⟩ := hex_max
  rcases L with _ | ⟨u, _ | ⟨p, rest⟩⟩
  · have := hL.1; simp at this
  · have := hL.1; simp at this
  · have hup : K.Adj u p := (List.isChain_cons_cons.mp hL.2.2.1).1
    have hu_leaf : ∀ w, K.Adj u w → w = p := leaf_of_max u p rest hL hmax
    have hu_ne_r : u ≠ r := by
      intro e
      subst e
      have hmem_r : u ∈ p :: rest := by
        have hlast : (p :: rest).getLast? = some u := by simpa using hL.2.2.2
        exact List.mem_of_getLast? hlast
      exact (List.nodup_cons.mp hL.2.1).1 hmem_r
    have hu_notbad : ¬ bad u := hr_avoid u ⟨p, hup⟩ hu_ne_r
    cases rest with
    | nil =>
      by_cases hex2 : ∃ l' : Fin n, l' ≠ u ∧ K.Adj p l'
      · obtain ⟨l', hl'u, hpl'⟩ := hex2
        have hpr : p = r := by simpa using hL.2.2.2
        have hl'G : GoodPath [l', p] :=
          ⟨le_rfl, by simp [hpl'.ne.symm], by simp [hpl'.symm], by simp [hpr]⟩
        have hl'_leaf : ∀ w, K.Adj l' w → w = p :=
          leaf_of_max l' p [] hl'G (fun L' hL' => by simpa using hmax L' hL')
        exact ⟨u, p, hu_notbad, hup, hu_leaf, Or.inr ⟨l', hl'u, hpl', hl'_leaf⟩⟩
      · push Not at hex2
        exact ⟨u, p, hu_notbad, hup, hu_leaf, Or.inl ⟨u, fun w hpw => by
          by_contra hne
          push Not at hne
          exact hex2 w hne.1 hpw⟩⟩
    | cons q rest' =>
      by_cases hex2 : ∃ l' : Fin n, l' ≠ u ∧ l' ≠ q ∧ K.Adj p l'
      · obtain ⟨l', hl'u, hl'q, hpl'⟩ := hex2
        have hch_tail : List.IsChain K.Adj (p :: q :: rest') :=
          (List.isChain_cons_cons.mp hL.2.2.1).2
        have hnod_tail : (p :: q :: rest').Nodup := (List.nodup_cons.mp hL.2.1).2
        have hl'_not_rest' : l' ∉ rest' := fun hmem =>
          no_chord_in_tree K hcyc p q rest' hch_tail hnod_tail l' hpl' hmem
        have hl'_not_tail : l' ∉ p :: q :: rest' := by
          simp [hpl'.ne.symm, hl'q, hl'_not_rest']
        have hl'G : GoodPath (l' :: p :: q :: rest') := by
          refine ⟨by simp, List.nodup_cons.mpr ⟨hl'_not_tail, hnod_tail⟩,
            List.isChain_cons_cons.mpr ⟨hpl'.symm, hch_tail⟩, ?_⟩
          simpa using hL.2.2.2
        have hl'_leaf : ∀ w, K.Adj l' w → w = p :=
          leaf_of_max l' p (q :: rest') hl'G (fun L' hL' => by simpa using hmax L' hL')
        exact ⟨u, p, hu_notbad, hup, hu_leaf, Or.inr ⟨l', hl'u, hpl', hl'_leaf⟩⟩
      · push Not at hex2
        exact ⟨u, p, hu_notbad, hup, hu_leaf, Or.inl ⟨q, fun w hpw => by
          by_contra hne
          push Not at hne
          exact hex2 w hne.1 hne.2 hpw⟩⟩

lemma lower_bound_aux (n k : ℕ) (G : Fin k → (Fin n → Bool) → Bool)
    (hG_nc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y') :
    ∀ m : ℕ, ∀ (s : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)),
      2 * K.edgeSet.ncard + A.card = m →
      (∀ (v : Fin n) (c : K.Walk v v), ¬ c.IsCycle) →
      (∀ a ∈ A, ∀ w : Fin n, ¬ K.Adj a w) →
      (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) →
      (∀ i i' : Fin n, (i ∈ A ∨ ∃ w, K.Adj i w) → (i' ∈ A ∨ ∃ w, K.Adj i' w) →
        (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i false) ≠ G j (Function.update x i true)) →
        (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i' false) ≠ G j (Function.update x i' true)) →
        i = i') →
      JointFG n k (fKA K A) G s →
      ∃ (T : Finset (Fin n)) (t : ℕ),
        (∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) ∧
        A.card + K.edgeSet.ncard + T.card + t ≤ s + 1 ∧
        JointG n k G t := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s K A hm hcyc hAfree hne hshared hJ
    let bad : Fin n → Prop := fun i =>
      ∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i false) ≠ G j (Function.update x i true)
    have hnotbad_indep : ∀ i : Fin n, ¬ bad i →
        ∀ (j : Fin k) (b : Bool) (x : Fin n → Bool), G j (Function.update x i b) = G j x := by
      intro i hnb j b x
      have heq : G j (Function.update x i false) = G j (Function.update x i true) := by
        by_contra hne'
        exact hnb ⟨j, x, hne'⟩
      cases hb : b <;> cases hx : x i
      · rw [← hx, Function.update_eq_self]
      · rw [heq, ← hx, Function.update_eq_self]
      · rw [← heq, ← hx, Function.update_eq_self]
      · rw [← hx, Function.update_eq_self]
    by_cases hE : ∃ u v : Fin n, K.Adj u v
    · obtain ⟨l, p, hl_nb, hlp, hleaf, hcase⟩ := good_leaf_avoiding K bad hcyc
        (fun i i' hi hi' bi bi' => hshared i i' (Or.inr hi) (Or.inr hi') bi bi') hE
      have hlA : l ∉ A := fun h => hAfree l h p hlp
      have hpA : p ∉ A := fun h => hAfree p h l hlp.symm
      have hdepl : ∃ x : Fin n → Bool,
          fKA K A (Function.update x l (!x l)) ≠ fKA K A x := fKA_dep_edge K A l p hlp hpA
      have hG_indep_l : ∀ (j : Fin k) (b : Bool) (x : Fin n → Bool),
          G j (Function.update x l b) = G j x := hnotbad_indep l hl_nb
      have hrf : (fun x => fKA K A (Function.update x l false)) = fKA (delV K {l}) A :=
        funext (res_false_leaf K A l hlA)
      have hrt : (fun x => fKA K A (Function.update x l true)) = fKA (delV K {l, p}) (insert p A) :=
        funext (res_true_leaf K A l p hlA hlp hleaf)
      have hnc_t : ∃ x y : Fin n → Bool,
          fKA K A (Function.update x l true) ≠ fKA K A (Function.update y l true) := by
        simp_rw [res_true_leaf K A l p hlA hlp hleaf]
        exact fKA_nc (delV K {l, p}) (insert p A) (Or.inl ⟨p, Finset.mem_insert_self p A⟩)
      have hedge0 : K.edgeSet.ncard = (delV K {l}).edgeSet.ncard + 1 :=
        delV_leaf_ncard K l p hlp hleaf
      rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
      · by_cases hne0 : A.Nonempty ∨ ∃ u v : Fin n, (delV K {l}).Adj u v
        · have hnc_f : ∃ x y : Fin n → Bool,
              fKA K A (Function.update x l false) ≠ fKA K A (Function.update y l false) := by
            simp_rw [res_false_leaf K A l hlA]
            exact fKA_nc (delV K {l}) A hne0
          have hnc_both : ∀ b : Bool, ∃ x y : Fin n → Bool,
              fKA K A (Function.update x l b) ≠ fKA K A (Function.update y l b) := by
            intro b; cases b
            · exact hnc_f
            · exact hnc_t
          obtain ⟨b, hs2, hJb⟩ := two_gates_multi n k s (fKA K A) G l hdepl hnc_both hG_nc
            hG_indep_l hJ
          cases b
          · rw [hrf] at hJb
            have hshared0 : ∀ i i' : Fin n,
                (i ∈ A ∨ ∃ w, (delV K {l}).Adj i w) → (i' ∈ A ∨ ∃ w, (delV K {l}).Adj i' w) →
                bad i → bad i' → i = i' := by
              intro i i' hi hi' bi bi'
              exact hshared i i' (hi.imp id (fun ⟨w, hw⟩ => ⟨w, hw.1⟩))
                (hi'.imp id (fun ⟨w, hw⟩ => ⟨w, hw.1⟩)) bi bi'
            obtain ⟨T', t, hT'cov, hT'sz, hGt⟩ := ih (2 * (delV K {l}).edgeSet.ncard + A.card)
              (by omega) (s - 2) (delV K {l}) A rfl (delV_acyclic K {l} hcyc)
              (fun a ha w hw => hAfree a ha w hw.1) hne0 hshared0 hJb
            refine ⟨insert p T', t, ?_, ?_, hGt⟩
            · intro u v huv
              by_cases hul : u = l
              · subst hul; rw [hleaf v huv]; exact Or.inr (Finset.mem_insert_self p _)
              · by_cases hvl : v = l
                · subst hvl; rw [hleaf u huv.symm]; exact Or.inl (Finset.mem_insert_self p _)
                · rcases hT'cov u v ⟨huv, by simpa using hul, by simpa using hvl⟩ with hu | hv
                  · exact Or.inl (Finset.mem_insert_of_mem hu)
                  · exact Or.inr (Finset.mem_insert_of_mem hv)
            · have := Finset.card_insert_le p T'
              omega
          · rw [hrt] at hJb
            obtain ⟨hdrop2, hlt2⟩ := delV_leaf2_ncard K l p q hlp hleaf hq
            have hAp_card : (insert p A).card = A.card + 1 := Finset.card_insert_of_notMem hpA
            have hAfree1 : ∀ a ∈ insert p A, ∀ w : Fin n, ¬ (delV K {l, p}).Adj a w := by
              intro a ha w hw
              rcases Finset.mem_insert.mp ha with rfl | haA
              · exact hw.2.1 (by simp)
              · exact hAfree a haA w hw.1
            have hshared1 : ∀ i i' : Fin n,
                (i ∈ insert p A ∨ ∃ w, (delV K {l, p}).Adj i w) →
                (i' ∈ insert p A ∨ ∃ w, (delV K {l, p}).Adj i' w) →
                bad i → bad i' → i = i' := by
              have hact : ∀ z : Fin n, (z ∈ insert p A ∨ ∃ w, (delV K {l, p}).Adj z w) →
                  (z ∈ A ∨ ∃ w, K.Adj z w) := by
                rintro z (hz | ⟨w, hw⟩)
                · rcases Finset.mem_insert.mp hz with rfl | hzA
                  · exact Or.inr ⟨l, hlp.symm⟩
                  · exact Or.inl hzA
                · exact Or.inr ⟨w, hw.1⟩
              intro i i' hi hi' bi bi'
              exact hshared i i' (hact i hi) (hact i' hi') bi bi'
            have hm_lt : 2 * (delV K {l, p}).edgeSet.ncard + (insert p A).card < m := by omega
            obtain ⟨T', t, hT'cov, hT'sz, hGt⟩ := ih
              (2 * (delV K {l, p}).edgeSet.ncard + (insert p A).card) hm_lt (s - 2)
              (delV K {l, p}) (insert p A) rfl (delV_acyclic K {l, p} hcyc)
              hAfree1 (Or.inl ⟨p, Finset.mem_insert_self p A⟩) hshared1 hJb
            refine ⟨insert p T', t, ?_, ?_, hGt⟩
            · intro u v huv
              by_cases hup : u = p
              · rw [hup]; exact Or.inl (Finset.mem_insert_self p _)
              · by_cases hvp : v = p
                · rw [hvp]; exact Or.inr (Finset.mem_insert_self p _)
                · have hul : u ≠ l := fun e => hvp (hleaf v (e ▸ huv))
                  have hvl : v ≠ l := fun e => hup (hleaf u (e ▸ huv.symm))
                  rcases hT'cov u v ⟨huv, by simp [hul, hup], by simp [hvl, hvp]⟩ with hu | hv
                  · exact Or.inl (Finset.mem_insert_of_mem hu)
                  · exact Or.inr (Finset.mem_insert_of_mem hv)
            · have := Finset.card_insert_le p T'
              omega
        · push Not at hne0
          obtain ⟨hA0, hE0⟩ := hne0
          have hAcard : A.card = 0 := by rw [hA0]; rfl
          have hE0_empty : (delV K {l}).edgeSet = ∅ := by
            ext e
            induction e using Sym2.ind with
            | _ u v =>
              simp only [SimpleGraph.mem_edgeSet, Set.mem_empty_iff_false, iff_false]
              exact hE0 u v
          have hEcard : K.edgeSet.ncard = 1 := by
            rw [hedge0, hE0_empty, Set.ncard_empty]
          obtain ⟨hs1, hJt⟩ := one_gate_multi n k s (fKA K A) G l true hdepl hnc_t hG_nc
            (fun j x => hG_indep_l j true x) hJ
          obtain ⟨C', ok', hsz', _, o', hev'⟩ := hJt
          refine ⟨{p}, s - 1, ?_, ?_, ⟨C', ok', hsz', o', fun x j => (hev' x).2 j⟩⟩
          · intro u v huv
            by_cases hul : u = l
            · subst hul; rw [hleaf v huv]; exact Or.inr (Finset.mem_singleton_self p)
            · by_cases hvl : v = l
              · subst hvl; rw [hleaf u huv.symm]; exact Or.inl (Finset.mem_singleton_self p)
              · exact False.elim (hE0 u v ⟨huv, by simpa using hul, by simpa using hvl⟩)
          · simp [hAcard, hEcard]
            omega
      · have hpl : p ≠ l := hlp.ne.symm
        have hpl'0 : (delV K {l}).Adj p l' := ⟨hpl', by simpa using hpl, by simpa using hl'l⟩
        have hnc_f : ∃ x y : Fin n → Bool,
            fKA K A (Function.update x l false) ≠ fKA K A (Function.update y l false) := by
          simp_rw [res_false_leaf K A l hlA]
          exact fKA_nc (delV K {l}) A (Or.inr ⟨p, l', hpl'0⟩)
        obtain ⟨hs1, hJf⟩ := one_gate_multi n k s (fKA K A) G l false hdepl hnc_f hG_nc
          (fun j x => hG_indep_l j false x) hJ
        rw [hrf] at hJf
        have hshared0 : ∀ i i' : Fin n,
            (i ∈ A ∨ ∃ w, (delV K {l}).Adj i w) → (i' ∈ A ∨ ∃ w, (delV K {l}).Adj i' w) →
            bad i → bad i' → i = i' := by
          intro i i' hi hi' bi bi'
          exact hshared i i' (hi.imp id (fun ⟨w, hw⟩ => ⟨w, hw.1⟩))
            (hi'.imp id (fun ⟨w, hw⟩ => ⟨w, hw.1⟩)) bi bi'
        obtain ⟨T', t, hT'cov, hT'sz, hGt⟩ := ih (2 * (delV K {l}).edgeSet.ncard + A.card)
          (by omega) (s - 1) (delV K {l}) A rfl (delV_acyclic K {l} hcyc)
          (fun a ha w hw => hAfree a ha w hw.1) (Or.inr ⟨p, l', hpl'0⟩) hshared0 hJf
        obtain ⟨T, hTcov, hTle⟩ := cov_swap K l p l' hl'l hpl' hleaf hleaf' T' hT'cov
        exact ⟨T, t, hTcov, by omega, hGt⟩
    · push Not at hE
      have hE_empty : K.edgeSet = ∅ := by
        ext e
        induction e using Sym2.ind with
        | _ u v =>
          simp only [SimpleGraph.mem_edgeSet, Set.mem_empty_iff_false, iff_false]
          exact hE u v
      have hEcard : K.edgeSet.ncard = 0 := by rw [hE_empty, Set.ncard_empty]
      have hAne : A.Nonempty := by
        rcases hne with hA | ⟨u, v, huv⟩
        · exact hA
        · exact False.elim (hE u v huv)
      by_cases hA1 : A.card = 1
      · obtain ⟨C, ok, hsz, _, o, hev⟩ := hJ
        refine ⟨∅, s, fun u v huv => False.elim (hE u v huv), by simp [hA1, hEcard]; omega,
          ⟨C, ok, hsz, o, fun x j => (hev x).2 j⟩⟩
      · have hA2 : 2 ≤ A.card := by
          have := Finset.card_pos.mpr hAne
          omega
        obtain ⟨a1, ha1, a2, ha2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
        have hex_a : ∃ a ∈ A, ¬ bad a := by
          by_cases hb1 : bad a1
          · refine ⟨a2, ha2, fun hb2 => h12 (hshared a1 a2 (Or.inl ha1) (Or.inl ha2) hb1 hb2)⟩
          · exact ⟨a1, ha1, hb1⟩
        obtain ⟨a, haA, ha_nb⟩ := hex_a
        have hdeea : ∃ x : Fin n → Bool,
            fKA K A (Function.update x a (!x a)) ≠ fKA K A x := fKA_dep_free K A a haA
        have hrf : (fun x => fKA K A (Function.update x a false)) = fKA K (A.erase a) :=
          funext (res_false_free K A a haA (hAfree a haA))
        have hAer_ne : (A.erase a).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem haA]
          omega
        have hnc_f : ∃ x y : Fin n → Bool,
            fKA K A (Function.update x a false) ≠ fKA K A (Function.update y a false) := by
          simp_rw [res_false_free K A a haA (hAfree a haA)]
          exact fKA_nc K (A.erase a) (Or.inl hAer_ne)
        obtain ⟨hs1, hJf⟩ := one_gate_multi n k s (fKA K A) G a false hdeea hnc_f hG_nc
          (fun j x => hnotbad_indep a ha_nb j false x) hJ
        rw [hrf] at hJf
        have hAer_card : (A.erase a).card = A.card - 1 := Finset.card_erase_of_mem haA
        have hshared_er : ∀ i i' : Fin n,
            (i ∈ A.erase a ∨ ∃ w, K.Adj i w) → (i' ∈ A.erase a ∨ ∃ w, K.Adj i' w) →
            bad i → bad i' → i = i' := by
          intro i i' hi hi' bi bi'
          exact hshared i i' (hi.imp (fun h => (Finset.mem_erase.mp h).2) id)
            (hi'.imp (fun h => (Finset.mem_erase.mp h).2) id) bi bi'
        obtain ⟨T, t, hTcov, hTsz, hGt⟩ := ih (2 * K.edgeSet.ncard + (A.erase a).card)
          (by omega) (s - 1) K (A.erase a) rfl hcyc
          (fun b hb w => hAfree b (Finset.mem_erase.mp hb).2 w) (Or.inl hAer_ne) hshared_er hJf
        exact ⟨T, t, hTcov, by omega, hGt⟩

def orChainAcc : ℕ → ℕ → List ℕ → List Gate × ℕ
  | _, cur, [] => ([], cur)
  | base, cur, w :: rest =>
    let r := orChainAcc (base + 1) base rest
    (⟨GateOp.or, [cur, w]⟩ :: r.1, r.2)

def orChain (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | w :: rest => orChainAcc base w rest

lemma orChainAcc_len : ∀ (base cur : ℕ) (rest : List ℕ),
    (orChainAcc base cur rest).1.length = rest.length := by
  intro base cur rest
  induction rest generalizing base cur with
  | nil => simp [orChainAcc]
  | cons w rest' ih =>
    simp only [orChainAcc, List.length_cons]
    rw [ih]

lemma orChain_len (base : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (orChain base ws).1.length + 1 = ws.length := by
  cases ws with
  | nil => exact False.elim (hne rfl)
  | cons w rest =>
    simp [orChain, orChainAcc_len]

lemma orChainAcc_ok : ∀ (base cur : ℕ) (rest : List ℕ) (g : Gate),
    g ∈ (orChainAcc base cur rest).1 → Ok g := by
  intro base cur rest
  induction rest generalizing base cur with
  | nil => intro g hg; simp [orChainAcc] at hg
  | cons w rest' ih =>
    intro g hg
    simp only [orChainAcc, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · exact ih (base + 1) base g hg

lemma orChain_ok (base : ℕ) (ws : List ℕ) (g : Gate)
    (hg : g ∈ (orChain base ws).1) : Ok g := by
  cases ws with
  | nil => simp [orChain] at hg
  | cons w rest => exact orChainAcc_ok base w rest g hg

lemma orChainAcc_eval : ∀ (rest : List ℕ) (cur : ℕ) (w : List Bool),
    cur < w.length → (∀ a ∈ rest, a < w.length) →
    (orChainAcc w.length cur rest).2 < w.length + (orChainAcc w.length cur rest).1.length ∧
    (wiresFrom (orChainAcc w.length cur rest).1 w).getD (orChainAcc w.length cur rest).2 false =
      (w.getD cur false || rest.any (fun a => w.getD a false)) := by
  intro rest
  induction rest with
  | nil =>
    intro cur w hcur _
    simp [orChainAcc, wiresFrom, hcur]
  | cons w2 rest' ih =>
    intro cur w hcur hlt
    let v : Bool := w.getD cur false || w.getD w2 false
    have hstep : wiresFrom (orChainAcc w.length cur (w2 :: rest')).1 w =
        wiresFrom (orChainAcc (w.length + 1) w.length rest').1 (w ++ [v]) := by
      simp only [orChainAcc]
      change wiresFrom (orChainAcc (w.length + 1) w.length rest').1
        (w ++ [GateOp.or.eval ([cur, w2].map fun i => w.getD i false)]) = _
      simp [GateOp.eval, v]
    have hlen : (w ++ [v]).length = w.length + 1 := by simp
    have hlt' : ∀ a ∈ rest', a < (w ++ [v]).length := by
      intro a ha
      rw [hlen]
      have := hlt a (List.mem_cons_of_mem _ ha)
      omega
    have hrec := ih w.length (w ++ [v]) (by rw [hlen]; omega) hlt'
    rw [hlen] at hrec
    refine ⟨?_, ?_⟩
    · simp only [orChainAcc, List.length_cons]
      have := hrec.1
      omega
    · simp only [orChainAcc] at hstep ⊢
      rw [hstep, hrec.2]
      have htail : rest'.any (fun a => (w ++ [v]).getD a false) =
          rest'.any (fun a => w.getD a false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        constructor
        · rintro ⟨a, ha, h⟩
          have ha_lt := hlt a (List.mem_cons_of_mem _ ha)
          rw [getD_snoc_ne _ _ _ _ (by omega)] at h
          exact ⟨a, ha, h⟩
        · rintro ⟨a, ha, h⟩
          have ha_lt := hlt a (List.mem_cons_of_mem _ ha)
          exact ⟨a, ha, by rwa [getD_snoc_ne _ _ _ _ (by omega)]⟩
      have hhead : (w ++ [v]).getD w.length false = v := getD_snoc_eq w v false
      simp only [List.any_cons, hhead, htail, v, Bool.or_assoc]

lemma orChain_eval (ws : List ℕ) (w : List Bool) (hne : ws ≠ [])
    (hlt : ∀ a ∈ ws, a < w.length) :
    (orChain w.length ws).2 < w.length + (orChain w.length ws).1.length ∧
    (wiresFrom (orChain w.length ws).1 w).getD (orChain w.length ws).2 false =
      ws.any (fun a => w.getD a false) := by
  cases ws with
  | nil => exact False.elim (hne rfl)
  | cons w1 rest =>
    have h := orChainAcc_eval rest w1 w (hlt w1 List.mem_cons_self)
      (fun a ha => hlt a (List.mem_cons_of_mem _ ha))
    simpa [orChain, List.any_cons] using h

def buildStars : ℕ → List (Fin n × List (Fin n)) → List Gate × List ℕ
  | _, [] => ([], [])
  | base, (v, us) :: rest =>
    let r1 := orChain base (us.map Fin.val)
    let b1 := base + r1.1.length
    let gAnd : Gate := ⟨GateOp.and, [v.val, r1.2]⟩
    let r2 := buildStars (b1 + 1) rest
    (r1.1 ++ gAnd :: r2.1, b1 :: r2.2)

lemma buildStars_len {n : ℕ} : ∀ (base : ℕ) (stars : List (Fin n × List (Fin n))),
    (∀ p ∈ stars, p.2 ≠ []) →
    (buildStars base stars).1.length = (stars.map (fun p => p.2.length)).sum ∧
    (buildStars base stars).2.length = stars.length := by
  intro base stars
  induction stars generalizing base with
  | nil => intro _; simp [buildStars]
  | cons hd rest ih =>
    rcases hd with ⟨v, us⟩
    intro hne
    have hus : us ≠ [] := hne (v, us) List.mem_cons_self
    have h1 := orChain_len base (us.map Fin.val) (by simpa using hus)
    have h2 := ih (base + (orChain base (us.map Fin.val)).1.length + 1)
      (fun p hp => hne p (List.mem_cons_of_mem _ hp))
    simp only [buildStars, List.length_append, List.length_cons, List.map_cons, List.sum_cons]
    simp only [List.length_map] at h1
    exact ⟨by omega, by omega⟩

lemma buildStars_ok {n : ℕ} : ∀ (base : ℕ) (stars : List (Fin n × List (Fin n))) (g : Gate),
    g ∈ (buildStars base stars).1 → Ok g := by
  intro base stars
  induction stars generalizing base with
  | nil => intro g hg; simp [buildStars] at hg
  | cons hd rest ih =>
    rcases hd with ⟨v, us⟩
    intro g hg
    simp only [buildStars, List.mem_append, List.mem_cons] at hg
    rcases hg with h1 | rfl | h2
    · exact orChain_ok base (us.map Fin.val) g h1
    · exact ⟨Or.inl rfl, by simp⟩
    · exact ih _ g h2

lemma buildStars_eval {n : ℕ} :
    ∀ (stars : List (Fin n × List (Fin n))) (w : List Bool),
      n ≤ w.length →
      (∀ p ∈ stars, p.2 ≠ []) →
      (∀ a ∈ (buildStars w.length stars).2, a < w.length + (buildStars w.length stars).1.length) ∧
      ((buildStars w.length stars).2.any (fun a => (wiresFrom (buildStars w.length stars).1 w).getD a false) =
        stars.any (fun p => w.getD p.1.val false && p.2.any (fun u => w.getD u.val false))) := by
  intro stars
  induction stars with
  | nil => intro w _ _; simp [buildStars]
  | cons hd rest ih =>
    rcases hd with ⟨v, us⟩
    intro w hwn hne
    have hus : us ≠ [] := hne (v, us) List.mem_cons_self
    have hus_lt : ∀ a ∈ us.map Fin.val, a < w.length := by
      intro a ha
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
      omega
    have hor := orChain_eval (us.map Fin.val) w (by simpa using hus) hus_lt
    set r1 := orChain w.length (us.map Fin.val)
    set w1 := wiresFrom r1.1 w
    have hw1_len : w1.length = w.length + r1.1.length := length_wiresFrom r1.1 w
    set gAnd : Gate := ⟨GateOp.and, [v.val, r1.2]⟩
    set w2 := w1 ++ [w1.getD v.val false && w1.getD r1.2 false]
    have hw2_eq : wiresFrom (r1.1 ++ [gAnd]) w = w2 := by
      rw [wiresFrom_append]
      change wiresFrom [] (w1 ++ [GateOp.and.eval ([v.val, r1.2].map fun i => w1.getD i false)]) = w2
      simp [wiresFrom, GateOp.eval, w2]
    have hw2_len : w2.length = w.length + r1.1.length + 1 := by simp [w2, hw1_len]
    have hrec := ih w2 (by omega) (fun p hp => hne p (List.mem_cons_of_mem _ hp))
    rw [hw2_len] at hrec
    have hwf : wiresFrom (buildStars w.length ((v, us) :: rest)).1 w =
        wiresFrom (buildStars (w.length + r1.1.length + 1) rest).1 w2 := by
      simp only [buildStars]
      have hassoc : r1.1 ++ gAnd :: (buildStars (w.length + r1.1.length + 1) rest).1 =
          (r1.1 ++ [gAnd]) ++ (buildStars (w.length + r1.1.length + 1) rest).1 := by simp
      rw [hassoc, wiresFrom_append, hw2_eq]
    have hw_pres : ∀ a < w.length, w2.getD a false = w.getD a false := by
      intro a ha
      dsimp [w2, w1]
      rw [getD_snoc_ne _ _ _ _ (by rw [hw1_len]; omega), getD_wiresFrom r1.1 w a ha]
    have hhead_val : (wiresFrom (buildStars (w.length + r1.1.length + 1) rest).1 w2).getD
        (w.length + r1.1.length) false =
        (w.getD v.val false && us.any (fun u => w.getD u.val false)) := by
      rw [getD_wiresFrom _ w2 (w.length + r1.1.length) (by omega)]
      dsimp [w2]
      rw [getD_snoc_len _ _ _ _ hw1_len]
      have hv_val : w1.getD v.val false = w.getD v.val false := getD_wiresFrom r1.1 w v.val (by omega)
      have hr1_val : w1.getD r1.2 false = us.any (fun u => w.getD u.val false) := by
        dsimp [w1, r1]
        rw [hor.2]
        simp [List.any_map, Function.comp_def]
      rw [hv_val, hr1_val]
    constructor
    · intro a ha
      simp only [buildStars, List.mem_cons, List.length_append, List.length_cons] at ha ⊢
      rcases ha with rfl | ha'
      · omega
      · have := hrec.1 a ha'
        dsimp [r1] at this
        omega
    · have h2 : (buildStars w.length ((v, us) :: rest)).2 =
          (w.length + r1.1.length) :: (buildStars (w.length + r1.1.length + 1) rest).2 := rfl
      rw [h2, List.any_cons, hwf, hhead_val, hrec.2]
      simp only [List.any_cons]
      congr 1
      apply List.any_congr rfl
      intro p
      have hp1 : w2.getD p.1.val false = w.getD p.1.val false := hw_pres p.1.val (by omega)
      have hp2 : p.2.any (fun u => w2.getD u.val false) = p.2.any (fun u => w.getD u.val false) := by
        apply List.any_congr rfl
        intro u
        exact hw_pres u.val (by omega)
      rw [hp1, hp2]

lemma upper_bound (n k s : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (G : Fin k → (Fin n → Bool) → Bool)
    (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v)
    (hG_nc : ∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y')
    (T : Finset (Fin n)) (t : ℕ)
    (hTcov : ∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T)
    (hsz : A.card + K.edgeSet.ncard + T.card + t ≤ s + 1)
    (hGt : JointG n k G t) :
    JointFG n k (fKA K A) G s := by
  classical
  obtain ⟨C', ok', hC'sz, o, hevG⟩ := hGt
  have hC'sz' : C'.gates.length ≤ t := hC'sz
  have ho_lt : ∀ j : Fin k, o j < n + C'.gates.length := by
    intro j
    by_contra h
    obtain ⟨y, y', hy⟩ := hG_nc j
    apply hy
    rw [← hevG y j, ← hevG y' j]
    have hlen : ∀ x : Fin n → Bool, (C'.wires (List.ofFn x)).length = n + C'.gates.length := by
      intro x
      change (wiresFrom C'.gates (List.ofFn x)).length = _
      rw [length_wiresFrom]
      simp
    rw [List.getD_eq_default _ _ (by rw [hlen y]; omega),
      List.getD_eq_default _ _ (by rw [hlen y']; omega)]
  have howner : ∀ e : Sym2 (Fin n), e ∈ K.edgeSet → ∃ v ∈ T, v ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rcases hTcov u v he with hu | hv
      · exact ⟨u, hu, by simp⟩
      · exact ⟨v, hv, by simp⟩
  let owner (e : Sym2 (Fin n)) : Option (Fin n) :=
    if h : e ∈ K.edgeSet then some (Classical.choose (howner e h)) else none
  have howner_spec : ∀ (u v : Fin n) (h : K.Adj u v),
      ∃ c ∈ T, owner s(u, v) = some c ∧ (c = u ∨ c = v) := by
    intro u v h
    have he : s(u, v) ∈ K.edgeSet := h
    have hsp := Classical.choose_spec (howner s(u, v) he)
    refine ⟨Classical.choose (howner s(u, v) he), hsp.1, by simp [owner, he], ?_⟩
    simpa [Sym2.mem_iff] using hsp.2
  let nbrs (v : Fin n) : Finset (Fin n) :=
    Finset.univ.filter (fun u : Fin n => K.Adj v u ∧ owner s(v, u) = some v)
  have hsum_nbrs : ∑ v ∈ T, (nbrs v).card = K.edgeSet.ncard := by
    let E : Finset (Sym2 (Fin n)) := Finset.univ.filter (fun e => e ∈ K.edgeSet)
    have hE_card : E.card = K.edgeSet.ncard := by
      rw [Set.ncard_eq_toFinset_card' K.edgeSet]
      congr 1
      ext e
      simp [E]
    rw [← hE_card]
    have hfib := Finset.card_eq_sum_card_fiberwise (s := E) (t := T)
      (f := fun e => (owner e).getD (if h : 0 < n then ⟨0, h⟩ else Classical.choice (by
        rcases hne with ⟨a, _⟩ | ⟨a, _, _⟩ <;> exact ⟨a⟩)) )
      (by
        intro e he
        have heK : e ∈ K.edgeSet := (Finset.mem_filter.mp he).2
        simp only [owner, heK, ↓reduceDIte, Option.getD_some]
        exact (Classical.choose_spec (howner e heK)).1)
    rw [hfib]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.card_bij (fun u _ => s(v, u))
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'.1⟩, ?_⟩
      simp [hu'.2]
    · intro u1 hu1 u2 hu2 h
      have h1 := (Finset.mem_filter.mp hu1).2.1
      rw [Sym2.eq_iff] at h
      rcases h with ⟨_, e⟩ | ⟨_, e2⟩
      · exact e
      · exact False.elim (K.loopless.irrefl v (e2 ▸ h1))
    · intro e he
      have heK : e ∈ K.edgeSet := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      have hev : owner e = some v := by
        have h2 := (Finset.mem_filter.mp he).2
        simp only [owner, heK, ↓reduceDIte, Option.getD_some] at h2
        simp [owner, heK, h2]
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨c, _, hc, hcab⟩ := howner_spec a b heK
        rw [hev] at hc
        have hcv : c = v := Option.some.inj hc.symm
        subst hcv
        rcases hcab with rfl | rfl
        · exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heK, hev⟩, rfl⟩
        · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heK.symm, by rwa [Sym2.eq_swap]⟩,
            Sym2.eq_swap⟩
  let T1 : Finset (Fin n) := T.filter (fun v => (nbrs v).Nonempty)
  have hT1_le : T1.card ≤ T.card := Finset.card_filter_le _ _
  have hsum_T1 : ∑ v ∈ T1, (nbrs v).card = K.edgeSet.ncard := by
    rw [← hsum_nbrs]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hvT hv
    simp only [Finset.mem_filter, not_and] at hv
    have hemp : nbrs v = ∅ := Finset.not_nonempty_iff_eq_empty.mp (hv hvT)
    simp [hemp]
  let stars : List (Fin n × List (Fin n)) := T1.toList.map (fun v => (v, (nbrs v).toList))
  have hstars_ne : ∀ p ∈ stars, p.2 ≠ [] := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    have hne_v : (nbrs v).Nonempty := (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
    intro hemp
    dsimp at hemp
    obtain ⟨u, hu⟩ := hne_v
    have hmem : u ∈ (nbrs v).toList := Finset.mem_toList.mpr hu
    rw [hemp] at hmem
    simp at hmem
  let base0 := n + C'.gates.length
  let rStars := buildStars base0 stars
  have hstars_len : rStars.1.length = K.edgeSet.ncard ∧ rStars.2.length = T1.card := by
    obtain ⟨h1, h2⟩ := buildStars_len base0 stars hstars_ne
    refine ⟨?_, ?_⟩
    · rw [h1]
      have hmap : stars.map (fun p => p.2.length) = T1.toList.map (fun v => (nbrs v).card) := by
        simp [stars, List.map_map, Function.comp_def]
      rw [hmap, ← hsum_T1]
      rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    · rw [h2]
      simp [stars]
  let topWires : List ℕ := A.toList.map Fin.val ++ rStars.2
  have htop_len : topWires.length = A.card + T1.card := by
    simp [topWires, hstars_len.2]
  have htop_ne : topWires ≠ [] := by
    intro hemp
    have h0 : A.card + T1.card = 0 := by rw [← htop_len, hemp]; rfl
    rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
    · have := Finset.card_pos.mpr ⟨a, ha⟩; omega
    · obtain ⟨c, hcT, hc_own, hcab⟩ := howner_spec u v huv
      have hne_c : (nbrs c).Nonempty := by
        rcases hcab with rfl | rfl
        · exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hc_own⟩⟩
        · exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, by rwa [Sym2.eq_swap]⟩⟩
      have hcT1 : c ∈ T1 := Finset.mem_filter.mpr ⟨hcT, hne_c⟩
      have := Finset.card_pos.mpr ⟨c, hcT1⟩
      omega
  let base1 := base0 + rStars.1.length
  let rTop := orChain base1 topWires
  have htop_gates : rTop.1.length + 1 = A.card + T1.card := by
    rw [← htop_len]
    exact orChain_len base1 topWires htop_ne
  let allGates : List Gate := C'.gates ++ rStars.1 ++ rTop.1
  have hall_ok : FanInTwo ⟨allGates, rTop.2⟩ := by
    intro g hg
    simp only [allGates, List.mem_append] at hg
    rcases hg with (h | h) | h
    · exact ok' g h
    · exact buildStars_ok base0 stars g h
    · exact orChain_ok base1 topWires g h
  have hall_sz : (⟨allGates, rTop.2⟩ : Circuit).size ≤ s := by
    change allGates.length ≤ s
    simp only [allGates, List.length_append, hstars_len.1]
    omega
  refine ⟨⟨allGates, rTop.2⟩, hall_ok, hall_sz, rTop.2, o, ?_⟩
  intro x
  set w0 := wiresFrom C'.gates (List.ofFn x)
  have hw0_len : w0.length = base0 := by
    dsimp [w0, base0]
    rw [length_wiresFrom]
    simp
  set w1 := wiresFrom rStars.1 w0
  have hw1_len : w1.length = base1 := by
    dsimp [w1, base1]
    rw [length_wiresFrom, hw0_len]
  have hwall : (⟨allGates, rTop.2⟩ : Circuit).wires (List.ofFn x) = wiresFrom rTop.1 w1 := by
    change wiresFrom (C'.gates ++ rStars.1 ++ rTop.1) (List.ofFn x) = _
    rw [wiresFrom_append, wiresFrom_append]
  have hstars_ev := buildStars_eval stars w0 (by rw [hw0_len]; dsimp [base0]; omega) hstars_ne
  rw [hw0_len] at hstars_ev
  have htop_lt : ∀ a ∈ topWires, a < w1.length := by
    intro a ha
    rw [hw1_len]
    simp only [topWires, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨u, _, rfl⟩ | ha2
    · dsimp [base1, base0]; omega
    · exact hstars_ev.1 a ha2
  have htop_ev := orChain_eval topWires w1 htop_ne htop_lt
  rw [hw1_len] at htop_ev
  constructor
  · rw [hwall, htop_ev.2]
    apply Bool.eq_iff_iff.mpr
    rw [fKA_eq_true]
    simp only [topWires, List.any_append, Bool.or_eq_true, List.any_map]
    have hA_iff : (A.toList.any (fun a => w1.getD a.val false) = true) ↔ ∃ a ∈ A, x a = true := by
      simp only [List.any_eq_true, Finset.mem_toList]
      constructor
      · rintro ⟨a, ha, hwa⟩
        have : w1.getD a.val false = x a := by
          dsimp [w1, w0]
          rw [getD_wiresFrom rStars.1 _ a.val (by rw [hw0_len]; dsimp [base0]; omega),
            getD_wiresFrom C'.gates (List.ofFn x) a.val (by simp)]
          simp
        rw [this] at hwa
        exact ⟨a, ha, hwa⟩
      · rintro ⟨a, ha, hxa⟩
        refine ⟨a, ha, ?_⟩
        dsimp [w1, w0]
        rw [getD_wiresFrom rStars.1 _ a.val (by rw [hw0_len]; dsimp [base0]; omega),
          getD_wiresFrom C'.gates (List.ofFn x) a.val (by simp)]
        simpa using hxa
    have hE_iff : (rStars.2.any (fun a => w1.getD a false) = true) ↔
        ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true := by
      rw [show w1 = wiresFrom rStars.1 w0 from rfl, hstars_ev.2]
      simp only [stars, List.any_map, List.any_eq_true, Function.comp_def, Bool.and_eq_true,
        Finset.mem_toList]
      have hw0_in : ∀ u : Fin n, w0.getD u.val false = x u := by
        intro u
        dsimp [w0]
        rw [getD_wiresFrom C'.gates (List.ofFn x) u.val (by simp)]
        simp
      constructor
      · rintro ⟨v, _, hvx, u, hu, hux⟩
        rw [hw0_in v] at hvx
        rw [hw0_in u] at hux
        exact ⟨v, u, (Finset.mem_filter.mp hu).2.1, hvx, hux⟩
      · rintro ⟨u, v, huv, hux, hvx⟩
        obtain ⟨c, hcT, hc_own, hcab⟩ := howner_spec u v huv
        rcases hcab with hcu | hcv
        · rw [hcu] at hcT hc_own
          have hv_mem : v ∈ nbrs u := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hc_own⟩
          exact ⟨u, Finset.mem_filter.mpr ⟨hcT, ⟨v, hv_mem⟩⟩, by rw [hw0_in]; exact hux,
            v, hv_mem, by rw [hw0_in]; exact hvx⟩
        · rw [hcv] at hcT hc_own
          have hu_mem : u ∈ nbrs v :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm, by rwa [Sym2.eq_swap]⟩
          exact ⟨v, Finset.mem_filter.mpr ⟨hcT, ⟨u, hu_mem⟩⟩, by rw [hw0_in]; exact hvx,
            u, hu_mem, by rw [hw0_in]; exact hux⟩
    simp only [Function.comp_def]
    rw [hA_iff, hE_iff]
  · intro j
    rw [hwall]
    dsimp [w1]
    rw [getD_wiresFrom rTop.1 _ (o j) (by rw [length_wiresFrom, hw0_len]; dsimp [base0]; have := ho_lt j; omega),
      getD_wiresFrom rStars.1 w0 (o j) (by rw [hw0_len]; exact ho_lt j)]
    exact hevG x j

end PEqualNP.Outside.L_meta_659

theorem PEqualNP.Outside.L_meta_659 :
    ∀ (n k s : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (G : Fin k → (Fin n → Bool) → Bool), (∀ (v : Fin n) (c : K.Walk v v), ¬ c.IsCycle) → (∀ a ∈ A, ∀ w : Fin n, ¬ K.Adj a w) → (A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) → (∀ j : Fin k, ∃ y y' : Fin n → Bool, G j y ≠ G j y') → (∀ i i' : Fin n, (i ∈ A ∨ ∃ w, K.Adj i w) → (i' ∈ A ∨ ∃ w, K.Adj i' w) → (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i false) ≠ G j (Function.update x i true)) → (∃ (j : Fin k) (x : Fin n → Bool), G j (Function.update x i' false) ≠ G j (Function.update x i' true)) → i = i') → ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ (o1 : ℕ) (o : Fin k → ℕ), ∀ x : Fin n → Bool, ((C.wires (List.ofFn x)).getD o1 false = true ↔ ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)) ∧ ∀ j : Fin k, (C.wires (List.ofFn x)).getD (o j) false = G j x) ↔ ∃ (T : Finset (Fin n)) (t : ℕ), (∀ u v : Fin n, K.Adj u v → u ∈ T ∨ v ∈ T) ∧ A.card + K.edgeSet.ncard + T.card + t ≤ s + 1 ∧ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ t ∧ ∃ o : Fin k → ℕ, ∀ (x : Fin n → Bool) (j : Fin k), (C.wires (List.ofFn x)).getD (o j) false = G j x) := by
  intro n k s K A G hcyc hAfree hne hG_nc hshared
  constructor
  · rintro ⟨C, ok, hsz, o1, o, hev⟩
    have hJ : PEqualNP.Outside.L_meta_659.JointFG n k (PEqualNP.Outside.L_meta_659.fKA K A) G s := by
      refine ⟨C, ok, hsz, o1, o, fun x => ⟨?_, (hev x).2⟩⟩
      apply Bool.eq_iff_iff.mpr
      rw [PEqualNP.Outside.L_meta_659.fKA_eq_true]
      exact (hev x).1
    exact PEqualNP.Outside.L_meta_659.lower_bound_aux n k G hG_nc
      (2 * K.edgeSet.ncard + A.card) s K A rfl hcyc hAfree hne hshared hJ
  · rintro ⟨T, t, hTcov, hsz, C', ok', hC'sz, o, hevG⟩
    have hJ := PEqualNP.Outside.L_meta_659.upper_bound n k s K A G hne hG_nc T t hTcov hsz
      ⟨C', ok', hC'sz, o, hevG⟩
    obtain ⟨C, ok, hCsz, o1, o', hev⟩ := hJ
    refine ⟨C, ok, hCsz, o1, o', fun x => ⟨?_, (hev x).2⟩⟩
    rw [(hev x).1, PEqualNP.Outside.L_meta_659.fKA_eq_true]
