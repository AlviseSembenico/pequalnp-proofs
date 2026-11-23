import Mathlib

namespace PEqualNP.Outside.L_meta_664

lemma two_eq_zero (F : Type) [Field F] [CharP F 2] : (2 : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F 2

lemma add_self_zero {F : Type} [Field F] [CharP F 2] (x : F) : x + x = 0 := by
  have h2 : (2 : F) = 0 := two_eq_zero F
  calc
    x + x = 2 * x := by ring
    _ = 0 * x := by rw [h2]
    _ = 0 := zero_mul x

lemma add_sq_char2 {F : Type} [Field F] [CharP F 2] (x y : F) :
    (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  have h2 : (2 : F) = 0 := two_eq_zero F
  calc
    (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
    _ = x ^ 2 + 0 * (x * y) + y ^ 2 := by rw [h2]
    _ = x ^ 2 + y ^ 2 := by ring

lemma add_eq_zero_iff {F : Type} [Field F] [CharP F 2] (x y : F) :
    x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = x + (y + y) := by rw [add_self_zero y, add_zero]
      _ = (x + y) + y := by ring
      _ = 0 + y := by rw [h]
      _ = y := zero_add y
  · rintro rfl
    exact add_self_zero x

lemma add_cancel_char2 {F : Type} [Field F] [CharP F 2] (x y : F) :
    x + y + y = x := by
  rw [add_assoc, add_self_zero y, add_zero]

lemma sq_eq_zero_of_field {F : Type} [Field F] {x : F} (h : x ^ 2 = 0) : x = 0 := by
  rw [sq, mul_eq_zero] at h
  exact h.elim id id

def Q {F : Type} [Field F] (b : F) (v : F × F) : F :=
  v.1 ^ 2 + b * v.1 * v.2 + v.2 ^ 2

lemma Q_eq_zero_iff {F : Type} [Field F] (b : F)
    (hb : ∀ X : F, X ^ 2 + b * X + 1 ≠ 0) (v : F × F) :
    Q b v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    by_cases h2 : v.2 = 0
    · have h1 : v.1 ^ 2 = 0 := by
        simpa [Q, h2] using hv
      exact Prod.ext (sq_eq_zero_of_field h1) h2
    · exfalso
      have hne : (v.1 / v.2) ^ 2 + b * (v.1 / v.2) + 1 ≠ 0 := hb (v.1 / v.2)
      apply hne
      have hmul : ((v.1 / v.2) ^ 2 + b * (v.1 / v.2) + 1) * v.2 ^ 2 = Q b v := by
        unfold Q
        field_simp [h2]
      have h0 : ((v.1 / v.2) ^ 2 + b * (v.1 / v.2) + 1) * v.2 ^ 2 = 0 := by
        rw [hmul, hv]
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact False.elim (h2 (sq_eq_zero_of_field h))
  · rintro rfl
    simp [Q]

lemma Q_line {F : Type} [Field F] [CharP F 2] (b : F) (p d : F × F) (t : F) :
    Q b (p + t • d) = (Q b d * t ^ 2 + b * (p.1 * d.2 + p.2 * d.1) * t) + Q b p := by
  have h2 : (2 : F) = 0 := two_eq_zero F
  unfold Q
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  calc
    (p.1 + t * d.1) ^ 2 + b * (p.1 + t * d.1) * (p.2 + t * d.2) + (p.2 + t * d.2) ^ 2
        = ((d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * t ^ 2 +
            b * (p.1 * d.2 + p.2 * d.1) * t) +
            (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) +
            2 * (p.1 * t * d.1 + p.2 * t * d.2) := by ring
    _ = ((d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * t ^ 2 +
            b * (p.1 * d.2 + p.2 * d.1) * t) +
            (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) +
            0 * (p.1 * t * d.1 + p.2 * t * d.2) := by rw [h2]
    _ = ((d.1 ^ 2 + b * d.1 * d.2 + d.2 ^ 2) * t ^ 2 +
            b * (p.1 * d.2 + p.2 * d.1) * t) +
            (p.1 ^ 2 + b * p.1 * p.2 + p.2 ^ 2) := by ring

lemma lin_add {F : Type} [Field F] [CharP F 2] (c a x y : F) :
    (c * (x + y) ^ 2 + a * (x + y)) = (c * x ^ 2 + a * x) + (c * y ^ 2 + a * y) := by
  rw [add_sq_char2]
  ring

lemma card_filter_mem_eq_natCard {F : Type} [Field F] [Fintype F]
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] :
    (Finset.univ.filter (fun y : F => y ∈ A)).card = Nat.card A := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]

lemma case_a_zero {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (A : AddSubgroup F) [DecidablePred (· ∈ A)] (c q0 : F) (hc : c ≠ 0) :
    (Finset.univ.filter (fun t : F => c * t ^ 2 + q0 ∈ A)).card = Nat.card A := by
  let f : F → F := fun t => c * t ^ 2 + q0
  have hinj : Function.Injective f := by
    intro t1 t2 h
    have h1 : c * t1 ^ 2 = c * t2 ^ 2 := add_right_cancel h
    have h2 : t1 ^ 2 = t2 ^ 2 := mul_left_cancel₀ hc h1
    have h3 : (t1 + t2) ^ 2 = 0 := by
      rw [add_sq_char2, h2, add_self_zero]
    exact (add_eq_zero_iff t1 t2).mp (sq_eq_zero_of_field h3)
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  rw [← card_filter_mem_eq_natCard A]
  apply Finset.card_bij (fun t _ => f t)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht
  · intro t1 _ t2 _ h
    exact hinj h
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hbij.2 y with ⟨t, rfl⟩
    exact ⟨t, by simp [f, hy], rfl⟩

lemma case_a_ne_zero {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (A : AddSubgroup F) [DecidablePred (· ∈ A)]
    (c a q0 : F) (hc : c ≠ 0) (ha : a ≠ 0)
    (hq0 : ∀ t : F, c * t ^ 2 + a * t ≠ q0) :
    (Finset.univ.filter (fun t : F => (c * t ^ 2 + a * t) + q0 ∈ A)).card = 0 ∨
      (Finset.univ.filter (fun t : F => (c * t ^ 2 + a * t) + q0 ∈ A)).card = Nat.card A := by
  let L : F → F := fun t => c * t ^ 2 + a * t
  let r : F := a / c
  have hr0 : r ≠ 0 := div_ne_zero ha hc
  have hL_add : ∀ x y : F, L (x + y) = L x + L y := fun x y => lin_add c a x y
  have hL_zero_iff : ∀ t : F, L t = 0 ↔ t = 0 ∨ t = r := by
    intro t
    have hfac : L t = t * (c * t + a) := by
      dsimp [L]
      ring
    rw [hfac, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have hct : c * t = a := (add_eq_zero_iff (c * t) a).mp h
        dsimp [r]
        field_simp [hc]
        rw [mul_comm, hct]
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · right
        have hcr : c * r = a := by
          dsimp [r]
          exact mul_div_cancel₀ a hc
        rw [hcr, add_self_zero]
  have hL_eq_iff : ∀ t1 t2 : F, L t1 = L t2 ↔ t2 = t1 ∨ t2 = t1 + r := by
    intro t1 t2
    rw [← add_eq_zero_iff (L t1) (L t2), ← hL_add, hL_zero_iff]
    constructor
    · rintro (h | h)
      · left
        exact ((add_eq_zero_iff t1 t2).mp h).symm
      · right
        calc
          t2 = t1 + (t1 + t2) := by
            rw [← add_assoc, add_self_zero, zero_add]
          _ = t1 + r := by rw [h]
    · rintro (h | h)
      · left
        rw [h]
        exact add_self_zero t1
      · right
        rw [h, ← add_assoc, add_self_zero, zero_add]
  let I : Finset F := Finset.univ.image L
  have hI_add : ∀ x ∈ I, ∀ y ∈ I, x + y ∈ I := by
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨tx, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨ty, _, rfl⟩
    exact Finset.mem_image.mpr ⟨tx + ty, Finset.mem_univ _, hL_add tx ty⟩
  have hfiber_card : ∀ y ∈ I, (Finset.univ.filter (fun t : F => L t = y)).card = 2 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨t0, _, rfl⟩
    have hset : Finset.univ.filter (fun t : F => L t = L t0) = {t0, t0 + r} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [eq_comm, hL_eq_iff]
    rw [hset, Finset.card_pair]
    intro heq
    have : r = 0 := by
      have h := congrArg (fun z => t0 + z) heq
      rw [add_self_zero, ← add_assoc, add_self_zero, zero_add] at h
      exact h.symm
    exact hr0 this
  have hI_card : I.card * 2 = Fintype.card F := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset F)) (t := I) (f := L)
      (fun x _ => Finset.mem_image_of_mem L (Finset.mem_univ x))
    rw [Finset.card_univ] at hsum
    have h2 : (∑ y ∈ I, (Finset.univ.filter (fun t : F => L t = y)).card) = I.card * 2 := by
      rw [Finset.sum_congr rfl hfiber_card, Finset.sum_const, smul_eq_mul]
    rw [← h2, ← hsum]
  have hnotI_add : ∀ u v : F, u ∉ I → v ∉ I → u + v ∈ I := by
    intro u v hu hv
    let J : Finset F := I.image (fun x => x + u)
    have hJ_card : J.card = I.card := by
      apply Finset.card_image_of_injective
      intro x1 x2 h
      exact add_right_cancel h
    have hdisj : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro x hxI hxJ
      rcases Finset.mem_image.mp hxJ with ⟨y, hyI, hyu⟩
      have huI : u ∈ I := by
        have hxy : x + y = u := by
          rw [← hyu]
          calc
            (y + u) + y = (y + y) + u := by ring
            _ = 0 + u := by rw [add_self_zero]
            _ = u := zero_add u
        rw [← hxy]
        exact hI_add x hxI y hyI
      exact hu huI
    have hunion_card : (I ∪ J).card = Fintype.card F := by
      rw [Finset.card_union_of_disjoint hdisj, hJ_card, ← mul_two, hI_card]
    have hunion_eq : I ∪ J = Finset.univ := Finset.eq_univ_of_card (I ∪ J) hunion_card
    have hv_mem : v ∈ I ∪ J := by
      rw [hunion_eq]
      exact Finset.mem_univ v
    rcases Finset.mem_union.mp hv_mem with hvI | hvJ
    · exact False.elim (hv hvI)
    · rcases Finset.mem_image.mp hvJ with ⟨y, hyI, hyu⟩
      have huv : u + v = y := by
        rw [← hyu]
        calc
          u + (y + u) = y + (u + u) := by ring
          _ = y + 0 := by rw [add_self_zero]
          _ = y := add_zero y
      rw [huv]
      exact hyI
  have hq0_notI : q0 ∉ I := by
    intro h
    rcases Finset.mem_image.mp h with ⟨t, _, ht⟩
    exact hq0 t ht
  let S : Finset F := Finset.univ.filter (fun t : F => L t + q0 ∈ A)
  let AF : Finset F := Finset.univ.filter (fun y : F => y ∈ A)
  let T : Finset F := AF.filter (fun x : F => x + q0 ∈ I)
  have hS_card : S.card = T.card * 2 := by
    let T' : Finset F := T.image (fun x => x + q0)
    have hT'_sub : T' ⊆ I := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact (Finset.mem_filter.mp hx).2
    have hT'_card : T'.card = T.card := by
      apply Finset.card_image_of_injective
      intro x1 x2 h
      exact add_right_cancel h
    have hS_maps : ∀ t ∈ S, L t ∈ T' := by
      intro t ht
      have htA : L t + q0 ∈ A := (Finset.mem_filter.mp ht).2
      apply Finset.mem_image.mpr
      refine ⟨L t + q0, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, htA⟩, ?_⟩
        rw [add_cancel_char2]
        exact Finset.mem_image_of_mem L (Finset.mem_univ t)
      · exact add_cancel_char2 (L t) q0
    have hsum := Finset.card_eq_sum_card_fiberwise (s := S) (t := T') (f := L) hS_maps
    have hfib : ∀ y ∈ T', (S.filter (fun t : F => L t = y)).card = 2 := by
      intro y hy
      have hfilter_eq : S.filter (fun t : F => L t = y) =
          Finset.univ.filter (fun t : F => L t = y) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
        constructor
        · exact fun h => h.2
        · intro hLt
          refine ⟨?_, hLt⟩
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          rw [hLt, add_cancel_char2]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      rw [hfilter_eq]
      exact hfiber_card y (hT'_sub hy)
    rw [hsum, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hT'_card]
  by_cases hsub : ∀ x ∈ AF, x ∈ I
  · left
    have hT_empty : T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hxAF : x ∈ AF := (Finset.mem_filter.mp hx).1
      have hxq0 : x + q0 ∈ I := (Finset.mem_filter.mp hx).2
      have hxI : x ∈ I := hsub x hxAF
      have hq0I : q0 ∈ I := by
        have h := hI_add x hxI (x + q0) hxq0
        have heq : x + (x + q0) = q0 := by
          rw [← add_assoc, add_self_zero, zero_add]
        rwa [heq] at h
      exact hq0_notI hq0I
    rw [hS_card, hT_empty, Finset.card_empty, zero_mul]
  · right
    push Not at hsub
    rcases hsub with ⟨x0, hx0AF, hx0_notI⟩
    have hx0A : x0 ∈ A := (Finset.mem_filter.mp hx0AF).2
    have hT_eq : T = AF.filter (fun x : F => x ∉ I) := by
      ext x
      simp only [T, Finset.mem_filter]
      constructor
      · rintro ⟨hxAF, hxq0⟩
        refine ⟨hxAF, ?_⟩
        intro hxI
        have hq0I : q0 ∈ I := by
          have h := hI_add x hxI (x + q0) hxq0
          have heq : x + (x + q0) = q0 := by
            rw [← add_assoc, add_self_zero, zero_add]
          rwa [heq] at h
        exact hq0_notI hq0I
      · rintro ⟨hxAF, hx_notI⟩
        exact ⟨hxAF, hnotI_add x q0 hx_notI hq0_notI⟩
    have hswap : (AF.filter (fun x : F => x ∈ I)).card =
        (AF.filter (fun x : F => x ∉ I)).card := by
      apply Finset.card_bij (fun x _ => x + x0)
      · intro x hx
        have hxAF : x ∈ AF := (Finset.mem_filter.mp hx).1
        have hxA : x ∈ A := (Finset.mem_filter.mp hxAF).2
        have hxI : x ∈ I := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, A.add_mem hxA hx0A⟩, ?_⟩
        intro hxx0I
        have hx0I : x0 ∈ I := by
          have h := hI_add x hxI (x + x0) hxx0I
          have heq : x + (x + x0) = x0 := by
            rw [← add_assoc, add_self_zero, zero_add]
          rwa [heq] at h
        exact hx0_notI hx0I
      · intro x1 _ x2 _ h
        exact add_right_cancel h
      · intro y hy
        have hyAF : y ∈ AF := (Finset.mem_filter.mp hy).1
        have hyA : y ∈ A := (Finset.mem_filter.mp hyAF).2
        have hy_notI : y ∉ I := (Finset.mem_filter.mp hy).2
        refine ⟨y + x0, ?_, add_cancel_char2 y x0⟩
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, A.add_mem hyA hx0A⟩,
            hnotI_add y x0 hy_notI hx0_notI⟩
    have hdisjA : Disjoint (AF.filter (fun x : F => x ∈ I)) (AF.filter (fun x : F => x ∉ I)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunionA : AF.filter (fun x : F => x ∈ I) ∪ AF.filter (fun x : F => x ∉ I) = AF := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases hx : x ∈ I
      · simp [hx]
      · simp [hx]
    have hsplit : (AF.filter (fun x : F => x ∈ I)).card +
        (AF.filter (fun x : F => x ∉ I)).card = AF.card := by
      rw [← Finset.card_union_of_disjoint hdisjA, hunionA]
    rw [hswap, ← hT_eq, ← mul_two] at hsplit
    rw [hS_card, hsplit, ← card_filter_mem_eq_natCard A]

end PEqualNP.Outside.L_meta_664

theorem PEqualNP.Outside.L_meta_664 :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  have hrew : ∀ t : F,
      (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 =
        (PEqualNP.Outside.L_meta_664.Q b d * t ^ 2 + b * (p.1 * d.2 + p.2 * d.1) * t) +
          PEqualNP.Outside.L_meta_664.Q b p := fun t =>
    PEqualNP.Outside.L_meta_664.Q_line b p d t
  have hc : PEqualNP.Outside.L_meta_664.Q b d ≠ 0 := by
    intro h0
    exact hd ((PEqualNP.Outside.L_meta_664.Q_eq_zero_iff b hb d).mp h0)
  have hfilter :
      Finset.univ.filter (fun t : F =>
        (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A) =
      Finset.univ.filter (fun t : F =>
        (PEqualNP.Outside.L_meta_664.Q b d * t ^ 2 + b * (p.1 * d.2 + p.2 * d.1) * t) +
          PEqualNP.Outside.L_meta_664.Q b p ∈ A) := by
    congr 1
    funext t
    rw [hrew t]
  rw [hfilter]
  set c := PEqualNP.Outside.L_meta_664.Q b d
  set a := b * (p.1 * d.2 + p.2 * d.1)
  set q0 := PEqualNP.Outside.L_meta_664.Q b p
  constructor
  · by_cases ha : a = 0
    · right
      have h0 : Finset.univ.filter (fun t : F => (c * t ^ 2 + a * t) + q0 ∈ A) =
          Finset.univ.filter (fun t : F => c * t ^ 2 + q0 ∈ A) := by
        simp [ha]
      rw [h0]
      exact PEqualNP.Outside.L_meta_664.case_a_zero A c q0 hc
    · have hq0 : ∀ t : F, c * t ^ 2 + a * t ≠ q0 := by
        intro t ht
        have hQ0 : PEqualNP.Outside.L_meta_664.Q b (p + t • d) = 0 := by
          rw [PEqualNP.Outside.L_meta_664.Q_line]
          show (c * t ^ 2 + a * t) + q0 = 0
          rw [ht, PEqualNP.Outside.L_meta_664.add_self_zero]
        have hpd0 : p + t • d = 0 :=
          (PEqualNP.Outside.L_meta_664.Q_eq_zero_iff b hb (p + t • d)).mp hQ0
        have hp1 : p.1 = t * d.1 := by
          have h1 : p.1 + t * d.1 = 0 := by
            simpa [Prod.fst_add, Prod.smul_fst, smul_eq_mul] using congrArg Prod.fst hpd0
          exact (PEqualNP.Outside.L_meta_664.add_eq_zero_iff p.1 (t * d.1)).mp h1
        have hp2 : p.2 = t * d.2 := by
          have h2 : p.2 + t * d.2 = 0 := by
            simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using congrArg Prod.snd hpd0
          exact (PEqualNP.Outside.L_meta_664.add_eq_zero_iff p.2 (t * d.2)).mp h2
        have ha0 : a = 0 := by
          show b * (p.1 * d.2 + p.2 * d.1) = 0
          rw [hp1, hp2]
          have hdet : t * d.1 * d.2 + t * d.2 * d.1 = 0 := by
            have heq : t * d.1 * d.2 + t * d.2 * d.1 =
                (t * d.1 * d.2) + (t * d.1 * d.2) := by ring
            rw [heq, PEqualNP.Outside.L_meta_664.add_self_zero]
          rw [hdet, mul_zero]
        exact ha ha0
      exact PEqualNP.Outside.L_meta_664.case_a_ne_zero A c a q0 hc ha hq0
  · intro hp
    have ha0 : a = 0 := by
      show b * (p.1 * d.2 + p.2 * d.1) = 0
      rw [hp]
      simp
    have h0 : Finset.univ.filter (fun t : F => (c * t ^ 2 + a * t) + q0 ∈ A) =
        Finset.univ.filter (fun t : F => c * t ^ 2 + q0 ∈ A) := by
      simp [ha0]
    rw [h0]
    exact PEqualNP.Outside.L_meta_664.case_a_zero A c q0 hc
