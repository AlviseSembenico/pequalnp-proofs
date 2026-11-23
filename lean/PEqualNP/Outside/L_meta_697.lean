import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_697

open PEqualNP.CircuitLowerBounds
open PEqualNP.LowMerge

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    change (wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma wf_append (g1 g2 : List Gate) (w : List Bool) : wf (g1 ++ g2) w = wf g2 (wf g1 w) := by
  simp [wf, List.foldl_append]

lemma getD_wf_lt (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < w.length →
    (wf gs w).getD k false = w.getD k false := by
  induction gs with
  | nil => intro w k _; rfl
  | cons g gs ih =>
    intro w k hk
    change (wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD k false = _
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    rw [ih _ k hk']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma wireVal_or (C : Circuit) (inp : List Bool) (g a b : ℕ)
    (hle : inp.length ≤ g) (ha : a < g) (hb : b < g)
    (hg : C.gates[g - inp.length]? = some ⟨GateOp.or, [a, b]⟩) :
    wireVal C inp g = (wireVal C inp a || wireVal C inp b) := by
  set j := g - inp.length
  have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hgj : C.gates[j] = ⟨GateOp.or, [a, b]⟩ := (List.getElem?_eq_some_iff.mp hg).2
  set pre := C.gates.take j
  set post := C.gates.drop (j + 1)
  have hsplit : C.gates = pre ++ ⟨GateOp.or, [a, b]⟩ :: post := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hjlt
    rw [h2, hgj] at h1
    exact h1.symm
  have hpre_len : pre.length = j := by simp [pre, Nat.le_of_lt hjlt]
  set w0 := wf pre inp
  have hw0_len : w0.length = g := by
    dsimp [w0]
    rw [wf_len, hpre_len]
    omega
  set v : Bool := w0.getD a false || w0.getD b false
  have hfull : C.wires inp = wf post (w0 ++ [v]) := by
    change wf C.gates inp = _
    rw [hsplit, wf_append]
    change wf post (w0 ++ [GateOp.or.eval ([a, b].map fun i => w0.getD i false)]) = _
    simp [GateOp.eval, v]
  have hwa : wireVal C inp a = w0.getD a false := by
    unfold wireVal
    rw [hfull, getD_wf_lt post (w0 ++ [v]) a (by simp [hw0_len]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : a < w0.length)]
  have hwb : wireVal C inp b = w0.getD b false := by
    unfold wireVal
    rw [hfull, getD_wf_lt post (w0 ++ [v]) b (by simp [hw0_len]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : b < w0.length)]
  have hwg : wireVal C inp g = v := by
    unfold wireVal
    rw [hfull, getD_wf_lt post (w0 ++ [v]) g (by simp [hw0_len])]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : w0.length ≤ g),
      hw0_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hwg, hwa, hwb]

lemma inc_of_low_point (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ)
    (w : Fin L) (p : Fin P) (hlow : IsLow P L inc C g w)
    (hv : wireVal C (pointLineInput P L p w) g = true) : inc p w = true := by
  have hs := hlow (fun q => decide (q = p)) hv
  simp only [lineSum, decide_eq_true_eq] at hs
  obtain ⟨q, hqw, hqp⟩ := hs
  rw [hqp] at hqw
  exact hqw

end PEqualNP.Outside.L_meta_697

theorem PEqualNP.Outside.L_meta_697 :
    ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ), (∀ (p p' : Fin P) (w w' : Fin L), p ≠ p' → w ≠ w' → ¬ (inc p w = true ∧ inc p w' = true ∧ inc p' w = true ∧ inc p' w' = true)) → (∀ (x : Fin P → Bool) (y y' : Fin L → Bool), (C.wires (List.ofFn x ++ List.ofFn y)).getD g false = (C.wires (List.ofFn x ++ List.ofFn y')).getD g false) → ∀ (w w' : Fin L), PEqualNP.LowMerge.IsLowMerge P L inc C g w → PEqualNP.LowMerge.IsLowMerge P L inc C g w' → w = w' := by
  intro P L inc C g hno2 hign w w' hm1 hm2
  obtain ⟨hge, a, ha, b, hb, hgate, hlow1, hab1, hba1⟩ := hm1
  obtain ⟨_, _, _, _, _, _, hlow2, _, _⟩ := hm2
  obtain ⟨p1, hp1a, hp1b⟩ := Finset.not_subset.mp hab1
  obtain ⟨p2, hp2b, hp2a⟩ := Finset.not_subset.mp hba1
  have hp12 : p1 ≠ p2 := fun e => hp2a (e ▸ hp1a)
  have hlen : ∀ (p : Fin P) (u : Fin L), (PEqualNP.LowMerge.pointLineInput P L p u).length = P + L := by
    intro p u
    simp [PEqualNP.LowMerge.pointLineInput, PEqualNP.LowMerge.restrictInput]
  have hp1a' : PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.pointLineInput P L p1 w) a = true :=
    (Finset.mem_filter.mp hp1a).2
  have hp2b' : PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.pointLineInput P L p2 w) b = true :=
    (Finset.mem_filter.mp hp2b).2
  have hg1w : PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.pointLineInput P L p1 w) g = true := by
    rw [PEqualNP.Outside.L_meta_697.wireVal_or C _ g a b (by rw [hlen]; exact hge) ha hb
      (by rw [hlen]; exact hgate), hp1a']
    rfl
  have hg2w : PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.pointLineInput P L p2 w) g = true := by
    rw [PEqualNP.Outside.L_meta_697.wireVal_or C _ g a b (by rw [hlen]; exact hge) ha hb
      (by rw [hlen]; exact hgate), hp2b']
    simp
  have hg1w' : PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.pointLineInput P L p1 w') g = true := by
    rw [← hg1w]
    exact hign (fun q => decide (q = p1)) (fun v => decide (v = w')) (fun v => decide (v = w))
  have hg2w' : PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.pointLineInput P L p2 w') g = true := by
    rw [← hg2w]
    exact hign (fun q => decide (q = p2)) (fun v => decide (v = w')) (fun v => decide (v = w))
  have hi1w := PEqualNP.Outside.L_meta_697.inc_of_low_point P L inc C g w p1 hlow1 hg1w
  have hi2w := PEqualNP.Outside.L_meta_697.inc_of_low_point P L inc C g w p2 hlow1 hg2w
  have hi1w' := PEqualNP.Outside.L_meta_697.inc_of_low_point P L inc C g w' p1 hlow2 hg1w'
  have hi2w' := PEqualNP.Outside.L_meta_697.inc_of_low_point P L inc C g w' p2 hlow2 hg2w'
  by_contra hne
  exact hno2 p1 p2 w w' hp12 hne ⟨hi1w, hi1w', hi2w, hi2w'⟩
