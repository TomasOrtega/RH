import Mathlib
import GroundTheory.PAdicHodge.PtEvalPtProdEqZeroOfMem
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0} [CompleteSpace L] [IsAlgClosed L]

/- English proof (translation)
Rewrite using `[ξAnn, annRes_coeAnn]`. Both sides reduce to the same expression.
-/
theorem annRes_ξAnn {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) ≤ ρ0)
    (hs : (σ0 : ℝ) ≤ σ1) (ξ : T.int) : T.annRes h hs (T.ξAnn ξ) = T.ξAnn ξ := by
  rw [ξAnn, annRes_coeAnn]; rfl

/- English proof (translation)
Use `set a : AnnRad ρ0 σ0 := annIn ρ0 σ0`. Use `set b : AnnRad ρ0 σ0 := ⟨σ1, hs.le, σ1.2.2.trans h.le⟩`. Use `set c : AnnRad ρ0 σ0 := ⟨ρ1, hs.le.trans σ1.2.2, h.le⟩`. Use `set d : AnnRad ρ0 σ0 := annOut ρ0 σ0`. Use `set M : ℝ := (Real.log (T.annNorm ρ0 σ0 d w) - Real.log (T.annNorm ρ0 σ0 c w)) / (Real.log d - Real.log c) - (Real.log (T.annNorm ρ0 σ0 b w) - Real.log (T.annNorm ρ0 σ0 a w)) / (Real.log b - Real.log a)`.

Use `set Good : ℕ → Prop := fun n => ∃ l : List T.Pt, l.length = n ∧ (∀ P ∈ l, (σ1 : ℝ) ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ ρ1) ∧ (l.map fun P => T.ξAnn P.1).prod ∣ w`. Establish `hbound : ∀ n, Good n → n ≤ ⌊M⌋₊`. Introduce and unpack `n ⟨l, rfl, hl, hdvd⟩`. Use `T.length_le_of_prod_dvd w hw a b c d hs σ1.2.2 h l hl hdvd` as an intermediate fact. Conclude with `Nat.le_floor this`.

Establish `hG0 : Good 0` using `⟨[], rfl, by simp, by simp⟩`. Use `set N := Nat.findGreatest Good ⌊M⌋₊`. Establish `hGN : Good N` using `Nat.findGreatest_spec (P := Good) (Nat.zero_le _) hG0`. Establish `hnot : ¬ Good (N + 1)`. Introduce `hG`.

Distinguish the cases in `hle : N + 1 ≤ ⌊M⌋₊`. Conclude with `Nat.findGreatest_is_greatest (Nat.lt_succ_self N) hle hG`. Conclude with `hle (hbound _ hG)`. Take `⟨l, hlen, hl, v, hwv⟩` from `hGN`. Use `set P := (l.map fun P => T.ξAnn P.1).prod`.

Establish `hPpos : ∀ r, 0 < T.annNorm ρ0 σ0 r P` using `fun r => by`. Rewrite using `[T.annNorm_list_prod_ξAnn]`. Conclude with `List.prod_pos fun x hx => by`. Take `⟨Q, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `lt_of_lt_of_le (T.ptRad_pos' Q.2) (le_max_left _ _)`.

Establish `hv : ∀ r, 0 < T.annNorm ρ0 σ0 r v` using `fun r => by`. Establish `h1` using `hw r`. Rewrite `h1` using `[hwv, annNorm_mul]`. Conclude with `pos_of_mul_pos_right h1 (hPpos r).le`. Establish `hnozero : ∀ (ξ : T.int) (hξ : T.IsPrimOne ξ) (hr : T.ptRad ξ ∈ Set.Icc (σ0 : ℝ) ρ0), (σ1 : ℝ) ≤ T.ptRad ξ → T.ptRad ξ ≤ ρ1 → T.annEval hξ hr v ≠ 0`.

Introduce `ξ hξ hr h1 h2 h0`. Take `⟨y, hy⟩` from `(T.annEval_eq_zero_iff hξ hr v).1 h0`. Use `hnot ⟨⟨ξ, hξ⟩ :: l, by rw [List.length_cons, hlen], fun Q hQ => ?_, ⟨y, ?_⟩⟩` and prove the remaining obligations. Break down `List.mem_cons.1 hQ with rfl | hQ` into its components or cases. Conclude with `⟨h1, h2⟩`.

Conclude with `hl Q hQ`. Rewrite using `[List.map_cons, List.prod_cons, hwv, hy]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨μ, hμ, hμle⟩` from `T.exists_pos_le_annNorm v hv`. Take `⟨e, he⟩` from `T.exists_coeAnn_near v (half_pos hμ)`.

Establish `hgood : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn e) < T.annNorm ρ0 σ0 s v` using `fun s => (he s).trans_le ((half_le_self hμ.le).trans (hμle s))`. Establish `hm : ∀ s : ℝ, (σ1 : ℝ) ≤ s → s ≤ ρ1 → T.mult (e : T.RobbaExt ρ0) s = 0`. Introduce `s h1 h2`. Assume the negation of the conclusion as `hne`. Establish `hpos : 1 ≤ T.mult (e : T.RobbaExt ρ0) s`.

Use `T.mult_nonneg (e : T.RobbaExt ρ0) s` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set rs : AnnRad ρ0 σ0 := ⟨s, hs.le.trans h1, h2.trans h.le⟩`. Take `⟨ξ, hξ, hrad, hz⟩` from `T.exists_zero_ann v hv rs (hs.trans_le h1) (h2.trans_lt h) e hgood hpos`. Conclude with `hnozero ξ hξ _ (by rw [hrad]; exact h1) (by rw [hrad]; exact h2) hz`.

Establish `hu` using `T.isUnit_annRes_of_mult_eq_zero v e hgood h hs.le hm`. Use `⟨l, T.annRes h.le hs.le v, hl, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[hwv, map_mul, map_list_prod, List.map_map]`. Use `congr 2`. Conclude with `List.map_congr_left fun Q _ => T.annRes_ξAnn h.le hs.le Q.1`.
-/
theorem exists_factor_ann (w : T.Ann ρ0 σ0) (hw : ∀ r, 0 < T.annNorm ρ0 σ0 r w)
    {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) < ρ0) (hs : (σ0 : ℝ) < σ1) :
    ∃ (l : List T.Pt) (u : T.Ann ρ1 σ1), (∀ P ∈ l, (σ1 : ℝ) ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ ρ1) ∧
      IsUnit u ∧ T.annRes h.le hs.le w = (l.map fun P => T.ξAnn P.1).prod * u := by
  classical
  set a : AnnRad ρ0 σ0 := annIn ρ0 σ0
  set b : AnnRad ρ0 σ0 := ⟨σ1, hs.le, σ1.2.2.trans h.le⟩
  set c : AnnRad ρ0 σ0 := ⟨ρ1, hs.le.trans σ1.2.2, h.le⟩
  set d : AnnRad ρ0 σ0 := annOut ρ0 σ0
  set M : ℝ :=
    (Real.log (T.annNorm ρ0 σ0 d w) - Real.log (T.annNorm ρ0 σ0 c w)) / (Real.log d - Real.log c) -
      (Real.log (T.annNorm ρ0 σ0 b w) - Real.log (T.annNorm ρ0 σ0 a w)) / (Real.log b - Real.log a)
  set Good : ℕ → Prop := fun n => ∃ l : List T.Pt, l.length = n ∧
    (∀ P ∈ l, (σ1 : ℝ) ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ ρ1) ∧ (l.map fun P => T.ξAnn P.1).prod ∣ w
  have hbound : ∀ n, Good n → n ≤ ⌊M⌋₊ := by
    rintro n ⟨l, rfl, hl, hdvd⟩
    have := T.length_le_of_prod_dvd w hw a b c d hs σ1.2.2 h l hl hdvd
    exact Nat.le_floor this
  have hG0 : Good 0 := ⟨[], rfl, by simp, by simp⟩
  set N := Nat.findGreatest Good ⌊M⌋₊
  have hGN : Good N := Nat.findGreatest_spec (P := Good) (Nat.zero_le _) hG0
  have hnot : ¬ Good (N + 1) := by
    intro hG
    by_cases hle : N + 1 ≤ ⌊M⌋₊
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self N) hle hG
    · exact hle (hbound _ hG)
  obtain ⟨l, hlen, hl, v, hwv⟩ := hGN
  set P := (l.map fun P => T.ξAnn P.1).prod
  have hPpos : ∀ r, 0 < T.annNorm ρ0 σ0 r P := fun r => by
    rw [T.annNorm_list_prod_ξAnn]
    exact List.prod_pos fun x hx => by
      obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
      exact lt_of_lt_of_le (T.ptRad_pos' Q.2) (le_max_left _ _)
  have hv : ∀ r, 0 < T.annNorm ρ0 σ0 r v := fun r => by
    have h1 := hw r
    rw [hwv, annNorm_mul] at h1
    exact pos_of_mul_pos_right h1 (hPpos r).le

  have hnozero : ∀ (ξ : T.int) (hξ : T.IsPrimOne ξ) (hr : T.ptRad ξ ∈ Set.Icc (σ0 : ℝ) ρ0),
      (σ1 : ℝ) ≤ T.ptRad ξ → T.ptRad ξ ≤ ρ1 → T.annEval hξ hr v ≠ 0 := by
    intro ξ hξ hr h1 h2 h0
    obtain ⟨y, hy⟩ := (T.annEval_eq_zero_iff hξ hr v).1 h0
    refine hnot ⟨⟨ξ, hξ⟩ :: l, by rw [List.length_cons, hlen], fun Q hQ => ?_, ⟨y, ?_⟩⟩
    · rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨h1, h2⟩
      · exact hl Q hQ
    · rw [List.map_cons, List.prod_cons, hwv, hy]; ring

  obtain ⟨μ, hμ, hμle⟩ := T.exists_pos_le_annNorm v hv
  obtain ⟨e, he⟩ := T.exists_coeAnn_near v (half_pos hμ)
  have hgood : ∀ s, T.annNorm ρ0 σ0 s (v - T.coeAnn e) < T.annNorm ρ0 σ0 s v := fun s =>
    (he s).trans_le ((half_le_self hμ.le).trans (hμle s))
  have hm : ∀ s : ℝ, (σ1 : ℝ) ≤ s → s ≤ ρ1 → T.mult (e : T.RobbaExt ρ0) s = 0 := by
    intro s h1 h2
    by_contra hne
    have hpos : 1 ≤ T.mult (e : T.RobbaExt ρ0) s := by
      have := T.mult_nonneg (e : T.RobbaExt ρ0) s; omega
    set rs : AnnRad ρ0 σ0 := ⟨s, hs.le.trans h1, h2.trans h.le⟩
    obtain ⟨ξ, hξ, hrad, hz⟩ := T.exists_zero_ann v hv rs (hs.trans_le h1) (h2.trans_lt h) e hgood hpos
    exact hnozero ξ hξ _ (by rw [hrad]; exact h1) (by rw [hrad]; exact h2) hz
  have hu := T.isUnit_annRes_of_mult_eq_zero v e hgood h hs.le hm
  refine ⟨l, T.annRes h.le hs.le v, hl, hu, ?_⟩
  rw [hwv, map_mul, map_list_prod, List.map_map]
  congr 2
  exact List.map_congr_left fun Q _ => T.annRes_ξAnn h.le hs.le Q.1

end TeichLift

end GroundTheory.PAdicHodge
