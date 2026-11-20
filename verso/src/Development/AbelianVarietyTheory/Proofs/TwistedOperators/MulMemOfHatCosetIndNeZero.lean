import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData

open MeasureTheory ValuativeRel Matrix in
/- English proof (translation)
Take `⟨a, ha0, ha1⟩` from `Valuation.RankOne.nontrivial (valuation k)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb0, hb1⟩ : ∃ b : k, valuation k b ≠ 0 ∧ valuation k b < 1 := by`. Break down `lt_or_gt_of_ne ha1 with h | h` into its components or cases. Conclude with `⟨a, ha0, h⟩`. Use `⟨a⁻¹, by simpa using ha0, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ h`. Establish `hb : b ≠ 0`. Introduce `h`. Simplify using `[h] at hb0`.

Use `⟨⟨fun m : ℕ => (fun x => (b ^ m)⁻¹ * x) '' (𝒪[k] : Set k), fun m => (_root_.GlobalTheory.SplitWeil.isCompact_int k).image (continuous_const.mul continuous_id), ?_⟩⟩` and prove the remaining obligations. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Use `set S := (IsRankLeOne.nonempty (R := k)).some`. Establish `hf` using `S.strictMono`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, S.emb (valuation k b) ^ m * S.emb (valuation k x) ≤ 1 := by`.

Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Conclude with `⟨0, by simp⟩`. Establish `hpos : 0 < S.emb (valuation k x)`. Rewrite using `[← map_zero S.emb]`. Conclude with `hf (zero_lt_iff.2 (by simpa using hx))`.

Establish `hlt : S.emb (valuation k b) < 1`. Rewrite using `[← map_one S.emb]`. Conclude with `hf hb1`. Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 hpos) hlt`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Set.mem_iUnion, Set.mem_image]`. Use `⟨m, b ^ m * x, ?_, by field_simp⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Valuation.mem_integer_iff, ← hf.le_iff_le, map_one, map_mul, map_mul, map_pow, map_pow]`. Conclude with `hm`.
-/
private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField' (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨a, ha0, ha1⟩ := Valuation.RankOne.nontrivial (valuation k)
  obtain ⟨b, hb0, hb1⟩ : ∃ b : k, valuation k b ≠ 0 ∧ valuation k b < 1 := by
    rcases lt_or_gt_of_ne ha1 with h | h
    · exact ⟨a, ha0, h⟩
    · refine ⟨a⁻¹, by simpa using ha0, ?_⟩
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
  have hb : b ≠ 0 := by
    intro h
    simp [h] at hb0
  refine ⟨⟨fun m : ℕ => (fun x => (b ^ m)⁻¹ * x) '' (𝒪[k] : Set k),
    fun m => (_root_.GlobalTheory.SplitWeil.isCompact_int k).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  set S := (IsRankLeOne.nonempty (R := k)).some
  have hf := S.strictMono
  obtain ⟨m, hm⟩ : ∃ m : ℕ, S.emb (valuation k b) ^ m * S.emb (valuation k x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    have hpos : 0 < S.emb (valuation k x) := by
      rw [← map_zero S.emb]
      exact hf (zero_lt_iff.2 (by simpa using hx))
    have hlt : S.emb (valuation k b) < 1 := by
      rw [← map_one S.emb]
      exact hf hb1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hlt
    refine ⟨m, ?_⟩
    calc _ ≤ (S.emb (valuation k x))⁻¹ * S.emb (valuation k x) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨m, b ^ m * x, ?_, by field_simp⟩
  rw [SetLike.mem_coe, Valuation.mem_integer_iff, ← hf.le_iff_le, map_one, map_mul, map_mul,
    map_pow, map_pow]
  exact hm

open MeasureTheory ValuativeRel Matrix in

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ψ hψ ν _ n _ _ c ε yb η hne i`. Use `haveI := sigmaCompactSpace_of_isNonarchimedeanLocalField' k`. Assume the negation of the conclusion as `hx`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht, hψt⟩ : ∃ t ∈ 𝒪[k], ψ (t * (ε * η i * c)) ≠ 1 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hx (_root_.GlobalTheory.RootEx.Unram.mem_of_psi hψ h)`. Establish `hvmem : Pi.single i ((c : k) * t) ∈ _root_.GlobalTheory.StepData.box n c` using `by show ∀ j, valuation k (Pi.single (M := fun _ => k) i ((c : k) * t) j) ≤ valuation k (c : k)`. Introduce `j`. Break down `eq_or_ne j i with rfl | hj` into its components or cases.

Simplify using `only [Pi.single_eq_same, map_mul]`. Conclude with `mul_le_of_le_one_right' ht`. Simplify using `[Pi.single_eq_of_ne hj]`. Apply `hne` to reduce the goal to its premises. Unfold `_root_.GlobalTheory.StepData.hat`.

Use `set g : (n → k) → ℂ := fun y => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y * (ψ (ε * η ⬝ᵥ y) : ℂ) with hg`. Establish `hshift : ∀ y, g (y + Pi.single i ((c : k) * t)) = (ψ (t * (ε * η i * c)) : ℂ) * g y`. Introduce `y`. Establish `hind : _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb (y + Pi.single i ((c : k) * t)) = _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y`. Unfold `_root_.GlobalTheory.StepData.cosetInd`.

Simplify using `only [Set.indicator]`. Establish `hq : Submodule.Quotient.mk (p` using `_root_.GlobalTheory.StepData.box n c) (y + Pi.single i ((c : k) * t)) = Submodule.Quotient.mk y := by`. Rewrite using `[Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hvmem, add_zero]`. Establish `hv0` using `(Submodule.Quotient.mk_eq_zero _).2 hvmem`. Use `split_ifs with h₁ h₂ h₂`.

Both sides reduce to the same expression. Conclude with `absurd (hq.symm.trans h₁) h₂`. Conclude with `absurd (hq.trans h₂) h₁`. Both sides reduce to the same expression. Simplify using `only [hg, hind, dotProduct_add, dotProduct_single, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul]`.

Establish `hr : ε * (η i * ((c : k) * t)) = t * (ε * η i * c)` using `by ring`. Rewrite using `[hr]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) g (Pi.single i ((c : k) * t))`. Simplify using `only [hshift, integral_const_mul] at h1`.

Establish `hne1 : (ψ (t * (ε * η i * c)) : ℂ) ≠ 1`. Introduce `h`. Conclude with `hψt (Circle.ext_iff.mpr (by simpa using h))`. Establish `hzero : ((ψ (t * (ε * η i * c)) : ℂ) - 1) * (∫ y, g y ∂Measure.pi fun _ => ν) = 0`. Rewrite using `[sub_mul, h1, one_mul, sub_self]`.

Conclude with `(mul_eq_zero.1 hzero).resolve_left (sub_ne_zero.2 hne1)`.
-/
theorem _root_.GlobalTheory.StepData.mul_mem_of_hat_cosetInd_ne_zero : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ψ : AddChar k Circle) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : kˣ) (ε : k)
    (yb : (n → k) ⧸ _root_.GlobalTheory.StepData.box n c) (η : n → k),
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb) η ≠ 0 →
    ∀ i, ε * η i * (c : k) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ hψ ν _ n _ _ c ε yb η hne i
  haveI := sigmaCompactSpace_of_isNonarchimedeanLocalField' k
  by_contra hx
  obtain ⟨t, ht, hψt⟩ : ∃ t ∈ 𝒪[k], ψ (t * (ε * η i * c)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hx (_root_.GlobalTheory.RootEx.Unram.mem_of_psi hψ h)
  have hvmem : Pi.single i ((c : k) * t) ∈ _root_.GlobalTheory.StepData.box n c := by
    show ∀ j, valuation k (Pi.single (M := fun _ => k) i ((c : k) * t) j) ≤ valuation k (c : k)
    intro j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Pi.single_eq_same, map_mul]
      exact mul_le_of_le_one_right' ht
    · simp [Pi.single_eq_of_ne hj]
  apply hne
  unfold _root_.GlobalTheory.StepData.hat
  set g : (n → k) → ℂ := fun y => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y *
    (ψ (ε * η ⬝ᵥ y) : ℂ) with hg
  have hshift : ∀ y, g (y + Pi.single i ((c : k) * t)) = (ψ (t * (ε * η i * c)) : ℂ) * g y := by
    intro y
    have hind : _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb
        (y + Pi.single i ((c : k) * t)) =
          _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y := by
      unfold _root_.GlobalTheory.StepData.cosetInd
      simp only [Set.indicator]
      have hq : Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n c)
          (y + Pi.single i ((c : k) * t)) = Submodule.Quotient.mk y := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hvmem, add_zero]
      have hv0 := (Submodule.Quotient.mk_eq_zero _).2 hvmem
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (hq.symm.trans h₁) h₂
      · exact absurd (hq.trans h₂) h₁
      · rfl
    simp only [hg, hind, dotProduct_add, dotProduct_single, mul_add, AddChar.map_add_eq_mul,
      Circle.coe_mul]
    have hr : ε * (η i * ((c : k) * t)) = t * (ε * η i * c) := by ring
    rw [hr]
    ring
  have h1 := integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) g
    (Pi.single i ((c : k) * t))
  simp only [hshift, integral_const_mul] at h1
  have hne1 : (ψ (t * (ε * η i * c)) : ℂ) ≠ 1 := by
    intro h
    exact hψt (Circle.ext_iff.mpr (by simpa using h))
  have hzero : ((ψ (t * (ε * η i * c)) : ℂ) - 1) * (∫ y, g y ∂Measure.pi fun _ => ν) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left (sub_ne_zero.2 hne1)

end GlobalTheory.StepData
