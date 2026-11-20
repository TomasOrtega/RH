import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsResidueEqZeroIff
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.HaarLatticeScale

/- English proof (translation)
Take `⟨a, ha⟩` from `v.valuedAdicCompletion_surjective F (WithZero.exp n)`. Conclude with `⟨a, ha⟩`.
-/
theorem exists_valued_eq_exp (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (n : ℤ) : ∃ a : Fv F v, Valued.v a = WithZero.exp n := by
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp n)
  exact ⟨a, ha⟩

/- English proof (translation)
Break down `eq_or_ne t 0 with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_one_iff_le_exp (t : WithZero (Multiplicative ℤ)) :
    t < 1 ↔ t ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne t 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_valued_eq_exp F v (-n)`. Establish `ha0 : a ≠ 0`. Introduce `h`. Rewrite `ha` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero ha.symm`.

Set `e' : V ≃L[Fv F v] (ι → Fv F v)` to `e.trans (ContinuousLinearEquiv.piCongrRight fun _ : ι => ContinuousLinearEquiv.unitsEquivAut (Fv F v) (Units.mk0 a ha0))`. Establish `he' : ∀ x i, e' x i = e x i * a` using `fun x i => by`. Simplify using `[e']`. Establish `hv : ∀ (y : Fv F v) (m : ℤ), Valued.v (y * a) ≤ WithZero.exp m ↔ Valued.v y ≤ WithZero.exp (n + m)`. Introduce `y m`.

Rewrite using `[map_mul, ha, WithZero.exp_neg, mul_inv_le_iff₀ WithZero.exp_pos, ← WithZero.exp_add, add_comm]`. Establish `h` using `GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v V μ ι e' {0}`. Establish `h1 : {x | ∀ i, e' x i ∈ v.adicCompletionIntegers F} = {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`.

Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, he', ← WithZero.exp_zero, hv, add_zero]`. Establish `hres : ∀ y : v.adicCompletionIntegers F, IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 ↔ Valued.v (y : Fv F v) ≤ WithZero.exp (-1 : ℤ)`. Introduce `y`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, ← lt_one_iff_le_exp]`.

Conclude with `Valuation.mem_maximalIdeal_iff _ _`. Establish `h2 : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e' x i = (y i : Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} = {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp (n - 1)}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff, funext_iff, Pi.zero_apply, hres]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hy'⟩ i`. Rewrite using `[sub_eq_add_neg, ← hv, ← he', hy]`. Conclude with `hy' i`. Introduce `hx`. Establish `hx' : ∀ i, Valued.v (e' x i) ≤ WithZero.exp (-1 : ℤ)` using `fun i => by`.

Rewrite using `[he', hv, ← sub_eq_add_neg]`. Conclude with `hx i`. Use `⟨fun i => ⟨e' x i, ?_⟩, fun i => rfl, hx'⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `((lt_one_iff_le_exp _).2 (hx' i)).le`.

Rewrite `h` using `[h1, h2]`. Simplify using `using h`.
-/
theorem step (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type)
    [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι]
    (e : V ≃L[Fv F v] (ι → Fv F v)) (n : ℤ) :
    μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp (n - 1)} *
      (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ Fintype.card ι =
    μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp F v (-n)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  let e' : V ≃L[Fv F v] (ι → Fv F v) := e.trans
    (ContinuousLinearEquiv.piCongrRight fun _ : ι =>
      ContinuousLinearEquiv.unitsEquivAut (Fv F v) (Units.mk0 a ha0))
  have he' : ∀ x i, e' x i = e x i * a := fun x i => by
    simp [e']
  have hv : ∀ (y : Fv F v) (m : ℤ),
      Valued.v (y * a) ≤ WithZero.exp m ↔ Valued.v y ≤ WithZero.exp (n + m) := by
    intro y m
    rw [map_mul, ha, WithZero.exp_neg, mul_inv_le_iff₀ WithZero.exp_pos, ← WithZero.exp_add,
      add_comm]
  have h := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v V μ ι e' {0}
  have h1 : {x | ∀ i, e' x i ∈ v.adicCompletionIntegers F} =
      {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} := by
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, he', ← WithZero.exp_zero, hv, add_zero]
  have hres : ∀ y : v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 ↔
        Valued.v (y : Fv F v) ≤ WithZero.exp (-1 : ℤ) := by
    intro y
    rw [IsLocalRing.residue_eq_zero_iff, ← lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  have h2 : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e' x i = (y i : Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈
        ({0} : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)))} =
      {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp (n - 1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, funext_iff, Pi.zero_apply, hres]
    constructor
    · rintro ⟨y, hy, hy'⟩ i
      rw [sub_eq_add_neg, ← hv, ← he', hy]
      exact hy' i
    · intro hx
      have hx' : ∀ i, Valued.v (e' x i) ≤ WithZero.exp (-1 : ℤ) := fun i => by
        rw [he', hv, ← sub_eq_add_neg]
        exact hx i
      refine ⟨fun i => ⟨e' x i, ?_⟩, fun i => rfl, hx'⟩
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact ((lt_one_iff_le_exp _).2 (hx' i)).le
  rw [h1, h2] at h
  simpa using h

/- English proof (translation)
Introduce `F _ _ v V _ _ _ _ _ _ μ _ ι _ e n`. Use `haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v`. Establish `hq : (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ≠ 0`. Conclude with `Nat.card_pos.ne'` after adjusting the coercions. Establish `hs` using `step F v V μ ι e`.

Use `set q : ℝ := (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ)`. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero`. Simplify using `only [zpow_zero, one_pow, one_mul, WithZero.exp_zero]`. Both sides reduce to the same expression.

Consider the case `succ k ih`. Rewrite using `[← hs, add_sub_cancel_right, ih, zpow_add_one₀ hq, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `pred k ih`. Apply `mul_right_cancel₀ (pow_ne_zero (Fintype.card ι) hq)` to reduce the goal to its premises.

Rewrite using `[hs, ih, zpow_sub_one₀ hq, mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem measureReal_valued_le_exp : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (e : V ≃L[Fv F v] (ι → Fv F v)) (n : ℤ), μ.real {x | ∀ i, Valued.v (e x i) ≤ WithZero.exp n} = ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ n) ^ Fintype.card ι * μ.real {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} := by
  intro F _ _ v V _ _ _ _ _ _ μ _ ι _ e n
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hq : (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hs := step F v V μ ι e
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ)
  induction n using Int.induction_on with
  | zero =>
    simp only [zpow_zero, one_pow, one_mul, WithZero.exp_zero]
    rfl
  | succ k ih =>
    rw [← hs, add_sub_cancel_right, ih, zpow_add_one₀ hq, mul_pow]
    ring
  | pred k ih =>
    apply mul_right_cancel₀ (pow_ne_zero (Fintype.card ι) hq)
    rw [hs, ih, zpow_sub_one₀ hq, mul_pow, inv_pow]
    field_simp

end GlobalTheory.HaarLatticeScale
