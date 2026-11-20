import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.KCurve
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Set `b` to `Module.finBasis ℝ V`. Establish `e : (μ : (Fin q → V) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ V), (∏ i, b.coord (r i) (x i)) • μ fun i => b (r i)`. Use function extensionality and compare the values at `x`. Establish `h : x = fun i => ∑ j, b.coord j (x i) • b j` using `funext fun i => (b.sum_repr (x i)).symm`. Use `conv_lhs => rw [h, μ.map_sum]`.

Simplify using `only [μ.map_smul_univ]`. Rewrite using `[e]`. Use `continuous_finset_sum _ fun r _ => Continuous.fun_smul ?_ continuous_const` and prove the remaining obligations. Conclude with `continuous_finset_prod _ fun i _ => (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)`.
-/
private theorem multi_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : MultilinearMap ℝ (fun _ : Fin q => V) ℂ) : Continuous μ := by
  let b := Module.finBasis ℝ V
  have e : (μ : (Fin q → V) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (x i)) • μ fun i => b (r i) := by
    funext x
    have h : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    conv_lhs => rw [h, μ.map_sum]
    simp only [μ.map_smul_univ]
  rw [e]
  refine continuous_finset_sum _ fun r _ => Continuous.fun_smul ?_ continuous_const
  exact continuous_finset_prod _ fun i _ =>
    (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

/- English proof (translation)
Set `ν : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℂ` to `⟨μ, multi_cont μ⟩`. Establish `h` using `(ν.hasFDerivAt (c 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.2 hc)`. Rewrite `h` using `[ContinuousMultilinearMap.linearDeriv_apply]`. Conclude with `h`.
-/
private theorem multi_deriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : MultilinearMap ℝ (fun _ : Fin q => V) ℂ) (c : ℝ → Fin q → V) (c' : Fin q → V)
    (hc : ∀ i, HasDerivAt (fun t => c t i) (c' i) 0) :
    HasDerivAt (fun t => μ (c t)) (∑ i, μ (Function.update (c 0) i (c' i))) 0 := by
  let ν : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℂ := ⟨μ, multi_cont μ⟩
  have h := (ν.hasFDerivAt (c 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.2 hc)
  rw [ContinuousMultilinearMap.linearDeriv_apply] at h
  exact h

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h : star Y.1 = Y.1` using `Y.2`. Rewrite using `[hp_val, h, ← two_smul ℝ, smul_smul]`. Evaluate the numerical expressions.
-/
private theorem hp_herm {E : Type} [Field E] {a : ℕ} (Y : Herm E a) : hp (toL Y.1) = Y := by
  apply Subtype.ext
  have h : star Y.1 = Y.1 := Y.2
  rw [hp_val, h, ← two_smul ℝ, smul_smul]
  norm_num

/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in`. Establish `h1 : HasDerivAt (fun t => (k t).1) Z 0` using `hk`. Use `open scoped Matrix.Norms.Operator in`. Establish `h2 : HasDerivAt (fun t => star (k t).1) (star Z) 0` using `(hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 hk j) i).star : HasDerivAt (fun t => toL (star (k t).1)) (toL (star Z)) 0)`. Use `open scoped Matrix.Norms.Operator in`.

Establish `h` using `(h1.mul_const Y).mul h2`. Simplify using `only [h0, hZ, OneMemClass.coe_one, star_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h`. Conclude with `h`.
-/
private theorem conj_deriv {E : Type} [Field E] [NumberField E] {a : ℕ} (k : ℝ → Kinf E a)
    (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (h0 : k 0 = 1)
    (hk : HasDerivAt (fun t => toL (k t).1) (toL Z) 0) (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t => toL ((k t).1 * Y * star (k t).1)) (toL (Z * Y - Y * Z)) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 : HasDerivAt (fun t => (k t).1) Z 0 := hk
  open scoped Matrix.Norms.Operator in
  have h2 : HasDerivAt (fun t => star (k t).1) (star Z) 0 :=
    (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 hk j) i).star :
      HasDerivAt (fun t => toL (star (k t).1)) (toL (star Z)) 0)
  open scoped Matrix.Norms.Operator in
  have h := (h1.mul_const Y).mul h2
  simp only [h0, hZ, OneMemClass.coe_one, star_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h
  exact h

/- English proof (translation)
Introduce `E _ _ _ a M _ _ _ _ κ L hS q ω hω Z hZ Y`. Take `⟨k, h0, hk⟩` from `kCurve E a Z hZ`. Rewrite using `[← sub_eq_zero]`. Assume the negation of the conclusion as `hne`. Take `⟨l, hl, hd⟩` from `hS k Z h0 hk _ hne`.

Apply `hl` to reduce the goal to its premises. Set `μ : MultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ` to `(l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hp)`. Establish `hμ : ∀ X : Fin q → Herm E a, μ (fun i => toL (X i).1) = l (ω X)` using `fun X => by`. Express the relevant statement in the definitionally equal form `l (ω fun i => hp (toL (X i).1)) = _`. Simplify using `only [hp_herm]`.

Establish `h1` using `multi_deriv μ (fun t i => toL (adHerm (k t) (Y i)).1) (fun i => toL (brH Z hZ (Y i)).1) (fun i => conj_deriv k Z hZ h0 hk (Y i).1)`. Establish `h2 : ∀ t, μ (fun i => toL (adHerm (k t) (Y i)).1) = l (κ (k t) (ω Y))` using `fun t => by`. Rewrite using `[hμ, hω]`. Simplify using `only [h2] at h1`. Rewrite using `[map_sub, (hd (ω Y)).unique h1, map_sum, sub_eq_zero]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hμ]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `only [Function.update_self]`. Simplify using `only [Function.update_of_ne h, h0, adHerm, OneMemClass.coe_one, star_one, mul_one, one_mul]`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.infAbs :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M),
      SepDer κ L → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω := by
  intro E _ _ _ a M _ _ _ _ κ L hS q ω hω Z hZ Y
  obtain ⟨k, h0, hk⟩ := kCurve E a Z hZ
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨l, hl, hd⟩ := hS k Z h0 hk _ hne
  apply hl
  let μ : MultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hp)
  have hμ : ∀ X : Fin q → Herm E a, μ (fun i => toL (X i).1) = l (ω X) := fun X => by
    change l (ω fun i => hp (toL (X i).1)) = _
    simp only [hp_herm]
  have h1 := multi_deriv μ (fun t i => toL (adHerm (k t) (Y i)).1) (fun i => toL (brH Z hZ (Y i)).1)
    (fun i => conj_deriv k Z hZ h0 hk (Y i).1)
  have h2 : ∀ t, μ (fun i => toL (adHerm (k t) (Y i)).1) = l (κ (k t) (ω Y)) := fun t => by
    rw [hμ, hω]
  simp only [h2] at h1
  rw [map_sub, (hd (ω Y)).unique h1, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hμ]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]
  · simp only [Function.update_of_ne h, h0, adHerm, OneMemClass.coe_one, star_one, mul_one, one_mul]
