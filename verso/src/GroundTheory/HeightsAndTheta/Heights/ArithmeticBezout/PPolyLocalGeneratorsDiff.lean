import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPolyLocalGenerators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

variable {n : ℕ}

def polyDiff (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) where
  toFun f j := eval p (pderiv j f)
  map_add' f g := by ext j; simp
  map_smul' c f := by ext j; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem polyDiff_apply (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    polyDiff p f j = eval p (pderiv j f) := rfl

def dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  LinearMap.mk₂ ℂ (fun w v => ∑ j, w j * v j)
    (fun w w' v => by simp [add_mul, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_assoc, Finset.mul_sum])
    (fun w v v' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_left_comm, Finset.mul_sum])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dotForm_apply (w v : Fin n → ℂ) : dotForm w v = ∑ j, w j * v j := rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_polyTangent_iff (S : Set (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ) :
    v ∈ polyTangent S p ↔ ∀ q ∈ S, dotForm (polyDiff p q) v = 0 := Iff.rfl

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[mem_polyTangent_iff, mem_polyTangent_iff]`. Use `⟨fun hv f hf => ?_, fun hv f hf => hv f (hST hf)⟩` and prove the remaining obligations. Establish `hle : Submodule.span ℂ (polyDiff p '' S) ≤ LinearMap.ker (dotForm.flip v)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]`. Conclude with `hv g hg`. Use `hle (h f hf)` as an intermediate fact. Simplify `this` using `only [LinearMap.mem_ker, LinearMap.flip_apply]`.
-/
theorem polyTangent_eq_of_subset (S T : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hST : S ⊆ T) (h : ∀ f ∈ T, polyDiff p f ∈ Submodule.span ℂ (polyDiff p '' S)) :
    polyTangent S p = polyTangent T p := by
  ext v
  rw [mem_polyTangent_iff, mem_polyTangent_iff]
  refine ⟨fun hv f hf => ?_, fun hv f hf => hv f (hST hf)⟩
  have hle : Submodule.span ℂ (polyDiff p '' S) ≤ LinearMap.ker (dotForm.flip v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hv g hg
  have := hle (h f hf)
  simpa only [LinearMap.mem_ker, LinearMap.flip_apply] using this

def tanLinPoly (p w : Fin n → ℂ) : MvPolynomial (Fin n) ℂ := ∑ j, C (w j) * (X j - C (p j))

/- English proof (translation)
Simplify using `[tanLinPoly]`.
-/
theorem eval_tanLinPoly (p w : Fin n → ℂ) : eval p (tanLinPoly p w) = 0 := by
  simp [tanLinPoly]

/- English proof (translation)
Simplify using `only [tanLinPoly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem tanLinPoly_add (p w w' : Fin n → ℂ) : tanLinPoly p (w + w') = tanLinPoly p w + tanLinPoly p w' := by
  simp only [tanLinPoly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [tanLinPoly, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem tanLinPoly_smul (p w : Fin n → ℂ) (c : ℂ) : tanLinPoly p (c • w) = C c * tanLinPoly p w := by
  simp only [tanLinPoly, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[tanLinPoly]`.
-/
theorem tanLinPoly_zero (p : Fin n → ℂ) : tanLinPoly p 0 = 0 := by
  simp [tanLinPoly]

/- English proof (translation)
Simplify using `only [tanLinPoly, Pi.single_apply]`. Simplify using the standard rewrite rules.
-/
theorem tanLinPoly_single (p : Fin n → ℂ) (i : Fin n) :
    tanLinPoly p (Pi.single i 1) = X i - C (p i) := by
  classical
  simp only [tanLinPoly, Pi.single_apply]
  simp

/- English proof (translation)
Use extensionality with `i`. Simplify using `[polyDiff_apply, tanLinPoly, Pi.single_apply]`.
-/
theorem polyDiff_tanLinPoly (p w : Fin n → ℂ) : polyDiff p (tanLinPoly p w) = w := by
  classical
  ext i
  simp [polyDiff_apply, tanLinPoly, Pi.single_apply]

/- English proof (translation)
Simplify using `[RingHom.mem_ker]`.
-/
theorem X_sub_C_mem_ker (p : Fin n → ℂ) (j : Fin n) :
    X j - C (p j) ∈ RingHom.ker (eval p) := by
  simp [RingHom.mem_ker]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : polyDiff p (C a) = 0` using `by ext j; simp [polyDiff_apply]`. Simplify using `[h, tanLinPoly_zero]`. Consider the case `add f g hf hg`.

Establish `e : f + g - C (eval p (f + g)) - tanLinPoly p (polyDiff p (f + g)) = (f - C (eval p f) - tanLinPoly p (polyDiff p f)) + (g - C (eval p g) - tanLinPoly p (polyDiff p g))`. Rewrite using `[map_add, map_add, map_add, tanLinPoly_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem hf hg`.

Consider the case `mul_X f i hf`. Establish `hd : polyDiff p (f * X i) = p i • polyDiff p f + eval p f • Pi.single i 1`. Use extensionality with `j`. Simplify using `only [polyDiff_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivation.leibniz, pderiv_X, map_add]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `only [Pi.single_eq_same, mul_one, map_mul, eval_X]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero, map_zero, map_mul, eval_X, zero_add, add_zero]`. Establish `e : f * X i - C (eval p (f * X i)) - tanLinPoly p (polyDiff p (f * X i)) = C (p i) * (f - C (eval p f) - tanLinPoly p (polyDiff p f)) + (f - C (eval p f)) * (X i - C (p i))`.

Rewrite using `[hd, tanLinPoly_add, tanLinPoly_smul, tanLinPoly_smul, tanLinPoly_single, map_mul, eval_X, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `add_mem (Ideal.mul_mem_left _ _ hf) ?_` and prove the remaining obligations. Rewrite using `[pow_two]`.

Use `Ideal.mul_mem_mul ?_ (X_sub_C_mem_ker p i)` and prove the remaining obligations. Simplify using `[RingHom.mem_ker]`.
-/
theorem sub_tanLinPoly_mem_sq (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) - tanLinPoly p (polyDiff p f) ∈ RingHom.ker (eval p) ^ 2 := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : polyDiff p (C a) = 0 := by ext j; simp [polyDiff_apply]
    simp [h, tanLinPoly_zero]
  | add f g hf hg =>
    have e : f + g - C (eval p (f + g)) - tanLinPoly p (polyDiff p (f + g)) =
        (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (g - C (eval p g) - tanLinPoly p (polyDiff p g)) := by
      rw [map_add, map_add, map_add, tanLinPoly_add]; ring
    rw [e]
    exact add_mem hf hg
  | mul_X f i hf =>
    have hd : polyDiff p (f * X i) = p i • polyDiff p f + eval p f • Pi.single i 1 := by
      ext j
      simp only [polyDiff_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
        pderiv_X, map_add]
      by_cases hij : i = j
      · subst hij
        simp only [Pi.single_eq_same, mul_one, map_mul, eval_X]
        ring
      · simp only [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero, map_zero,
          map_mul, eval_X, zero_add, add_zero]
    have e : f * X i - C (eval p (f * X i)) - tanLinPoly p (polyDiff p (f * X i)) =
        C (p i) * (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (f - C (eval p f)) * (X i - C (p i)) := by
      rw [hd, tanLinPoly_add, tanLinPoly_smul, tanLinPoly_smul, tanLinPoly_single, map_mul, eval_X, map_mul]
      ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hf) ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (X_sub_C_mem_ker p i)
    simp [RingHom.mem_ker]

/- English proof (translation)
Simplify `sub_tanLinPoly_mem_sq p f` using `[h0, h1, tanLinPoly_zero]`.
-/
theorem mem_sq_of_polyDiff_eq_zero (p : Fin n → ℂ) {f : MvPolynomial (Fin n) ℂ}
    (h0 : eval p f = 0) (h1 : polyDiff p f = 0) : f ∈ RingHom.ker (eval p) ^ 2 := by
  simpa [h0, h1, tanLinPoly_zero] using sub_tanLinPoly_mem_sq p f

/- English proof (translation)
Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hd`. Establish `hg0 : eval p (f - ∑ i, C (c i) * h i) = 0` using `by simp [hf, hh]`. Establish `hg1 : polyDiff p (f - ∑ i, C (c i) * h i) = 0`. Simplify using `only [map_sub, map_sum, C_mul', map_smul]`. Rewrite using `[← hc]`.

Simplify using the standard rewrite rules. Establish `hsum : ∑ i, C (c i) * h i ∈ Ideal.span (Set.range h)` using `sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Establish `e : f = (f - ∑ i, C (c i) * h i) + ∑ i, C (c i) * h i` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem (Ideal.mem_sup_right (mem_sq_of_polyDiff_eq_zero p hg0 hg1)) (Ideal.mem_sup_left hsum)`.
-/
theorem mem_span_sup_sq_of_polyDiff_mem (p : Fin n → ℂ) {ι : Type*} [Fintype ι]
    (h : ι → MvPolynomial (Fin n) ℂ) (hh : ∀ i, eval p (h i) = 0) {f : MvPolynomial (Fin n) ℂ}
    (hf : eval p f = 0) (hd : polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ h))) :
    f ∈ Ideal.span (Set.range h) ⊔ RingHom.ker (eval p) ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hd
  have hg0 : eval p (f - ∑ i, C (c i) * h i) = 0 := by simp [hf, hh]
  have hg1 : polyDiff p (f - ∑ i, C (c i) * h i) = 0 := by
    simp only [map_sub, map_sum, C_mul', map_smul]
    rw [← hc]
    simp
  have hsum : ∑ i, C (c i) * h i ∈ Ideal.span (Set.range h) :=
    sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have e : f = (f - ∑ i, C (c i) * h i) + ∑ i, C (c i) * h i := by ring
  rw [e]
  exact add_mem (Ideal.mem_sup_right (mem_sq_of_polyDiff_eq_zero p hg0 hg1))
    (Ideal.mem_sup_left hsum)

/- English proof (translation)
Apply `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson ⊥)` to reduce the goal to its premises. Rewrite using `[Ideal.smul_eq_mul, ← pow_two]` and apply the resulting hypothesis.
-/
theorem maximalIdeal_le_span_of_le_sup_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (T : Set R)
    (h : IsLocalRing.maximalIdeal R ≤ Ideal.span T ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R ≤ Ideal.span T := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rwa [Ideal.smul_eq_mul, ← pow_two]

/- English proof (translation)
Use `set D : Submodule ℂ (Fin n → ℂ) := (J.restrictScalars ℂ).map (polyDiff p) with hDdef`. Establish `hinj : Function.Injective (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))`. Introduce `w w' hww`. Use extensionality with `j`. Use `LinearMap.congr_fun hww (Pi.single j 1)` as an intermediate fact.

Simplify `this` using `[dotForm_apply, Pi.single_apply]`. Use `set W := D.map (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))`. Establish `hW : finrank ℂ W = finrank ℂ D` using `(LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj D)).symm`. Establish `hco : W.dualCoannihilator = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p`. Use extensionality with `v`.

Rewrite using `[Submodule.mem_dualCoannihilator, mem_polyTangent_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h q hq`. Conclude with `h _ (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hq))`. Introduce and unpack `h _ ⟨w, ⟨q, hq, rfl⟩, rfl⟩`.

Conclude with `h q hq`. Establish `hsum` using `Subspace.finrank_add_finrank_dualCoannihilator_eq W`. Rewrite `hsum` using `[hco, hW, Module.finrank_fin_fun]`. Establish `hD : finrank ℂ D = n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p)`. Use linear arithmetic over natural numbers and integers.

Set `b` to `Module.finBasisOfFinrankEq ℂ D hD`. Establish `hb : ∀ i, ∃ q ∈ J, polyDiff p q = (b i : Fin n → ℂ)`. Introduce `i`. Take `⟨q, hq, e⟩` from `Submodule.mem_map.1 (b i).2`. Conclude with `⟨q, hq, e⟩`.

Use `choose q hqJ hq using hb`. Establish `hcomp : polyDiff p ∘ q = D.subtype ∘ b` using `funext hq`. Use `⟨q, hqJ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp]`. Conclude with `b.linearIndependent.map' D.subtype (Submodule.ker_subtype D)`.

Introduce `f hf`. Establish `hspan : Submodule.span ℂ (Set.range (polyDiff p ∘ q)) = D`. Rewrite using `[hcomp, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hf`.
-/
theorem exists_polyDiff_basis (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    ∃ q : Fin (n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p)) →
        MvPolynomial (Fin n) ℂ,
      (∀ i, q i ∈ J) ∧ LinearIndependent ℂ (polyDiff p ∘ q) ∧
        ∀ f ∈ J, polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ q)) := by
  set D : Submodule ℂ (Fin n → ℂ) := (J.restrictScalars ℂ).map (polyDiff p) with hDdef
  have hinj : Function.Injective (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ)) := by
    intro w w' hww
    ext j
    have := LinearMap.congr_fun hww (Pi.single j 1)
    classical
    simpa [dotForm_apply, Pi.single_apply] using this
  set W := D.map (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  have hW : finrank ℂ W = finrank ℂ D :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj D)).symm
  have hco : W.dualCoannihilator = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_polyTangent_iff]
    constructor
    · intro h q hq
      exact h _ (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hq))
    · rintro h _ ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      exact h q hq
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hco, hW, Module.finrank_fin_fun] at hsum
  have hD : finrank ℂ D = n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) := by
    omega
  let b := Module.finBasisOfFinrankEq ℂ D hD
  have hb : ∀ i, ∃ q ∈ J, polyDiff p q = (b i : Fin n → ℂ) := by
    intro i
    obtain ⟨q, hq, e⟩ := Submodule.mem_map.1 (b i).2
    exact ⟨q, hq, e⟩
  choose q hqJ hq using hb
  have hcomp : polyDiff p ∘ q = D.subtype ∘ b := funext hq
  refine ⟨q, hqJ, ?_, ?_⟩
  · rw [hcomp]
    exact b.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  · intro f hf
    have hspan : Submodule.span ℂ (Set.range (polyDiff p ∘ q)) = D := by
      rw [hcomp, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    rw [hspan]
    exact Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hf

end

end GroundTheory.Heights₂.Heights
