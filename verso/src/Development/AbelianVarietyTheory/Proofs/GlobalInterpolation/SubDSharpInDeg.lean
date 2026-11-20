import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetDeg

/- English proof (translation)
Rewrite using `[f.as_sum, map_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_` and prove the remaining obligations. Establish `hd : Finsupp.weight w m = d` using `hf (mem_support_iff.mp hm)`. Rewrite using `[monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod, ← hd, Finsupp.weight_apply, Finsupp.sum, map_sum]`. Use `IsWeightedHomogeneous.C_mul ?_ _` and prove the remaining obligations.

Use `IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_nsmul]`. Conclude with `(hφ v).pow _`.
-/
theorem algHom_hom {K σ ρ M N : Type} [CommRing K] [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : ρ → N)
    (g : M →+ N) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial ρ K)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (g (w v))) {f : MvPolynomial σ K} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) (g d) := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hd : Finsupp.weight w m = d := hf (mem_support_iff.mp hm)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod, ← hd, Finsupp.weight_apply,
    Finsupp.sum, map_sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_
  rw [map_pow, map_nsmul]
  exact (hφ v).pow _

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {a b : ℕ}

def posW (a : ℕ) (τ : ι) : ι × Fin a × Fin a → ℕ := fun v => if v.1 = τ then 1 else 0

def derW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun _ => 0) fun k => if k.1 = τ then 1 else 0

/- English proof (translation)
Set `g : (Fin a → ℕ) →+ ℕ` to `{ toFun := fun x => if τ' = τ then ∑ i, x i else 0 map_zero' := by simp map_add' := by`. Introduce `x y`. Apply the tactic sequence `split_ifs <;> simp [Finset.sum_add_distrib] }`. Use `algHom_hom (Formalism.GradedWeylDivisibility.colW a a) (posW a τ) g _ (fun v => ?_) hf` and prove the remaining obligations. Establish `h` using `isWeightedHomogeneous_X K (posW a τ) (τ', v)`.

Establish `e : g (Formalism.GradedWeylDivisibility.colW a a v) = posW a τ (τ', v)`. Simplify using `[g, Formalism.GradedWeylDivisibility.colW, posW, Pi.single_apply]`. Rewrite using `[e]`. Simplify `h` using `[Formalism.GradedWeylDivisibility.blockEmb]`.
-/
theorem blockEmb_hom (τ τ' : ι) (ν : Fin a → ℕ) {f : MvPolynomial (Fin a × Fin a) K}
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f ν) :
    IsWeightedHomogeneous (posW a τ) (Formalism.GradedWeylDivisibility.blockEmb K τ' f) (if τ' = τ then ∑ i, ν i else 0) := by
  let g : (Fin a → ℕ) →+ ℕ :=
    { toFun := fun x => if τ' = τ then ∑ i, x i else 0
      map_zero' := by simp
      map_add' := by
        intro x y
        split_ifs <;> simp [Finset.sum_add_distrib] }
  refine algHom_hom (Formalism.GradedWeylDivisibility.colW a a) (posW a τ) g _ (fun v => ?_) hf
  have h := isWeightedHomogeneous_X K (posW a τ) (τ', v)
  have e : g (Formalism.GradedWeylDivisibility.colW a a v) = posW a τ (τ', v) := by
    simp [g, Formalism.GradedWeylDivisibility.colW, posW, Pi.single_apply]
  rw [e]
  simpa [Formalism.GradedWeylDivisibility.blockEmb] using h

/- English proof (translation)
Rewrite using `[frDet, Matrix.det_apply]`. Use `IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_` and prove the remaining obligations. Establish `h : IsWeightedHomogeneous (posW a τ) (∏ i : Fin a, (X (τ', σ i, i) : Pol K ι a)) (∑ _i : Fin a, if τ' = τ then 1 else 0)` using `IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X K (posW a τ) (τ', σ i, i)`. Apply the tactic sequence `have e : (∑ _i : Fin a, if τ' = τ then 1 else 0) = if τ' = τ then a else 0 := by split_ifs <;> simp`. Rewrite `h` using `[e]`.

Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1` into its components or cases. Simplify `h` using `[h1]`. Simplify `h.neg` using `[h1]`.
-/
theorem frDet_hom (τ τ' : ι) :
    IsWeightedHomogeneous (posW a τ) (frDet K a τ') (if τ' = τ then a else 0) := by
  rw [frDet, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have h : IsWeightedHomogeneous (posW a τ) (∏ i : Fin a, (X (τ', σ i, i) : Pol K ι a))
      (∑ _i : Fin a, if τ' = τ then 1 else 0) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X K (posW a τ) (τ', σ i, i)
  have e : (∑ _i : Fin a, if τ' = τ then 1 else 0) = if τ' = τ then a else 0 := by
    split_ifs <;> simp
  rw [e] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simpa [h1] using h
  · simpa [h1] using h.neg

/- English proof (translation)
Use `algHom_hom (posW a τ) (derW a b τ) (AddMonoidHom.id ℕ) _ (fun v => ?_) hP` and prove the remaining obligations. Rewrite using `[subD, aeval_X]`. Use `split_ifs with h`. Use `IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_` and prove the remaining obligations. Use `(isWeightedHomogeneous_X K (derW a b τ) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul (isWeightedHomogeneous_X K (derW a b τ) (Sum.inr (v.1, β, v.2.1)))` as an intermediate fact.

Simplify `this` using `[derW, posW]`. Conclude with `isWeightedHomogeneous_zero _ _ _`.
-/
theorem subD_hom (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (derW a b τ) (subD K ι a b P) d := by
  refine algHom_hom (posW a τ) (derW a b τ) (AddMonoidHom.id ℕ) _ (fun v => ?_) hP
  rw [subD, aeval_X]
  split_ifs with h
  · refine IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_
    have := (isWeightedHomogeneous_X K (derW a b τ) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (derW a b τ) (Sum.inr (v.1, β, v.2.1)))
    simpa [derW, posW] using this
  · exact isWeightedHomogeneous_zero _ _ _

variable [Fintype ι]

/- English proof (translation)
Establish `: Formalism.L2.DIV.VV K lam ≤ weightedHomogeneousSubmodule K (posW a τ) (∑ i, (lam τ).natW i)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun τ' => Formalism.GradedWeylDivisibility.blockEmb K τ' (F τ')) (fun τ' => if τ' = τ then ∑ i, (lam τ').natW i else 0) (w := posW a τ) fun τ' _ => blockEmb_hom τ τ' _ (hF τ').1`. Simplify using `using h`.

Conclude with `this hP`.
-/
theorem VV_hom (lam : ι → DomWeight a) (τ : ι) {P : Pol K ι a} (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    IsWeightedHomogeneous (posW a τ) P (∑ i, (lam τ).natW i) := by
  have : Formalism.L2.DIV.VV K lam ≤ weightedHomogeneousSubmodule K (posW a τ) (∑ i, (lam τ).natW i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => Formalism.GradedWeylDivisibility.blockEmb K τ' (F τ'))
      (fun τ' => if τ' = τ then ∑ i, (lam τ').natW i else 0) (w := posW a τ)
      fun τ' _ => blockEmb_hom τ τ' _ (hF τ').1
    simpa using h
  exact this hP

/- English proof (translation)
Use `hP.mul ?_` and prove the remaining obligations. Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun τ' => frDet K a τ' ^ n τ') (fun τ' => n τ' • if τ' = τ then a else 0) (w := posW a τ) fun τ' _ => (frDet_hom τ τ').pow _`. Simplify using `using h`.
-/
theorem sharp_hom (n : ι → ℕ) (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (posW a τ) (sharp n P) (d + n τ * a) := by
  refine hP.mul ?_
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => frDet K a τ' ^ n τ')
    (fun τ' => n τ' • if τ' = τ then a else 0) (w := posW a τ)
    fun τ' _ => (frDet_hom τ τ').pow _
  simpa using h

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]`. Rewrite using `[Fintype.sum_prod_type (α₁ := ι) (α₂ := Fin b × Fin a), Finset.sum_eq_single τ]`. Simplify using `[derW, Fintype.sum_prod_type]`. Introduce `x _ hx`. Simplify using `[derW, hx]`.

Simplify using the standard rewrite rules.
-/
theorem weight_derW (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (derW a b τ) μ = ∑ β : Fin b, ∑ α : Fin a, μ (Sum.inr (τ, β, α)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type (α₁ := ι) (α₂ := Fin b × Fin a), Finset.sum_eq_single τ]
  · simp [derW, Fintype.sum_prod_type]
  · intro x _ hx
    simp [derW, hx]
  · simp

/- English proof (translation)
Establish `hi` using `i.2`. Establish `h : lam.detShift ≤ lam.w i`. Rewrite using `[DomWeight.detShift, dif_pos (by omega)]`. Conclude with `lam.anti (by rw [Fin.le_def]; simp only; omega)`. Rewrite using `[DomWeight.natW]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem natW_cast (lam : DomWeight a) (i : Fin a) : (lam.natW i : ℤ) = lam.w i - lam.detShift := by
  have hi := i.2
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dif_pos (by omega)]
    exact lam.anti (by rw [Fin.le_def]; simp only; omega)
  rw [DomWeight.natW]
  omega

end GlobalTheory.JetDeg

open GlobalTheory.JetDeg in

/- English proof (translation)
Introduce `K _ ι _ a b hab lam lam' s s' n hw P hP μ hμ τ`. Establish `h` using `subD_hom (b := b) τ (sharp_hom n τ (VV_hom lam τ hP)) (mem_support_iff.mp hμ)`. Rewrite `h` using `[weight_derW]`. Simplify using `only [Finsupp.comapDomain_apply]`. Rewrite using `[h]`.

Use `push_cast`. Establish `e : ∀ i, (lam τ).w i + s' τ = ((lam τ).natW i : ℤ) + n τ` using `fun i => by`. Rewrite using `[natW_cast, hw.2.2 τ]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[e, Finset.sum_add_distrib, mul_comm]`.
-/
theorem GlobalTheory.subD_sharp_inDeg : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n → ∀ P ∈ Formalism.L2.DIV.VV K lam, ∀ μ ∈ (subD K ι a b (sharp n P)).support, InDeg lam s' (Finsupp.comapDomain Sum.inr μ Sum.inr_injective.injOn) := by
  classical
  intro K _ ι _ a b hab lam lam' s s' n hw P hP μ hμ τ
  have h := subD_hom (b := b) τ (sharp_hom n τ (VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  rw [weight_derW] at h
  simp only [Finsupp.comapDomain_apply]
  rw [h]
  push_cast
  have e : ∀ i, (lam τ).w i + s' τ = ((lam τ).natW i : ℤ) + n τ := fun i => by
    rw [natW_cast, hw.2.2 τ]; ring
  simp [e, Finset.sum_add_distrib, mul_comm]

end
