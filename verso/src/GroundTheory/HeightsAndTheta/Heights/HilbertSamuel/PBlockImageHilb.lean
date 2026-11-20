import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageHilb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageHilb

section Subst

variable {σ τ M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']

/- English proof (translation)
Proceed by induction on `hf using IsWeightedHomogeneous.induction_on with`. Consider the case `zero => simpa using isWeightedHomogeneous_zero ℚ w' (ψ m)`. Consider the case `add p q hp hq ihp ihq => simpa using ihp.add ihq`. Consider the case `monomial d r hr`. Rewrite using `[aeval_monomial, algebraMap_eq, ← hr, Finsupp.weight_apply, map_finsuppSum]`.

Use `IsWeightedHomogeneous.C_mul ?_ r` and prove the remaining obligations. Simplify using `only [map_nsmul]`. Conclude with `IsWeightedHomogeneous.prod _ _ _ fun i _ => (hφ i).pow (d i)`.
-/
theorem isWeightedHomogeneous_aeval {w : σ → M} {w' : τ → M'} (ψ : M →+ M') (φ : σ → MvPolynomial τ ℚ)
    (hφ : ∀ i, IsWeightedHomogeneous w' (φ i) (ψ (w i))) {f : MvPolynomial σ ℚ} {m : M}
    (hf : IsWeightedHomogeneous w f m) : IsWeightedHomogeneous w' (aeval φ f) (ψ m) := by
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero ℚ w' (ψ m)
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial d r hr =>
    rw [aeval_monomial, algebraMap_eq, ← hr, Finsupp.weight_apply, map_finsuppSum]
    refine IsWeightedHomogeneous.C_mul ?_ r
    simp only [map_nsmul]
    exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (hφ i).pow (d i)

end Subst

section Cone

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]

def mConeMapQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

def valSpan {σ M : Type*} [AddCommMonoid M] (w : σ → M) (y : σ → Ω) (m : M) : Submodule ℚ Ω :=
  (weightedHomogeneousSubmodule ℚ w m).map (aeval y : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toLinearMap

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `hring : ((mConeMapQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Ω)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[mConeMapQ, mConeMap]`. Introduce `i`.

Simplify using `[mConeMapQ, mConeMap]`. Establish `hker : mCoordIdeal y = (RingHom.ker (mConeMapQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ))`. Use extensionality with `f`. Rewrite using `[Ideal.mem_comap]`. Simplify using `only [mCoordIdeal, RingHom.mem_ker]`.

Establish `h` using `RingHom.congr_fun hring f`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h`. Rewrite using `[h]`. Set `_` to `MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)`. Establish `e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) = MvPolynomial.map (Int.castRingHom ℚ)`.

Rewrite using `[MvPolynomial.algebraMap_def, algebraMap_int_eq]`. Establish `h` using `IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))) (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (mConeMapQ y))`. Rewrite `h` using `[e]`. Rewrite using `[hker]`. Conclude with `h`.
-/
theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (mConeMapQ y) := by
  have hring : ((mConeMapQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapQ, mConeMap]
    · intro i
      simp [mConeMapQ, mConeMap]
  have hker : mCoordIdeal y = (RingHom.ker (mConeMapQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (mConeMapQ y))
  rw [e] at h
  rw [hker]
  exact h

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[NumbersDVR.blockWeight, Pi.single_apply]`.
-/
theorem weight_blockWeight_apply (μ : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) μ k = ∑ i : ι k, μ ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Establish `hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]`. Simplify using `only [mConeMapQ, aeval_monomial]`.

Rewrite using `[Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMapQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    mConeMapQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ μ p = ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hf (mem_support_iff.mp hμ)]
  simp only [mConeMapQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

/- English proof (translation)
Rewrite using `[map_mCoordIdeal]`. Use `set W := weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a`. Use `set P := RingHom.ker (mConeMapQ y)`. Set `φ₁ : W →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P` to `(Ideal.Quotient.mkₐ ℚ P).toLinearMap ∘ₗ W.subtype`. Set `φ₂ : W →ₗ[ℚ] Ω` to `(aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap ∘ₗ W.subtype`.

Establish `hk : LinearMap.ker φ₁ = LinearMap.ker φ₂`. Use extensionality with `⟨f, hf⟩`. Simplify using `only [LinearMap.mem_ker, φ₁, φ₂, LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, P, RingHom.mem_ker]`. Rewrite using `[mConeMapQ_eq y hf, mul_eq_zero, C_eq_zero, or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))]`. Establish `h₁ : LinearMap.range φ₁ = NumbersDVR.gradedPiece P a`.

Simplify using `only [φ₁, LinearMap.range_comp, Submodule.range_subtype, NumbersDVR.gradedPiece, W]`. Establish `h₂ : LinearMap.range φ₂ = valSpan (NumbersDVR.blockWeight ι) y a`. Simplify using `only [φ₂, LinearMap.range_comp, Submodule.range_subtype, valSpan, W]`. Establish `h` using `LinearEquiv.finrank_eq ((φ₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans φ₂.quotKerEquivRange)`. Rewrite `h` using `[h₁, h₂]`.

Unfold `NumbersDVR.hilbFn`. Rewrite using `[if_pos (fun k => Nat.cast_nonneg _)]`. Use `show ((Module.finrank ℚ (NumbersDVR.gradedPiece P a) : ℕ) : ℤ) = _`. Rewrite using `[h]`.
-/
theorem hilbFn_eq_finrank (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => (a k : ℤ)) =
      Module.finrank ℚ (valSpan (NumbersDVR.blockWeight ι) y a) := by
  rw [map_mCoordIdeal]
  set W := weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a
  set P := RingHom.ker (mConeMapQ y)
  let φ₁ : W →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P := (Ideal.Quotient.mkₐ ℚ P).toLinearMap ∘ₗ W.subtype
  let φ₂ : W →ₗ[ℚ] Ω := (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap ∘ₗ W.subtype
  have hk : LinearMap.ker φ₁ = LinearMap.ker φ₂ := by
    ext ⟨f, hf⟩
    simp only [LinearMap.mem_ker, φ₁, φ₂, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, P, RingHom.mem_ker]
    rw [mConeMapQ_eq y hf, mul_eq_zero, C_eq_zero,
      or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))]
  have h₁ : LinearMap.range φ₁ = NumbersDVR.gradedPiece P a := by
    simp only [φ₁, LinearMap.range_comp, Submodule.range_subtype, NumbersDVR.gradedPiece, W]
  have h₂ : LinearMap.range φ₂ = valSpan (NumbersDVR.blockWeight ι) y a := by
    simp only [φ₂, LinearMap.range_comp, Submodule.range_subtype, valSpan, W]
  have h := LinearEquiv.finrank_eq
    ((φ₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans φ₂.quotKerEquivRange)
  rw [h₁, h₂] at h
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Nat.cast_nonneg _)]
  show ((Module.finrank ℚ (NumbersDVR.gradedPiece P a) : ℕ) : ℤ) = _
  rw [h]

end Cone

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] {κ : Type} [Fintype κ]

def fwdSubst (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) (j : Ix κ) : MvPolynomial (Σ k, ι k) ℚ :=
  ∑ i, MvPolynomial.C ((M j i : ℤ) : ℚ) * MvPolynomial.X ⟨k₀, i⟩

def backSubst (k₀ : K) (N : Matrix (ι k₀) (Ix κ) ℤ) : (Σ k, ι k) → MvPolynomial (Ix κ) ℚ
  | ⟨k, i⟩ => if h : k = k₀ then ∑ j, MvPolynomial.C ((N (h ▸ i) j : ℤ) : ℚ) * MvPolynomial.X j else 0

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Set `ψ : (Unit → ℕ) →+ (K → ℕ)` to `{ toFun := fun a => Pi.single k₀ (a ()), map_zero' := by simp, map_add' := fun a b => by simp [Pi.single_add] }`. Establish `hφ : ∀ j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (fwdSubst k₀ M j) (ψ (NumbersDVR.blockWeight (GlobalTheory κ) j))` using `fun j => by`. Establish `e : ψ (NumbersDVR.blockWeight (GlobalTheory κ) j) = Pi.single k₀ 1`.

Simplify using `[ψ, NumbersDVR.blockWeight]`. Rewrite using `[e]`. Conclude with `IsWeightedHomogeneous.sum _ _ _ fun i _ => (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight ι) ⟨k₀, i⟩).C_mul _`. Use `⟨aeval (fwdSubst k₀ M) f, ?_, ?_⟩` and prove the remaining obligations. Simplify `isWeightedHomogeneous_aeval ψ _ hφ hf` using `[ψ]`.

Simplify using `only [AlgHom.toLinearMap_apply]`. Establish `e : (fun j => aeval y (fwdSubst k₀ M j)) = x`. Use function extensionality and compare the values at `j`. Simplify using `[fwdSubst, hxy.1 j]`. Rewrite using `[← AlgHom.comp_apply, comp_aeval, e]`.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Set `ψ : (K → ℕ) →+ (Unit → ℕ)` to `{ toFun := fun a _ => ∑ k, a k, map_zero' := by ext; simp, map_add' := fun a b => by ext; simp [Finset.sum_add_distrib] }`. Establish `hφ : ∀ p, IsWeightedHomogeneous (NumbersDVR.blockWeight (GlobalTheory κ)) (backSubst k₀ N p) (ψ (NumbersDVR.blockWeight ι p))`. Introduce and unpack `⟨k, i⟩`. Establish `e : ψ (NumbersDVR.blockWeight ι ⟨k, i⟩) = fun _ => 1`.

Use function extensionality and compare the values at `u`. Simplify using `[ψ, NumbersDVR.blockWeight]`. Rewrite using `[e]`. Distinguish the cases in `h : k = k₀`. Substitute `h` using the available equality.

Simplify using `only [backSubst, dite_true]`. Use `IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_` and prove the remaining obligations. Use `(isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight (GlobalTheory κ)) j).C_mul _ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Simplify using `[NumbersDVR.blockWeight]`.

Simplify using `only [backSubst, h, dite_false]`. Conclude with `isWeightedHomogeneous_zero ℚ _ _`. Use `⟨aeval (backSubst k₀ N) g, ?_, ?_⟩` and prove the remaining obligations. Simplify `isWeightedHomogeneous_aeval ψ _ hφ hg` using `[ψ]`. Simplify using `only [AlgHom.toLinearMap_apply]`.

Rewrite using `[← AlgHom.comp_apply, comp_aeval]`. Use `hom_congr_vars (Subsingleton.elim _ _) (fun p hp _ => ?_) rfl` and prove the remaining obligations. Take `⟨k, i⟩` from `p`. Take `⟨μ, hμ, hp⟩` from `(mem_vars_iff_mem_support _).mp hp`. Distinguish the cases in `h : k = k₀`.

Substitute `h` using the available equality. Simplify using `[backSubst, hxy.2 i]`. It suffices to derive a contradiction. Establish `hw` using `congrFun (hg (mem_support_iff.mp hμ)) k`. Rewrite `hw` using `[weight_blockWeight_apply, Pi.single_eq_of_ne h]`.

Use `Finset.single_le_sum (fun i' _ => Nat.zero_le (μ ⟨k, i'⟩)) (Finset.mem_univ i)` as an intermediate fact. Rewrite `this` using `[hw]`. Conclude with `(Finsupp.mem_support_iff.mp hp) (Nat.le_zero.mp this)`.
-/
theorem valSpan_eq {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix κ) (ι k₀) ℤ} {N : Matrix (ι k₀) (Ix κ) ℤ}
    {x : Ix κ → Ω} (hxy : IsBlockImage y k₀ M N x) (n : ℕ) :
    valSpan (NumbersDVR.blockWeight (GlobalTheory κ)) x (fun _ => n) = valSpan (NumbersDVR.blockWeight ι) y (Pi.single k₀ n) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    let ψ : (Unit → ℕ) →+ (K → ℕ) :=
      { toFun := fun a => Pi.single k₀ (a ()), map_zero' := by simp, map_add' := fun a b => by simp [Pi.single_add] }
    have hφ : ∀ j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (fwdSubst k₀ M j)
        (ψ (NumbersDVR.blockWeight (GlobalTheory κ) j)) := fun j => by
      have e : ψ (NumbersDVR.blockWeight (GlobalTheory κ) j) = Pi.single k₀ 1 := by
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      exact IsWeightedHomogeneous.sum _ _ _ fun i _ =>
        (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight ι) ⟨k₀, i⟩).C_mul _
    refine ⟨aeval (fwdSubst k₀ M) f, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hf
    · simp only [AlgHom.toLinearMap_apply]
      have e : (fun j => aeval y (fwdSubst k₀ M j)) = x := by
        funext j
        simp [fwdSubst, hxy.1 j]
      rw [← AlgHom.comp_apply, comp_aeval, e]
  · rintro _ ⟨g, hg, rfl⟩
    let ψ : (K → ℕ) →+ (Unit → ℕ) :=
      { toFun := fun a _ => ∑ k, a k, map_zero' := by ext; simp,
        map_add' := fun a b => by ext; simp [Finset.sum_add_distrib] }
    have hφ : ∀ p, IsWeightedHomogeneous (NumbersDVR.blockWeight (GlobalTheory κ)) (backSubst k₀ N p)
        (ψ (NumbersDVR.blockWeight ι p)) := by
      rintro ⟨k, i⟩
      have e : ψ (NumbersDVR.blockWeight ι ⟨k, i⟩) = fun _ => 1 := by
        funext u
        simp [ψ, NumbersDVR.blockWeight]
      rw [e]
      by_cases h : k = k₀
      · subst h
        simp only [backSubst, dite_true]
        refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
        convert (isWeightedHomogeneous_X ℚ (NumbersDVR.blockWeight (GlobalTheory κ)) j).C_mul _ using 1
        funext u
        simp [NumbersDVR.blockWeight]
      · simp only [backSubst, h, dite_false]
        exact isWeightedHomogeneous_zero ℚ _ _
    refine ⟨aeval (backSubst k₀ N) g, ?_, ?_⟩
    · simpa [ψ] using isWeightedHomogeneous_aeval ψ _ hφ hg
    · simp only [AlgHom.toLinearMap_apply]
      rw [← AlgHom.comp_apply, comp_aeval]
      refine hom_congr_vars (Subsingleton.elim _ _) (fun p hp _ => ?_) rfl
      obtain ⟨k, i⟩ := p
      obtain ⟨μ, hμ, hp⟩ := (mem_vars_iff_mem_support _).mp hp
      by_cases h : k = k₀
      · subst h
        simp [backSubst, hxy.2 i]
      · exfalso
        have hw := congrFun (hg (mem_support_iff.mp hμ)) k
        rw [weight_blockWeight_apply, Pi.single_eq_of_ne h] at hw
        have := Finset.single_le_sum (fun i' _ => Nat.zero_le (μ ⟨k, i'⟩)) (Finset.mem_univ i)
        rw [hw] at this
        exact (Finsupp.mem_support_iff.mp hp) (Nat.le_zero.mp this)

end Block

end BlockImageHilb

open BlockImageHilb in

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ _ κ _ y k₀ M N x hxy n`. Rewrite using `[coordIdeal_eq_mCoordIdeal]`. Establish `e : (fun k => if k = k₀ then (n : ℤ) else 0) = fun k => ((Pi.single k₀ n : K → ℕ) k : ℤ)`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = k₀`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[e, hilbFn_eq_finrank y (Pi.single k₀ n), ← valSpan_eq hxy n]`. Conclude with `hilbFn_eq_finrank (ι := GlobalTheory κ) x (fun _ => n)`.
-/
theorem BlockImageHilb.proof : BlockImageHilb.Statement := by
  intro K _ _ ι _ Ω _ _ κ _ y k₀ M N x hxy n
  rw [coordIdeal_eq_mCoordIdeal]
  have e : (fun k => if k = k₀ then (n : ℤ) else 0) = fun k => ((Pi.single k₀ n : K → ℕ) k : ℤ) := by
    funext k
    by_cases h : k = k₀
    · subst h; simp
    · simp [h]
  rw [e, hilbFn_eq_finrank y (Pi.single k₀ n), ← valSpan_eq hxy n]
  exact hilbFn_eq_finrank (ι := GlobalTheory κ) x (fun _ => n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
