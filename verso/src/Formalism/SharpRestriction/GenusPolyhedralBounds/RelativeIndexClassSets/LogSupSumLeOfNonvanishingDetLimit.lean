import Mathlib
import Formalism.LocalRingCardinality.DataArith
import Formalism.FilteredPoleLength.LocalDescentLevels.InvFromBlocksApplyZero
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairedCharacterCondition

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions

namespace Formalism.MainNotions.Gaps.SizeBoundsAlt

def lnN {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal : ℝ)

def vDiff (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk la.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 K))).factors

def InCodiff {K : Type} [Field K] [NumberField K] (x : K) : Prop :=
  ∀ a : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K ((a : K) * x) = (z : ℚ)

section Poly

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}

def polyOf (φ : V →ₗ[K] K) (z : (ι →₀ ℕ) →₀ V) : MvPolynomial ι K :=
  z.sum fun β v => MvPolynomial.monomial β (φ v)

def detPoly {ρ : ℕ} (φ : Fin ρ → V →ₗ[K] K) (z : Fin ρ → (ι →₀ ℕ) →₀ V) : MvPolynomial ι K :=
  (Matrix.of fun i k => polyOf (φ i) (z k)).det

end Poly

section Arch

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

structure Herm (N2 : (K →+* ℂ) → V → ℝ) (dH : ℕ) where
  e : ∀ σ : K →+* ℂ, V →ₛₗ[σ] EuclideanSpace ℂ (Fin dH)
  norm_e : ∀ σ f, ‖e σ f‖ = N2 σ f

def Herm.OpLe {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) (σ : K →+* ℂ) (φ : V →ₗ[K] K) (C : ℝ) : Prop :=
  ∃ a : EuclideanSpace ℂ (Fin dH), ‖a‖ ≤ C ∧ ∀ f, σ (φ f) = inner ℂ a (Hm.e σ f)

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def Trans (M : Submodule (𝓞 K) V) {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) (Ctr : ℝ) : Prop :=
  ∀ Λ : ℝ, 0 < Λ → (∀ f ∈ M, f ≠ 0 → Λ ^ 2 ≤ ∑ σ : K →+* ℂ, N2 σ f ^ 2) →
    ∃ (m : ℕ) (cf : Fin m → (V →ₗ[K] K)), Submodule.span K (Set.range cf) = ⊤ ∧
      (∀ j, ∀ f ∈ M, InCodiff (cf j f)) ∧ ∀ σ j, Hm.OpLe σ (cf j) (Ctr / Λ)

end Arch

section NF1

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Unfold `lnN`. Apply `Real.log_pos` to reduce the goal to its premises. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm la` after adjusting the coercions.
-/
theorem lnN_pos (la : HeightOneSpectrum (𝓞 K)) : 0 < lnN la := by
  unfold lnN
  apply Real.log_pos
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm la

/- English proof (translation)
Unfold `vAdd`. Rewrite using `[map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vAdd_mul' (la : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd la (x * y) = vAdd la x + vAdd la y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

/- English proof (translation)
Unfold `vAdd`. Rewrite using `[map_pow, WithZero.log_pow, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vAdd_pow' (la : HeightOneSpectrum (𝓞 K)) (x : K) (n : ℕ) : vAdd la (x ^ n) = n * vAdd la x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

/- English proof (translation)
Unfold `vAdd`. Rewrite using `[map_zpow₀, WithZero.log_zpow, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem additiveValuation_zpow (la : HeightOneSpectrum (𝓞 K)) (x : K) (m : ℤ) : vAdd la (x ^ m) = m * vAdd la x := by
  unfold vAdd
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `vAdd`. Establish `h0 : la.valuation K x ≠ 0` using `(map_ne_zero _).2 hx`. Rewrite using `[← WithZero.exp_zero, ← WithZero.log_le_iff_le_exp h0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_le_one_iff (la : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    la.valuation K x ≤ 1 ↔ 0 ≤ vAdd la x := by
  unfold vAdd
  have h0 : la.valuation K x ≠ 0 := (map_ne_zero _).2 hx
  rw [← WithZero.exp_zero, ← WithZero.log_le_iff_le_exp h0]
  omega

/- English proof (translation)
Take `⟨π, hπ⟩` from `la.valuation_exists_uniformizer K`. Establish `hπ0 : π ≠ 0`. Introduce `h`. Rewrite `hπ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`.

Use `⟨π ^ m, zpow_ne_zero _ hπ0, ?_⟩` and prove the remaining obligations. Rewrite using `[additiveValuation_zpow]`. Unfold `vAdd`. Rewrite using `[hπ, WithZero.log_exp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_vAdd_eq (la : HeightOneSpectrum (𝓞 K)) (m : ℤ) : ∃ t : K, t ≠ 0 ∧ vAdd la t = m := by
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π ^ m, zpow_ne_zero _ hπ0, ?_⟩
  rw [additiveValuation_zpow]
  unfold vAdd
  rw [hπ, WithZero.log_exp]
  ring

/- English proof (translation)
Establish `h0 : la.valuation K a ≠ 0` using `(map_ne_zero _).2 ha`. Rewrite using `[NumberField.FinitePlace.norm_embedding', WithZeroMulInt.toNNReal_neg_apply _ h0]`. Establish `h1 : (WithZero.unzero h0).toAdd = WithZero.log (la.valuation K a)` using `by conv_rhs => rw [← WithZero.coe_unzero h0]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Use `push_cast`. Rewrite using `[Real.log_zpow]`. Unfold `vAdd lnN`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_norm_eq_neg_valuation (la : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    Real.log ‖NumberField.FinitePlace.embedding la a‖ = -((vAdd la a : ℝ) * lnN la) := by
  have h0 : la.valuation K a ≠ 0 := (map_ne_zero _).2 ha
  rw [NumberField.FinitePlace.norm_embedding', WithZeroMulInt.toNNReal_neg_apply _ h0]
  have h1 : (WithZero.unzero h0).toAdd = WithZero.log (la.valuation K a) := by
    conv_rhs => rw [← WithZero.coe_unzero h0]
    rfl
  rw [h1]
  push_cast
  rw [Real.log_zpow]
  unfold vAdd lnN
  push_cast
  ring

/- English proof (translation)
Establish `hpos : ∀ la : HeightOneSpectrum (𝓞 K), 0 < ‖NumberField.FinitePlace.embedding la a‖` using `fun la => norm_pos_iff.2 ((map_ne_zero _).2 ha)`. Establish `hfin : (Function.mulSupport fun la : HeightOneSpectrum (𝓞 K) => ‖NumberField.FinitePlace.embedding la a‖).Finite`. Establish `h` using `NumberField.FinitePlace.hasFiniteMulSupport (K := K) ha`. Establish `h2 : (Function.mulSupport fun w : NumberField.FinitePlace K => w a).Finite` using `h`. Use `(h2.image NumberField.FinitePlace.equivHeightOneSpectrum).subset ?_` and prove the remaining obligations.

Introduce `la hla`. Use `⟨NumberField.FinitePlace.equivHeightOneSpectrum.symm la, ?_, by simp⟩` and prove the remaining obligations. Simplify `hla` using `[NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply]`. Prove the components needed by the constructor for the conclusion. Use `hfin.subset ?_` and prove the remaining obligations.

Introduce `la hla`. Rewrite `hla` using `[Function.mem_support]`. Rewrite using `[Function.mem_mulSupport]`. Introduce `h1`. Apply `hla` to reduce the goal to its premises.

Use `log_norm_eq_neg_valuation la ha` as an intermediate fact. Rewrite `this` using `[h1, Real.log_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprod` using `NumberField.FinitePlace.prod_eq_inv_abs_norm (K := K) ha`. Rewrite `hprod` using `[← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]`.

Simplify using `only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply] at hprod`. Establish `hlog` using `congrArg Real.log hprod`. Rewrite `hlog` using `[Real.log_finprod hpos, Rat.cast_inv, Rat.cast_abs, Real.log_inv]`. Establish `h3 : ∑ᶠ la : HeightOneSpectrum (𝓞 K), (vAdd la a : ℝ) * lnN la = -∑ᶠ la : HeightOneSpectrum (𝓞 K), Real.log ‖NumberField.FinitePlace.embedding la a‖`. Rewrite using `[← finsum_neg_distrib]`.

Conclude with `finsum_congr fun la => by rw [log_norm_eq_neg_valuation la ha]; ring`. Rewrite using `[h3, hlog, neg_neg]`. Rewrite using `[← Real.log_prod (fun σ _ => by simpa using ha)]`. Use `congr 1`. Rewrite using `[Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f a‖) (fun φ => ‖φ a‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ a]`.

Rewrite using `[eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]`.
-/
theorem sum_vAdd (a : K) (ha : a ≠ 0) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) => (vAdd la a : ℝ) * lnN la).Finite ∧
    ∑ᶠ la : HeightOneSpectrum (𝓞 K), (vAdd la a : ℝ) * lnN la = ∑ σ : K →+* ℂ, Real.log ‖σ a‖ := by
  classical
  have hpos : ∀ la : HeightOneSpectrum (𝓞 K), 0 < ‖NumberField.FinitePlace.embedding la a‖ := fun la =>
    norm_pos_iff.2 ((map_ne_zero _).2 ha)
  have hfin : (Function.mulSupport fun la : HeightOneSpectrum (𝓞 K) =>
      ‖NumberField.FinitePlace.embedding la a‖).Finite := by
    have h := NumberField.FinitePlace.hasFiniteMulSupport (K := K) ha
    have h2 : (Function.mulSupport fun w : NumberField.FinitePlace K => w a).Finite := h
    refine (h2.image NumberField.FinitePlace.equivHeightOneSpectrum).subset ?_
    intro la hla
    refine ⟨NumberField.FinitePlace.equivHeightOneSpectrum.symm la, ?_, by simp⟩
    simpa [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply] using hla
  constructor
  · refine hfin.subset ?_
    intro la hla
    rw [Function.mem_support] at hla
    rw [Function.mem_mulSupport]
    intro h1
    apply hla
    have := log_norm_eq_neg_valuation la ha
    rw [h1, Real.log_one] at this
    linarith
  · have hprod := NumberField.FinitePlace.prod_eq_inv_abs_norm (K := K) ha
    rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm] at hprod
    simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply] at hprod
    have hlog := congrArg Real.log hprod
    rw [Real.log_finprod hpos, Rat.cast_inv, Rat.cast_abs, Real.log_inv] at hlog
    have h3 : ∑ᶠ la : HeightOneSpectrum (𝓞 K), (vAdd la a : ℝ) * lnN la =
        -∑ᶠ la : HeightOneSpectrum (𝓞 K), Real.log ‖NumberField.FinitePlace.embedding la a‖ := by
      rw [← finsum_neg_distrib]
      exact finsum_congr fun la => by rw [log_norm_eq_neg_valuation la ha]; ring
    rw [h3, hlog, neg_neg]
    rw [← Real.log_prod (fun σ _ => by simpa using ha)]
    congr 1
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f a‖)
      (fun φ => ‖φ a‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
      ← Algebra.norm_eq_prod_embeddings ℚ ℂ a]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

end NF1

section NormalFormTwo

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `differentIdeal_ne_bot`.
-/
theorem differentIdeal_ne_bot_of_numberField (K : Type) [Field K] [NumberField K] : differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
  differentIdeal_ne_bot

/- English proof (translation)
Establish `hI : differentIdeal ℤ (𝓞 K) ≠ 0` using `differentIdeal_ne_bot_of_numberField K`. Establish `hfin` using `Ideal.finite_factors hI`. Establish `hsub : (Function.support fun la : HeightOneSpectrum (𝓞 K) => (vDiff K la : ℝ) * lnN la) ⊆ {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ differentIdeal ℤ (𝓞 K)}`. Introduce `v hv`. Rewrite `hv` using `[Function.mem_support]`.

Assume the negation of the conclusion as `hnd`. Apply `hv` to reduce the goal to its premises. Establish `: vDiff K v = 0`. Unfold `vDiff`. Assume the negation of the conclusion as `hc`.

Conclude with `hnd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).1 hc)`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Establish `hsub' : (Function.support fun la : HeightOneSpectrum (𝓞 K) => (vDiff K la : ℝ) * lnN la) ⊆ (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K)))`.

Simplify using `using hsub`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub']`. Establish `hN : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) = |((discr K : ℤ) : ℝ)|`. Rewrite using `[absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[← hN]`.

Establish `hprod : (Ideal.absNorm (∏ᶠ v : HeightOneSpectrum (𝓞 K), v.maxPowDividing (differentIdeal ℤ (𝓞 K))) : ℝ) = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 K))) : ℝ)` using `((Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one (by simp) _`. Rewrite `hprod` using `[Ideal.finprod_heightOneSpectrum_factorization hI]`. Rewrite using `[hprod]`. Establish `hms : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 K))) : ℝ)) ⊆ (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K)))`. Introduce `v hv`.

Rewrite `hv` using `[Function.mem_mulSupport]`. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]`. Assume the negation of the conclusion as `hnd`. Apply `hv` to reduce the goal to its premises. Establish `: (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 K))).factors = 0`.

Assume the negation of the conclusion as `hc`. Conclude with `hnd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).1 hc)`. Simplify using `[HeightOneSpectrum.maxPowDividing, this]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hms, Real.log_prod]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only [HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow, Real.log_pow, vDiff, lnN]`. Introduce `v _`. Establish `h1 : v.maxPowDividing (differentIdeal ℤ (𝓞 K)) ≠ ⊥`. Unfold `HeightOneSpectrum.maxPowDividing`. Conclude with `pow_ne_zero _ v.ne_bot`.

Conclude with `(Ideal.absNorm_ne_zero_iff _).mpr (Ideal.finiteQuotientOfFreeOfNeBot _ h1)` after adjusting the coercions.
-/
theorem sum_vDiff (K : Type) [Field K] [NumberField K] :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) => (vDiff K la : ℝ) * lnN la).Finite ∧
    ∑ᶠ la : HeightOneSpectrum (𝓞 K), (vDiff K la : ℝ) * lnN la = Real.log |((discr K : ℤ) : ℝ)| := by
  classical
  have hI : differentIdeal ℤ (𝓞 K) ≠ 0 := differentIdeal_ne_bot_of_numberField K
  have hfin := Ideal.finite_factors hI
  have hsub : (Function.support fun la : HeightOneSpectrum (𝓞 K) => (vDiff K la : ℝ) * lnN la) ⊆
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ differentIdeal ℤ (𝓞 K)} := by
    intro v hv
    rw [Function.mem_support] at hv
    by_contra hnd
    apply hv
    have : vDiff K v = 0 := by
      unfold vDiff
      by_contra hc
      exact hnd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).1 hc)
    rw [this]; simp
  refine ⟨hfin.subset hsub, ?_⟩
  have hsub' : (Function.support fun la : HeightOneSpectrum (𝓞 K) => (vDiff K la : ℝ) * lnN la) ⊆
      (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) := by
    simpa using hsub
  rw [finsum_eq_sum_of_support_subset _ hsub']
  have hN : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) = |((discr K : ℤ) : ℝ)| := by
    rw [absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
  rw [← hN]
  have hprod : (Ideal.absNorm (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      v.maxPowDividing (differentIdeal ℤ (𝓞 K))) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 K))) : ℝ) :=
    ((Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  rw [Ideal.finprod_heightOneSpectrum_factorization hI] at hprod
  rw [hprod]
  have hms : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 K))) : ℝ)) ⊆
      (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    by_contra hnd
    apply hv
    have : (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 K))).factors = 0 := by
      by_contra hc
      exact hnd ((Associates.count_ne_zero_iff_dvd hI v.irreducible).1 hc)
    simp [HeightOneSpectrum.maxPowDividing, this]
  rw [finprod_eq_prod_of_mulSupport_subset _ hms, Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp only [HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow, Real.log_pow, vDiff, lnN]
  · intro v _
    have h1 : v.maxPowDividing (differentIdeal ℤ (𝓞 K)) ≠ ⊥ := by
      unfold HeightOneSpectrum.maxPowDividing
      exact pow_ne_zero _ v.ne_bot
    exact_mod_cast (Ideal.absNorm_ne_zero_iff _).mpr
      (Ideal.finiteQuotientOfFreeOfNeBot _ h1)

/- English proof (translation)
Establish `hI : differentIdeal ℤ (𝓞 K) ≠ 0` using `differentIdeal_ne_bot_of_numberField K`. Establish `hxd : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)`. Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0)]`. Introduce `a ha`. Take `⟨a', rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`.

Take `⟨z, hz⟩` from `h a'`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply, mul_comm, hz]`. Simplify using the standard rewrite rules. Establish `hnd : ¬ la.asIdeal ^ (vDiff K la + 1) ∣ differentIdeal ℤ (𝓞 K)`.

Rewrite using `[← Associates.mk_le_mk_iff_dvd, Associates.mk_pow, Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI) la.associates_irreducible]`. Unfold `vDiff`. Use linear arithmetic over natural numbers and integers. Rewrite `hnd` using `[Ideal.dvd_iff_le, SetLike.not_le_iff_exists]`. Take `⟨y, hyI, hyn⟩` from `hnd`.

Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Conclude with `hyn (Submodule.zero_mem _)`. Establish `hyK : ((y : 𝓞 K) : K) ≠ 0`. Simplify using `using hy0`.

Establish `hmem : x * (y : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)`. Establish `h1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1`. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]`. Conclude with `mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero _ _ one_ne_zero)`. Rewrite using `[← h1]`.

Conclude with `FractionalIdeal.mul_mem_mul hxd ((FractionalIdeal.mem_coeIdeal _).2 ⟨y, hyI, rfl⟩)`. Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 hmem`. Establish `hv1 : la.valuation K (x * (y : K)) ≤ 1`. Rewrite using `[← hb]`. Conclude with `la.valuation_le_one b`.

Establish `hvx : la.valuation K x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Establish `hvy : la.valuation K (y : K) ≠ 0` using `(Valuation.ne_zero_iff _).2 hyK`. Establish `hl : WithZero.log (la.valuation K x) + WithZero.log (la.valuation K (y : K)) ≤ 0`. Rewrite using `[← WithZero.log_mul hvx hvy, ← map_mul, ← WithZero.log_one, WithZero.log_le_log (by rw [map_mul]; exact mul_ne_zero hvx hvy) one_ne_zero]`. Conclude with `hv1`.

Establish `hy2 : -((vDiff K la : ℤ) + 1) < WithZero.log (la.valuation K (y : K))`. Rewrite using `[WithZero.lt_log_iff_exp_lt hvy]`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Use `(la.intValuation_le_pow_iff_mem y (vDiff K la + 1)).not.2 hyn` as an intermediate fact. Rewrite `this` using `[not_le]`.

Move the coercions through the operations in `at this`. Conclude with `this`. Unfold `vAdd`. Use linear arithmetic over natural numbers and integers.
-/
theorem vAdd_of_inCodiff {x : K} (hx : x ≠ 0) (h : InCodiff x) (la : HeightOneSpectrum (𝓞 K)) :
    -(vDiff K la : ℤ) ≤ vAdd la x := by
  classical
  have hI : differentIdeal ℤ (𝓞 K) ≠ 0 := differentIdeal_ne_bot_of_numberField K

  have hxd : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0)]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := h a'
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm, hz]
    simp

  have hnd : ¬ la.asIdeal ^ (vDiff K la + 1) ∣ differentIdeal ℤ (𝓞 K) := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI) la.associates_irreducible]
    unfold vDiff
    omega
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hnd
  obtain ⟨y, hyI, hyn⟩ := hnd
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyn (Submodule.zero_mem _)
  have hyK : ((y : 𝓞 K) : K) ≠ 0 := by
    simpa using hy0

  have hmem : x * (y : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1 := by
      rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]
      exact mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero _ _ one_ne_zero)
    rw [← h1]
    exact FractionalIdeal.mul_mem_mul hxd ((FractionalIdeal.mem_coeIdeal _).2 ⟨y, hyI, rfl⟩)
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  have hv1 : la.valuation K (x * (y : K)) ≤ 1 := by
    rw [← hb]; exact la.valuation_le_one b
  have hvx : la.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hvy : la.valuation K (y : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hyK
  have hl : WithZero.log (la.valuation K x) + WithZero.log (la.valuation K (y : K)) ≤ 0 := by
    rw [← WithZero.log_mul hvx hvy, ← map_mul, ← WithZero.log_one,
      WithZero.log_le_log (by rw [map_mul]; exact mul_ne_zero hvx hvy) one_ne_zero]
    exact hv1
  have hy2 : -((vDiff K la : ℤ) + 1) < WithZero.log (la.valuation K (y : K)) := by
    rw [WithZero.lt_log_iff_exp_lt hvy]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have := (la.intValuation_le_pow_iff_mem y (vDiff K la + 1)).not.2 hyn
    rw [not_le] at this
    push_cast at this
    exact this
  unfold vAdd
  omega

end NormalFormTwo

/- English proof (translation)
Use `(Formalism.LatticeBaseChangeAlt.complexHadamard n M (∑ i, ∑ j, ‖M i j‖) fun i j => ?_).1` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem had_cols (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2) := by
  refine (Formalism.LatticeBaseChangeAlt.complexHadamard n M (∑ i, ∑ j, ‖M i j‖) fun i j => ?_).1
  calc ‖M i j‖ ≤ ∑ j', ‖M i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖M i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖M i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖M i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/- English proof (translation)
Use `(had_cols ρ _).trans ?_` and prove the remaining obligations. Use `Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Real.sqrt_le_left (norm_nonneg _)]`. Simplify using `using hw.sum_inner_products_le (x k) (s := Finset.univ)`.
-/
theorem had_onb {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : ℕ) (w x : Fin ρ → E)
    (hw : Orthonormal ℂ w) :
    ‖(Matrix.of fun l k => inner ℂ (w l) (x k)).det‖ ≤ ∏ k, ‖x k‖ := by
  refine (had_cols ρ _).trans ?_
  refine Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun k _ => ?_
  rw [Real.sqrt_le_left (norm_nonneg _)]
  simpa using hw.sum_inner_products_le (x k) (s := Finset.univ)

/- English proof (translation)
Distinguish the cases in `hx : LinearIndependent ℂ x`. Use `set w : Fin ρ → E := InnerProductSpace.gramSchmidtNormed ℂ x with hwdef`. Establish `hw : Orthonormal ℂ w` using `InnerProductSpace.gramSchmidtNormed_orthonormal hx`. Establish `hexp : ∀ k, x k = ∑ l, inner ℂ (w l) (x k) • w l`. Introduce `k`.

Establish `hmem : x k ∈ Submodule.span ℂ (Set.range w)`. Rewrite using `[hwdef, InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem`. Establish `hcl : ∀ l, inner ℂ (w l) (x k) = c l`.

Introduce `l`. Rewrite using `[← hc]`. Conclude with `hw.inner_right_fintype c l`. Rewrite using `[← hc]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[hc, hcl]`. Establish `hfac : (Matrix.of fun i k => inner ℂ (a i) (x k)) = (Matrix.of fun i l => inner ℂ (a i) (w l)) * (Matrix.of fun l k => inner ℂ (w l) (x k))`. Use extensionality with `i k`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`.

Use `conv_lhs => rw [hexp k]`. Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right, mul_comm]`. Rewrite using `[hfac, Matrix.det_mul, norm_mul]`.

Use `mul_le_mul ?_ (had_onb ρ w x hw) (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)` and prove the remaining obligations. Establish `h1 : ‖(Matrix.of fun i l => inner ℂ (a i) (w l)).det‖ = ‖(Matrix.of fun l i => inner ℂ (w l) (a i)).det‖`. Establish `h2 : (Matrix.of fun i l => inner ℂ (a i) (w l)) = ((Matrix.of fun l i => inner ℂ (w l) (a i)) : Matrix (Fin ρ) (Fin ρ) ℂ).conjTranspose`. Use extensionality with `i l`. Simplify using `[Matrix.conjTranspose_apply]`.

Rewrite using `[h2, Matrix.det_conjTranspose, norm_star]`. Rewrite using `[h1]`. Conclude with `had_onb ρ w a hw`. Establish `hdet : (Matrix.of fun i k => inner ℂ (a i) (x k)).det = 0`. Rewrite using `[← Matrix.exists_mulVec_eq_zero_iff]`.

Rewrite `hx` using `[Fintype.linearIndependent_iff]`. Use `push Not at hx`. Take `⟨g, hg, k0, hk0⟩` from `hx`. Use `⟨g, fun h => hk0 (by rw [h]; rfl), ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]`. Establish `: ∑ k, inner ℂ (a i) (x k) * g k = inner ℂ (a i) (∑ k, g k • x k)`. Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right, mul_comm]`.

Rewrite using `[this, hg, inner_zero_right]`. Rewrite using `[hdet, norm_zero]`. Conclude with `mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)`.
-/
theorem had_inner' {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : ℕ) (a x : Fin ρ → E) :
    ‖(Matrix.of fun i k => inner ℂ (a i) (x k)).det‖ ≤ (∏ i, ‖a i‖) * ∏ k, ‖x k‖ := by
  classical
  by_cases hx : LinearIndependent ℂ x
  · set w : Fin ρ → E := InnerProductSpace.gramSchmidtNormed ℂ x with hwdef
    have hw : Orthonormal ℂ w := InnerProductSpace.gramSchmidtNormed_orthonormal hx
    have hexp : ∀ k, x k = ∑ l, inner ℂ (w l) (x k) • w l := by
      intro k
      have hmem : x k ∈ Submodule.span ℂ (Set.range w) := by
        rw [hwdef, InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]
        exact Submodule.subset_span ⟨k, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
      have hcl : ∀ l, inner ℂ (w l) (x k) = c l := by
        intro l
        rw [← hc]
        exact hw.inner_right_fintype c l
      rw [← hc]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hc, hcl]
    have hfac : (Matrix.of fun i k => inner ℂ (a i) (x k)) =
        (Matrix.of fun i l => inner ℂ (a i) (w l)) * (Matrix.of fun l k => inner ℂ (w l) (x k)) := by
      ext i k
      rw [Matrix.mul_apply]
      simp only [Matrix.of_apply]
      conv_lhs => rw [hexp k]
      rw [inner_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [inner_smul_right, mul_comm]
    rw [hfac, Matrix.det_mul, norm_mul]
    refine mul_le_mul ?_ (had_onb ρ w x hw) (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have h1 : ‖(Matrix.of fun i l => inner ℂ (a i) (w l)).det‖ =
        ‖(Matrix.of fun l i => inner ℂ (w l) (a i)).det‖ := by
      have h2 : (Matrix.of fun i l => inner ℂ (a i) (w l)) =
          ((Matrix.of fun l i => inner ℂ (w l) (a i)) : Matrix (Fin ρ) (Fin ρ) ℂ).conjTranspose := by
        ext i l
        simp [Matrix.conjTranspose_apply]
      rw [h2, Matrix.det_conjTranspose, norm_star]
    rw [h1]
    exact had_onb ρ w a hw
  · have hdet : (Matrix.of fun i k => inner ℂ (a i) (x k)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      rw [Fintype.linearIndependent_iff] at hx
      push Not at hx
      obtain ⟨g, hg, k0, hk0⟩ := hx
      refine ⟨g, fun h => hk0 (by rw [h]; rfl), ?_⟩
      ext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      have : ∑ k, inner ℂ (a i) (x k) * g k = inner ℂ (a i) (∑ k, g k • x k) := by
        rw [inner_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [inner_smul_right, mul_comm]
      rw [this, hg, inner_zero_right]
    rw [hdet, norm_zero]
    exact mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/- English proof (translation)
The claim follows from `had_inner' ρ a x`.
-/
theorem had_inner (d ρ : ℕ) (a x : Fin ρ → EuclideanSpace ℂ (Fin d)) :
    ‖(Matrix.of fun i k => inner ℂ (a i) (x k)).det‖ ≤ (∏ i, ‖a i‖) * ∏ k, ‖x k‖ :=
  had_inner' ρ a x

/- English proof (translation)
Use `choose a ha1 ha2 using h`. Establish `h1 : σ (Matrix.of fun i k => φ i (v k)).det = (Matrix.of fun i k => inner ℂ (a i) (Hm.e σ (v k))).det`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i k`.

Simplify using `[ha2]`. Rewrite using `[h1]`. Use `(had_inner dH ρ a fun k => Hm.e σ (v k)).trans ?_` and prove the remaining obligations. Simplify using `only [Hm.norm_e]`. Use `mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun k _ => ?_)` and prove the remaining obligations.

Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ha1 i`. Rewrite using `[← Hm.norm_e]`. Conclude with `norm_nonneg _`.
-/
theorem Herm.had {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) (σ : K →+* ℂ) {ρ : ℕ}
    (φ : Fin ρ → V →ₗ[K] K) (C : Fin ρ → ℝ) (h : ∀ i, Hm.OpLe σ (φ i) (C i)) (v : Fin ρ → V) :
    ‖σ (Matrix.of fun i k => φ i (v k)).det‖ ≤ (∏ i, C i) * ∏ k, N2 σ (v k) := by
  choose a ha1 ha2 using h
  have h1 : σ (Matrix.of fun i k => φ i (v k)).det =
      (Matrix.of fun i k => inner ℂ (a i) (Hm.e σ (v k))).det := by
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp [ha2]
  rw [h1]
  refine (had_inner dH ρ a fun k => Hm.e σ (v k)).trans ?_
  simp only [Hm.norm_e]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun k _ => ?_)
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ha1 i
  · rw [← Hm.norm_e]; exact norm_nonneg _

section Det

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}

/- English proof (translation)
Unfold `polyOf`. Rewrite using `[Finsupp.sum, MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq' z.support β]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite using `[Finsupp.notMem_support_iff.mp h, map_zero]`.
-/
theorem coeff_polyOf (φ : V →ₗ[K] K) (z : (ι →₀ ℕ) →₀ V) (β : ι →₀ ℕ) :
    (polyOf φ z).coeff β = φ (z β) := by
  classical
  unfold polyOf
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' z.support β]
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, map_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem polyOf_eq_sum (φ : V →ₗ[K] K) (z : (ι →₀ ℕ) →₀ V) :
    polyOf φ z = ∑ β ∈ z.support, MvPolynomial.monomial β (φ (z β)) := rfl

/- English proof (translation)
Use extensionality with `β`. Simplify using `[coeff_polyOf]`.
-/
theorem polyOf_add (φ ψ : V →ₗ[K] K) (z : (ι →₀ ℕ) →₀ V) : polyOf (φ + ψ) z = polyOf φ z + polyOf ψ z := by
  ext β; simp [coeff_polyOf]

/- English proof (translation)
Use extensionality with `β`. Simplify using `[coeff_polyOf]`.
-/
theorem polyOf_smul (a : K) (φ : V →ₗ[K] K) (z : (ι →₀ ℕ) →₀ V) :
    polyOf (a • φ) z = MvPolynomial.C a * polyOf φ z := by
  ext β; simp [coeff_polyOf]

/- English proof (translation)
The claim follows from `(Matrix.detRowAlternating (n := Fin ρ) (R := R)).toMultilinearMap.map_sum_finset g A`.
-/
theorem det_sum_rows {R α : Type} [CommRing R] [DecidableEq α] {ρ : ℕ} (g : Fin ρ → α → Fin ρ → R) (A : Fin ρ → Finset α) :
    Matrix.det (fun i => ∑ j ∈ A i, g i j) = ∑ r ∈ Fintype.piFinset A, Matrix.det (fun i => g i (r i)) :=
  (Matrix.detRowAlternating (n := Fin ρ) (R := R)).toMultilinearMap.map_sum_finset g A

/- English proof (translation)
Unfold `detPoly`. Rewrite using `[← Matrix.det_transpose]`. Establish `h1 : (Matrix.of fun i k => polyOf (φ i) (z k)).transpose = fun k => ∑ β ∈ (z k).support, fun i => MvPolynomial.monomial β (φ i (z k β))`. Use function extensionality and compare the values at `k i`. Simplify using `[Matrix.transpose_apply, polyOf_eq_sum, Finset.sum_apply]`.

Rewrite using `[h1, det_sum_rows (fun k β => fun i => MvPolynomial.monomial β (φ i (z k β))) (fun k => (z k).support)]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `h4 : (fun k => fun i => MvPolynomial.monomial (b k) (φ i (z k (b k)))) = Matrix.of fun k i => MvPolynomial.monomial (b k) (1 : K) * ((MvPolynomial.C : K →+* MvPolynomial ι K).mapMatrix (Matrix.of fun i k => φ i (z k (b k))).transpose) k i`. Use function extensionality and compare the values at `k i`. Simplify using `only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply]`.

Rewrite using `[mul_comm, MvPolynomial.C_mul_monomial, mul_one]`. Rewrite using `[h4, Matrix.det_mul_column, ← RingHom.map_det, Matrix.det_transpose, ← MvPolynomial.monomial_sum_one, mul_comm, MvPolynomial.C_mul_monomial, mul_one]`.
-/
theorem detPoly_expand {ρ : ℕ} (φ : Fin ρ → V →ₗ[K] K) (z : Fin ρ → (ι →₀ ℕ) →₀ V) :
    detPoly φ z = ∑ b ∈ Fintype.piFinset (fun k => (z k).support),
      MvPolynomial.monomial (∑ k, b k) (Matrix.of fun i k => φ i (z k (b k))).det := by
  classical
  unfold detPoly
  rw [← Matrix.det_transpose]
  have h1 : (Matrix.of fun i k => polyOf (φ i) (z k)).transpose =
      fun k => ∑ β ∈ (z k).support, fun i => MvPolynomial.monomial β (φ i (z k β)) := by
    funext k i
    simp [Matrix.transpose_apply, polyOf_eq_sum, Finset.sum_apply]
  rw [h1, det_sum_rows (fun k β => fun i => MvPolynomial.monomial β (φ i (z k β))) (fun k => (z k).support)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h4 : (fun k => fun i => MvPolynomial.monomial (b k) (φ i (z k (b k)))) =
      Matrix.of fun k i => MvPolynomial.monomial (b k) (1 : K) *
        ((MvPolynomial.C : K →+* MvPolynomial ι K).mapMatrix (Matrix.of fun i k => φ i (z k (b k))).transpose) k i := by
    funext k i
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  rw [h4, Matrix.det_mul_column, ← RingHom.map_det, Matrix.det_transpose, ← MvPolynomial.monomial_sum_one,
    mul_comm, MvPolynomial.C_mul_monomial, mul_one]

/- English proof (translation)
Unfold `detPoly`. Establish `: (Matrix.of fun i k => polyOf (t • φ i) (z k)) = Matrix.of fun i k => (fun _ : Fin ρ => MvPolynomial.C t) i * (Matrix.of fun i k => polyOf (φ i) (z k)) i k`. Use function extensionality and compare the values at `i k`. Simplify using `[polyOf_smul]`. Rewrite using `[this, Matrix.det_mul_column]`.

Simplify using the standard rewrite rules.
-/
theorem detPoly_smul {ρ : ℕ} (t : K) (φ : Fin ρ → V →ₗ[K] K) (z : Fin ρ → (ι →₀ ℕ) →₀ V) :
    detPoly (fun i => t • φ i) z = MvPolynomial.C (t ^ ρ) * detPoly φ z := by
  classical
  unfold detPoly
  have : (Matrix.of fun i k => polyOf (t • φ i) (z k)) =
      Matrix.of fun i k => (fun _ : Fin ρ => MvPolynomial.C t) i * (Matrix.of fun i k => polyOf (φ i) (z k)) i k := by
    funext i k; simp [polyOf_smul]
  rw [this, Matrix.det_mul_column]
  simp

/- English proof (translation)
Take `⟨φ, hφ⟩` from `hW`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hφ` to reduce the goal to its premises. Establish `hrep : ∀ i, ∃ a : Fin m → K, φ i = ∑ j, a j • cf j`.

Introduce `i`. Establish `: φ i ∈ Submodule.span K (Set.range cf)` using `by rw [hcf]; trivial`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp this`. Conclude with `⟨a, ha.symm⟩`. Use `choose a ha using hrep`.

Unfold `detPoly`. Establish `h1 : (Matrix.of fun i k => polyOf (φ i) (z k)) = fun i => ∑ j ∈ (Finset.univ : Finset (Fin m)), fun k => MvPolynomial.C (a i j) * polyOf (cf j) (z k)`. Use function extensionality and compare the values at `i k`. Rewrite using `[Finset.sum_apply, Matrix.of_apply, ha i]`. Use extensionality with `β`.

Simplify using `[coeff_polyOf, MvPolynomial.coeff_sum]`. Rewrite using `[h1, det_sum_rows (fun i j => fun k => MvPolynomial.C (a i j) * polyOf (cf j) (z k)) (fun _ => (Finset.univ : Finset (Fin m)))]`. Use `Finset.sum_eq_zero fun J _ => ?_` and prove the remaining obligations. Establish `h4 : (fun i => fun k => MvPolynomial.C (a i (J i)) * polyOf (cf (J i)) (z k)) = Matrix.of fun i k => (fun i => MvPolynomial.C (a i (J i))) i * (Matrix.of fun i k => polyOf (cf (J i)) (z k)) i k`. Use function extensionality and compare the values at `i k`.

Both sides reduce to the same expression. Rewrite using `[h4, Matrix.det_mul_column]`. Use `hcon J` as an intermediate fact. Unfold `detPoly at this`. Rewrite using `[this, mul_zero]`.
-/
theorem exists_minor_ne_zero {ρ m : ℕ} (cf : Fin m → (V →ₗ[K] K)) (hcf : Submodule.span K (Set.range cf) = ⊤)
    (z : Fin ρ → (ι →₀ ℕ) →₀ V) (hW : ∃ φ : Fin ρ → V →ₗ[K] K, detPoly φ z ≠ 0) :
    ∃ J : Fin ρ → Fin m, detPoly (fun i => cf (J i)) z ≠ 0 := by
  classical
  obtain ⟨φ, hφ⟩ := hW
  by_contra hcon
  push Not at hcon
  apply hφ
  have hrep : ∀ i, ∃ a : Fin m → K, φ i = ∑ j, a j • cf j := by
    intro i
    have : φ i ∈ Submodule.span K (Set.range cf) := by rw [hcf]; trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp this
    exact ⟨a, ha.symm⟩
  choose a ha using hrep
  unfold detPoly
  have h1 : (Matrix.of fun i k => polyOf (φ i) (z k)) =
      fun i => ∑ j ∈ (Finset.univ : Finset (Fin m)), fun k => MvPolynomial.C (a i j) * polyOf (cf j) (z k) := by
    funext i k
    rw [Finset.sum_apply, Matrix.of_apply, ha i]
    ext β
    simp [coeff_polyOf, MvPolynomial.coeff_sum]
  rw [h1, det_sum_rows (fun i j => fun k => MvPolynomial.C (a i j) * polyOf (cf j) (z k))
    (fun _ => (Finset.univ : Finset (Fin m)))]
  refine Finset.sum_eq_zero fun J _ => ?_
  have h4 : (fun i => fun k => MvPolynomial.C (a i (J i)) * polyOf (cf (J i)) (z k)) =
      Matrix.of fun i k => (fun i => MvPolynomial.C (a i (J i))) i *
        (Matrix.of fun i k => polyOf (cf (J i)) (z k)) i k := by
    funext i k; rfl
  rw [h4, Matrix.det_mul_column]
  have := hcon J
  unfold detPoly at this
  rw [this, mul_zero]

end Det

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < Fintype.card ι` using `by exact_mod_cast Fintype.card_pos`. Take `⟨m, hm⟩ : ∃ m : ℝ, m = (∑ σ, x σ) / (Fintype.card ι : ℝ)` from `⟨_, rfl⟩`. Rewrite using `[← hm]`. Establish `h1 : ∀ σ, Real.exp m * (x σ - m + 1) ≤ Real.exp (x σ)`. Introduce `σ`.

Establish `h` using `Real.add_one_le_exp (x σ - m)`. Establish `h' : Real.exp (x σ) = Real.exp m * Real.exp (x σ - m)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h']`. Conclude with `mul_le_mul_of_nonneg_left h (Real.exp_pos m).le`. Establish `hs : ∑ σ, x σ = (Fintype.card ι : ℝ) * m` using `by rw [hm]; field_simp`. Establish `h2 : ∑ σ, Real.exp m * (x σ - m + 1) = (Fintype.card ι : ℝ) * Real.exp m`. Rewrite using `[← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]`.

Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2]`. Conclude with `Finset.sum_le_sum fun σ _ => h1 σ`.
-/
theorem sz_jensen {ι : Type} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    (Fintype.card ι : ℝ) * Real.exp ((∑ σ, x σ) / (Fintype.card ι : ℝ)) ≤ ∑ σ, Real.exp (x σ) := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (∑ σ, x σ) / (Fintype.card ι : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have h1 : ∀ σ, Real.exp m * (x σ - m + 1) ≤ Real.exp (x σ) := by
    intro σ
    have h := Real.add_one_le_exp (x σ - m)
    have h' : Real.exp (x σ) = Real.exp m * Real.exp (x σ - m) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h']
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos m).le
  have hs : ∑ σ, x σ = (Fintype.card ι : ℝ) * m := by rw [hm]; field_simp
  have h2 : ∑ σ, Real.exp m * (x σ - m + 1) = (Fintype.card ι : ℝ) * Real.exp m := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  rw [← h2]
  exact Finset.sum_le_sum fun σ _ => h1 σ

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < Fintype.card ι` using `by exact_mod_cast Fintype.card_pos`. Establish `hJ` using `sz_jensen (fun σ => 2 * Real.log (s σ))`. Establish `hsq : ∀ σ, Real.exp (2 * Real.log (s σ)) = s σ ^ 2`. Introduce `σ`. Rewrite using `[two_mul, Real.exp_add, Real.exp_log (hs σ)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmean : -(2 * A0) ≤ (∑ σ, 2 * Real.log (s σ)) / (Fintype.card ι : ℝ)`. Rewrite using `[← Finset.mul_sum, mul_div_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (Fintype.card ι : ℝ) * Real.exp (-(2 * A0)) ≤ ∑ σ, s σ ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : ∑ σ, s σ ^ 2 ≤ Real.exp Pd * ∑ σ, n2 σ ^ 2`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun σ _ => hS2 σ`. Establish `h6 : Real.exp (-(A0 + Pd / 2)) ^ 2 = Real.exp (-Pd) * Real.exp (-(2 * A0))`.

Rewrite using `[sq, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h5 : (Real.sqrt (Fintype.card ι) * Real.exp (-(A0 + Pd / 2))) ^ 2 = Real.exp (-Pd) * ((Fintype.card ι : ℝ) * Real.exp (-(2 * A0)))`. Rewrite using `[mul_pow, Real.sq_sqrt hn0.le, h6]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h5]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]`.
-/
theorem quadratic_mean_of_log_average {ι : Type} [Fintype ι] [Nonempty ι] (s n2 : ι → ℝ) (hs : ∀ σ, 0 < s σ)
    (A0 Pd : ℝ) (hLAM : -A0 ≤ (∑ σ, Real.log (s σ)) / (Fintype.card ι : ℝ))
    (hS2 : ∀ σ, s σ ^ 2 ≤ Real.exp Pd * n2 σ ^ 2) :
    (Real.sqrt (Fintype.card ι) * Real.exp (-(A0 + Pd / 2))) ^ 2 ≤ ∑ σ, n2 σ ^ 2 := by
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hJ := sz_jensen (fun σ => 2 * Real.log (s σ))
  have hsq : ∀ σ, Real.exp (2 * Real.log (s σ)) = s σ ^ 2 := by
    intro σ; rw [two_mul, Real.exp_add, Real.exp_log (hs σ)]; ring
  have hmean : -(2 * A0) ≤ (∑ σ, 2 * Real.log (s σ)) / (Fintype.card ι : ℝ) := by
    rw [← Finset.mul_sum, mul_div_assoc]; linarith
  have h3 : (Fintype.card ι : ℝ) * Real.exp (-(2 * A0)) ≤ ∑ σ, s σ ^ 2 := by
    calc (Fintype.card ι : ℝ) * Real.exp (-(2 * A0))
        ≤ (Fintype.card ι : ℝ) * Real.exp ((∑ σ, 2 * Real.log (s σ)) / (Fintype.card ι : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmean) hn0.le
      _ ≤ ∑ σ, Real.exp (2 * Real.log (s σ)) := hJ
      _ = ∑ σ, s σ ^ 2 := Finset.sum_congr rfl fun σ _ => hsq σ
  have h4 : ∑ σ, s σ ^ 2 ≤ Real.exp Pd * ∑ σ, n2 σ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun σ _ => hS2 σ
  have h6 : Real.exp (-(A0 + Pd / 2)) ^ 2 = Real.exp (-Pd) * Real.exp (-(2 * A0)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h5 : (Real.sqrt (Fintype.card ι) * Real.exp (-(A0 + Pd / 2))) ^ 2 =
      Real.exp (-Pd) * ((Fintype.card ι : ℝ) * Real.exp (-(2 * A0))) := by
    rw [mul_pow, Real.sq_sqrt hn0.le, h6]; ring
  rw [h5]
  calc Real.exp (-Pd) * ((Fintype.card ι : ℝ) * Real.exp (-(2 * A0)))
      ≤ Real.exp (-Pd) * (Real.exp Pd * ∑ σ, n2 σ ^ 2) :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (Real.exp_pos _).le
    _ = ∑ σ, n2 σ ^ 2 := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/- English proof (translation)
Establish `e1 : a0 * LamW ≤ a0 * (G * L)` using `mul_le_mul_of_nonneg_left hW ha0`. Establish `e2 : a0 * (G * L) + G * F0 = G * (ka + a0)` using `by rw [← hwt]; ring`. Establish `e3 : G * (ka + a0) ≤ G * (2 * ka)` using `mul_le_mul_of_nonneg_left (by linarith) hG`. Establish `e4 : a0 * lrw ≤ a0 * (Prw * (L - 1))` using `mul_le_mul_of_nonneg_left hrw ha0`. Establish `e5 : a0 * (Prw * (L - 1)) = Prw * (ka - F0)`.

Establish `h : a0 * L = ka + a0 - F0` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `e6 : Prw * (ka - F0) ≤ Prw * ka` using `mul_le_mul_of_nonneg_left (by linarith) hPrw`. Establish `e7 : t * ld ≤ t * Pd` using `mul_le_mul_of_nonneg_left hd (by linarith)`. Establish `e8 : (t - 1 / 2) * lnK ≤ (t - 1 / 2) * PO` using `mul_le_mul_of_nonneg_left hn (by linarith)`.

Establish `e9 : (t + 1 / 2) * (Pd + PO) * 1 ≤ (t + 1 / 2) * (Pd + PO) * ka` using `mul_le_mul_of_nonneg_left hka (mul_nonneg (by linarith) (by linarith))`. Establish `e10 : (2 * G + Prw + tableDegreeThreeBase + (t + 1 / 2) * (Pd + PO)) * ka = G * (2 * ka) + Prw * ka + tableDegreeThreeBase * ka + (t + 1 / 2) * (Pd + PO) * ka` using `by ring`. Establish `e11 : a0 * (LamW + lrw) = a0 * LamW + a0 * lrw` using `by ring`. Establish `e12 : (t + 1 / 2) * (Pd + PO) * 1 = t * Pd + Pd / 2 + ((t - 1 / 2) * PO + PO)` using `by ring`. Rewrite using `[e10, e11]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deep_size (t a0 LamW Lam0 lrw G Prw tableDegreeThreeBase Pd PO L F0 ka ld lnK lrd : ℝ) (ht : 1 ≤ t) (ha0 : 0 ≤ a0)
    (hG : 0 ≤ G) (hPrw : 0 ≤ Prw) (hPd : 0 ≤ Pd) (hPO : 0 ≤ PO) (hka : 1 ≤ ka) (hF0 : 0 ≤ F0)
    (hW : LamW ≤ G * L) (h0 : Lam0 ≤ G * F0) (hwt : a0 * L + F0 = ka + a0) (ha : a0 ≤ ka)
    (hrw : lrw ≤ Prw * (L - 1)) (hd : ld ≤ Pd) (hn : lnK ≤ PO) (hr : lrd ≤ PO) :
    a0 * (LamW + lrw) + Lam0 + (tableDegreeThreeBase * ka + Pd / 2) + (t * ld + (t - 1 / 2) * lnK) + lrd ≤
      (2 * G + Prw + tableDegreeThreeBase + (t + 1 / 2) * (Pd + PO)) * ka := by
  have e1 : a0 * LamW ≤ a0 * (G * L) := mul_le_mul_of_nonneg_left hW ha0
  have e2 : a0 * (G * L) + G * F0 = G * (ka + a0) := by rw [← hwt]; ring
  have e3 : G * (ka + a0) ≤ G * (2 * ka) := mul_le_mul_of_nonneg_left (by linarith) hG
  have e4 : a0 * lrw ≤ a0 * (Prw * (L - 1)) := mul_le_mul_of_nonneg_left hrw ha0
  have e5 : a0 * (Prw * (L - 1)) = Prw * (ka - F0) := by
    have h : a0 * L = ka + a0 - F0 := by linarith
    calc a0 * (Prw * (L - 1)) = Prw * (a0 * L - a0) := by ring
      _ = Prw * (ka - F0) := by rw [h]; ring
  have e6 : Prw * (ka - F0) ≤ Prw * ka := mul_le_mul_of_nonneg_left (by linarith) hPrw
  have e7 : t * ld ≤ t * Pd := mul_le_mul_of_nonneg_left hd (by linarith)
  have e8 : (t - 1 / 2) * lnK ≤ (t - 1 / 2) * PO := mul_le_mul_of_nonneg_left hn (by linarith)
  have e9 : (t + 1 / 2) * (Pd + PO) * 1 ≤ (t + 1 / 2) * (Pd + PO) * ka :=
    mul_le_mul_of_nonneg_left hka (mul_nonneg (by linarith) (by linarith))
  have e10 : (2 * G + Prw + tableDegreeThreeBase + (t + 1 / 2) * (Pd + PO)) * ka =
      G * (2 * ka) + Prw * ka + tableDegreeThreeBase * ka + (t + 1 / 2) * (Pd + PO) * ka := by ring
  have e11 : a0 * (LamW + lrw) = a0 * LamW + a0 * lrw := by ring
  have e12 : (t + 1 / 2) * (Pd + PO) * 1 = t * Pd + Pd / 2 + ((t - 1 / 2) * PO + PO) := by ring
  rw [e10, e11]
  linarith

section Core

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {ι : Type}

def GaussLe (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V)
    (c : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 K)) (φ : Fin ρ → V →ₗ[K] K), (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) →
    ∀ β, (detPoly φ z).coeff β ≠ 0 → c la ≤ (vAdd la ((detPoly φ z).coeff β) : ℝ)

/- English proof (translation)
Take `⟨t, ht0, ht⟩` from `exists_vAdd_eq la (vDiff K la : ℤ)`. Establish `hint : ∀ i, ∀ f ∈ M, la.valuation K ((t • φ i) f) ≤ 1`. Introduce `i f hf`. Rewrite using `[LinearMap.smul_apply, smul_eq_mul]`. Distinguish the cases in `h0 : φ i f = 0`.

Rewrite using `[h0, mul_zero, map_zero]`. Conclude with `zero_le_one`. Rewrite using `[val_le_one_iff la (mul_ne_zero ht0 h0), vAdd_mul' la ht0 h0, ht]`. Use `vAdd_of_inCodiff h0 (hcod i f hf) la` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hco : (detPoly (fun i => t • φ i) z).coeff β = t ^ ρ * (detPoly φ z).coeff β`. Rewrite using `[detPoly_smul, MvPolynomial.coeff_C_mul]`. Establish `hne : (detPoly (fun i => t • φ i) z).coeff β ≠ 0`. Rewrite using `[hco]`. Conclude with `mul_ne_zero (pow_ne_zero _ ht0) ha`.

Establish `h` using `hG la (fun i => t • φ i) hint β hne`. Rewrite `h` using `[hco, vAdd_mul' la (pow_ne_zero _ ht0) ha, vAdd_pow', ht]`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core_val {M : Submodule (𝓞 K) V} {ρ : ℕ} {z : Fin ρ → (ι →₀ ℕ) →₀ V}
    {c : HeightOneSpectrum (𝓞 K) → ℝ} (hG : GaussLe M z c) (φ : Fin ρ → V →ₗ[K] K)
    (hcod : ∀ i, ∀ f ∈ M, InCodiff (φ i f)) (β : ι →₀ ℕ) (ha : (detPoly φ z).coeff β ≠ 0)
    (la : HeightOneSpectrum (𝓞 K)) :
    c la ≤ (vAdd la ((detPoly φ z).coeff β) : ℝ) + ρ * (vDiff K la : ℝ) := by
  obtain ⟨t, ht0, ht⟩ := exists_vAdd_eq la (vDiff K la : ℤ)
  have hint : ∀ i, ∀ f ∈ M, la.valuation K ((t • φ i) f) ≤ 1 := by
    intro i f hf
    rw [LinearMap.smul_apply, smul_eq_mul]
    by_cases h0 : φ i f = 0
    · rw [h0, mul_zero, map_zero]; exact zero_le_one
    · rw [val_le_one_iff la (mul_ne_zero ht0 h0), vAdd_mul' la ht0 h0, ht]
      have := vAdd_of_inCodiff h0 (hcod i f hf) la
      omega
  have hco : (detPoly (fun i => t • φ i) z).coeff β = t ^ ρ * (detPoly φ z).coeff β := by
    rw [detPoly_smul, MvPolynomial.coeff_C_mul]
  have hne : (detPoly (fun i => t • φ i) z).coeff β ≠ 0 := by
    rw [hco]; exact mul_ne_zero (pow_ne_zero _ ht0) ha
  have h := hG la (fun i => t • φ i) hint β hne
  rw [hco, vAdd_mul' la (pow_ne_zero _ ht0) ha, vAdd_pow', ht] at h
  push_cast at h
  linarith

/- English proof (translation)
Establish `hC : 0 ≤ ∏ i, C i` using `Finset.prod_nonneg fun i _ => by`. Take `⟨a, ha, _⟩` from `h i`. Conclude with `(norm_nonneg a).trans ha`. Establish `hN : ∀ f, 0 ≤ N2 σ f` using `fun f => by rw [← Hm.norm_e]; exact norm_nonneg _`. Rewrite using `[detPoly_expand, MvPolynomial.coeff_sum, map_sum, Finset.prod_univ_sum, Finset.mul_sum]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs`. Conclude with `Hm.had σ φ C h fun k => z k (b k)`. Rewrite using `[map_zero, norm_zero]`.

Conclude with `mul_nonneg hC (Finset.prod_nonneg fun k _ => hN _)`.
-/
theorem core_arch {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) (σ : K →+* ℂ) {ρ : ℕ}
    (φ : Fin ρ → V →ₗ[K] K) (C : Fin ρ → ℝ) (h : ∀ i, Hm.OpLe σ (φ i) (C i))
    (z : Fin ρ → (ι →₀ ℕ) →₀ V) (β : ι →₀ ℕ) :
    ‖σ ((detPoly φ z).coeff β)‖ ≤ (∏ i, C i) * ∏ k, ∑ γ ∈ (z k).support, N2 σ (z k γ) := by
  classical
  have hC : 0 ≤ ∏ i, C i := Finset.prod_nonneg fun i _ => by
    obtain ⟨a, ha, _⟩ := h i
    exact (norm_nonneg a).trans ha
  have hN : ∀ f, 0 ≤ N2 σ f := fun f => by rw [← Hm.norm_e]; exact norm_nonneg _
  rw [detPoly_expand, MvPolynomial.coeff_sum, map_sum, Finset.prod_univ_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact Hm.had σ φ C h fun k => z k (b k)
  · rw [map_zero, norm_zero]
    exact mul_nonneg hC (Finset.prod_nonneg fun k _ => hN _)

/- English proof (translation)
Take `⟨J, hJ⟩` from `exists_minor_ne_zero cf hspan z hW`. Take `⟨β, hβ⟩` from `MvPolynomial.ne_zero_iff.mp hJ`. Use `set a := (detPoly (fun i => cf (J i)) z).coeff β with ha`. Take `⟨hf1, hs1⟩` from `sum_vAdd a hβ`. Take `⟨hf2, hs2⟩` from `sum_vDiff K`.

Establish `hle : ∀ la, c la * lnN la ≤ (vAdd la a : ℝ) * lnN la + ρ * ((vDiff K la : ℝ) * lnN la)`. Introduce `la`. Establish `h1` using `core_val hG (fun i => cf (J i)) (fun i => hcod (J i)) β hβ la`. Establish `h2` using `(lnN_pos la).le`. Combine the equalities or inequalities in the displayed calculation.

Establish `hS1 : Summable fun la : HeightOneSpectrum (𝓞 K) => (vAdd la a : ℝ) * lnN la` using `summable_of_hasFiniteSupport hf1`. Establish `hS2 : Summable fun la : HeightOneSpectrum (𝓞 K) => (vDiff K la : ℝ) * lnN la` using `summable_of_hasFiniteSupport hf2`. Establish `hSg` using `hS1.add (hS2.mul_left (ρ : ℝ))`. Establish `hSc : Summable fun la => c la * lnN la` using `Summable.of_nonneg_of_le (fun la => mul_nonneg (hc0 la) (lnN_pos la).le) hle hSg`. Use `⟨hSc, ?_⟩` and prove the remaining obligations.

Establish `h1 : ∑' la, c la * lnN la ≤ ∑ σ : K →+* ℂ, Real.log ‖σ a‖ + ρ * Real.log |((discr K : ℤ) : ℝ)|`. Use `(hSc.tsum_le_tsum hle hSg).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hS1.tsum_add (hS2.mul_left _), tsum_mul_left, tsum_eq_finsum hf1, tsum_eq_finsum hf2, hs1, hs2]`. Establish `h2 : ∀ σ : K →+* ℂ, Real.log ‖σ a‖ ≤ ρ * Real.log Bop + ∑ k, E σ k`. Introduce `σ`.

Establish `hpos : 0 < ‖σ a‖` using `norm_pos_iff.mpr ((map_ne_zero σ).mpr hβ)`. Establish `hb` using `core_arch Hm σ (fun i => cf (J i)) (fun _ => Bop) (fun i => hop σ (J i)) z β`. Establish `hb2 : ‖σ a‖ ≤ Bop ^ ρ * Real.exp (∑ k, E σ k)`. Use `hb.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_sum]`.

Use `mul_le_mul_of_nonneg_left ?_ (pow_pos hB _).le` and prove the remaining obligations. Use `Finset.prod_le_prod (fun k _ => Finset.sum_nonneg fun γ _ => ?_) fun k _ => hE σ k` and prove the remaining obligations. Rewrite using `[← Hm.norm_e]`. Conclude with `norm_nonneg _`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear relations using `[Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => h2 σ]`.
-/
theorem deepCore (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V)
    (c : HeightOneSpectrum (𝓞 K) → ℝ) (hc0 : ∀ la, 0 ≤ c la) (hG : GaussLe M z c)
    (hW : ∃ φ : Fin ρ → V →ₗ[K] K, detPoly φ z ≠ 0)
    {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) {m : ℕ} (cf : Fin m → (V →ₗ[K] K))
    (hspan : Submodule.span K (Set.range cf) = ⊤) (hcod : ∀ j, ∀ f ∈ M, InCodiff (cf j f))
    (Bop : ℝ) (hB : 0 < Bop) (hop : ∀ σ j, Hm.OpLe σ (cf j) Bop)
    (E : (K →+* ℂ) → Fin ρ → ℝ)
    (hE : ∀ σ k, ∑ γ ∈ (z k).support, N2 σ (z k γ) ≤ Real.exp (E σ k)) :
    Summable (fun la => c la * lnN la) ∧
      ∑' la, c la * lnN la ≤ ρ * Real.log |((discr K : ℤ) : ℝ)| +
        ∑ σ : K →+* ℂ, (ρ * Real.log Bop + ∑ k, E σ k) := by
  classical
  obtain ⟨J, hJ⟩ := exists_minor_ne_zero cf hspan z hW
  obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hJ
  set a := (detPoly (fun i => cf (J i)) z).coeff β with ha
  obtain ⟨hf1, hs1⟩ := sum_vAdd a hβ
  obtain ⟨hf2, hs2⟩ := sum_vDiff K
  have hle : ∀ la, c la * lnN la ≤ (vAdd la a : ℝ) * lnN la + ρ * ((vDiff K la : ℝ) * lnN la) := by
    intro la
    have h1 := core_val hG (fun i => cf (J i)) (fun i => hcod (J i)) β hβ la
    have h2 := (lnN_pos la).le
    calc c la * lnN la ≤ ((vAdd la a : ℝ) + ρ * (vDiff K la : ℝ)) * lnN la :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  have hS1 : Summable fun la : HeightOneSpectrum (𝓞 K) => (vAdd la a : ℝ) * lnN la :=
    summable_of_hasFiniteSupport hf1
  have hS2 : Summable fun la : HeightOneSpectrum (𝓞 K) => (vDiff K la : ℝ) * lnN la :=
    summable_of_hasFiniteSupport hf2
  have hSg := hS1.add (hS2.mul_left (ρ : ℝ))
  have hSc : Summable fun la => c la * lnN la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (hc0 la) (lnN_pos la).le) hle hSg
  refine ⟨hSc, ?_⟩
  have h1 : ∑' la, c la * lnN la ≤ ∑ σ : K →+* ℂ, Real.log ‖σ a‖ + ρ * Real.log |((discr K : ℤ) : ℝ)| := by
    refine (hSc.tsum_le_tsum hle hSg).trans (le_of_eq ?_)
    rw [hS1.tsum_add (hS2.mul_left _), tsum_mul_left, tsum_eq_finsum hf1, tsum_eq_finsum hf2, hs1, hs2]
  have h2 : ∀ σ : K →+* ℂ, Real.log ‖σ a‖ ≤ ρ * Real.log Bop + ∑ k, E σ k := by
    intro σ
    have hpos : 0 < ‖σ a‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hβ)
    have hb := core_arch Hm σ (fun i => cf (J i)) (fun _ => Bop) (fun i => hop σ (J i)) z β
    have hb2 : ‖σ a‖ ≤ Bop ^ ρ * Real.exp (∑ k, E σ k) := by
      refine hb.trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_sum]
      refine mul_le_mul_of_nonneg_left ?_ (pow_pos hB _).le
      refine Finset.prod_le_prod (fun k _ => Finset.sum_nonneg fun γ _ => ?_) fun k _ => hE σ k
      rw [← Hm.norm_e]; exact norm_nonneg _
    calc Real.log ‖σ a‖ ≤ Real.log (Bop ^ ρ * Real.exp (∑ k, E σ k)) := Real.log_le_log hpos hb2
      _ = _ := by rw [Real.log_mul (pow_pos hB _).ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
  linarith [Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => h2 σ]

end Core

section GC

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {ι : Type}

def gaussC (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V) (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  sInf {n : ℕ | ∃ (φ : Fin ρ → V →ₗ[K] K) (β : ι →₀ ℕ), (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) ∧
    (detPoly φ z).coeff β ≠ 0 ∧ vAdd la ((detPoly φ z).coeff β) = (n : ℤ)}

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)`.
-/
theorem gc_det_mem {F : Type} [Field F] (S : Subring F) {ρ : ℕ} (A : Matrix (Fin ρ) (Fin ρ) F)
    (h : ∀ i k, A i k ∈ S) : A.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

/- English proof (translation)
Rewrite using `[← Valuation.mem_integer_iff, detPoly_expand, MvPolynomial.coeff_sum]`. Use `Subring.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_monomial]`. Use `split_ifs`. Conclude with `gc_det_mem _ _ fun i k => (Valuation.mem_integer_iff _ _).mpr (hφ i _ (hz k _))`.

Conclude with `Subring.zero_mem _`.
-/
theorem gc_coeff_int {M : Submodule (𝓞 K) V} {ρ : ℕ} {z : Fin ρ → (ι →₀ ℕ) →₀ V} (hz : ∀ k β, z k β ∈ M)
    (la : HeightOneSpectrum (𝓞 K)) (φ : Fin ρ → V →ₗ[K] K)
    (hφ : ∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) (β : ι →₀ ℕ) :
    la.valuation K ((detPoly φ z).coeff β) ≤ 1 := by
  classical
  rw [← Valuation.mem_integer_iff, detPoly_expand, MvPolynomial.coeff_sum]
  refine Subring.sum_mem _ fun b _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact gc_det_mem _ _ fun i k => (Valuation.mem_integer_iff _ _).mpr (hφ i _ (hz k _))
  · exact Subring.zero_mem _

/- English proof (translation)
The claim follows from `Nat.cast_nonneg _`.
-/
theorem gaussC_nonneg (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V)
    (la : HeightOneSpectrum (𝓞 K)) : (0 : ℝ) ≤ (gaussC M z la : ℝ) := Nat.cast_nonneg _

/- English proof (translation)
Introduce `la φ hφ β hβ`. Establish `h0 : 0 ≤ vAdd la ((detPoly φ z).coeff β)` using `(val_le_one_iff la hβ).mp (gc_coeff_int hz la φ hφ β)`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le h0`. Establish `hle : gaussC M z la ≤ n` using `Nat.sInf_le ⟨φ, β, hφ, hβ, hn⟩`. Rewrite using `[hn]`.

Use `show ((gaussC M z la : ℕ) : ℝ) ≤ (((n : ℕ) : ℤ) : ℝ)`. Conclude with `hle` after adjusting the coercions.
-/
theorem gaussC_gaussLe {M : Submodule (𝓞 K) V} {ρ : ℕ} {z : Fin ρ → (ι →₀ ℕ) →₀ V} (hz : ∀ k β, z k β ∈ M) :
    GaussLe M z (fun la => (gaussC M z la : ℝ)) := by
  intro la φ hφ β hβ
  have h0 : 0 ≤ vAdd la ((detPoly φ z).coeff β) := (val_le_one_iff la hβ).mp (gc_coeff_int hz la φ hφ β)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
  have hle : gaussC M z la ≤ n := Nat.sInf_le ⟨φ, β, hφ, hβ, hn⟩
  rw [hn]
  show ((gaussC M z la : ℕ) : ℝ) ≤ (((n : ℕ) : ℤ) : ℝ)
  exact_mod_cast hle

end GC

section Sum

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {ι : Type}

/- English proof (translation)
Establish `hcard : (Fintype.card (K →+* ℂ) : ℝ) = (finrank ℚ K : ℝ)` using `by rw [Embeddings.card K ℂ]`. Establish `hn : 0 < (finrank ℚ K : ℝ)` using `by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))`. Rewrite `hLW`, `hL0` using `[hcard]`. Use `set n : ℝ := (finrank ℚ K : ℝ) with hndef`. Use `set Λ : ℝ := Real.sqrt n * Real.exp (-(A0 + Pd / 2)) with hΛ`.

Establish `hΛ0 : 0 < Λ` using `mul_pos (Real.sqrt_pos.mpr hn) (Real.exp_pos _)`. Establish `hlam : ∀ f ∈ M, f ≠ 0 → Λ ^ 2 ≤ ∑ σ : K →+* ℂ, N2 σ f ^ 2`. Introduce `f hf hf0`. Use `quadratic_mean_of_log_average (fun σ : K →+* ℂ => sup σ f) (fun σ => N2 σ f) (fun σ => hsup σ f hf0) A0 Pd (hLAM f hf hf0) (fun σ => hS2 σ f)` as an intermediate fact. Rewrite `this` using `[hcard]`. Then use the resulting hypothesis.

Take `⟨m, cf, hspan, hcod, hop⟩` from `hT Λ hΛ0 hlam`. Take `⟨hS, hb⟩` from `deepCore M z c hc0 hG hW Hm cf hspan hcod (Ctr / Λ) (div_pos hCtr hΛ0) hop (fun σ k => a0 * (lrw + mx σ) + S σ k) hE`. Use `⟨hS, hb.trans ?_⟩` and prove the remaining obligations. Establish `hlogB : Real.log (Ctr / Λ) = Real.log Ctr - Real.log n / 2 + (A0 + Pd / 2)`. Rewrite using `[Real.log_div hCtr.ne' hΛ0.ne', hΛ, Real.log_mul (Real.sqrt_pos.mpr hn).ne' (Real.exp_pos _).ne', Real.log_sqrt hn.le, Real.log_exp]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e1 : ∑ σ : K →+* ℂ, ((ρ : ℝ) * Real.log (Ctr / Λ) + ∑ k, (a0 * (lrw + mx σ) + S σ k)) = n * (ρ * Real.log (Ctr / Λ)) + ρ * (a0 * (n * lrw + ∑ σ, mx σ)) + ∑ k, ∑ σ, S σ k`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hcard]`. Rewrite using `[Finset.sum_comm]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, hlogB]`. Establish `h1 : ∑ σ, mx σ ≤ n * LamW` using `by rw [div_le_iff₀ hn] at hLW; linarith`. Establish `h2 : ∑ k, ∑ σ, S σ k ≤ ρ * (n * Lam0)`. Combine the equalities or inequalities in the displayed calculation. Use `hL0 k` as an intermediate fact.

Rewrite `this` using `[div_le_iff₀ hn]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = ρ * (n * Lam0) := by simp`. Establish `h3 : (ρ : ℝ) * (a0 * (n * lrw + ∑ σ, mx σ)) ≤ ρ * (a0 * (n * lrw + n * LamW))`. Establish `: (0 : ℝ) ≤ ρ` using `Nat.cast_nonneg _`.

Use `gcongr`. Use polynomial arithmetic with `[h2, h3]`.
-/
theorem log_sup_sum_le_of_nonvanishing_det (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V)
    (c : HeightOneSpectrum (𝓞 K) → ℝ) (hc0 : ∀ la, 0 ≤ c la) (hG : GaussLe M z c)
    (hW : ∃ φ : Fin ρ → V →ₗ[K] K, detPoly φ z ≠ 0)
    {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) (Ctr : ℝ) (hCtr : 0 < Ctr) (hT : Trans M Hm Ctr)
    (sup : (K →+* ℂ) → V → ℝ) (hsup : ∀ σ f, f ≠ 0 → 0 < sup σ f) (A0 Pd : ℝ)
    (hLAM : ∀ f ∈ M, f ≠ 0 → -A0 ≤ (∑ σ : K →+* ℂ, Real.log (sup σ f)) / (Fintype.card (K →+* ℂ) : ℝ))
    (hS2 : ∀ σ f, sup σ f ^ 2 ≤ Real.exp Pd * N2 σ f ^ 2)
    (a0 lrw : ℝ) (mx : (K →+* ℂ) → ℝ) (S : (K →+* ℂ) → Fin ρ → ℝ)
    (hE : ∀ σ k, ∑ γ ∈ (z k).support, N2 σ (z k γ) ≤ Real.exp (a0 * (lrw + mx σ) + S σ k))
    (LamW Lam0 : ℝ) (ha0 : 0 ≤ a0)
    (hLW : (∑ σ, mx σ) / (Fintype.card (K →+* ℂ) : ℝ) ≤ LamW)
    (hL0 : ∀ k, (∑ σ, S σ k) / (Fintype.card (K →+* ℂ) : ℝ) ≤ Lam0) :
    Summable (fun la => c la * lnN la) ∧
      ∑' la, c la * lnN la ≤ ρ * ((finrank ℚ K : ℝ) * (a0 * (LamW + lrw) + Lam0 + (A0 + Pd / 2) +
        (Real.log Ctr - Real.log (finrank ℚ K : ℝ) / 2)) + Real.log |((discr K : ℤ) : ℝ)|) := by
  classical
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = (finrank ℚ K : ℝ) := by rw [Embeddings.card K ℂ]
  have hn : 0 < (finrank ℚ K : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  rw [hcard] at hLW hL0
  set n : ℝ := (finrank ℚ K : ℝ) with hndef
  set Λ : ℝ := Real.sqrt n * Real.exp (-(A0 + Pd / 2)) with hΛ
  have hΛ0 : 0 < Λ := mul_pos (Real.sqrt_pos.mpr hn) (Real.exp_pos _)
  have hlam : ∀ f ∈ M, f ≠ 0 → Λ ^ 2 ≤ ∑ σ : K →+* ℂ, N2 σ f ^ 2 := by
    intro f hf hf0
    have := quadratic_mean_of_log_average (fun σ : K →+* ℂ => sup σ f) (fun σ => N2 σ f) (fun σ => hsup σ f hf0) A0 Pd
      (hLAM f hf hf0) (fun σ => hS2 σ f)
    rwa [hcard] at this
  obtain ⟨m, cf, hspan, hcod, hop⟩ := hT Λ hΛ0 hlam
  obtain ⟨hS, hb⟩ := deepCore M z c hc0 hG hW Hm cf hspan hcod (Ctr / Λ) (div_pos hCtr hΛ0) hop
    (fun σ k => a0 * (lrw + mx σ) + S σ k) hE
  refine ⟨hS, hb.trans ?_⟩
  have hlogB : Real.log (Ctr / Λ) = Real.log Ctr - Real.log n / 2 + (A0 + Pd / 2) := by
    rw [Real.log_div hCtr.ne' hΛ0.ne', hΛ, Real.log_mul (Real.sqrt_pos.mpr hn).ne' (Real.exp_pos _).ne',
      Real.log_sqrt hn.le, Real.log_exp]
    ring
  have e1 : ∑ σ : K →+* ℂ, ((ρ : ℝ) * Real.log (Ctr / Λ) + ∑ k, (a0 * (lrw + mx σ) + S σ k)) =
      n * (ρ * Real.log (Ctr / Λ)) + ρ * (a0 * (n * lrw + ∑ σ, mx σ)) + ∑ k, ∑ σ, S σ k := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, hcard]
    rw [Finset.sum_comm]
    ring
  rw [e1, hlogB]
  have h1 : ∑ σ, mx σ ≤ n * LamW := by rw [div_le_iff₀ hn] at hLW; linarith
  have h2 : ∑ k, ∑ σ, S σ k ≤ ρ * (n * Lam0) := by
    calc ∑ k, ∑ σ, S σ k ≤ ∑ _k : Fin ρ, n * Lam0 := Finset.sum_le_sum fun k _ => by
          have := hL0 k; rw [div_le_iff₀ hn] at this; linarith
      _ = ρ * (n * Lam0) := by simp
  have h3 : (ρ : ℝ) * (a0 * (n * lrw + ∑ σ, mx σ)) ≤ ρ * (a0 * (n * lrw + n * LamW)) := by
    have : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
    gcongr
  nlinarith [h2, h3]

/- English proof (translation)
Establish `key : ∀ δ : ℝ, 0 < δ → Summable (fun la => c la * lnN la) ∧ ∑' la, c la * lnN la ≤ ρ * ((finrank ℚ K : ℝ) * (a0 * (LamW + lrw) + Lam0 + (A0 + Pd / 2) + (Real.log C0 + δ - Real.log (finrank ℚ K : ℝ) / 2)) + Real.log |((discr K : ℤ) : ℝ)|)`. Introduce `δ hδ`. Establish `h1 : C0 < C0 * Real.exp δ`. Establish `: 1 < Real.exp δ` using `Real.one_lt_exp_iff.mpr hδ`. Use the polynomial consequences of the given equalities and inequalities.

Use `log_sup_sum_le_of_nonvanishing_det M z c hc0 hG hW Hm (C0 * Real.exp δ) (hC0.trans h1) (hT _ h1) sup hsup A0 Pd hLAM hS2 a0 lrw mx S hE LamW Lam0 ha0 hLW hL0` as an intermediate fact. Rewrite `this` using `[Real.log_mul hC0.ne' (Real.exp_pos _).ne', Real.log_exp]`. Then use the resulting hypothesis. Use `⟨(key 1 one_pos).1, le_of_forall_pos_le_add fun ε hε => ?_⟩` and prove the remaining obligations. Establish `hn : (0 : ℝ) ≤ (finrank ℚ K : ℝ)` using `Nat.cast_nonneg _`. Establish `hρ : (0 : ℝ) ≤ (ρ : ℝ)` using `Nat.cast_nonneg _`.

Establish `hq : 0 < (ρ : ℝ) * (finrank ℚ K : ℝ) + 1` using `by positivity`. Use `(key (ε / ((ρ : ℝ) * (finrank ℚ K : ℝ) + 1)) (div_pos hε hq)).2` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Establish `h2 : (ρ : ℝ) * (finrank ℚ K : ℝ) * (ε / ((ρ : ℝ) * (finrank ℚ K : ℝ) + 1)) ≤ ε`. Rewrite using `[← mul_div_assoc, div_le_iff₀ hq]`.

Use polynomial arithmetic with `[mul_nonneg hρ hn]`. Use polynomial arithmetic with `[h2]`.
-/
theorem log_sup_sum_le_of_nonvanishing_det_limit (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V)
    (c : HeightOneSpectrum (𝓞 K) → ℝ) (hc0 : ∀ la, 0 ≤ c la) (hG : GaussLe M z c)
    (hW : ∃ φ : Fin ρ → V →ₗ[K] K, detPoly φ z ≠ 0)
    {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) (C0 : ℝ) (hC0 : 0 < C0)
    (hT : ∀ Ctr, C0 < Ctr → Trans M Hm Ctr)
    (sup : (K →+* ℂ) → V → ℝ) (hsup : ∀ σ f, f ≠ 0 → 0 < sup σ f) (A0 Pd : ℝ)
    (hLAM : ∀ f ∈ M, f ≠ 0 → -A0 ≤ (∑ σ : K →+* ℂ, Real.log (sup σ f)) / (Fintype.card (K →+* ℂ) : ℝ))
    (hS2 : ∀ σ f, sup σ f ^ 2 ≤ Real.exp Pd * N2 σ f ^ 2)
    (a0 lrw : ℝ) (mx : (K →+* ℂ) → ℝ) (S : (K →+* ℂ) → Fin ρ → ℝ)
    (hE : ∀ σ k, ∑ γ ∈ (z k).support, N2 σ (z k γ) ≤ Real.exp (a0 * (lrw + mx σ) + S σ k))
    (LamW Lam0 : ℝ) (ha0 : 0 ≤ a0)
    (hLW : (∑ σ, mx σ) / (Fintype.card (K →+* ℂ) : ℝ) ≤ LamW)
    (hL0 : ∀ k, (∑ σ, S σ k) / (Fintype.card (K →+* ℂ) : ℝ) ≤ Lam0) :
    Summable (fun la => c la * lnN la) ∧
      ∑' la, c la * lnN la ≤ ρ * ((finrank ℚ K : ℝ) * (a0 * (LamW + lrw) + Lam0 + (A0 + Pd / 2) +
        (Real.log C0 - Real.log (finrank ℚ K : ℝ) / 2)) + Real.log |((discr K : ℤ) : ℝ)|) := by
  have key : ∀ δ : ℝ, 0 < δ → Summable (fun la => c la * lnN la) ∧
      ∑' la, c la * lnN la ≤ ρ * ((finrank ℚ K : ℝ) * (a0 * (LamW + lrw) + Lam0 + (A0 + Pd / 2) +
        (Real.log C0 + δ - Real.log (finrank ℚ K : ℝ) / 2)) + Real.log |((discr K : ℤ) : ℝ)|) := by
    intro δ hδ
    have h1 : C0 < C0 * Real.exp δ := by
      have : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
      nlinarith
    have := log_sup_sum_le_of_nonvanishing_det M z c hc0 hG hW Hm (C0 * Real.exp δ) (hC0.trans h1) (hT _ h1) sup hsup A0 Pd hLAM hS2
      a0 lrw mx S hE LamW Lam0 ha0 hLW hL0
    rwa [Real.log_mul hC0.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  refine ⟨(key 1 one_pos).1, le_of_forall_pos_le_add fun ε hε => ?_⟩
  have hn : (0 : ℝ) ≤ (finrank ℚ K : ℝ) := Nat.cast_nonneg _
  have hρ : (0 : ℝ) ≤ (ρ : ℝ) := Nat.cast_nonneg _
  have hq : 0 < (ρ : ℝ) * (finrank ℚ K : ℝ) + 1 := by positivity
  have := (key (ε / ((ρ : ℝ) * (finrank ℚ K : ℝ) + 1)) (div_pos hε hq)).2
  refine this.trans ?_
  have h2 : (ρ : ℝ) * (finrank ℚ K : ℝ) * (ε / ((ρ : ℝ) * (finrank ℚ K : ℝ) + 1)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hq]
    nlinarith [mul_nonneg hρ hn]
  nlinarith [h2]

/- English proof (translation)
Take `⟨hS, hb⟩` from `log_sup_sum_le_of_nonvanishing_det_limit M z c hc0 hG hW Hm C0 hC0 hT sup hsup (tableDegreeThreeBase * ka) Pd hLAM hS2 a0 lrw mx S hE (G * L) (G * F0) ha0 hLW hL0`. Establish `hnpos : 0 < (finrank ℚ K : ℝ)` using `by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))`. Establish `hfun : (fun la => c la * lw K la) = fun la => (c la * lnN la) / (finrank ℚ K : ℝ)`. Use function extensionality and compare the values at `la`. Unfold `lw lnN`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Use `⟨hS.div_const _, ?_⟩` and prove the remaining obligations. Rewrite using `[tsum_div_const, div_le_iff₀ hnpos]`. Use `hb.trans ?_` and prove the remaining obligations.

Establish `hsz` using `deep_size t a0 (G * L) (G * F0) lrw G Prw tableDegreeThreeBase Pd PO L F0 ka ld (Real.log (finrank ℚ K : ℝ)) (Real.log |((discr K : ℤ) : ℝ)| / (finrank ℚ K : ℝ)) ht ha0 hG0 hPrw hPd hPO hka hF0 le_rfl le_rfl hwt ha hrw hd hn hr`. Establish `hρ : (0 : ℝ) ≤ (ρ : ℝ)` using `Nat.cast_nonneg _`. Establish `hdisc : Real.log |((discr K : ℤ) : ℝ)| = (finrank ℚ K : ℝ) * (Real.log |((discr K : ℤ) : ℝ)| / (finrank ℚ K : ℝ))` using `by field_simp`. Rewrite using `[mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ hρ` and prove the remaining obligations.

Rewrite using `[hdisc, ← mul_add, mul_comm _ (finrank ℚ K : ℝ)]`. Use `mul_le_mul_of_nonneg_left ?_ hnpos.le` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deepSum (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V)
    (c : HeightOneSpectrum (𝓞 K) → ℝ) (hc0 : ∀ la, 0 ≤ c la) (hG : GaussLe M z c)
    (hW : ∃ φ : Fin ρ → V →ₗ[K] K, detPoly φ z ≠ 0)
    {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ} (Hm : Herm N2 dH) (C0 : ℝ) (hC0 : 0 < C0)
    (hT : ∀ Ctr, C0 < Ctr → Trans M Hm Ctr)
    (sup : (K →+* ℂ) → V → ℝ) (hsup : ∀ σ f, f ≠ 0 → 0 < sup σ f) (tableDegreeThreeBase ka Pd : ℝ)
    (hLAM : ∀ f ∈ M, f ≠ 0 →
      -(tableDegreeThreeBase * ka) ≤ (∑ σ : K →+* ℂ, Real.log (sup σ f)) / (Fintype.card (K →+* ℂ) : ℝ))
    (hS2 : ∀ σ f, sup σ f ^ 2 ≤ Real.exp Pd * N2 σ f ^ 2)
    (a0 lrw : ℝ) (mx : (K →+* ℂ) → ℝ) (S : (K →+* ℂ) → Fin ρ → ℝ)
    (hE : ∀ σ k, ∑ γ ∈ (z k).support, N2 σ (z k γ) ≤ Real.exp (a0 * (lrw + mx σ) + S σ k))
    (ha0 : 0 ≤ a0) (t G Prw PO L F0 ld : ℝ) (ht : 1 ≤ t) (hG0 : 0 ≤ G) (hPrw : 0 ≤ Prw) (hPd : 0 ≤ Pd)
    (hPO : 0 ≤ PO) (hka : 1 ≤ ka) (hF0 : 0 ≤ F0)
    (hLW : (∑ σ, mx σ) / (Fintype.card (K →+* ℂ) : ℝ) ≤ G * L)
    (hL0 : ∀ k, (∑ σ, S σ k) / (Fintype.card (K →+* ℂ) : ℝ) ≤ G * F0)
    (hwt : a0 * L + F0 = ka + a0) (ha : a0 ≤ ka) (hrw : lrw ≤ Prw * (L - 1)) (hd : ld ≤ Pd)
    (hCt : Real.log C0 ≤ t * (ld + Real.log (finrank ℚ K : ℝ)))
    (hn : Real.log (finrank ℚ K : ℝ) ≤ PO)
    (hr : Real.log |((discr K : ℤ) : ℝ)| / (finrank ℚ K : ℝ) ≤ PO) :
    Summable (fun la => c la * lw K la) ∧
      ∑' la, c la * lw K la ≤ ρ * ((2 * G + Prw + tableDegreeThreeBase + (t + 1 / 2) * (Pd + PO)) * ka) := by
  obtain ⟨hS, hb⟩ := log_sup_sum_le_of_nonvanishing_det_limit M z c hc0 hG hW Hm C0 hC0 hT sup hsup (tableDegreeThreeBase * ka) Pd hLAM hS2 a0 lrw mx S hE
    (G * L) (G * F0) ha0 hLW hL0
  have hnpos : 0 < (finrank ℚ K : ℝ) := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hfun : (fun la => c la * lw K la) = fun la => (c la * lnN la) / (finrank ℚ K : ℝ) := by
    funext la; unfold lw lnN; ring
  rw [hfun]
  refine ⟨hS.div_const _, ?_⟩
  rw [tsum_div_const, div_le_iff₀ hnpos]
  refine hb.trans ?_
  have hsz := deep_size t a0 (G * L) (G * F0) lrw G Prw tableDegreeThreeBase Pd PO L F0 ka ld (Real.log (finrank ℚ K : ℝ))
    (Real.log |((discr K : ℤ) : ℝ)| / (finrank ℚ K : ℝ)) ht ha0 hG0 hPrw hPd hPO hka hF0 le_rfl le_rfl hwt ha hrw hd hn hr
  have hρ : (0 : ℝ) ≤ (ρ : ℝ) := Nat.cast_nonneg _
  have hdisc : Real.log |((discr K : ℤ) : ℝ)| =
      (finrank ℚ K : ℝ) * (Real.log |((discr K : ℤ) : ℝ)| / (finrank ℚ K : ℝ)) := by field_simp
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hρ
  rw [hdisc, ← mul_add, mul_comm _ (finrank ℚ K : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ hnpos.le
  linarith

end Sum

def TrDualVec : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E),
    Submodule.span ℝ (L : Set E) = ⊤ → ∀ Λ : ℝ, 0 < Λ → (∀ x ∈ L, x ≠ 0 → Λ ≤ ‖x‖) →
    ∀ B : ℝ, (finrank ℝ E : ℝ) / Λ < B →
    ∃ y : Fin (finrank ℝ E) → E, LinearIndependent ℝ y ∧
      (∀ j, ∀ x ∈ L, ∃ z : ℤ, inner ℝ x (y j) = (z : ℝ)) ∧ ∀ j, ‖y j‖ ≤ B

def TrTraceDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] (ℓ : V →+ ℚ),
    ∃ cf : V →ₗ[K] K, ∀ f, Algebra.trace ℚ K (cf f) = ℓ f

def TrScale : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.span K (M : Set V) = ⊤ →
    ∀ f : V, ∃ m : ℤ, m ≠ 0 ∧ ((m : K) • f) ∈ M

/- English proof (translation)
Establish `: DiscreteTopology M` using `hd`. Establish `: IsZLattice ℝ M` using `⟨hs⟩`. Establish `hr : finrank ℤ M = N` using `by rw [ZLattice.rank ℝ M]; simp`. Establish `: Module.Free ℤ M` using `ZLattice.module_free ℝ M`. Establish `: Module.Finite ℤ M` using `ZLattice.module_finite ℝ M`.

Set `b : Basis (Fin N) ℤ M` to `Module.finBasisOfFinrankEq ℤ M hr`. Set `bR : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))` to `b.ofZLatticeBasis ℝ M`. Set `w : Fin N → EuclideanSpace ℝ (Fin N)` to `fun i => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm (LinearMap.toContinuousLinearMap (bR.coord i))`. Establish `hw : ∀ i x, inner ℝ (w i) x = bR.coord i x`. Introduce `i x`.

Simplify using `only [w, InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression. Use `⟨w, ?_, ?_⟩` and prove the remaining obligations. Introduce `j y hy`. Use `⟨b.repr ⟨y, hy⟩ j, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw]`. Conclude with `b.ofZLatticeBasis_repr_apply ℝ M ⟨y, hy⟩ j`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Establish `h1` using `congrArg (fun z => inner ℝ z (bR j)) hg`.

Simplify using `only [sum_inner, inner_smul_left, hw, inner_zero_left] at h1`. Simplify `h1` using `[Basis.coord_apply, Finsupp.single_apply]`.
-/
theorem tr_dual_nonempty {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (hd : DiscreteTopology M)
    (hs : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) :
    ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ PI.dualZ M) ∧ LinearIndependent ℝ v := by
  have : DiscreteTopology M := hd
  have : IsZLattice ℝ M := ⟨hs⟩
  have hr : finrank ℤ M = N := by rw [ZLattice.rank ℝ M]; simp
  have : Module.Free ℤ M := ZLattice.module_free ℝ M
  have : Module.Finite ℤ M := ZLattice.module_finite ℝ M
  let b : Basis (Fin N) ℤ M := Module.finBasisOfFinrankEq ℤ M hr
  let bR : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)) := b.ofZLatticeBasis ℝ M
  let w : Fin N → EuclideanSpace ℝ (Fin N) := fun i =>
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm (LinearMap.toContinuousLinearMap (bR.coord i))
  have hw : ∀ i x, inner ℝ (w i) x = bR.coord i x := by
    intro i x
    simp only [w, InnerProductSpace.toDual_symm_apply]
    rfl
  refine ⟨w, ?_, ?_⟩
  · intro j y hy
    refine ⟨b.repr ⟨y, hy⟩ j, ?_⟩
    rw [hw]
    exact b.ofZLatticeBasis_repr_apply ℝ M ⟨y, hy⟩ j
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (fun z => inner ℝ z (bR j)) hg
    simp only [sum_inner, inner_smul_left, hw, inner_zero_left] at h1
    simpa [Basis.coord_apply, Finsupp.single_apply] using h1

/- English proof (translation)
Establish `hd : DiscreteTopology M`. Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Rewrite using `[Metric.isOpen_singleton_iff]`. Use `⟨Λ, hΛ, fun y hy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `h1 : (y : EuclideanSpace ℝ (Fin N)) ≠ 0` using `fun h => hne (Subtype.ext h)`. Establish `h2` using `hL y y.2 h1`. Rewrite `hy` using `[dist_zero_right]`. Conclude with `absurd hy (not_lt.mpr h2)`. Establish `hmain` using `hT N M hd hs 1 le_rfl hN`.

Rewrite `hmain` using `[Nat.add_sub_cancel]`. Establish `hex : ∃ x ∈ M, x ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h0 : (M : Set (EuclideanSpace ℝ (Fin N))) ⊆ {0}` using `fun x hx => hcon x hx`.

Establish `h1 : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) ≤ ⊥`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Simplify using `using h0 hx`. Rewrite `h1` using `[hs]`.

Establish `h2 : finrank ℝ (EuclideanSpace ℝ (Fin N)) = 0`. Establish `: (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) = ⊥` using `le_bot_iff.mp h1`. Rewrite using `[← finrank_top, this, finrank_bot]`. Simplify using `at h2`. Use linear arithmetic over natural numbers and integers.

Establish `hlow : Λ ≤ PI.succMin M 1`. Unfold `PI.succMin`. Apply `le_csInf` to reduce the goal to its premises. Take `⟨x, hx, hx0⟩` from `hex`. Conclude with `⟨‖x‖, norm_nonneg _, fun _ => x, fun _ => hx, by`.

Rewrite using `[linearIndependent_unique_iff]`. Conclude with `hx0, fun _ => le_rfl⟩`. Introduce and unpack `t ⟨_, v, hv, hli, hvt⟩`. Conclude with `(hL _ (hv 0) (hli.ne_zero 0)).trans (hvt 0)`. Establish `hnn : 0 ≤ PI.succMin (PI.dualZ M) N`.

Unfold `PI.succMin`. Conclude with `Real.sInf_nonneg (fun t ht => ht.1)`. Establish `hle : PI.succMin (PI.dualZ M) N ≤ (N : ℝ) / Λ`. Rewrite using `[le_div_iff₀ hΛ]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hlt : PI.succMin (PI.dualZ M) N < B` using `lt_of_le_of_lt hle hB`. Take `⟨v0, hv0, hli0⟩` from `tr_dual_nonempty M hd hs`. Unfold `PI.succMin at hlt`. Establish `hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ PI.dualZ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty` using `⟨∑ j, ‖v0 j‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), v0, hv0, hli0, fun j => Finset.single_le_sum (f := fun j => ‖v0 j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)⟩`. Take `⟨t, ⟨_, v, hv, hli, hvt⟩, htB⟩` from `exists_lt_of_csInf_lt hne hlt`.

Conclude with `⟨v, hv, hli, fun j => (hvt j).trans htB.le⟩`.
-/
theorem tr_dualVec_std (hT : PI.TransferenceMinima) {N : ℕ} (hN : 1 ≤ N)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    (hs : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) (Λ : ℝ) (hΛ : 0 < Λ)
    (hL : ∀ x ∈ M, x ≠ 0 → Λ ≤ ‖x‖) (B : ℝ) (hB : (N : ℝ) / Λ < B) :
    ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ PI.dualZ M) ∧ LinearIndependent ℝ v ∧
      ∀ j, ‖v j‖ ≤ B := by
  have hd : DiscreteTopology M := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [Metric.isOpen_singleton_iff]
    refine ⟨Λ, hΛ, fun y hy => ?_⟩
    by_contra hne
    have h1 : (y : EuclideanSpace ℝ (Fin N)) ≠ 0 := fun h => hne (Subtype.ext h)
    have h2 := hL y y.2 h1
    rw [dist_zero_right] at hy
    exact absurd hy (not_lt.mpr h2)
  have hmain := hT N M hd hs 1 le_rfl hN
  rw [Nat.add_sub_cancel] at hmain

  have hex : ∃ x ∈ M, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : (M : Set (EuclideanSpace ℝ (Fin N))) ⊆ {0} := fun x hx => hcon x hx
    have h1 : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) ≤ ⊥ := by
      rw [Submodule.span_le]; intro x hx; simpa using h0 hx
    rw [hs] at h1
    have h2 : finrank ℝ (EuclideanSpace ℝ (Fin N)) = 0 := by
      have : (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) = ⊥ := le_bot_iff.mp h1
      rw [← finrank_top, this, finrank_bot]
    simp at h2
    omega
  have hlow : Λ ≤ PI.succMin M 1 := by
    unfold PI.succMin
    apply le_csInf
    · obtain ⟨x, hx, hx0⟩ := hex
      exact ⟨‖x‖, norm_nonneg _, fun _ => x, fun _ => hx, by
        rw [linearIndependent_unique_iff]; exact hx0, fun _ => le_rfl⟩
    · rintro t ⟨_, v, hv, hli, hvt⟩
      exact (hL _ (hv 0) (hli.ne_zero 0)).trans (hvt 0)
  have hnn : 0 ≤ PI.succMin (PI.dualZ M) N := by
    unfold PI.succMin
    exact Real.sInf_nonneg (fun t ht => ht.1)
  have hle : PI.succMin (PI.dualZ M) N ≤ (N : ℝ) / Λ := by
    rw [le_div_iff₀ hΛ]
    calc PI.succMin (PI.dualZ M) N * Λ ≤ PI.succMin (PI.dualZ M) N * PI.succMin M 1 :=
          mul_le_mul_of_nonneg_left hlow hnn
      _ = PI.succMin M 1 * PI.succMin (PI.dualZ M) N := mul_comm _ _
      _ ≤ N := hmain
  have hlt : PI.succMin (PI.dualZ M) N < B := lt_of_le_of_lt hle hB
  obtain ⟨v0, hv0, hli0⟩ := tr_dual_nonempty M hd hs
  unfold PI.succMin at hlt
  have hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ PI.dualZ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty :=
    ⟨∑ j, ‖v0 j‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), v0, hv0, hli0, fun j =>
      Finset.single_le_sum (f := fun j => ‖v0 j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)⟩
  obtain ⟨t, ⟨_, v, hv, hli, hvt⟩, htB⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨v, hv, hli, fun j => (hvt j).trans htB.le⟩

/- English proof (translation)
Introduce `E _ _ _ L hspan Λ hΛ hL B hB`. Break down `Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos` into its components or cases. Establish `hemp : IsEmpty (Fin (finrank ℝ E))` using `by rw [h0]; infer_instance`. Conclude with `⟨fun j => isEmptyElim j, linearIndependent_empty_type, fun j => isEmptyElim j, fun j => isEmptyElim j⟩`. Set `u : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))` to `(stdOrthonormalBasis ℝ E).repr`.

Set `M' : Submodule ℤ (EuclideanSpace ℝ (Fin (finrank ℝ E)))` to `L.map (u.toLinearEquiv.toLinearMap.restrictScalars ℤ)`. Establish `hmem : ∀ x, x ∈ M' ↔ ∃ l ∈ L, u l = x`. Introduce `x`. Simplify using `only [M', Submodule.mem_map]`. Both sides reduce to the same expression.

Establish `hs : Submodule.span ℝ (M' : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) = ⊤`. Establish `h1 : (M' : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) = u.toLinearEquiv.toLinearMap '' (L : Set E)`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, hmem, Set.mem_image]`. Both sides reduce to the same expression.

Rewrite using `[h1, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `u.surjective`. Take `⟨v, hv, hli, hvB⟩` from `tr_dualVec_std hT hpos M' hs Λ hΛ (by`. Introduce `x hx hx0`. Take `⟨l, hl, rfl⟩` from `(hmem x).1 hx`.

Rewrite using `[u.norm_map]`. Conclude with `hL l hl (fun h => hx0 (by rw [h, map_zero]))) B hB`. Use `⟨fun j => u.symm (v j), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hli.map' u.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)`. Introduce `j x hx`.

Take `⟨z, hz⟩` from `hv j (u x) ((hmem _).2 ⟨x, hx, rfl⟩)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, real_inner_comm, ← u.inner_map_map, u.apply_symm_apply]`. Introduce `j`. Rewrite using `[u.symm.norm_map]`.

Conclude with `hvB j`.
-/
theorem tr_dualVec (hT : PI.TransferenceMinima) : TrDualVec := by
  intro E _ _ _ L hspan Λ hΛ hL B hB
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · have hemp : IsEmpty (Fin (finrank ℝ E)) := by rw [h0]; infer_instance
    exact ⟨fun j => isEmptyElim j, linearIndependent_empty_type, fun j => isEmptyElim j,
      fun j => isEmptyElim j⟩
  · let u : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) := (stdOrthonormalBasis ℝ E).repr
    let M' : Submodule ℤ (EuclideanSpace ℝ (Fin (finrank ℝ E))) :=
      L.map (u.toLinearEquiv.toLinearMap.restrictScalars ℤ)
    have hmem : ∀ x, x ∈ M' ↔ ∃ l ∈ L, u l = x := by
      intro x; simp only [M', Submodule.mem_map]; rfl
    have hs : Submodule.span ℝ (M' : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) = ⊤ := by
      have h1 : (M' : Set (EuclideanSpace ℝ (Fin (finrank ℝ E)))) = u.toLinearEquiv.toLinearMap '' (L : Set E) := by
        ext x; simp only [SetLike.mem_coe, hmem, Set.mem_image]; rfl
      rw [h1, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
      exact u.surjective
    obtain ⟨v, hv, hli, hvB⟩ := tr_dualVec_std hT hpos M' hs Λ hΛ (by
      intro x hx hx0
      obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
      rw [u.norm_map]
      exact hL l hl (fun h => hx0 (by rw [h, map_zero]))) B hB
    refine ⟨fun j => u.symm (v j), ?_, ?_, ?_⟩
    · exact hli.map' u.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)
    · intro j x hx
      obtain ⟨z, hz⟩ := hv j (u x) ((hmem _).2 ⟨x, hx, rfl⟩)
      refine ⟨z, ?_⟩
      rw [← hz, real_inner_comm, ← u.inner_map_map, u.apply_symm_apply]
    · intro j
      rw [u.symm.norm_map]
      exact hvB j

/- English proof (translation)
Establish `hB` using `traceForm_nondegenerate ℚ K`. Use `⟨((Algebra.traceForm ℚ K).toDual hB).symm g.toRatLinearMap, fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) g.toRatLinearMap a`. Rewrite `h` using `[Algebra.traceForm_apply]`. Rewrite using `[mul_comm]`.

Simplify using `using h`.
-/
theorem tr_exists_c (K : Type) [Field K] [NumberField K] (g : K →+ ℚ) :
    ∃ c : K, ∀ a, Algebra.trace ℚ K (a * c) = g a := by
  have hB := traceForm_nondegenerate ℚ K
  refine ⟨((Algebra.traceForm ℚ K).toDual hB).symm g.toRatLinearMap, fun a => ?_⟩
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) g.toRatLinearMap a
  rw [Algebra.traceForm_apply] at h
  rw [mul_comm]
  simpa using h

/- English proof (translation)
Establish `hB` using `traceForm_nondegenerate ℚ K`. Apply `((Algebra.traceForm ℚ K).toDual hB).injective` to reduce the goal to its premises. Use extensionality with `a`. Rewrite using `[LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm c, mul_comm c']`. Conclude with `h a`.
-/
theorem tr_c_unique {K : Type} [Field K] [NumberField K] {c c' : K}
    (h : ∀ a, Algebra.trace ℚ K (a * c) = Algebra.trace ℚ K (a * c')) : c = c' := by
  have hB := traceForm_nondegenerate ℚ K
  apply ((Algebra.traceForm ℚ K).toDual hB).injective
  ext a
  rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
    Algebra.traceForm_apply, mul_comm c, mul_comm c']
  exact h a

/- English proof (translation)
Establish `hex : ∀ f : V, ∃ c : K, ∀ a, Algebra.trace ℚ K (a * c) = ℓ (a • f)` using `fun f => tr_exists_c K (ℓ.comp ((smulAddHom K V).flip f))`. Use `choose c hc using hex`. Use `⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, fun a f => hc f a⟩` and prove the remaining obligations. Introduce `f g`. Apply `tr_c_unique` to reduce the goal to its premises.

Introduce `a`. Rewrite using `[hc, mul_add, map_add, hc, hc, smul_add, map_add]`. Introduce `b f`. Apply `tr_c_unique` to reduce the goal to its premises. Introduce `a`.

Rewrite using `[hc, RingHom.id_apply, smul_eq_mul, ← mul_assoc, hc, smul_smul]`.
-/
theorem tr_traceDual' (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    (ℓ : V →+ ℚ) : ∃ cf : V →ₗ[K] K, ∀ (a : K) f, Algebra.trace ℚ K (a * cf f) = ℓ (a • f) := by
  have hex : ∀ f : V, ∃ c : K, ∀ a, Algebra.trace ℚ K (a * c) = ℓ (a • f) := fun f =>
    tr_exists_c K (ℓ.comp ((smulAddHom K V).flip f))
  choose c hc using hex
  refine ⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, fun a f => hc f a⟩
  · intro f g
    apply tr_c_unique
    intro a
    rw [hc, mul_add, map_add, hc, hc, smul_add, map_add]
  · intro b f
    apply tr_c_unique
    intro a
    rw [hc, RingHom.id_apply, smul_eq_mul, ← mul_assoc, hc, smul_smul]

/- English proof (translation)
Introduce `K _ _ V _ _ ℓ`. Take `⟨cf, h⟩` from `tr_traceDual' K V ℓ`. Conclude with `⟨cf, fun f => by simpa using h 1 f⟩`.
-/
theorem tr_traceDual : TrTraceDual := by
  intro K _ _ V _ _ ℓ
  obtain ⟨cf, h⟩ := tr_traceDual' K V ℓ
  exact ⟨cf, fun f => by simpa using h 1 f⟩

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale .. | (apply UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale <;> assumption) | (intros; apply UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale <;> assumption) | (apply @UpperTheory. …`.
-/
theorem tr_scale : TrScale := by
  first | exact UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale .. | (apply UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale <;> assumption) | (intros; apply UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale <;> assumption) | (apply @UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale <;> assumption) | (apply @UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale <;> first | assumption | infer_instance)

section TrA

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ}

def Herm.Conj (Hm : Herm N2 dH) : Prop :=
  ∀ (σ : K →+* ℂ) (f g : V),
    inner ℂ (Hm.e (ComplexEmbedding.conjugate σ) f) (Hm.e (ComplexEmbedding.conjugate σ) g) =
      star (inner ℂ (Hm.e σ f) (Hm.e σ g))

abbrev TrW (K : Type) [Field K] [NumberField K] (dH : ℕ) : Type := EuclideanSpace ℂ ((K →+* ℂ) × Fin dH)

def tr_iota (Hm : Herm N2 dH) : V →+ TrW K dH where
  toFun f := WithLp.toLp 2 (fun p => Hm.e p.1 f p.2)
  map_zero' := by ext p; simp
  map_add' f g := by ext p; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tr_iota_apply (Hm : Herm N2 dH) (f : V) (p : (K →+* ℂ) × Fin dH) :
    tr_iota Hm f p = Hm.e p.1 f p.2 := rfl

def tr_comp (y : TrW K dH) (σ : K →+* ℂ) : EuclideanSpace ℂ (Fin dH) := WithLp.toLp 2 (fun i => y (σ, i))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tr_comp_apply (y : TrW K dH) (σ : K →+* ℂ) (i : Fin dH) : tr_comp y σ i = y (σ, i) := rfl

/- English proof (translation)
Use extensionality with `i`. Both sides reduce to the same expression.
-/
theorem tr_comp_iota (Hm : Herm N2 dH) (f : V) (σ : K →+* ℂ) : tr_comp (tr_iota Hm f) σ = Hm.e σ f := by
  ext i; rfl

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[EuclideanSpace.norm_sq_eq]`. Both sides reduce to the same expression.
-/
theorem tr_norm_sq (y : TrW K dH) : ‖y‖ ^ 2 = ∑ σ : K →+* ℂ, ‖tr_comp y σ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/- English proof (translation)
Rewrite using `[tr_norm_sq]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[tr_comp_iota, Hm.norm_e]`.
-/
theorem tr_norm_iota_sq (Hm : Herm N2 dH) (f : V) : ‖tr_iota Hm f‖ ^ 2 = ∑ σ : K →+* ℂ, N2 σ f ^ 2 := by
  rw [tr_norm_sq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [tr_comp_iota, Hm.norm_e]

/- English proof (translation)
Establish `h : ‖tr_comp y σ‖ ^ 2 ≤ ‖y‖ ^ 2`. Rewrite using `[tr_norm_sq y]`. Conclude with `Finset.single_le_sum (f := fun τ => ‖tr_comp y τ‖ ^ 2) (fun τ _ => by positivity) (Finset.mem_univ σ)`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h`.
-/
theorem tr_norm_comp_le (y : TrW K dH) (σ : K →+* ℂ) : ‖tr_comp y σ‖ ≤ ‖y‖ := by
  have h : ‖tr_comp y σ‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [tr_norm_sq y]
    exact Finset.single_le_sum (f := fun τ => ‖tr_comp y τ‖ ^ 2) (fun τ _ => by positivity) (Finset.mem_univ σ)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

def tr_psi (Hm : Herm N2 dH) (y : TrW K dH) (σ : K →+* ℂ) (f : V) : ℂ := inner ℂ (tr_comp y σ) (Hm.e σ f)

/- English proof (translation)
Rewrite using `[real_inner_comm, PiLp.inner_apply, Fintype.sum_prod_type, Complex.re_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[tr_psi, PiLp.inner_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tr_iota_apply, tr_comp_apply]`.

Simplify using `[Complex.inner, RCLike.inner_apply, mul_comm]`.
-/
theorem tr_inner_eq (Hm : Herm N2 dH) (y : TrW K dH) (f : V) :
    inner ℝ (tr_iota Hm f) y = (∑ σ : K →+* ℂ, tr_psi Hm y σ f).re := by
  rw [real_inner_comm, PiLp.inner_apply, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [tr_psi, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tr_iota_apply, tr_comp_apply]
  simp [Complex.inner, RCLike.inner_apply, mul_comm]

/- English proof (translation)
Rewrite using `[tr_psi, tr_psi, (Hm.e σ).map_smulₛₗ, inner_smul_right]`.
-/
theorem tr_psi_smul (Hm : Herm N2 dH) (y : TrW K dH) (σ : K →+* ℂ) (a : K) (f : V) :
    tr_psi Hm y σ (a • f) = σ a * tr_psi Hm y σ f := by
  rw [tr_psi, tr_psi, (Hm.e σ).map_smulₛₗ, inner_smul_right]

/- English proof (translation)
Use extensionality with `p`. Rewrite using `[tr_iota_apply, (Hm.e p.1).map_smulₛₗ]`. Simplify using `[tr_iota_apply]`.
-/
theorem tr_iota_smul_rat (Hm : Herm N2 dH) (q : ℚ) (f : V) :
    tr_iota Hm ((q : K) • f) = (q : ℝ) • tr_iota Hm f := by
  ext p
  rw [tr_iota_apply, (Hm.e p.1).map_smulₛₗ]
  simp [tr_iota_apply]

end TrA

section TrB

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ}

/- English proof (translation)
Use extensionality with `i`. Simplify using `[tr_comp_apply]`.
-/
theorem tr_comp_zero (σ : K →+* ℂ) : tr_comp (0 : TrW K dH) σ = 0 := by
  ext i; simp [tr_comp_apply]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[tr_comp_apply]`.
-/
theorem tr_comp_add (x y : TrW K dH) (σ : K →+* ℂ) : tr_comp (x + y) σ = tr_comp x σ + tr_comp y σ := by
  ext i; simp [tr_comp_apply]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[tr_comp_apply]`.
-/
theorem tr_comp_smul (r : ℝ) (x : TrW K dH) (σ : K →+* ℂ) : tr_comp (r • x) σ = (r : ℂ) • tr_comp x σ := by
  ext i; simp [tr_comp_apply]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, _, rfl⟩` from `hx`. Simplify using `only [tr_psi, tr_comp_iota]`. Conclude with `hc σ g f`.

Consider the case `zero => simp [tr_psi, tr_comp_zero]`. Consider the case `add x y _ _ hx hy`. Simplify using `only [tr_psi, tr_comp_add, inner_add_left, star_add] at hx hy ⊢`. Rewrite using `[hx, hy]`. Consider the case `smul r x _ hx`.

Simplify using `only [tr_psi, tr_comp_smul, inner_smul_left, star_mul'] at hx ⊢`. Rewrite using `[hx]`. Simplify using the standard rewrite rules.
-/
theorem tr_psi_conj (Hm : Herm N2 dH) (hc : Hm.Conj) (S : Set V) {y : TrW K dH}
    (hy : y ∈ Submodule.span ℝ (tr_iota Hm '' S)) (σ : K →+* ℂ) (f : V) :
    tr_psi Hm y (ComplexEmbedding.conjugate σ) f = star (tr_psi Hm y σ f) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, _, rfl⟩ := hx
    simp only [tr_psi, tr_comp_iota]
    exact hc σ g f
  | zero => simp [tr_psi, tr_comp_zero]
  | add x y _ _ hx hy =>
    simp only [tr_psi, tr_comp_add, inner_add_left, star_add] at hx hy ⊢
    rw [hx, hy]
  | smul r x _ hx =>
    simp only [tr_psi, tr_comp_smul, inner_smul_left, star_mul'] at hx ⊢
    rw [hx]
    simp

/- English proof (translation)
Establish `h : star (∑ σ : K →+* ℂ, tr_psi Hm y σ f) = ∑ σ : K →+* ℂ, tr_psi Hm y σ f`. Rewrite using `[star_sum]`. Rewrite using `[← Equiv.sum_comp (ComplexEmbedding.involutive_conjugate K).toPerm (fun σ => tr_psi Hm y σ f)]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Conclude with `(tr_psi_conj Hm hc S hy σ f).symm`.

Conclude with `(Complex.conj_eq_iff_real.1 h).elim fun r hr => by rw [hr]; simp`.
-/
theorem tr_sum_psi_real (Hm : Herm N2 dH) (hc : Hm.Conj) (S : Set V) {y : TrW K dH}
    (hy : y ∈ Submodule.span ℝ (tr_iota Hm '' S)) (f : V) :
    (((∑ σ : K →+* ℂ, tr_psi Hm y σ f).re : ℝ) : ℂ) = ∑ σ : K →+* ℂ, tr_psi Hm y σ f := by
  have h : star (∑ σ : K →+* ℂ, tr_psi Hm y σ f) = ∑ σ : K →+* ℂ, tr_psi Hm y σ f := by
    rw [star_sum]
    rw [← Equiv.sum_comp (ComplexEmbedding.involutive_conjugate K).toPerm (fun σ => tr_psi Hm y σ f)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact (tr_psi_conj Hm hc S hy σ f).symm
  exact (Complex.conj_eq_iff_real.1 h).elim fun r hr => by rw [hr]; simp

/- English proof (translation)
Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := x)`. Rewrite `h` using `[eq_ratCast]`. Rewrite using `[h]`. Conclude with `(Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x) (fun _ => by simp [RingHom.equivRatAlgHom_apply])).symm`.
-/
theorem tr_trace_eq_sum (x : K) : ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])).symm

/- English proof (translation)
The claim follows from `(linearIndependent_monoidHom K ℂ).comp (fun τ : K →+* ℂ => (τ : K →* ℂ)) (fun a b h => by ext x; exact DFunLike.congr_fun h x)`.
-/
theorem tr_embeddings_li : LinearIndependent ℂ (fun τ : K →+* ℂ => (τ : K → ℂ)) :=
  (linearIndependent_monoidHom K ℂ).comp (fun τ : K →+* ℂ => (τ : K →* ℂ))
    (fun a b h => by ext x; exact DFunLike.congr_fun h x)

/- English proof (translation)
Establish `key : ∀ a : K, ∑ τ : K →+* ℂ, (τ (cf f) - tr_psi Hm y τ f) * τ a = 0`. Introduce `a`. Establish `e1 : ∑ τ : K →+* ℂ, τ (cf f) * τ a = ∑ τ : K →+* ℂ, tr_psi Hm y τ f * τ a`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, map_mul, mul_comm]`. Use `_ = ((Algebra.trace ℚ K (cf (a • f)) : ℚ) : ℂ) := (tr_trace_eq_sum _).symm`. Use `_ = (((Algebra.trace ℚ K (cf (a • f)) : ℚ) : ℝ) : ℂ) := by push_cast; rfl`. Use `_ = ∑ τ : K →+* ℂ, tr_psi Hm y τ (a • f) := by rw [hcf, tr_inner_eq, hreal]`. Use `_ = ∑ τ : K →+* ℂ, tr_psi Hm y τ f * τ a := by`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[tr_psi_smul, mul_comm]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib, e1, sub_self]`. Establish `h` using `Fintype.linearIndependent_iff.1 (tr_embeddings_li (K := K)) (fun τ => τ (cf f) - tr_psi Hm y τ f) (by`. Use function extensionality and compare the values at `a`.

Simplify `key a) σ` using `[Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem tr_opLe_key (Hm : Herm N2 dH) (y : TrW K dH)
    (hreal : ∀ g, (((∑ σ : K →+* ℂ, tr_psi Hm y σ g).re : ℝ) : ℂ) = ∑ σ : K →+* ℂ, tr_psi Hm y σ g)
    (cf : V →ₗ[K] K) (hcf : ∀ g, ((Algebra.trace ℚ K (cf g) : ℚ) : ℝ) = inner ℝ (tr_iota Hm g) y)
    (σ : K →+* ℂ) (f : V) : σ (cf f) = tr_psi Hm y σ f := by
  have key : ∀ a : K, ∑ τ : K →+* ℂ, (τ (cf f) - tr_psi Hm y τ f) * τ a = 0 := by
    intro a
    have e1 : ∑ τ : K →+* ℂ, τ (cf f) * τ a = ∑ τ : K →+* ℂ, tr_psi Hm y τ f * τ a := by
      calc ∑ τ : K →+* ℂ, τ (cf f) * τ a = ∑ τ : K →+* ℂ, τ (cf (a • f)) := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            rw [map_smul, smul_eq_mul, map_mul, mul_comm]
        _ = ((Algebra.trace ℚ K (cf (a • f)) : ℚ) : ℂ) := (tr_trace_eq_sum _).symm
        _ = (((Algebra.trace ℚ K (cf (a • f)) : ℚ) : ℝ) : ℂ) := by push_cast; rfl
        _ = ∑ τ : K →+* ℂ, tr_psi Hm y τ (a • f) := by rw [hcf, tr_inner_eq, hreal]
        _ = ∑ τ : K →+* ℂ, tr_psi Hm y τ f * τ a := by
            refine Finset.sum_congr rfl fun τ _ => ?_
            rw [tr_psi_smul, mul_comm]
    simp only [sub_mul, Finset.sum_sub_distrib, e1, sub_self]
  have h := Fintype.linearIndependent_iff.1 (tr_embeddings_li (K := K))
    (fun τ => τ (cf f) - tr_psi Hm y τ f) (by
      funext a
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using key a) σ
  exact sub_eq_zero.1 h

/- English proof (translation)
Use `set b := Module.finBasis K V`. Use `set ω := Module.finBasis ℚ K`. Rewrite using `[← b.sum_repr f, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `hcc : b.repr f j = ∑ i, ((ω.repr (b.repr f j) i : ℚ) : K) * ω i` using `by conv_lhs => rw [← ω.sum_repr (b.repr f j)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, eq_ratCast]`. Rewrite using `[hcc, Finset.sum_smul, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul, tr_iota_smul_rat]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, i), rfl⟩)`.
-/
theorem tr_iota_mem_span [FiniteDimensional K V] (Hm : Herm N2 dH) (f : V) :
    tr_iota Hm f ∈ Submodule.span ℝ (Set.range fun p : Fin (finrank K V) × Fin (finrank ℚ K) =>
      tr_iota Hm ((Module.finBasis ℚ K p.2) • (Module.finBasis K V p.1))) := by
  set b := Module.finBasis K V
  set ω := Module.finBasis ℚ K
  rw [← b.sum_repr f, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hcc : b.repr f j = ∑ i, ((ω.repr (b.repr f j) i : ℚ) : K) * ω i := by
    conv_lhs => rw [← ω.sum_repr (b.repr f j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, eq_ratCast]
  rw [hcc, Finset.sum_smul, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mul_smul, tr_iota_smul_rat]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, i), rfl⟩)

end TrB

section TrC

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ}
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Establish `h` using `tr_iota_smul_rat Hm (m : ℚ) f`. Move the coercions through the operations in `at h`. Conclude with `h`.
-/
theorem tr_iota_smul_int (Hm : Herm N2 dH) (m : ℤ) (f : V) :
    tr_iota Hm ((m : K) • f) = (m : ℝ) • tr_iota Hm f := by
  have h := tr_iota_smul_rat Hm (m : ℚ) f
  push_cast at h
  exact h

/- English proof (translation)
Introduce `Λ hΛ hlow`. Set `E : Submodule ℝ (TrW K dH)` to `Submodule.span ℝ (tr_iota Hm '' (M : Set V))`. Set `L : Submodule ℤ E` to `AddSubgroup.toIntSubmodule ((M.toAddSubgroup.map (tr_iota Hm)).comap E.subtype.toAddMonoidHom)`. Establish `hLmem : ∀ x : E, x ∈ L ↔ ∃ f ∈ M, tr_iota Hm f = (x : TrW K dH)`. Introduce `x`.

Conclude with `Iff.rfl`. Establish `hLset : (L : Set E) = ((↑) : E → TrW K dH) ⁻¹' (tr_iota Hm '' (M : Set V))`. Use extensionality with `x`. Conclude with `hLmem x`. Establish `hspanL : Submodule.span ℝ (L : Set E) = ⊤`.

Rewrite using `[hLset]`. Conclude with `Submodule.span_span_coe_preimage`. Establish `hlowL : ∀ x ∈ L, x ≠ 0 → Λ ≤ ‖x‖`. Introduce `x hx hx0`. Take `⟨f, hf, hfx⟩` from `(hLmem x).1 hx`.

Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`. Apply `hx0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hfx, map_zero]`.

Both sides reduce to the same expression. Establish `h` using `hlow f hf hf0`. Rewrite `h` using `[← tr_norm_iota_sq Hm f, hfx]`. Conclude with `(pow_le_pow_iff_left₀ hΛ.le (norm_nonneg _) two_ne_zero).1 h`. Establish `hfr : finrank ℝ E ≤ finrank K V * finrank ℚ K`.

Establish `hle : E ≤ Submodule.span ℝ (Set.range fun p : Fin (finrank K V) × Fin (finrank ℚ K) => tr_iota Hm ((Module.finBasis ℚ K p.2) • (Module.finBasis K V p.1)))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, _, rfl⟩`. Conclude with `tr_iota_mem_span Hm f`. Use `(Submodule.finrank_mono hle).trans ?_` and prove the remaining obligations.

Use `(finrank_range_le_card _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hB : (finrank ℝ E : ℝ) / Λ < Ctr / Λ`. Use `div_lt_div_of_pos_right ?_ hΛ` and prove the remaining obligations. Use `lt_of_le_of_lt ?_ hC` and prove the remaining obligations.

Conclude with `hfr` after adjusting the coercions. Take `⟨y, hyli, hyint, hynorm⟩` from `h1 E L hspanL Λ hΛ hlowL (Ctr / Λ) hB`. Establish `hint : ∀ j, ∀ f ∈ M, ∃ z : ℤ, inner ℝ (tr_iota Hm f) (y j : TrW K dH) = (z : ℝ)`. Introduce `j f hf`. Conclude with `hyint j ⟨tr_iota Hm f, Submodule.subset_span ⟨f, hf, rfl⟩⟩ ((hLmem _).2 ⟨f, hf, rfl⟩)`.

Establish `hrat : ∀ j (f : V), ∃ q : ℚ, (q : ℝ) = inner ℝ (tr_iota Hm f) (y j : TrW K dH)`. Introduce `j f`. Take `⟨m, hm0, hmM⟩` from `h3 K V M hM f`. Take `⟨z, hz⟩` from `hint j _ hmM`. Rewrite `hz` using `[tr_iota_smul_int, real_inner_smul_left]`.

Establish `hm0' : (m : ℝ) ≠ 0` using `by exact_mod_cast hm0`. Use `⟨(z : ℚ) / m, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← hz]`. Clear the denominators using the available nonvanishing facts.

Use `choose lf hlf using hrat`. Set `ℓ : Fin (finrank ℝ E) → V →+ ℚ` to `fun j => { toFun := lf j map_zero' := by`. Establish `: ((lf j 0 : ℚ) : ℝ) = ((0 : ℚ) : ℝ)` using `by rw [hlf, map_zero, inner_zero_left]; simp`. Conclude with `this` after adjusting the coercions. Use the proof step `map_add' := fun f g => by`.

Establish `: ((lf j (f + g) : ℚ) : ℝ) = ((lf j f + lf j g : ℚ) : ℝ)`. Use `push_cast`. Rewrite using `[hlf, hlf, hlf, map_add, inner_add_left]`. Conclude with `this }` after adjusting the coercions. Use `choose cf hcf using fun j => h2 K V (ℓ j)`.

Establish `hcf' : ∀ j g, ((Algebra.trace ℚ K (cf j g) : ℚ) : ℝ) = inner ℝ (tr_iota Hm g) (y j : TrW K dH)`. Introduce `j g`. Rewrite using `[hcf j g]`. Conclude with `hlf j g`. Establish `hiotaE : ∀ f : V, tr_iota Hm f ∈ E`.

Introduce `f`. Take `⟨m, hm0, hmM⟩` from `h3 K V M hM f`. Establish `hm0' : (m : ℝ) ≠ 0` using `by exact_mod_cast hm0`. Establish `h : tr_iota Hm ((m : K) • f) ∈ E` using `Submodule.subset_span ⟨_, hmM, rfl⟩`. Rewrite `h` using `[tr_iota_smul_int]`.

Establish `h'` using `E.smul_mem (m : ℝ)⁻¹ h`. Rewrite `h'` using `[smul_smul, inv_mul_cancel₀ hm0', one_smul]`. Then use the resulting hypothesis. Use `⟨finrank ℝ E, cf, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hco : (Submodule.span K (Set.range cf)).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `f hf`. Rewrite `hf` using `[Submodule.mem_dualCoannihilator]`. Establish `hz : ∀ j, inner ℝ (tr_iota Hm f) (y j : TrW K dH) = 0`. Introduce `j`. Rewrite using `[← hcf' j f, hf (cf j) (Submodule.subset_span ⟨j, rfl⟩)]`.

Simplify using the standard rewrite rules. Establish `htop : Submodule.span ℝ (Set.range y) = ⊤` using `hyli.span_eq_top_of_card_eq_finrank' (by simp)`. Establish `hzero : (⟨tr_iota Hm f, hiotaE f⟩ : E) = 0`. Establish `hall : ∀ x : E, inner ℝ (⟨tr_iota Hm f, hiotaE f⟩ : E) x = 0`. Introduce `x`.

Establish `hx : x ∈ Submodule.span ℝ (Set.range y)` using `htop ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `hz j`. Consider the case `zero => exact inner_zero_right _`.

Consider the case `add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]`. Consider the case `smul r a _ ha => rw [inner_smul_right, ha, mul_zero]`. Conclude with `inner_self_eq_zero.1 (hall _)`. Establish `hi0 : tr_iota Hm f = 0` using `congrArg Subtype.val hzero`. Assume the negation of the conclusion as `hf0`.

Establish `hf0' : f ≠ 0` using `hf0`. Take `⟨m, hm0, hmM⟩` from `h3 K V M hM f`. Establish `hmK : (m : K) ≠ 0` using `by exact_mod_cast hm0`. Establish `hne : (m : K) • f ≠ 0` using `smul_ne_zero hmK hf0'`. Establish `h` using `hlow _ hmM hne`.

Rewrite `h` using `[← tr_norm_iota_sq Hm, tr_iota_smul_int, hi0, smul_zero, norm_zero]`. Use polynomial arithmetic with `[pow_pos hΛ 2]`. Establish `h` using `Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K (Set.range cf))`. Rewrite `h` using `[hco, Submodule.dualAnnihilator_bot]`. Conclude with `h.symm`.

Introduce `j f hf a`. Establish `haf : (a : K) • f ∈ M`. Rewrite using `[algebraMap_smul]`. Conclude with `M.smul_mem a hf`. Take `⟨z, hz⟩` from `hint j _ haf`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `: ((Algebra.trace ℚ K ((a : K) * cf j f) : ℚ) : ℝ) = ((z : ℚ) : ℝ)`. Rewrite using `[← smul_eq_mul, ← map_smul, hcf', hz]`. Simplify using the standard rewrite rules. Conclude with `this` after adjusting the coercions.

Introduce `σ j`. Use `⟨tr_comp (y j : TrW K dH) σ, (tr_norm_comp_le _ _).trans (hynorm j), fun f => ?_⟩` and prove the remaining obligations. Conclude with `tr_opLe_key Hm (y j : TrW K dH) (fun g => tr_sum_psi_real Hm hc (M : Set V) (y j).2 g) (cf j) (hcf' j) σ f`.
-/
theorem trans_of_stages (h1 : TrDualVec) (h2 : TrTraceDual) (h3 : TrScale) [FiniteDimensional K V]
    (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (Hm : Herm N2 dH) (hc : Hm.Conj)
    (Ctr : ℝ) (hC : ((finrank K V * finrank ℚ K : ℕ) : ℝ) < Ctr) : Trans M Hm Ctr := by
  intro Λ hΛ hlow
  classical
  let E : Submodule ℝ (TrW K dH) := Submodule.span ℝ (tr_iota Hm '' (M : Set V))
  let L : Submodule ℤ E :=
    AddSubgroup.toIntSubmodule ((M.toAddSubgroup.map (tr_iota Hm)).comap E.subtype.toAddMonoidHom)
  have hLmem : ∀ x : E, x ∈ L ↔ ∃ f ∈ M, tr_iota Hm f = (x : TrW K dH) := by
    intro x
    exact Iff.rfl
  have hLset : (L : Set E) = ((↑) : E → TrW K dH) ⁻¹' (tr_iota Hm '' (M : Set V)) := by
    ext x
    exact hLmem x
  have hspanL : Submodule.span ℝ (L : Set E) = ⊤ := by
    rw [hLset]
    exact Submodule.span_span_coe_preimage
  have hlowL : ∀ x ∈ L, x ≠ 0 → Λ ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨f, hf, hfx⟩ := (hLmem x).1 hx
    have hf0 : f ≠ 0 := by
      rintro rfl
      apply hx0
      apply Subtype.ext
      rw [← hfx, map_zero]
      rfl
    have h := hlow f hf hf0
    rw [← tr_norm_iota_sq Hm f, hfx] at h
    exact (pow_le_pow_iff_left₀ hΛ.le (norm_nonneg _) two_ne_zero).1 h
  have hfr : finrank ℝ E ≤ finrank K V * finrank ℚ K := by
    have hle : E ≤ Submodule.span ℝ (Set.range fun p : Fin (finrank K V) × Fin (finrank ℚ K) =>
        tr_iota Hm ((Module.finBasis ℚ K p.2) • (Module.finBasis K V p.1))) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, _, rfl⟩
      exact tr_iota_mem_span Hm f
    refine (Submodule.finrank_mono hle).trans ?_
    refine (finrank_range_le_card _).trans ?_
    simp
  have hB : (finrank ℝ E : ℝ) / Λ < Ctr / Λ := by
    refine div_lt_div_of_pos_right ?_ hΛ
    refine lt_of_le_of_lt ?_ hC
    exact_mod_cast hfr
  obtain ⟨y, hyli, hyint, hynorm⟩ := h1 E L hspanL Λ hΛ hlowL (Ctr / Λ) hB

  have hint : ∀ j, ∀ f ∈ M, ∃ z : ℤ, inner ℝ (tr_iota Hm f) (y j : TrW K dH) = (z : ℝ) := by
    intro j f hf
    exact hyint j ⟨tr_iota Hm f, Submodule.subset_span ⟨f, hf, rfl⟩⟩ ((hLmem _).2 ⟨f, hf, rfl⟩)
  have hrat : ∀ j (f : V), ∃ q : ℚ, (q : ℝ) = inner ℝ (tr_iota Hm f) (y j : TrW K dH) := by
    intro j f
    obtain ⟨m, hm0, hmM⟩ := h3 K V M hM f
    obtain ⟨z, hz⟩ := hint j _ hmM
    rw [tr_iota_smul_int, real_inner_smul_left] at hz
    have hm0' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    refine ⟨(z : ℚ) / m, ?_⟩
    push_cast
    rw [← hz]
    field_simp
  choose lf hlf using hrat
  let ℓ : Fin (finrank ℝ E) → V →+ ℚ := fun j =>
    { toFun := lf j
      map_zero' := by
        have : ((lf j 0 : ℚ) : ℝ) = ((0 : ℚ) : ℝ) := by rw [hlf, map_zero, inner_zero_left]; simp
        exact_mod_cast this
      map_add' := fun f g => by
        have : ((lf j (f + g) : ℚ) : ℝ) = ((lf j f + lf j g : ℚ) : ℝ) := by
          push_cast
          rw [hlf, hlf, hlf, map_add, inner_add_left]
        exact_mod_cast this }
  choose cf hcf using fun j => h2 K V (ℓ j)
  have hcf' : ∀ j g, ((Algebra.trace ℚ K (cf j g) : ℚ) : ℝ) = inner ℝ (tr_iota Hm g) (y j : TrW K dH) := by
    intro j g
    rw [hcf j g]
    exact hlf j g
  have hiotaE : ∀ f : V, tr_iota Hm f ∈ E := by
    intro f
    obtain ⟨m, hm0, hmM⟩ := h3 K V M hM f
    have hm0' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    have h : tr_iota Hm ((m : K) • f) ∈ E := Submodule.subset_span ⟨_, hmM, rfl⟩
    rw [tr_iota_smul_int] at h
    have h' := E.smul_mem (m : ℝ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hm0', one_smul] at h'
  refine ⟨finrank ℝ E, cf, ?_, ?_, ?_⟩
  ·
    have hco : (Submodule.span K (Set.range cf)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro f hf
      rw [Submodule.mem_dualCoannihilator] at hf
      have hz : ∀ j, inner ℝ (tr_iota Hm f) (y j : TrW K dH) = 0 := by
        intro j
        rw [← hcf' j f, hf (cf j) (Submodule.subset_span ⟨j, rfl⟩)]
        simp
      have htop : Submodule.span ℝ (Set.range y) = ⊤ :=
        hyli.span_eq_top_of_card_eq_finrank' (by simp)
      have hzero : (⟨tr_iota Hm f, hiotaE f⟩ : E) = 0 := by
        have hall : ∀ x : E, inner ℝ (⟨tr_iota Hm f, hiotaE f⟩ : E) x = 0 := by
          intro x
          have hx : x ∈ Submodule.span ℝ (Set.range y) := htop ▸ Submodule.mem_top
          induction hx using Submodule.span_induction with
          | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hz j
          | zero => exact inner_zero_right _
          | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
          | smul r a _ ha => rw [inner_smul_right, ha, mul_zero]
        exact inner_self_eq_zero.1 (hall _)
      have hi0 : tr_iota Hm f = 0 := congrArg Subtype.val hzero
      by_contra hf0
      have hf0' : f ≠ 0 := hf0
      obtain ⟨m, hm0, hmM⟩ := h3 K V M hM f
      have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
      have hne : (m : K) • f ≠ 0 := smul_ne_zero hmK hf0'
      have h := hlow _ hmM hne
      rw [← tr_norm_iota_sq Hm, tr_iota_smul_int, hi0, smul_zero, norm_zero] at h
      nlinarith [pow_pos hΛ 2]
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span K (Set.range cf))
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  · intro j f hf a
    have haf : (a : K) • f ∈ M := by
      rw [algebraMap_smul]
      exact M.smul_mem a hf
    obtain ⟨z, hz⟩ := hint j _ haf
    refine ⟨z, ?_⟩
    have : ((Algebra.trace ℚ K ((a : K) * cf j f) : ℚ) : ℝ) = ((z : ℚ) : ℝ) := by
      rw [← smul_eq_mul, ← map_smul, hcf', hz]
      simp
    exact_mod_cast this
  · intro σ j
    refine ⟨tr_comp (y j : TrW K dH) σ, (tr_norm_comp_le _ _).trans (hynorm j), fun f => ?_⟩
    exact tr_opLe_key Hm (y j : TrW K dH) (fun g => tr_sum_psi_real Hm hc (M : Set V) (y j).2 g) (cf j)
      (hcf' j) σ f

end TrC

/- English proof (translation)
The claim follows from `trans_of_stages (tr_dualVec hT) tr_traceDual tr_scale M hM Hm hc Ctr hC`.
-/
theorem trans_of_minima (hT : PI.TransferenceMinima) {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ}
    (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (Hm : Herm N2 dH) (hc : Hm.Conj)
    (Ctr : ℝ) (hC : ((finrank K V * finrank ℚ K : ℕ) : ℝ) < Ctr) : Trans M Hm Ctr :=
  trans_of_stages (tr_dualVec hT) tr_traceDual tr_scale M hM Hm hc Ctr hC

section FiltrationBoundaryCriterion

variable {R : Type} [CommRing R] {ι : Type} {W : Type} {G : W → Type} [∀ w, AddCommGroup (G w)]
  (inc : ∀ w, G w →+ R) (n : ∀ w, G w → ℝ)

def Bd (w : W) (p : MvPolynomial ι R) (B : ℝ) : Prop :=
  ∃ c : (ι →₀ ℕ) →₀ G w, (∀ β, inc w (c β) = p.coeff β) ∧ ∑ β ∈ c.support, n w (c β) ≤ B

def wtIter (add : W → W → W) (wL wθ : W) : ℕ → W
  | 0 => wθ
  | m + 1 => add wL (wtIter add wL wθ m)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [wtIter]`. Consider the case `succ k ih => rw [Nat.succ_add]`. Simplify using `only [wtIter]`. Rewrite using `[ih]`.
-/
theorem weight_iterate_add (add : W → W → W) (wL wθ : W) (k m : ℕ) :
    wtIter add wL wθ (k + m) = wtIter add wL (wtIter add wL wθ m) k := by
  induction k with
  | zero => simp [wtIter]
  | succ k ih => rw [Nat.succ_add]; simp only [wtIter]; rw [ih]

variable {inc n}

/- English proof (translation)
Use `Finset.sum_subset hS fun β _ hβ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.notMem_support_iff.mp hβ, h0]`.
-/
theorem sum_support_eq_sum_of_support_subset {A : Type} [AddCommGroup A] {m : A → ℝ} (h0 : m 0 = 0) (c : (ι →₀ ℕ) →₀ A)
    (S : Finset (ι →₀ ℕ)) (hS : c.support ⊆ S) : ∑ β ∈ c.support, m (c β) = ∑ β ∈ S, m (c β) := by
  refine Finset.sum_subset hS fun β _ hβ => ?_
  rw [Finsupp.notMem_support_iff.mp hβ, h0]

/- English proof (translation)
Take `⟨c, h1, h2⟩` from `h`. Conclude with `⟨c, h1, h2.trans hB⟩`.
-/
theorem bound_mono_of_le {w : W} {p : MvPolynomial ι R} {B B' : ℝ} (h : Bd inc n w p B) (hB : B ≤ B') :
    Bd inc n w p B' := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c, h1, h2.trans hB⟩

/- English proof (translation)
Take `⟨c, _, h2⟩` from `h`. Conclude with `(Finset.sum_nonneg fun _ _ => hnn _ _).trans h2`.
-/
theorem bound_nonneg_alt (hnn : ∀ w x, 0 ≤ n w x) {w : W} {p : MvPolynomial ι R} {B : ℝ} (h : Bd inc n w p B) :
    0 ≤ B := by
  obtain ⟨c, _, h2⟩ := h
  exact (Finset.sum_nonneg fun _ _ => hnn _ _).trans h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun β => by simp, by simp⟩`.
-/
theorem bound_zero_polynomial (w : W) : Bd inc n w (0 : MvPolynomial ι R) 0 :=
  ⟨0, fun β => by simp, by simp⟩

/- English proof (translation)
Take `⟨c, c1, c2⟩` from `hp`. Take `⟨c', c1', c2'⟩` from `hq`. Use `⟨c + c', fun β => by rw [Finsupp.add_apply, map_add, c1, c1', MvPolynomial.coeff_add], ?_⟩` and prove the remaining obligations. Rewrite using `[sum_support_eq_sum_of_support_subset (h0 w) (c + c') _ Finsupp.support_add]`. Rewrite `c2` using `[sum_support_eq_sum_of_support_subset (h0 w) c _ (Finset.subset_union_left (s₂ := c'.support))]`.

Rewrite `c2'` using `[sum_support_eq_sum_of_support_subset (h0 w) c' _ (Finset.subset_union_right (s₁ := c.support))]`. Use `le_trans ?_ (add_le_add c2 c2')` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_le_sum fun β _ => by rw [Finsupp.add_apply]; exact hadd _ _ _`.
-/
theorem bound_add (h0 : ∀ w, n w 0 = 0) (hadd : ∀ w x y, n w (x + y) ≤ n w x + n w y) {w : W}
    {p q : MvPolynomial ι R} {B B' : ℝ} (hp : Bd inc n w p B) (hq : Bd inc n w q B') :
    Bd inc n w (p + q) (B + B') := by
  classical
  obtain ⟨c, c1, c2⟩ := hp
  obtain ⟨c', c1', c2'⟩ := hq
  refine ⟨c + c', fun β => by rw [Finsupp.add_apply, map_add, c1, c1', MvPolynomial.coeff_add], ?_⟩
  rw [sum_support_eq_sum_of_support_subset (h0 w) (c + c') _ Finsupp.support_add]
  rw [sum_support_eq_sum_of_support_subset (h0 w) c _ (Finset.subset_union_left (s₂ := c'.support))] at c2
  rw [sum_support_eq_sum_of_support_subset (h0 w) c' _ (Finset.subset_union_right (s₁ := c.support))] at c2'
  refine le_trans ?_ (add_le_add c2 c2')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun β _ => by rw [Finsupp.add_apply]; exact hadd _ _ _

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using bound_zero_polynomial w`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `bound_add h0 hadd (h a (Finset.mem_insert_self _ _)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))`.
-/
theorem bound_sum_alt (h0 : ∀ w, n w 0 = 0) (hadd : ∀ w x y, n w (x + y) ≤ n w x + n w y) {w : W} {α : Type}
    (S : Finset α) (f : α → MvPolynomial ι R) (b : α → ℝ) (h : ∀ a ∈ S, Bd inc n w (f a) (b a)) :
    Bd inc n w (∑ a ∈ S, f a) (∑ a ∈ S, b a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using bound_zero_polynomial w
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact bound_add h0 hadd (h a (Finset.mem_insert_self _ _))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

/- English proof (translation)
Use `⟨Finsupp.single β a, fun γ => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [MvPolynomial.coeff_monomial, Finsupp.single_apply] split_ifs <;> simp`. Rewrite using `[sum_support_eq_sum_of_support_subset (h0 w) _ {β} Finsupp.support_single_subset]`. Simplify using the standard rewrite rules.
-/
theorem bound_monomial (h0 : ∀ w, n w 0 = 0) (w : W) (β : ι →₀ ℕ) (a : G w) :
    Bd inc n w (MvPolynomial.monomial β (inc w a)) (n w a) := by
  classical
  refine ⟨Finsupp.single β a, fun γ => ?_, ?_⟩
  · rw [MvPolynomial.coeff_monomial, Finsupp.single_apply]
    split_ifs <;> simp
  · rw [sum_support_eq_sum_of_support_subset (h0 w) _ {β} Finsupp.support_single_subset]
    simp

/- English proof (translation)
The claim follows from `bound_monomial h0 wθ 0 θ`.
-/
theorem Bd_C (h0 : ∀ w, n w 0 = 0) (wθ : W) (θ : G wθ) :
    Bd inc n wθ (MvPolynomial.C (inc wθ θ) : MvPolynomial ι R) (n wθ θ) :=
  bound_monomial h0 wθ 0 θ

/- English proof (translation)
Use `bound_sum_alt h0 hadd Finset.univ _ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, MvPolynomial.C_mul_X_eq_monomial]`. Conclude with `bound_monomial h0 wL _ _`.
-/
theorem Bd_lin (h0 : ∀ w, n w 0 = 0) (hadd : ∀ w x y, n w (x + y) ≤ n w x + n w y) {N : ℕ} {wL : W}
    (x : Fin N → ι) (w : Fin N → G wL) :
    Bd inc n wL (∑ j, MvPolynomial.X (x j) * MvPolynomial.C (inc wL (w j))) (∑ j, n wL (w j)) := by
  refine bound_sum_alt h0 hadd Finset.univ _ _ fun j _ => ?_
  rw [mul_comm, MvPolynomial.C_mul_X_eq_monomial]
  exact bound_monomial h0 wL _ _

/- English proof (translation)
Use extensionality with `γ`. Rewrite using `[MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq' c.support γ]`. Use `split_ifs with hγ`.

Conclude with `(h γ).symm`. Rewrite using `[← h γ, Finsupp.notMem_support_iff.mp hγ, map_zero]`.
-/
theorem polynomial_eq_sum_monomials {w : W} {p : MvPolynomial ι R} (c : (ι →₀ ℕ) →₀ G w) (h : ∀ β, inc w (c β) = p.coeff β) :
    p = ∑ β ∈ c.support, MvPolynomial.monomial β (inc w (c β)) := by
  classical
  ext γ
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' c.support γ]
  split_ifs with hγ
  · exact (h γ).symm
  · rw [← h γ, Finsupp.notMem_support_iff.mp hγ, map_zero]

/- English proof (translation)
Establish `hB'` using `bound_nonneg_alt hnn hq`. Take `⟨c, c1, c2⟩` from `hp`. Take `⟨c', c1', c2'⟩` from `hq`. Establish `hpq : p * q = ∑ a ∈ c.support, ∑ b ∈ c'.support, MvPolynomial.monomial (a + b) (inc w (c a) * inc w' (c' b))` using `by conv_lhs => rw [polynomial_eq_sum_monomials c c1, polynomial_eq_sum_monomials c' c1']`. Rewrite using `[Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.monomial_mul]`. Rewrite using `[hpq]`. Establish `key : Bd inc n (add w w') (∑ a ∈ c.support, ∑ b ∈ c'.support, MvPolynomial.monomial (a + b) (inc w (c a) * inc w' (c' b))) (∑ a ∈ c.support, ∑ b ∈ c'.support, n w (c a) * n w' (c' b))`. Use `bound_sum_alt h0 hadd _ _ _ fun a _ => bound_sum_alt h0 hadd _ _ _ fun b _ => ?_` and prove the remaining obligations.

Take `⟨H, H1, H2⟩` from `hmul w w' (c a) (c' b)`. Rewrite using `[← H1]`. Conclude with `bound_mono_of_le (bound_monomial h0 _ _ H) H2`. Use `bound_mono_of_le key ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul_sum]`.

Conclude with `mul_le_mul c2 c2' (Finset.sum_nonneg fun _ _ => hnn _ _) ((Finset.sum_nonneg fun _ _ => hnn _ _).trans c2)`.
-/
theorem Bd_mul (h0 : ∀ w, n w 0 = 0) (hnn : ∀ w x, 0 ≤ n w x) (hadd : ∀ w x y, n w (x + y) ≤ n w x + n w y)
    {add : W → W → W}
    (hmul : ∀ w w' (F : G w) (F' : G w'), ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ n _ H ≤ n w F * n w' F')
    {w w' : W} {p q : MvPolynomial ι R} {B B' : ℝ} (hp : Bd inc n w p B) (hq : Bd inc n w' q B') :
    Bd inc n (add w w') (p * q) (B * B') := by
  classical
  have hB' := bound_nonneg_alt hnn hq
  obtain ⟨c, c1, c2⟩ := hp
  obtain ⟨c', c1', c2'⟩ := hq
  have hpq : p * q = ∑ a ∈ c.support, ∑ b ∈ c'.support,
      MvPolynomial.monomial (a + b) (inc w (c a) * inc w' (c' b)) := by
    conv_lhs => rw [polynomial_eq_sum_monomials c c1, polynomial_eq_sum_monomials c' c1']
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [MvPolynomial.monomial_mul]
  rw [hpq]
  have key : Bd inc n (add w w') (∑ a ∈ c.support, ∑ b ∈ c'.support,
      MvPolynomial.monomial (a + b) (inc w (c a) * inc w' (c' b)))
      (∑ a ∈ c.support, ∑ b ∈ c'.support, n w (c a) * n w' (c' b)) := by
    refine bound_sum_alt h0 hadd _ _ _ fun a _ => bound_sum_alt h0 hadd _ _ _ fun b _ => ?_
    obtain ⟨H, H1, H2⟩ := hmul w w' (c a) (c' b)
    rw [← H1]
    exact bound_mono_of_le (bound_monomial h0 _ _ H) H2
  refine bound_mono_of_le key ?_
  rw [← Finset.sum_mul_sum]
  exact mul_le_mul c2 c2' (Finset.sum_nonneg fun _ _ => hnn _ _)
    ((Finset.sum_nonneg fun _ _ => hnn _ _).trans c2)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa [wtIter] using hq`. Consider the case `succ k ih`. Rewrite using `[pow_succ', mul_assoc, pow_succ', mul_assoc]`. Conclude with `Bd_mul h0 hnn hadd hmul hs ih`.
-/
theorem bound_pow_mul (h0 : ∀ w, n w 0 = 0) (hnn : ∀ w x, 0 ≤ n w x)
    (hadd : ∀ w x y, n w (x + y) ≤ n w x + n w y) {add : W → W → W}
    (hmul : ∀ w w' (F : G w) (F' : G w'), ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ n _ H ≤ n w F * n w' F')
    {wL w : W} {s q : MvPolynomial ι R} {S B : ℝ} (hs : Bd inc n wL s S) (hq : Bd inc n w q B) (k : ℕ) :
    Bd inc n (wtIter add wL w k) (s ^ k * q) (S ^ k * B) := by
  induction k with
  | zero => simpa [wtIter] using hq
  | succ k ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact Bd_mul h0 hnn hadd hmul hs ih

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa [wtIter] using hq`. Consider the case `insert a T ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, pow_add, mul_assoc, weight_iterate_add]`. Conclude with `bound_pow_mul h0 hnn hadd hmul (hs a) ih (al a)`.
-/
theorem bound_prod_pow_mul (h0 : ∀ w, n w 0 = 0) (hnn : ∀ w x, 0 ≤ n w x)
    (hadd : ∀ w x y, n w (x + y) ≤ n w x + n w y) {add : W → W → W}
    (hmul : ∀ w w' (F : G w) (F' : G w'), ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ n _ H ≤ n w F * n w' F')
    {wL w : W} {I : Type} (T : Finset I) (s : I → MvPolynomial ι R) {S B : ℝ} (hs : ∀ i, Bd inc n wL (s i) S)
    {q : MvPolynomial ι R} (hq : Bd inc n w q B) (al : I → ℕ) :
    Bd inc n (wtIter add wL w (∑ i ∈ T, al i)) ((∏ i ∈ T, s i ^ al i) * q) (S ^ (∑ i ∈ T, al i) * B) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa [wtIter] using hq
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, pow_add, mul_assoc, weight_iterate_add]
    exact bound_pow_mul h0 hnn hadd hmul (hs a) ih (al a)

/- English proof (translation)
The claim follows from `bound_prod_pow_mul h0 hnn hadd hmul Finset.univ s hs (Bd_C h0 wθ θ) al`.
-/
theorem Bd_word (h0 : ∀ w, n w 0 = 0) (hnn : ∀ w x, 0 ≤ n w x) (hadd : ∀ w x y, n w (x + y) ≤ n w x + n w y)
    {add : W → W → W}
    (hmul : ∀ w w' (F : G w) (F' : G w'), ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ n _ H ≤ n w F * n w' F')
    {wL wθ : W} {I : Type} [Fintype I] (s : I → MvPolynomial ι R) (S : ℝ) (hs : ∀ i, Bd inc n wL (s i) S)
    (θ : G wθ) (al : I → ℕ) :
    Bd inc n (wtIter add wL wθ (∑ i, al i)) ((∏ i, s i ^ al i) * MvPolynomial.C (inc wθ θ))
      (S ^ (∑ i, al i) * n wθ θ) :=
  bound_prod_pow_mul h0 hnn hadd hmul Finset.univ s hs (Bd_C h0 wθ θ) al

/- English proof (translation)
Take `⟨c, c1, c2⟩` from `h`. Establish `: z = c`. Use extensionality with `β`. Conclude with `hinj ((hz β).trans (c1 β).symm)`. Rewrite using `[this]`.

Conclude with `c2`.
-/
theorem Bd_bound (w : W) (hinj : Function.Injective (inc w)) (P : MvPolynomial ι R) (B : ℝ)
    (h : Bd inc n w P B) (z : (ι →₀ ℕ) →₀ G w) (hz : ∀ β, inc w (z β) = P.coeff β) :
    ∑ β ∈ z.support, n w (z β) ≤ B := by
  obtain ⟨c, c1, c2⟩ := h
  have : z = c := by
    ext β
    exact hinj ((hz β).trans (c1 β).symm)
  rw [this]
  exact c2

end FiltrationBoundaryCriterion

section AuxConj

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable {N2 : (K →+* ℂ) → V → ℝ} {dH : ℕ}

/- English proof (translation)
Establish `h1` using `@norm_add_sq ℂ _ _ _ _ (Hm.e σ f) (Hm.e σ g)`. Establish `h2` using `@norm_add_sq ℂ _ _ _ _ (Hm.e (ComplexEmbedding.conjugate σ) f) (Hm.e (ComplexEmbedding.conjugate σ) g)`. Rewrite `h1`, `h2` using `[← map_add, Hm.norm_e, Hm.norm_e, Hm.norm_e]`. Rewrite `h2` using `[hN, hN, hN]`. Simplify using `only [RCLike.re_to_complex] at h1 h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem re_inner_conjugate_embedding_eq (Hm : Herm N2 dH) (hN : ∀ σ f, N2 (ComplexEmbedding.conjugate σ) f = N2 σ f) (σ : K →+* ℂ)
    (f g : V) :
    (inner ℂ (Hm.e (ComplexEmbedding.conjugate σ) f) (Hm.e (ComplexEmbedding.conjugate σ) g)).re =
      (inner ℂ (Hm.e σ f) (Hm.e σ g)).re := by
  have h1 := @norm_add_sq ℂ _ _ _ _ (Hm.e σ f) (Hm.e σ g)
  have h2 := @norm_add_sq ℂ _ _ _ _ (Hm.e (ComplexEmbedding.conjugate σ) f) (Hm.e (ComplexEmbedding.conjugate σ) g)
  rw [← map_add, Hm.norm_e, Hm.norm_e, Hm.norm_e] at h1 h2
  rw [hN, hN, hN] at h2
  simp only [RCLike.re_to_complex] at h1 h2
  linarith

/- English proof (translation)
Introduce `σ f g`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : K, (σ a).im ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hc σ` to reduce the goal to its premises.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `Complex.conj_eq_iff_im.mpr (hcon x)`. Establish `r1` using `re_inner_conjugate_embedding_eq Hm hN σ f g`.

Establish `r2` using `re_inner_conjugate_embedding_eq Hm hN σ f (a • g)`. Rewrite `r2` using `[map_smulₛₗ, map_smulₛₗ, inner_smul_right, inner_smul_right, ComplexEmbedding.conjugate_coe_eq]`. Simplify using `only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at r2`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.star_def, Complex.conj_re]`.

Conclude with `r1`. Establish `: (σ a).im * ((inner ℂ (Hm.e (ComplexEmbedding.conjugate σ) f) (Hm.e (ComplexEmbedding.conjugate σ) g)).im + (inner ℂ (Hm.e σ f) (Hm.e σ g)).im) = 0`. Rewrite `r2` using `[r1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `(mul_eq_zero.mp this).resolve_left ha`.

Simplify using `only [Complex.star_def, Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem conj_of_norm (Hm : Herm N2 dH) (hN : ∀ σ f, N2 (ComplexEmbedding.conjugate σ) f = N2 σ f)
    (hc : ∀ σ : K →+* ℂ, ¬ ComplexEmbedding.IsReal σ) : Hm.Conj := by
  intro σ f g
  obtain ⟨a, ha⟩ : ∃ a : K, (σ a).im ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hc σ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (hcon x)
  have r1 := re_inner_conjugate_embedding_eq Hm hN σ f g
  have r2 := re_inner_conjugate_embedding_eq Hm hN σ f (a • g)
  rw [map_smulₛₗ, map_smulₛₗ, inner_smul_right, inner_smul_right, ComplexEmbedding.conjugate_coe_eq] at r2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at r2
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]; exact r1
  · have : (σ a).im * ((inner ℂ (Hm.e (ComplexEmbedding.conjugate σ) f) (Hm.e (ComplexEmbedding.conjugate σ) g)).im +
        (inner ℂ (Hm.e σ f) (Hm.e σ g)).im) = 0 := by
      rw [r1] at r2; linarith
    have h3 := (mul_eq_zero.mp this).resolve_left ha
    simp only [Complex.star_def, Complex.conj_im]
    linarith

end AuxConj

section AuxMax

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {ι : Type}

/- English proof (translation)
Establish `hmem` using `Nat.sInf_mem (s := {n : ℕ | ∃ (φ : Fin ρ → V →ₗ[K] K) (β : ι →₀ ℕ), (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) ∧ (detPoly φ z).coeff β ≠ 0 ∧ vAdd la ((detPoly φ z).coeff β) = (n : ℤ)}) hne`. Take `⟨φ, β, h1, h2, h3⟩` from `hmem`. Use `hG la φ h1 β h2` as an intermediate fact. Rewrite `this` using `[h3]`. Conclude with `this` after adjusting the coercions.
-/
theorem gaussC_max (M : Submodule (𝓞 K) V) {ρ : ℕ} (z : Fin ρ → (ι →₀ ℕ) →₀ V)
    (c : HeightOneSpectrum (𝓞 K) → ℝ) (hG : GaussLe M z c) (la : HeightOneSpectrum (𝓞 K))
    (hne : ∃ (n : ℕ) (φ : Fin ρ → V →ₗ[K] K) (β : ι →₀ ℕ), (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) ∧
      (detPoly φ z).coeff β ≠ 0 ∧ vAdd la ((detPoly φ z).coeff β) = (n : ℤ)) :
    c la ≤ (gaussC M z la : ℝ) := by
  have hmem := Nat.sInf_mem (s := {n : ℕ | ∃ (φ : Fin ρ → V →ₗ[K] K) (β : ι →₀ ℕ),
    (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) ∧
    (detPoly φ z).coeff β ≠ 0 ∧ vAdd la ((detPoly φ z).coeff β) = (n : ℤ)}) hne
  obtain ⟨φ, β, h1, h2, h3⟩ := hmem
  have := hG la φ h1 β h2
  rw [h3] at this
  exact_mod_cast this

end AuxMax

section Packet

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def SubMul (X : PJ D B P j) : Prop :=
  ∀ (σ : B.KO →+* ℂ) (w w' : WeightFamilies.Wt D j) (F : B.Cusp j w) (G : B.Cusp j w') (H : B.Cusp j (wadd w w')),
    X.inc _ H = X.inc w F * X.inc w' G → B.supN j _ σ H ≤ B.supN j w σ F * B.supN j w' σ G

def zPoly (X : PJ D B P j) {wL w0 : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → B.Cusp j wL)
    (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j w0) :
    MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) X.Forms :=
  (∏ i : Fin (WeightFamilies.dimY D j), (∑ k, MvPolynomial.X (i.succ, k) * MvPolynomial.C (X.inc wL (w k))) ^ al i) *
    MvPolynomial.C (X.inc w0 θ)

/- English proof (translation)
Unfold `WeightFamilies.Wt.size wadd`. Simplify using `only [Nat.cast_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem size_wadd (w w' : WeightFamilies.Wt D j) : (wadd w w').size = w.size + w'.size - 1 := by
  unfold WeightFamilies.Wt.size wadd
  simp only [Nat.cast_add, Finset.sum_add_distrib]
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [wtIter]`. Consider the case `succ m ih => rw [wtIter, size_wadd, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem size_wtIter (wL w0 : WeightFamilies.Wt D j) (m : ℕ) :
    (wtIter wadd wL w0 m).size = w0.size + m * (wL.size - 1) := by
  induction m with
  | zero => simp [wtIter]
  | succ m ih => rw [wtIter, size_wadd, ih]; push_cast; ring

/- English proof (translation)
Establish `h0 : ∀ w : WeightFamilies.Wt D j, B.supN j w σ 0 = 0` using `fun w => (B.supN_eq_zero j w σ 0).mpr rfl`. Establish `hnn : ∀ (w : WeightFamilies.Wt D j) x, 0 ≤ B.supN j w σ x` using `fun w x => B.supN_nonneg j w σ x`. Establish `hadd : ∀ (w : WeightFamilies.Wt D j) x y, B.supN j w σ (x + y) ≤ B.supN j w σ x + B.supN j w σ y` using `fun w x y => B.supN_add j w σ x y`. Establish `hmul : ∀ (w w' : WeightFamilies.Wt D j) (F : B.Cusp j w) (F' : B.Cusp j w'), ∃ H : B.Cusp j (wadd w w'), (X.inc _).toAddMonoidHom H = (X.inc w).toAddMonoidHom F * (X.inc w').toAddMonoidHom F' ∧ B.supN j _ σ H ≤ B.supN j w σ F * B.supN j w' σ F'`. Introduce `w w' F F'`.

Take `⟨H, hH⟩` from `X.inc_mul w w' F F'`. Conclude with `⟨H, hH.symm, hSM σ w w' F F' H hH.symm⟩`. Establish `hs : ∀ i : Fin (WeightFamilies.dimY D j), Bd (fun w => (X.inc w).toAddMonoidHom) (fun w => B.supN j w σ) wL (∑ k, MvPolynomial.X (i.succ, k) * MvPolynomial.C (X.inc wL (w k))) (∑ k, B.supN j wL σ (w k))` using `fun i => Bd_lin h0 hadd (fun k => (i.succ, k)) w`. Establish `hw` using `Bd_word h0 hnn hadd hmul _ _ hs θ al`. Conclude with `Bd_bound _ (X.inc_inj _) _ _ hw z hz`.
-/
theorem polynomial_coefficient_l1_bound (X : PJ D B P j) (hSM : SubMul X) {wL w0 : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → B.Cusp j wL)
    (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j w0) (σ : B.KO →+* ℂ)
    (z : ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j (wtIter wadd wL w0 (∑ i, al i)))
    (hz : ∀ β, X.inc _ (z β) = (zPoly X w al θ).coeff β) :
    ∑ γ ∈ z.support, B.supN j _ σ (z γ) ≤ (∑ k, B.supN j wL σ (w k)) ^ (∑ i, al i) * B.supN j w0 σ θ := by
  have h0 : ∀ w : WeightFamilies.Wt D j, B.supN j w σ 0 = 0 := fun w => (B.supN_eq_zero j w σ 0).mpr rfl
  have hnn : ∀ (w : WeightFamilies.Wt D j) x, 0 ≤ B.supN j w σ x := fun w x => B.supN_nonneg j w σ x
  have hadd : ∀ (w : WeightFamilies.Wt D j) x y, B.supN j w σ (x + y) ≤ B.supN j w σ x + B.supN j w σ y :=
    fun w x y => B.supN_add j w σ x y
  have hmul : ∀ (w w' : WeightFamilies.Wt D j) (F : B.Cusp j w) (F' : B.Cusp j w'), ∃ H : B.Cusp j (wadd w w'),
      (X.inc _).toAddMonoidHom H = (X.inc w).toAddMonoidHom F * (X.inc w').toAddMonoidHom F' ∧
        B.supN j _ σ H ≤ B.supN j w σ F * B.supN j w' σ F' := by
    intro w w' F F'
    obtain ⟨H, hH⟩ := X.inc_mul w w' F F'
    exact ⟨H, hH.symm, hSM σ w w' F F' H hH.symm⟩
  have hs : ∀ i : Fin (WeightFamilies.dimY D j), Bd (fun w => (X.inc w).toAddMonoidHom) (fun w => B.supN j w σ) wL
      (∑ k, MvPolynomial.X (i.succ, k) * MvPolynomial.C (X.inc wL (w k))) (∑ k, B.supN j wL σ (w k)) :=
    fun i => Bd_lin h0 hadd (fun k => (i.succ, k)) w
  have hw := Bd_word h0 hnn hadd hmul _ _ hs θ al
  exact Bd_bound _ (X.inc_inj _) _ _ hw z hz

/- English proof (translation)
Substitute `hwt` using the available equality. Use `set d : ℕ := finrank B.KO (B.Cusp j (wtIter wadd wL w0 a0)) with hddef`. Establish `hnK : 1 ≤ finrank ℚ B.KO` using `Module.finrank_pos (R := ℚ) (M := B.KO)`. Establish `hlognK : 0 ≤ Real.log (finrank ℚ B.KO : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hPd0 : 0 ≤ Pd` using `(Real.log_natCast_nonneg _).trans hd`.

Establish `hPO0 : 0 ≤ PO D large₂` using `hlognK.trans hO.1`. Establish `hE : ∀ σ k, ∑ γ ∈ (z k).support, B.l2NormAlt j _ σ (z k γ) ≤ Real.exp ((a0 : ℝ) * (Real.log N + mx σ) + Real.log (B.supN j w0 σ (th k)))`. Introduce `σ k`. Establish `hk` using `hal k`. Establish `h3 : ∑ γ ∈ (z k).support, B.supN j _ σ (z k γ) ≤ (∑ i, B.supN j wL σ (w i)) ^ a0 * B.supN j w0 σ (th k)`.

Establish `hzk` using `hz k`. Use `revert hzk`. Generalize the expression as in `z k = zk`. Use `revert zk`. Rewrite using `[← hk]`.

Introduce `zk hzk`. Conclude with `polynomial_coefficient_l1_bound X hSM w (al k) (th k) σ zk hzk`. Use `(Finset.sum_le_sum fun γ _ => B.l2Norm_le_supNorm_alt j _ σ (z k γ)).trans (h3.trans ?_)` and prove the remaining obligations. Establish `h4 : ∑ i, B.supN j wL σ (w i) ≤ Real.exp (Real.log N + mx σ)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.exp_add, Real.exp_nat_mul]`. Conclude with `mul_le_mul (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => B.supN_nonneg j wL σ _) h4 _) (Real.le_exp_log _) (B.supN_nonneg j w0 σ _) (pow_pos (Real.exp_pos _) _).le`. Establish `hC0 : Real.log (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1) ≤ 1 * (Real.log (d : ℝ) + Real.log (finrank ℚ B.KO : ℝ))`. Rewrite using `[one_mul]`. Break down `Nat.eq_zero_or_pos d with h | h` into its components or cases.

Rewrite using `[h]`. Simplify using `using hlognK`. Establish `h5 : (1 : ℝ) ≤ ((d * finrank ℚ B.KO : ℕ) : ℝ)` using `by exact_mod_cast Nat.mul_pos h hnK`. Rewrite using `[max_eq_left h5, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]`. Use `deepSum (B.Mlat j _) z c hc0 hG hW Hm (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) (fun Ctr h => hT Ctr (lt_of_le_of_lt (le_max_left _ _) h)) (fun σ => B.supN j _ σ) (fun σ f hf => lt_of_le_of_ne (B.supN_nonneg j _ σ f) (fun h => hf ((B.supN_ …` as an intermediate fact.

Establish `e : (1 : ℝ) + 1 / 2 = 3 / 2` using `by norm_num`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem deepPacket (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (th : Fin ρ → B.Cusp j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ)
    (hal : ∀ k, ∑ i, al k i = a0)
    (z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka)
    (hz : ∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β)
    (c : HeightOneSpectrum (𝓞 B.KO) → ℝ) (hc0 : ∀ la, 0 ≤ c la) (hG : GaussLe (B.Mlat j ka) z c)
    (hW : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, detPoly φ z ≠ 0)
    {dH : ℕ} (Hm : Herm (fun σ => B.l2NormAlt j ka σ) dH)
    (hT : ∀ Ctr, ((finrank B.KO (B.Cusp j ka) * finrank ℚ B.KO : ℕ) : ℝ) < Ctr → Trans (B.Mlat j ka) Hm Ctr)
    (hSM : SubMul X) (CL AL : ℝ) (hLAM : WeightFamilies.Conclusion1 large₂ B CL AL) (G Prw Pd : ℝ)
    (hS2 : ∀ σ (F : B.Cusp j ka), B.supN j ka σ F ^ 2 ≤ Real.exp Pd * B.l2NormAlt j ka σ F ^ 2)
    (hG0 : 0 ≤ G) (hPrw : 0 ≤ Prw)
    (mx : (B.KO →+* ℂ) → ℝ) (hmx : ∀ σ k, B.supN j wL σ (w k) ≤ Real.exp (mx σ))
    (hmxm : (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size)
    (hth : ∀ k, WeightFamilies.meanLogSup B (th k) ≤ G * w0.size)
    (ha : (a0 : ℝ) ≤ ka.size) (hrw : Real.log N ≤ Prw * (wL.size - 1))
    (hd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd) (hO : OPO large₂ B) :
    Summable (fun la => c la * X.lN la) ∧
      ∑' la, c la * X.lN la ≤
        ρ * ((2 * G + Prw + WeightFamilies.PP0v D large₂ CL AL + (3 / 2) * (Pd + PO D large₂)) * ka.size) := by
  subst hwt
  set d : ℕ := finrank B.KO (B.Cusp j (wtIter wadd wL w0 a0)) with hddef
  have hnK : 1 ≤ finrank ℚ B.KO := Module.finrank_pos (R := ℚ) (M := B.KO)
  have hlognK : 0 ≤ Real.log (finrank ℚ B.KO : ℝ) := Real.log_natCast_nonneg _
  have hPd0 : 0 ≤ Pd := (Real.log_natCast_nonneg _).trans hd
  have hPO0 : 0 ≤ PO D large₂ := hlognK.trans hO.1
  have hE : ∀ σ k, ∑ γ ∈ (z k).support, B.l2NormAlt j _ σ (z k γ) ≤
      Real.exp ((a0 : ℝ) * (Real.log N + mx σ) + Real.log (B.supN j w0 σ (th k))) := by
    intro σ k
    have hk := hal k
    have h3 : ∑ γ ∈ (z k).support, B.supN j _ σ (z k γ) ≤
        (∑ i, B.supN j wL σ (w i)) ^ a0 * B.supN j w0 σ (th k) := by
      have hzk := hz k
      revert hzk
      generalize z k = zk
      revert zk
      rw [← hk]
      intro zk hzk
      exact polynomial_coefficient_l1_bound X hSM w (al k) (th k) σ zk hzk
    refine (Finset.sum_le_sum fun γ _ => B.l2Norm_le_supNorm_alt j _ σ (z k γ)).trans (h3.trans ?_)
    have h4 : ∑ i, B.supN j wL σ (w i) ≤ Real.exp (Real.log N + mx σ) := by
      calc ∑ i, B.supN j wL σ (w i) ≤ ∑ _i : Fin N, Real.exp (mx σ) := Finset.sum_le_sum fun i _ => hmx σ i
        _ = N * Real.exp (mx σ) := by simp
        _ ≤ Real.exp (Real.log N) * Real.exp (mx σ) :=
            mul_le_mul_of_nonneg_right (Real.le_exp_log _) (Real.exp_pos _).le
        _ = _ := (Real.exp_add _ _).symm
    rw [Real.exp_add, Real.exp_nat_mul]
    exact mul_le_mul (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => B.supN_nonneg j wL σ _) h4 _)
      (Real.le_exp_log _) (B.supN_nonneg j w0 σ _) (pow_pos (Real.exp_pos _) _).le
  have hC0 : Real.log (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1) ≤
      1 * (Real.log (d : ℝ) + Real.log (finrank ℚ B.KO : ℝ)) := by
    rw [one_mul]
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h]; simpa using hlognK
    · have h5 : (1 : ℝ) ≤ ((d * finrank ℚ B.KO : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos h hnK
      rw [max_eq_left h5, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  have := deepSum (B.Mlat j _) z c hc0 hG hW Hm (max ((d * finrank ℚ B.KO : ℕ) : ℝ) 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) (fun Ctr h => hT Ctr (lt_of_le_of_lt (le_max_left _ _) h))
    (fun σ => B.supN j _ σ)
    (fun σ f hf => lt_of_le_of_ne (B.supN_nonneg j _ σ f) (fun h => hf ((B.supN_eq_zero j _ σ f).mp h.symm)))
    (WeightFamilies.PP0v D large₂ CL AL) (wtIter wadd wL w0 a0).size Pd
    (fun f hf hf0 => hLAM j h1 h2 _ f hf hf0)
    hS2
    (a0 : ℝ) (Real.log N) mx (fun σ k => Real.log (B.supN j w0 σ (th k))) hE (Nat.cast_nonneg _)
    1 G Prw (PO D large₂) wL.size w0.size (Real.log (d : ℝ)) le_rfl hG0 hPrw hPd0 hPO0
    (WeightFamilies.Wt.one_le_size _) (zero_le_one.trans (WeightFamilies.Wt.one_le_size _)) hmxm hth
    (by rw [size_wtIter]; ring) ha hrw hd hC0 hO.1 hO.2
  have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [e] at this
  exact this

end Packet

section GP

variable {R : Type} [CommRing R] {ι : Type} {W : Type} {G : W → Type} [∀ w, AddCommGroup (G w)]
  (inc : ∀ w, G w →+ R) (Pr : ∀ w, G w → Prop)

def Cf (w : W) (p : MvPolynomial ι R) : Prop :=
  ∃ c : (ι →₀ ℕ) →₀ G w, (∀ β, inc w (c β) = p.coeff β) ∧ ∀ β, Pr w (c β)

variable {inc Pr}

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun β => by simp, fun β => by simpa using p0 w⟩`.
-/
theorem gp_Cf_zero (p0 : ∀ w, Pr w 0) (w : W) : Cf inc Pr w (0 : MvPolynomial ι R) :=
  ⟨0, fun β => by simp, fun β => by simpa using p0 w⟩

/- English proof (translation)
Take `⟨c, c1, c2⟩` from `hp`. Take `⟨c', c1', c2'⟩` from `hq`. Conclude with `⟨c + c', fun β => by rw [Finsupp.add_apply, map_add, c1, c1', MvPolynomial.coeff_add], fun β => by rw [Finsupp.add_apply]; exact padd _ _ _ (c2 β) (c2' β)⟩`.
-/
theorem gp_Cf_add (padd : ∀ w x y, Pr w x → Pr w y → Pr w (x + y)) {w : W} {p q : MvPolynomial ι R}
    (hp : Cf inc Pr w p) (hq : Cf inc Pr w q) : Cf inc Pr w (p + q) := by
  obtain ⟨c, c1, c2⟩ := hp
  obtain ⟨c', c1', c2'⟩ := hq
  exact ⟨c + c', fun β => by rw [Finsupp.add_apply, map_add, c1, c1', MvPolynomial.coeff_add],
    fun β => by rw [Finsupp.add_apply]; exact padd _ _ _ (c2 β) (c2' β)⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using gp_Cf_zero p0 w`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `gp_Cf_add padd (h a (Finset.mem_insert_self _ _)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))`.
-/
theorem gp_Cf_sum (p0 : ∀ w, Pr w 0) (padd : ∀ w x y, Pr w x → Pr w y → Pr w (x + y)) {w : W} {α : Type}
    (S : Finset α) (f : α → MvPolynomial ι R) (h : ∀ a ∈ S, Cf inc Pr w (f a)) :
    Cf inc Pr w (∑ a ∈ S, f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using gp_Cf_zero p0 w
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact gp_Cf_add padd (h a (Finset.mem_insert_self _ _)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

/- English proof (translation)
Use `⟨Finsupp.single β a, fun γ => ?_, fun γ => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [MvPolynomial.coeff_monomial, Finsupp.single_apply] split_ifs <;> simp`. Rewrite using `[Finsupp.single_apply] split_ifs`. Conclude with `ha`. Conclude with `p0 w`.
-/
theorem gp_Cf_monomial (p0 : ∀ w, Pr w 0) (w : W) (β : ι →₀ ℕ) (a : G w) (ha : Pr w a) :
    Cf inc Pr w (MvPolynomial.monomial β (inc w a)) := by
  classical
  refine ⟨Finsupp.single β a, fun γ => ?_, fun γ => ?_⟩
  · rw [MvPolynomial.coeff_monomial, Finsupp.single_apply]
    split_ifs <;> simp
  · rw [Finsupp.single_apply]
    split_ifs
    · exact ha
    · exact p0 w

/- English proof (translation)
The claim follows from `gp_Cf_monomial p0 wθ 0 θ hθ`.
-/
theorem Cf_C (p0 : ∀ w, Pr w 0) (wθ : W) (θ : G wθ) (hθ : Pr wθ θ) :
    Cf inc Pr wθ (MvPolynomial.C (inc wθ θ) : MvPolynomial ι R) :=
  gp_Cf_monomial p0 wθ 0 θ hθ

/- English proof (translation)
Use `gp_Cf_sum p0 padd Finset.univ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, MvPolynomial.C_mul_X_eq_monomial]`. Conclude with `gp_Cf_monomial p0 wL _ _ (hw j)`.
-/
theorem Cf_lin (p0 : ∀ w, Pr w 0) (padd : ∀ w x y, Pr w x → Pr w y → Pr w (x + y)) {N : ℕ} {wL : W}
    (x : Fin N → ι) (w : Fin N → G wL) (hw : ∀ j, Pr wL (w j)) :
    Cf inc Pr wL (∑ j, MvPolynomial.X (x j) * MvPolynomial.C (inc wL (w j))) := by
  refine gp_Cf_sum p0 padd Finset.univ _ fun j _ => ?_
  rw [mul_comm, MvPolynomial.C_mul_X_eq_monomial]
  exact gp_Cf_monomial p0 wL _ _ (hw j)

/- English proof (translation)
Take `⟨c, c1, c2⟩` from `hp`. Take `⟨c', c1', c2'⟩` from `hq`. Establish `hpq : p * q = ∑ a ∈ c.support, ∑ b ∈ c'.support, MvPolynomial.monomial (a + b) (inc w (c a) * inc w' (c' b))` using `by conv_lhs => rw [polynomial_eq_sum_monomials c c1, polynomial_eq_sum_monomials c' c1']`. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.monomial_mul]`. Rewrite using `[hpq]`. Use `gp_Cf_sum p0 padd _ _ fun a _ => gp_Cf_sum p0 padd _ _ fun b _ => ?_` and prove the remaining obligations. Take `⟨H, H1, H2⟩` from `pmul w w' (c a) (c' b) (c2 a) (c2' b)`. Rewrite using `[← H1]`.

Conclude with `gp_Cf_monomial p0 _ _ H H2`.
-/
theorem Cf_mul (p0 : ∀ w, Pr w 0) (padd : ∀ w x y, Pr w x → Pr w y → Pr w (x + y)) {add : W → W → W}
    (pmul : ∀ w w' (F : G w) (F' : G w'), Pr w F → Pr w' F' →
      ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ Pr _ H)
    {w w' : W} {p q : MvPolynomial ι R} (hp : Cf inc Pr w p) (hq : Cf inc Pr w' q) :
    Cf inc Pr (add w w') (p * q) := by
  classical
  obtain ⟨c, c1, c2⟩ := hp
  obtain ⟨c', c1', c2'⟩ := hq
  have hpq : p * q = ∑ a ∈ c.support, ∑ b ∈ c'.support,
      MvPolynomial.monomial (a + b) (inc w (c a) * inc w' (c' b)) := by
    conv_lhs => rw [polynomial_eq_sum_monomials c c1, polynomial_eq_sum_monomials c' c1']
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [MvPolynomial.monomial_mul]
  rw [hpq]
  refine gp_Cf_sum p0 padd _ _ fun a _ => gp_Cf_sum p0 padd _ _ fun b _ => ?_
  obtain ⟨H, H1, H2⟩ := pmul w w' (c a) (c' b) (c2 a) (c2' b)
  rw [← H1]
  exact gp_Cf_monomial p0 _ _ H H2

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa [wtIter] using hq`. Consider the case `succ k ih`. Rewrite using `[pow_succ', mul_assoc]`. Conclude with `Cf_mul p0 padd pmul hs ih`.
-/
theorem gp_Cf_pow_mul (p0 : ∀ w, Pr w 0) (padd : ∀ w x y, Pr w x → Pr w y → Pr w (x + y)) {add : W → W → W}
    (pmul : ∀ w w' (F : G w) (F' : G w'), Pr w F → Pr w' F' →
      ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ Pr _ H)
    {wL w : W} {s q : MvPolynomial ι R} (hs : Cf inc Pr wL s) (hq : Cf inc Pr w q) (k : ℕ) :
    Cf inc Pr (wtIter add wL w k) (s ^ k * q) := by
  induction k with
  | zero => simpa [wtIter] using hq
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact Cf_mul p0 padd pmul hs ih

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa [wtIter] using hq`. Consider the case `insert a T ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, weight_iterate_add]`. Conclude with `gp_Cf_pow_mul p0 padd pmul (hs a) ih (al a)`.
-/
theorem gp_Cf_prod_pow_mul (p0 : ∀ w, Pr w 0) (padd : ∀ w x y, Pr w x → Pr w y → Pr w (x + y))
    {add : W → W → W}
    (pmul : ∀ w w' (F : G w) (F' : G w'), Pr w F → Pr w' F' →
      ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ Pr _ H)
    {wL w : W} {I : Type} (T : Finset I) (s : I → MvPolynomial ι R) (hs : ∀ i, Cf inc Pr wL (s i))
    {q : MvPolynomial ι R} (hq : Cf inc Pr w q) (al : I → ℕ) :
    Cf inc Pr (wtIter add wL w (∑ i ∈ T, al i)) ((∏ i ∈ T, s i ^ al i) * q) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa [wtIter] using hq
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc, weight_iterate_add]
    exact gp_Cf_pow_mul p0 padd pmul (hs a) ih (al a)

/- English proof (translation)
The claim follows from `gp_Cf_prod_pow_mul p0 padd pmul Finset.univ s hs (Cf_C p0 wθ θ hθ) al`.
-/
theorem Cf_word (p0 : ∀ w, Pr w 0) (padd : ∀ w x y, Pr w x → Pr w y → Pr w (x + y)) {add : W → W → W}
    (pmul : ∀ w w' (F : G w) (F' : G w'), Pr w F → Pr w' F' →
      ∃ H : G (add w w'), inc _ H = inc w F * inc w' F' ∧ Pr _ H)
    {wL wθ : W} {I : Type} [Fintype I] (s : I → MvPolynomial ι R) (hs : ∀ i, Cf inc Pr wL (s i))
    (θ : G wθ) (hθ : Pr wθ θ) (al : I → ℕ) :
    Cf inc Pr (wtIter add wL wθ (∑ i, al i)) ((∏ i, s i ^ al i) * MvPolynomial.C (inc wθ θ)) :=
  gp_Cf_prod_pow_mul p0 padd pmul Finset.univ s hs (Cf_C p0 wθ θ hθ) al

end GP

section GPPacket

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

/- English proof (translation)
Take `⟨H, hH⟩` from `X.inc_mul w w' F F'`. Use `⟨H, hH.symm, (X.Mlat_eq _ H).mpr fun la y => ?_⟩` and prove the remaining obligations. Rewrite using `[← hH, X.vAt_mul]`. Conclude with `add_nonneg ((X.Mlat_eq w F).mp hF la y) ((X.Mlat_eq w' F').mp hF' la y)`.
-/
theorem gp_mlat_mul (X : PJ D B P j) (w w' : WeightFamilies.Wt D j) (F : B.Cusp j w) (F' : B.Cusp j w')
    (hF : F ∈ B.Mlat j w) (hF' : F' ∈ B.Mlat j w') :
    ∃ H : B.Cusp j (wadd w w'), X.inc _ H = X.inc w F * X.inc w' F' ∧ H ∈ B.Mlat j _ := by
  obtain ⟨H, hH⟩ := X.inc_mul w w' F F'
  refine ⟨H, hH.symm, (X.Mlat_eq _ H).mpr fun la y => ?_⟩
  rw [← hH, X.vAt_mul]
  exact add_nonneg ((X.Mlat_eq w F).mp hF la y) ((X.Mlat_eq w' F').mp hF' la y)

/- English proof (translation)
Establish `p0 : ∀ w : WeightFamilies.Wt D j, (0 : B.Cusp j w) ∈ B.Mlat j w` using `fun w => (B.Mlat j w).zero_mem`. Establish `padd : ∀ (w : WeightFamilies.Wt D j) (x y : B.Cusp j w), x ∈ B.Mlat j w → y ∈ B.Mlat j w → x + y ∈ B.Mlat j w` using `fun w x y hx hy => (B.Mlat j w).add_mem hx hy`. Establish `pmul : ∀ (w w' : WeightFamilies.Wt D j) (F : B.Cusp j w) (F' : B.Cusp j w'), F ∈ B.Mlat j w → F' ∈ B.Mlat j w' → ∃ H : B.Cusp j (wadd w w'), (X.inc _).toAddMonoidHom H = (X.inc w).toAddMonoidHom F * (X.inc w').toAddMonoidHom F' ∧ H ∈ B.Mlat j _` using `fun w w' F F' hF hF' => gp_mlat_mul X w w' F F' hF hF'`. Establish `hs : ∀ i : Fin (WeightFamilies.dimY D j), Cf (fun w => (X.inc w).toAddMonoidHom) (fun w F => F ∈ B.Mlat j w) wL (∑ k, MvPolynomial.X (i.succ, k) * MvPolynomial.C (X.inc wL (w k)))` using `fun i => Cf_lin p0 padd (fun k => (i.succ, k)) w hw`. Conclude with `Cf_word p0 padd pmul _ hs θ hθ al`.
-/
theorem zPoly_cf (X : PJ D B P j) {wL w0 : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → B.Cusp j wL)
    (hw : ∀ k, w k ∈ B.Mlat j wL) (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j w0) (hθ : θ ∈ B.Mlat j w0) :
    ∃ z : ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j (wtIter wadd wL w0 (∑ i, al i)),
      (∀ β, X.inc _ (z β) = (zPoly X w al θ).coeff β) ∧ ∀ β, z β ∈ B.Mlat j _ := by
  have p0 : ∀ w : WeightFamilies.Wt D j, (0 : B.Cusp j w) ∈ B.Mlat j w := fun w => (B.Mlat j w).zero_mem
  have padd : ∀ (w : WeightFamilies.Wt D j) (x y : B.Cusp j w), x ∈ B.Mlat j w → y ∈ B.Mlat j w → x + y ∈ B.Mlat j w :=
    fun w x y hx hy => (B.Mlat j w).add_mem hx hy
  have pmul : ∀ (w w' : WeightFamilies.Wt D j) (F : B.Cusp j w) (F' : B.Cusp j w'), F ∈ B.Mlat j w → F' ∈ B.Mlat j w' →
      ∃ H : B.Cusp j (wadd w w'),
        (X.inc _).toAddMonoidHom H = (X.inc w).toAddMonoidHom F * (X.inc w').toAddMonoidHom F' ∧
          H ∈ B.Mlat j _ := fun w w' F F' hF hF' => gp_mlat_mul X w w' F F' hF hF'
  have hs : ∀ i : Fin (WeightFamilies.dimY D j), Cf (fun w => (X.inc w).toAddMonoidHom) (fun w F => F ∈ B.Mlat j w) wL
      (∑ k, MvPolynomial.X (i.succ, k) * MvPolynomial.C (X.inc wL (w k))) :=
    fun i => Cf_lin p0 padd (fun k => (i.succ, k)) w hw
  exact Cf_word p0 padd pmul _ hs θ hθ al

end GPPacket

open Module

/- English proof (translation)
Distinguish the cases in `ha : r = 0`. Rewrite using `[ha, IsDiscreteValuationRing.addVal_zero]`. Conclude with `le_top`. Use `set Zsat : Submodule R V1 := M1 ⊓ (Submodule.span F (Set.range z)).restrictScalars R with hZsat`. Set `U : Submodule F V1` to `Submodule.span F (Set.range z)`.

Set `bz : Basis (Fin ρ) F U` to `Basis.span hli`. Establish `hbz : ∀ k, ((bz k : U) : V1) = z k` using `fun k => congrArg Subtype.val (Basis.span_apply hli k)`. Establish `: FiniteDimensional F U` using `Module.Finite.of_basis bz`. Establish `hfr : finrank F U = ρ` using `by rw [finrank_eq_card_basis bz]; simp`. Set `ι : U →ₗ[R] V1` to `U.subtype.restrictScalars R`.

Establish `hι : Function.Injective ι` using `Subtype.val_injective`. Set `S : Submodule R U` to `M1.comap ι`. Set `T : Submodule R U` to `Submodule.span R (Set.range bz)`. Establish `hTS : T ≤ S`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Use `show ((bz k : U) : V1) ∈ M1`. Rewrite using `[hbz]`. Conclude with `hz k`. Establish `hTlat : Formalism.LatticeIndexTer.IsLat R F U T`.

Use `⟨Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← bz.span_eq]`. Conclude with `Submodule.span_mono Submodule.subset_span`. Establish `hSlat : Formalism.LatticeIndexTer.IsLat R F U S`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Apply `Submodule.fg_of_fg_map_injective ι hι` to reduce the goal to its premises. Conclude with `hfg.of_le (Submodule.map_comap_le _ _)`. Rewrite using `[eq_top_iff, ← hTlat.2]`. Conclude with `Submodule.span_mono hTS`. Take `⟨w0, hw0⟩` from `Formalism.LatticeIndexTer.lattice_has_basis R F U S hSlat`.

Set `w : Basis (Fin ρ) F U` to `w0.reindex (finCongr hfr)`. Establish `hw : S = Submodule.span R (Set.range w)`. Rewrite using `[Basis.range_reindex]`. Conclude with `hw0`. Establish `hwM : ∀ l, ((w l : U) : V1) ∈ M1`.

Introduce `l`. Establish `: w l ∈ S` using `by rw [hw]; exact Submodule.subset_span ⟨l, rfl⟩`. Conclude with `this`. Establish `hint : ∀ l i, ∃ c : R, algebraMap R F c = φ i ((w l : U) : V1)` using `fun l i => hφ i _ (hwM l)`. Use `choose W0 hW0 using hint`.

Set `Wm : Matrix (Fin ρ) (Fin ρ) R` to `Matrix.of fun i l => W0 l i`. Set `C : Matrix (Fin ρ) (Fin ρ) F` to `LinearMap.toMatrix bz w ((LinearEquiv.refl F U : U ≃ₗ[F] U) : U →ₗ[F] U)`. Establish `hprod : (Matrix.of fun i k => φ i (z k)) = (algebraMap R F).mapMatrix Wm * C`. Use extensionality with `i k`. Rewrite using `[Matrix.mul_apply]`.

Establish `h1 : z k = ∑ l, w.repr (bz k) l • ((w l : U) : V1)`. Establish `h` using `congrArg U.subtype (w.sum_repr (bz k))`. Rewrite `h` using `[map_sum]`. Rewrite using `[← hbz k]`. Simplify using `using h.symm`.

Simplify using `only [Matrix.of_apply]`. Rewrite using `[h1]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [C, Wm, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, LinearMap.toMatrix_apply, hW0]`.

Simplify using `[mul_comm]`. Establish `hdetprod : (Matrix.of fun i k => φ i (z k)).det = algebraMap R F Wm.det * C.det`. Rewrite using `[hprod, Matrix.det_mul, ← RingHom.map_det]`. Establish `hinj` using `IsFractionRing.injective R F`. Establish `haK : algebraMap R F r ≠ 0` using `fun h => ha (hinj (by rw [h, map_zero]))`.

Establish `hC0 : C.det ≠ 0`. Introduce `h`. Apply `haK` to reduce the goal to its premises. Rewrite using `[hr, hdetprod, h]`. Simplify using the standard rewrite rules.

Take `⟨a1, b1, hb1, hab⟩` from `IsFractionRing.div_surjective (A := R) C.det`. Establish `hb10 : b1 ≠ 0` using `nonZeroDivisors.ne_zero hb1`. Establish `hb1K : algebraMap R F b1 ≠ 0` using `fun h => hb10 (hinj (by rw [h, map_zero]))`. Establish `ha1eq : algebraMap R F a1 = C.det * algebraMap R F b1`. Rewrite using `[← hab]`.

Clear the denominators using the available nonvanishing facts. Establish `ha10 : a1 ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha1eq` using `[map_zero]`. Conclude with `(mul_ne_zero hC0 hb1K) ha1eq.symm`.

Establish `hidx` using `Formalism.LatticeIndexTer.lattice_index_eq_det_valuation R F U U (Fin ρ) bz w (LinearEquiv.refl F U) a1 b1 ha10 hb10 ha1eq`. Establish `hmapid : (Submodule.span R (Set.range bz)).map (((LinearEquiv.refl F U : U ≃ₗ[F] U) : U →ₗ[F] U).restrictScalars R) = T`. Use extensionality with `x`. Simplify using `[T]`. Rewrite `hidx` using `[hmapid, ← hw]`.

Establish `hrel : r * b1 = Wm.det * a1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, hr, hdetprod, ha1eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hW0ne : Wm.det ≠ 0`.

Introduce and unpack `h`. Rewrite `hrel` using `[h]`. Simplify using `at hrel`. Break down `hrel with h | h` into its components or cases. Conclude with `ha h`.

Conclude with `hb10 h`. Establish `hv : ∀ x : R, x ≠ 0 → IsDiscreteValuationRing.addVal R x ≠ ⊤`. Introduce `x hx h`. Conclude with `hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)`. Establish `hval : (IsDiscreteValuationRing.addVal R r).toNat + (IsDiscreteValuationRing.addVal R b1).toNat = (IsDiscreteValuationRing.addVal R Wm.det).toNat + (IsDiscreteValuationRing.addVal R a1).toNat`.

Use `congrArg (fun x => (IsDiscreteValuationRing.addVal R x).toNat) hrel` as an intermediate fact. Simplify using `only [IsDiscreteValuationRing.addVal_mul] at this`. Rewrite `this` using `[ENat.toNat_add (hv _ ha) (hv _ hb10), ENat.toNat_add (hv _ hW0ne) (hv _ ha10)]`. Conclude with `this`. Establish `hfin : Formalism.LatticeIndexTer.qlen R U S T ≠ ⊤` using `Formalism.LatticeIndexTer.lattice_quotient_finite R F U S T hSlat hTlat`.

Establish `hzero : Formalism.LatticeIndexTer.qlen R U T S = 0`. Unfold `Formalism.LatticeIndexTer.qlen`. Rewrite using `[Submodule.comap_subtype_eq_top.2 hTS]`. Conclude with `Module.length_eq_zero`. Set `g : S →ₗ[R] Zsat` to `LinearMap.codRestrict Zsat (ι ∘ₗ S.subtype) (fun x => ⟨x.2, x.1.2⟩)`.

Establish `hgT : T.comap S.subtype ≤ (Z.comap Zsat.subtype).comap g`. Introduce `x hx`. Establish `hTZ : T.map ι ≤ Z`. Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Use `show ((bz k : U) : V1) ∈ Z`. Rewrite using `[hbz]`. Conclude with `hZ1 (Submodule.subset_span ⟨k, rfl⟩)`. Conclude with `hTZ ⟨x.1, hx, rfl⟩`. Establish `hsurj : Function.Surjective (Submodule.mapQ _ _ g hgT)`.

Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with | H y => ?_`. Use `⟨Submodule.Quotient.mk ⟨⟨y.1, y.2.2⟩, y.2.1⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Establish `hle : Module.length R (↥Zsat ⧸ Z.comap Zsat.subtype) ≤ Formalism.LatticeIndexTer.qlen R U S T` using `Module.length_le_of_surjective _ hsurj`.

Use `hle.trans ?_` and prove the remaining obligations. Rewrite using `[← ENat.natCast_toNat hfin, ← ENat.natCast_toNat (hv _ ha)]`. Unfold `Formalism.LatticeIndexTer.idx at hidx`. Rewrite `hidx` using `[hzero]`. Simplify using `only [ENat.toNat_zero, Nat.cast_zero, sub_zero] at hidx`.

Establish `: (Formalism.LatticeIndexTer.qlen R U S T).toNat ≤ (IsDiscreteValuationRing.addVal R r).toNat` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem len_sat_le {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] {V1 : Type} [AddCommGroup V1] [Module F V1] [Module R V1] [IsScalarTower R F V1]
    (M1 : Submodule R V1) (hfg : M1.FG) {ρ : ℕ} (z : Fin ρ → V1) (hz : ∀ k, z k ∈ M1)
    (hli : LinearIndependent F z) (Z : Submodule R V1) (hZ1 : Submodule.span R (Set.range z) ≤ Z)
    (φ : Fin ρ → V1 →ₗ[F] F) (hφ : ∀ i, ∀ f ∈ M1, φ i f ∈ Set.range (algebraMap R F)) (r : R)
    (hr : algebraMap R F r = (Matrix.of fun i k => φ i (z k)).det) :
    Module.length R (↥(M1 ⊓ (Submodule.span F (Set.range z)).restrictScalars R) ⧸
      Z.comap (M1 ⊓ (Submodule.span F (Set.range z)).restrictScalars R).subtype) ≤
      IsDiscreteValuationRing.addVal R r := by
  classical
  by_cases ha : r = 0
  · rw [ha, IsDiscreteValuationRing.addVal_zero]; exact le_top
  set Zsat : Submodule R V1 := M1 ⊓ (Submodule.span F (Set.range z)).restrictScalars R with hZsat
  let U : Submodule F V1 := Submodule.span F (Set.range z)
  let bz : Basis (Fin ρ) F U := Basis.span hli
  have hbz : ∀ k, ((bz k : U) : V1) = z k := fun k => congrArg Subtype.val (Basis.span_apply hli k)
  have : FiniteDimensional F U := Module.Finite.of_basis bz
  have hfr : finrank F U = ρ := by rw [finrank_eq_card_basis bz]; simp
  let ι : U →ₗ[R] V1 := U.subtype.restrictScalars R
  have hι : Function.Injective ι := Subtype.val_injective
  let S : Submodule R U := M1.comap ι
  let T : Submodule R U := Submodule.span R (Set.range bz)
  have hTS : T ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show ((bz k : U) : V1) ∈ M1
    rw [hbz]; exact hz k
  have hTlat : Formalism.LatticeIndexTer.IsLat R F U T := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← bz.span_eq]
    exact Submodule.span_mono Submodule.subset_span
  have hSlat : Formalism.LatticeIndexTer.IsLat R F U S := by
    refine ⟨?_, ?_⟩
    · apply Submodule.fg_of_fg_map_injective ι hι
      exact hfg.of_le (Submodule.map_comap_le _ _)
    · rw [eq_top_iff, ← hTlat.2]
      exact Submodule.span_mono hTS
  obtain ⟨w0, hw0⟩ := Formalism.LatticeIndexTer.lattice_has_basis R F U S hSlat
  let w : Basis (Fin ρ) F U := w0.reindex (finCongr hfr)
  have hw : S = Submodule.span R (Set.range w) := by
    rw [Basis.range_reindex]; exact hw0
  have hwM : ∀ l, ((w l : U) : V1) ∈ M1 := by
    intro l
    have : w l ∈ S := by rw [hw]; exact Submodule.subset_span ⟨l, rfl⟩
    exact this

  have hint : ∀ l i, ∃ c : R, algebraMap R F c = φ i ((w l : U) : V1) := fun l i => hφ i _ (hwM l)
  choose W0 hW0 using hint
  let Wm : Matrix (Fin ρ) (Fin ρ) R := Matrix.of fun i l => W0 l i
  let C : Matrix (Fin ρ) (Fin ρ) F :=
    LinearMap.toMatrix bz w ((LinearEquiv.refl F U : U ≃ₗ[F] U) : U →ₗ[F] U)
  have hprod : (Matrix.of fun i k => φ i (z k)) = (algebraMap R F).mapMatrix Wm * C := by
    ext i k
    rw [Matrix.mul_apply]
    have h1 : z k = ∑ l, w.repr (bz k) l • ((w l : U) : V1) := by
      have h := congrArg U.subtype (w.sum_repr (bz k))
      rw [map_sum] at h
      rw [← hbz k]
      simpa using h.symm
    simp only [Matrix.of_apply]
    rw [h1]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [C, Wm, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      LinearMap.toMatrix_apply, hW0]
    simp [mul_comm]
  have hdetprod : (Matrix.of fun i k => φ i (z k)).det = algebraMap R F Wm.det * C.det := by
    rw [hprod, Matrix.det_mul, ← RingHom.map_det]
  have hinj := IsFractionRing.injective R F
  have haK : algebraMap R F r ≠ 0 := fun h => ha (hinj (by rw [h, map_zero]))
  have hC0 : C.det ≠ 0 := by
    intro h
    apply haK
    rw [hr, hdetprod, h]; simp
  obtain ⟨a1, b1, hb1, hab⟩ := IsFractionRing.div_surjective (A := R) C.det
  have hb10 : b1 ≠ 0 := nonZeroDivisors.ne_zero hb1
  have hb1K : algebraMap R F b1 ≠ 0 := fun h => hb10 (hinj (by rw [h, map_zero]))
  have ha1eq : algebraMap R F a1 = C.det * algebraMap R F b1 := by
    rw [← hab]; field_simp
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha1eq
    exact (mul_ne_zero hC0 hb1K) ha1eq.symm
  have hidx := Formalism.LatticeIndexTer.lattice_index_eq_det_valuation R F U U (Fin ρ) bz w (LinearEquiv.refl F U) a1 b1 ha10 hb10 ha1eq
  have hmapid : (Submodule.span R (Set.range bz)).map
      (((LinearEquiv.refl F U : U ≃ₗ[F] U) : U →ₗ[F] U).restrictScalars R) = T := by
    ext x; simp [T]
  rw [hmapid, ← hw] at hidx

  have hrel : r * b1 = Wm.det * a1 := by
    apply hinj
    rw [map_mul, map_mul, hr, hdetprod, ha1eq]; ring
  have hW0ne : Wm.det ≠ 0 := by
    rintro h
    rw [h] at hrel
    simp at hrel
    rcases hrel with h | h
    · exact ha h
    · exact hb10 h
  have hv : ∀ x : R, x ≠ 0 → IsDiscreteValuationRing.addVal R x ≠ ⊤ := by
    intro x hx h
    exact hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have hval : (IsDiscreteValuationRing.addVal R r).toNat + (IsDiscreteValuationRing.addVal R b1).toNat =
      (IsDiscreteValuationRing.addVal R Wm.det).toNat + (IsDiscreteValuationRing.addVal R a1).toNat := by
    have := congrArg (fun x => (IsDiscreteValuationRing.addVal R x).toNat) hrel
    simp only [IsDiscreteValuationRing.addVal_mul] at this
    rw [ENat.toNat_add (hv _ ha) (hv _ hb10), ENat.toNat_add (hv _ hW0ne) (hv _ ha10)] at this
    exact this

  have hfin : Formalism.LatticeIndexTer.qlen R U S T ≠ ⊤ := Formalism.LatticeIndexTer.lattice_quotient_finite R F U S T hSlat hTlat
  have hzero : Formalism.LatticeIndexTer.qlen R U T S = 0 := by
    unfold Formalism.LatticeIndexTer.qlen
    rw [Submodule.comap_subtype_eq_top.2 hTS]
    exact Module.length_eq_zero

  let g : S →ₗ[R] Zsat := LinearMap.codRestrict Zsat (ι ∘ₗ S.subtype) (fun x => ⟨x.2, x.1.2⟩)
  have hgT : T.comap S.subtype ≤ (Z.comap Zsat.subtype).comap g := by
    intro x hx
    have hTZ : T.map ι ≤ Z := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      show ((bz k : U) : V1) ∈ Z
      rw [hbz]; exact hZ1 (Submodule.subset_span ⟨k, rfl⟩)
    exact hTZ ⟨x.1, hx, rfl⟩
  have hsurj : Function.Surjective (Submodule.mapQ _ _ g hgT) := by
    intro y
    induction y using Submodule.Quotient.induction_on with | H y => ?_
    refine ⟨Submodule.Quotient.mk ⟨⟨y.1, y.2.2⟩, y.2.1⟩, ?_⟩
    rfl
  have hle : Module.length R (↥Zsat ⧸ Z.comap Zsat.subtype) ≤ Formalism.LatticeIndexTer.qlen R U S T :=
    Module.length_le_of_surjective _ hsurj
  refine hle.trans ?_
  rw [← ENat.natCast_toNat hfin, ← ENat.natCast_toNat (hv _ ha)]
  unfold Formalism.LatticeIndexTer.idx at hidx
  rw [hzero] at hidx
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero] at hidx
  have : (Formalism.LatticeIndexTer.qlen R U S T).toNat ≤ (IsDiscreteValuationRing.addVal R r).toNat := by omega
  exact_mod_cast this

section Br

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {ι : Type}

/- English proof (translation)
Take `⟨S, hS⟩` from `hfgM`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (Finset.univ.biUnion fun i : Fin ρ => S.image fun s => φ i s)`. Use `⟨algebraMap (𝓞 K) K b, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr (nonZeroDivisors.ne_zero b.2)`. Introduce `i f hf`.

Rewrite `hf` using `[← hS]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy⟩` from `hb (φ i x) (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩)`. Rewrite using `[LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def, ← hy]`.

Conclude with `la.valuation_le_one y`. Consider the case `zero => rw [map_zero, map_zero]`. Conclude with `zero_le_one`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `(Valuation.map_add_le _ hx hy)`.

Consider the case `smul o x _ hx`. Rewrite using `[← IsScalarTower.algebraMap_smul K o x, map_smul, smul_eq_mul, map_mul]`. Conclude with `mul_le_one' (la.valuation_le_one o) hx`.
-/
theorem br_scale {M : Submodule (𝓞 K) V} (hfgM : M.FG) (la : HeightOneSpectrum (𝓞 K)) {ρ : ℕ}
    (φ : Fin ρ → V →ₗ[K] K) :
    ∃ t : K, t ≠ 0 ∧ ∀ i, ∀ f ∈ M, la.valuation K ((t • φ i) f) ≤ 1 := by
  classical
  obtain ⟨S, hS⟩ := hfgM
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.biUnion fun i : Fin ρ => S.image fun s => φ i s)
  refine ⟨algebraMap (𝓞 K) K b, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr (nonZeroDivisors.ne_zero b.2)
  · intro i f hf
    rw [← hS] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hb (φ i x) (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩)
      rw [LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def, ← hy]
      exact la.valuation_le_one y
    | zero => rw [map_zero, map_zero]; exact zero_le_one
    | add x y _ _ hx hy => rw [map_add]; exact (Valuation.map_add_le _ hx hy)
    | smul o x _ hx =>
      rw [← IsScalarTower.algebraMap_smul K o x, map_smul, smul_eq_mul, map_mul]
      exact mul_le_one' (la.valuation_le_one o) hx

/- English proof (translation)
Take `⟨φ, hφ⟩` from `hW`. Take `⟨t, ht0, ht⟩` from `br_scale hfgM la φ`. Establish `hne : detPoly (fun i => t • φ i) z ≠ 0`. Rewrite using `[detPoly_smul]`. Conclude with `mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective ι K)).mpr (pow_ne_zero _ ht0)) hφ`.

Take `⟨β, hβ⟩` from `MvPolynomial.ne_zero_iff.mp hne`. Establish `h0 : 0 ≤ vAdd la ((detPoly (fun i => t • φ i) z).coeff β)` using `(val_le_one_iff la hβ).mp (gc_coeff_int hz la _ ht β)`. Take `⟨n, hn⟩` from `Int.eq_ofNat_of_zero_le h0`. Establish `hmem : ({n : ℕ | ∃ (φ : Fin ρ → V →ₗ[K] K) (β : ι →₀ ℕ), (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) ∧ (detPoly φ z).coeff β ≠ 0 ∧ vAdd la ((detPoly φ z).coeff β) = (n : ℤ)}).Nonempty` using `⟨n, _, β, ht, hβ, hn⟩`. Conclude with `Nat.sInf_mem hmem`.
-/
theorem br_nonempty {M : Submodule (𝓞 K) V} (hfgM : M.FG) {ρ : ℕ} {z : Fin ρ → (ι →₀ ℕ) →₀ V}
    (hz : ∀ k β, z k β ∈ M) (hW : ∃ φ : Fin ρ → V →ₗ[K] K, detPoly φ z ≠ 0) (la : HeightOneSpectrum (𝓞 K)) :
    ∃ (φ : Fin ρ → V →ₗ[K] K) (β : ι →₀ ℕ), (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) ∧
      (detPoly φ z).coeff β ≠ 0 ∧ vAdd la ((detPoly φ z).coeff β) = (gaussC M z la : ℤ) := by
  obtain ⟨φ, hφ⟩ := hW
  obtain ⟨t, ht0, ht⟩ := br_scale hfgM la φ
  have hne : detPoly (fun i => t • φ i) z ≠ 0 := by
    rw [detPoly_smul]
    exact mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective ι K)).mpr (pow_ne_zero _ ht0)) hφ
  obtain ⟨β, hβ⟩ := MvPolynomial.ne_zero_iff.mp hne
  have h0 : 0 ≤ vAdd la ((detPoly (fun i => t • φ i) z).coeff β) :=
    (val_le_one_iff la hβ).mp (gc_coeff_int hz la _ ht β)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
  have hmem : ({n : ℕ | ∃ (φ : Fin ρ → V →ₗ[K] K) (β : ι →₀ ℕ), (∀ i, ∀ f ∈ M, la.valuation K (φ i f) ≤ 1) ∧
      (detPoly φ z).coeff β ≠ 0 ∧ vAdd la ((detPoly φ z).coeff β) = (n : ℤ)}).Nonempty :=
    ⟨n, _, β, ht, hβ, hn⟩
  exact Nat.sInf_mem hmem

/- English proof (translation)
Take `⟨φ, β, hφ, hβ, hv⟩` from `br_nonempty hfgM hz hW la`. Use `set z1 : Fin ρ → V1 := fun k => ∑ β ∈ (z k).support, jF (MvPolynomial.monomial β 1) • u (z k β) with hz1def`. Use `set M1 : Submodule R V1 := Submodule.span R (u '' (M : Set V)) with hM1`. Use `choose φ1 hφ1 using fun i => hext (φ i)`. Establish `hφ1M : ∀ i, ∀ f ∈ M1, φ1 i f ∈ Set.range (algebraMap R F)`.

Introduce `i f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, hm, rfl⟩` from `hx`. Rewrite using `[hφ1]`.

Conclude with `hint _ (hφ i m hm)`. Consider the case `zero => exact ⟨0, by rw [map_zero, map_zero]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Conclude with `⟨a + b, by rw [map_add, map_add, ha, hb]⟩`. Consider the case `smul r x _ hx`. Take `⟨a, ha⟩` from `hx`. Conclude with `⟨r * a, by rw [← IsScalarTower.algebraMap_smul F r x, map_smul, smul_eq_mul, map_mul, ha]⟩`. Establish `hz1 : ∀ k, z1 k ∈ M1`.

Introduce `k`. Use `Submodule.sum_mem _ fun γ _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `hmon γ`. Rewrite using `[← hr, IsScalarTower.algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz k γ, rfl⟩)`.

Establish `hent : ∀ i k, φ1 i (z1 k) = jF (polyOf (φ i) (z k))`. Introduce `i k`. Rewrite using `[hz1def, polyOf_eq_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, hφ1, ← map_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]`.

Establish `hdet : (Matrix.of fun i k => φ1 i (z1 k)).det = jF (detPoly φ z)`. Unfold `detPoly`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use function extensionality and compare the values at `i k`.

Simplify using `[hent]`. Establish `hdetR : (Matrix.of fun i k => φ1 i (z1 k)).det ∈ (algebraMap R F).range` using `gc_det_mem _ _ fun i k => hφ1M i _ (hz1 k)`. Take `⟨r, hr⟩` from `hdetR`. Establish `hle` using `hgv (detPoly φ z) β r hβ (hr.trans hdet)`. Establish `hr0 : r ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hle` using `[IsDiscreteValuationRing.addVal_zero]`. Conclude with `absurd hle (by simp)`. Establish `hdet0 : (Matrix.of fun i k => φ1 i (z1 k)).det ≠ 0`. Rewrite using `[← hr]`.

Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr0`. Establish `hli : LinearIndependent F z1`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `hmv : (Matrix.of fun i k => φ1 i (z1 k)).mulVec g = 0`.

Use function extensionality and compare the values at `i`. Use `congrArg (φ1 i) hg` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Simplify using `only [map_smul, smul_eq_mul] at this`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]`.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Use `Matrix.eq_zero_of_mulVec_eq_zero hdet0 hmv` as an intermediate fact. Conclude with `fun k => congrFun this k`. Establish `hfg1 : M1.FG`.

Take `⟨S, hS⟩` from `hfgM`. Establish `hsub : M1 = Submodule.span R (u '' (S : Set V))`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[hM1, Submodule.span_le]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`.

Rewrite `hm` using `[SetLike.mem_coe, ← hS]`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul o x _ hx`. Take `⟨r', hr'⟩` from `hint (algebraMap (𝓞 K) K o) (la.valuation_le_one o)`. Rewrite using `[← IsScalarTower.algebraMap_smul K o x, hu, ← hr', SetLike.mem_coe, IsScalarTower.algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Use `Submodule.span_mono (Set.image_mono ?_)` and prove the remaining obligations. Rewrite using `[← hS]`. Conclude with `Submodule.subset_span`. Rewrite using `[hsub]`.

Conclude with `Submodule.fg_span ((Finset.finite_toSet S).image _)`. Use `(len_sat_le M1 hfg1 z1 hz1 hli Z hZ φ1 hφ1M r hr).trans (hle.trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[hv, Int.toNat_natCast]`.
-/
theorem len_le_gaussC {M : Submodule (𝓞 K) V} (hfgM : M.FG) {ρ : ℕ} {z : Fin ρ → (ι →₀ ℕ) →₀ V}
    (hz : ∀ k β, z k β ∈ M) (hW : ∃ φ : Fin ρ → V →ₗ[K] K, detPoly φ z ≠ 0) (la : HeightOneSpectrum (𝓞 K))
    {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (jF : MvPolynomial ι K →+* F)
    (hint : ∀ a : K, la.valuation K a ≤ 1 → jF (MvPolynomial.C a) ∈ Set.range (algebraMap R F))
    (hmon : ∀ β : ι →₀ ℕ, jF (MvPolynomial.monomial β 1) ∈ Set.range (algebraMap R F))
    (hgv : ∀ (p : MvPolynomial ι K) (β : ι →₀ ℕ) (r : R), p.coeff β ≠ 0 → algebraMap R F r = jF p →
      IsDiscreteValuationRing.addVal R r ≤ ((vAdd la (p.coeff β)).toNat : ℕ∞))
    {V1 : Type} [AddCommGroup V1] [Module F V1] [Module R V1] [IsScalarTower R F V1]
    (u : V →+ V1) (hu : ∀ (a : K) f, u (a • f) = jF (MvPolynomial.C a) • u f)
    (hext : ∀ φ : V →ₗ[K] K, ∃ φ1 : V1 →ₗ[F] F, ∀ f, φ1 (u f) = jF (MvPolynomial.C (φ f)))
    (Z : Submodule R V1)
    (hZ : Submodule.span R (Set.range fun k => ∑ β ∈ (z k).support, jF (MvPolynomial.monomial β 1) • u (z k β)) ≤ Z) :
    Module.length R (↥(Submodule.span R (u '' (M : Set V)) ⊓ (Submodule.span F (Set.range fun k =>
        ∑ β ∈ (z k).support, jF (MvPolynomial.monomial β 1) • u (z k β))).restrictScalars R) ⧸
      Z.comap (Submodule.span R (u '' (M : Set V)) ⊓ (Submodule.span F (Set.range fun k =>
        ∑ β ∈ (z k).support, jF (MvPolynomial.monomial β 1) • u (z k β))).restrictScalars R).subtype) ≤
      (gaussC M z la : ℕ∞) := by
  classical
  obtain ⟨φ, β, hφ, hβ, hv⟩ := br_nonempty hfgM hz hW la
  set z1 : Fin ρ → V1 := fun k => ∑ β ∈ (z k).support, jF (MvPolynomial.monomial β 1) • u (z k β) with hz1def
  set M1 : Submodule R V1 := Submodule.span R (u '' (M : Set V)) with hM1
  choose φ1 hφ1 using fun i => hext (φ i)

  have hφ1M : ∀ i, ∀ f ∈ M1, φ1 i f ∈ Set.range (algebraMap R F) := by
    intro i f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      rw [hφ1]; exact hint _ (hφ i m hm)
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨r * a, by rw [← IsScalarTower.algebraMap_smul F r x, map_smul, smul_eq_mul, map_mul, ha]⟩

  have hz1 : ∀ k, z1 k ∈ M1 := by
    intro k
    refine Submodule.sum_mem _ fun γ _ => ?_
    obtain ⟨r, hr⟩ := hmon γ
    rw [← hr, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz k γ, rfl⟩)

  have hent : ∀ i k, φ1 i (z1 k) = jF (polyOf (φ i) (z k)) := by
    intro i k
    rw [hz1def, polyOf_eq_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_smul, smul_eq_mul, hφ1, ← map_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  have hdet : (Matrix.of fun i k => φ1 i (z1 k)).det = jF (detPoly φ z) := by
    unfold detPoly
    rw [RingHom.map_det]
    congr 1
    funext i k
    simp [hent]
  have hdetR : (Matrix.of fun i k => φ1 i (z1 k)).det ∈ (algebraMap R F).range :=
    gc_det_mem _ _ fun i k => hφ1M i _ (hz1 k)
  obtain ⟨r, hr⟩ := hdetR
  have hle := hgv (detPoly φ z) β r hβ (hr.trans hdet)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [IsDiscreteValuationRing.addVal_zero] at hle
    exact absurd hle (by simp)
  have hdet0 : (Matrix.of fun i k => φ1 i (z1 k)).det ≠ 0 := by
    rw [← hr]; exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr0
  have hli : LinearIndependent F z1 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hmv : (Matrix.of fun i k => φ1 i (z1 k)).mulVec g = 0 := by
      funext i
      have := congrArg (φ1 i) hg
      rw [map_sum, map_zero] at this
      simp only [map_smul, smul_eq_mul] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet0 hmv
    exact fun k => congrFun this k

  have hfg1 : M1.FG := by
    obtain ⟨S, hS⟩ := hfgM
    have hsub : M1 = Submodule.span R (u '' (S : Set V)) := by
      apply le_antisymm
      · rw [hM1, Submodule.span_le]
        rintro _ ⟨m, hm, rfl⟩
        rw [SetLike.mem_coe, ← hS] at hm
        induction hm using Submodule.span_induction with
        | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
        | smul o x _ hx =>
          obtain ⟨r', hr'⟩ := hint (algebraMap (𝓞 K) K o) (la.valuation_le_one o)
          rw [← IsScalarTower.algebraMap_smul K o x, hu, ← hr', SetLike.mem_coe, IsScalarTower.algebraMap_smul]
          exact Submodule.smul_mem _ _ hx
      · refine Submodule.span_mono (Set.image_mono ?_)
        rw [← hS]; exact Submodule.subset_span
    rw [hsub]
    exact Submodule.fg_span ((Finset.finite_toSet S).image _)
  refine (len_sat_le M1 hfg1 z1 hz1 hli Z hZ φ1 hφ1M r hr).trans (hle.trans (le_of_eq ?_))
  rw [hv, Int.toNat_natCast]

end Br

section Final

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

/- English proof (translation)
Substitute `hwt` using the available equality. Establish `h : ∀ k, ∃ zk : ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j (wtIter wadd wL w0 a0), (∀ β, X.inc _ (zk β) = (zPoly X w (al k) (th k)).coeff β) ∧ ∀ β, zk β ∈ B.Mlat j _`. Introduce `k`. Use `zPoly_cf X w hw (al k) (th k) (hth k)` as an intermediate fact. Rewrite `this` using `[hal k]`. Then use the resulting hypothesis.

Use `choose z hz1 hz2 using h`. Conclude with `⟨z, hz1, hz2⟩`.
-/
theorem exists_zFam (X : PJ D B P j) (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (hw : ∀ k, w k ∈ B.Mlat j wL) (th : Fin ρ → B.Cusp j w0)
    (hth : ∀ k, th k ∈ B.Mlat j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ) (hal : ∀ k, ∑ i, al k i = a0) :
    ∃ z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka,
      (∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β) ∧ ∀ k β, z k β ∈ B.Mlat j ka := by
  subst hwt
  have h : ∀ k, ∃ zk : ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j (wtIter wadd wL w0 a0),
      (∀ β, X.inc _ (zk β) = (zPoly X w (al k) (th k)).coeff β) ∧ ∀ β, zk β ∈ B.Mlat j _ := by
    intro k
    have := zPoly_cf X w hw (al k) (th k) (hth k)
    rwa [hal k] at this
  choose z hz1 hz2 using h
  exact ⟨z, hz1, hz2⟩

/- English proof (translation)
Take `⟨z', hz1, hz2⟩` from `exists_zFam X ka wL w0 a0 hwt w hw th hthM al hal`. Establish `hzM : ∀ k β, z k β ∈ B.Mlat j ka`. Introduce `k β`. Establish `: z k β = z' k β` using `X.inc_inj ka ((hz k β).trans (hz1 k β).symm)`. Rewrite using `[this]`.

Conclude with `hz2 k β`. Conclude with `deepPacket large₂ X h1 h2 ka wL w0 a0 hwt w th al hal z hz _ (fun la => gaussC_nonneg _ z la) (gaussC_gaussLe hzM) hW Hm (fun Ctr hC => trans_of_minima transference_successive_minima _ (hlat j h1 h2 ka).span_eq_top Hm hconj Ctr hC) hSM CL AL hLAM G Prw Pd hS2 hG0 hPrw mx hmx hmxm …`.
-/
theorem deepFinal (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (hw : ∀ k, w k ∈ B.Mlat j wL) (th : Fin ρ → B.Cusp j w0)
    (hthM : ∀ k, th k ∈ B.Mlat j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ) (hal : ∀ k, ∑ i, al k i = a0)
    (z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka)
    (hz : ∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β)
    (hW : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, detPoly φ z ≠ 0)
    (hlat : WeightAlgebra.adm1 B) {dH : ℕ} (Hm : Herm (fun σ => B.l2NormAlt j ka σ) dH) (hconj : Hm.Conj)
    (hSM : SubMul X) (CL AL : ℝ) (hLAM : WeightAlgebra.adm5 large₂ B CL AL) (G Prw Pd : ℝ)
    (hS2 : ∀ σ (F : B.Cusp j ka), B.supN j ka σ F ^ 2 ≤ Real.exp Pd * B.l2NormAlt j ka σ F ^ 2)
    (hG0 : 0 ≤ G) (hPrw : 0 ≤ Prw)
    (mx : (B.KO →+* ℂ) → ℝ) (hmx : ∀ σ k, B.supN j wL σ (w k) ≤ Real.exp (mx σ))
    (hmxm : (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size)
    (hth : ∀ k, WeightFamilies.meanLogSup B (th k) ≤ G * w0.size)
    (ha : (a0 : ℝ) ≤ ka.size) (hrw : Real.log N ≤ Prw * (wL.size - 1))
    (hd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd) (hO : OPO large₂ B) :
    Summable (fun la => (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la) ∧
      ∑' la, (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la ≤
        ρ * ((2 * G + Prw + WeightFamilies.PP0v D large₂ CL AL + (3 / 2) * (Pd + PO D large₂)) * ka.size) := by
  obtain ⟨z', hz1, hz2⟩ := exists_zFam X ka wL w0 a0 hwt w hw th hthM al hal
  have hzM : ∀ k β, z k β ∈ B.Mlat j ka := by
    intro k β
    have : z k β = z' k β := X.inc_inj ka ((hz k β).trans (hz1 k β).symm)
    rw [this]; exact hz2 k β
  exact deepPacket large₂ X h1 h2 ka wL w0 a0 hwt w th al hal z hz _ (fun la => gaussC_nonneg _ z la)
    (gaussC_gaussLe hzM) hW Hm
    (fun Ctr hC => trans_of_minima transference_successive_minima _ (hlat j h1 h2 ka).span_eq_top Hm hconj Ctr hC)
    hSM CL AL hLAM G Prw Pd hS2 hG0 hPrw mx hmx hmxm hth ha hrw hd hO

/- English proof (translation)
Consider the cases of `a`. Consider the cases of `b`. Simplify using `only at h1 h2 h3`. Substitute `h1` using the available equality. Substitute `h2` using the available equality.

Substitute `h3` using the available equality. Both sides reduce to the same expression.
-/
theorem weight_ext (a b : WeightFamilies.Wt D j) (h1 : a.aP = b.aP) (h2 : a.aM = b.aM) (h3 : a.n = b.n) : a = b := by
  cases a; cases b; simp only at h1 h2 h3; subst h1; subst h2; subst h3; rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [wtIter]`. Consider the case `succ m ih => simp only [wtIter, wadd]`. Rewrite using `[ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_iterate_positive_part (wL w0 : WeightFamilies.Wt D j) (m : ℕ) (τ i) :
    (wtIter wadd wL w0 m).aP τ i = w0.aP τ i + m * wL.aP τ i := by
  induction m with
  | zero => simp [wtIter]
  | succ m ih => simp only [wtIter, wadd]; rw [ih]; ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [wtIter]`. Consider the case `succ m ih => simp only [wtIter, wadd]`. Rewrite using `[ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_iterate_negative_part (wL w0 : WeightFamilies.Wt D j) (m : ℕ) (τ i) :
    (wtIter wadd wL w0 m).aM τ i = w0.aM τ i + m * wL.aM τ i := by
  induction m with
  | zero => simp [wtIter]
  | succ m ih => simp only [wtIter, wadd]; rw [ih]; ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [wtIter]`. Consider the case `succ m ih => simp only [wtIter, wadd]`. Rewrite using `[ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_iterate_n (wL w0 : WeightFamilies.Wt D j) (m : ℕ) : (wtIter wadd wL w0 m).n = w0.n + m * wL.n := by
  induction m with
  | zero => simp [wtIter]
  | succ m ih => simp only [wtIter, wadd]; rw [ih]; ring

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hF`. Take `⟨a, rfl⟩` from `Nat.exists_eq_add_of_le hD`. Establish `ha : WeightFamilies.dimY D j + a - WeightFamilies.dimY D j = a` using `by omega`. Rewrite using `[ha]`. Apply `weight_ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `τ i`. Rewrite using `[weight_iterate_positive_part]`. Use `h2 τ i` as an intermediate fact. Simplify using `only [PJ.wF0, wadd, wsmul]`. Move the coercions through the operations in `at this`.

Use `zify`. Combine the linear equalities and inequalities to obtain the conclusion. Use function extensionality and compare the values at `τ i`. Rewrite using `[weight_iterate_negative_part]`. Use `h3 τ i` as an intermediate fact.

Simplify using `only [PJ.wF0, wadd, wsmul]`. Move the coercions through the operations in `at this`. Use `zify`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[weight_iterate_n]`.

Simplify using `only [PJ.wF0, wadd, wsmul]`. Rewrite using `[h1, hn, hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hwt_of (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (hF : IsF' ka wL wF T nP) (hn : wL.n = nW) (hk : ka.n = nP + T * nW) (hD : WeightFamilies.dimY D j ≤ T) :
    wtIter wadd wL (X.wF0 wL wF) (T - WeightFamilies.dimY D j) = ka := by
  obtain ⟨h1, h2, h3⟩ := hF
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hD
  have ha : WeightFamilies.dimY D j + a - WeightFamilies.dimY D j = a := by omega
  rw [ha]
  apply weight_ext
  · funext τ i
    rw [weight_iterate_positive_part]
    have := h2 τ i
    simp only [PJ.wF0, wadd, wsmul]
    push_cast at this
    zify
    linarith
  · funext τ i
    rw [weight_iterate_negative_part]
    have := h3 τ i
    simp only [PJ.wF0, wadd, wsmul]
    push_cast at this
    zify
    linarith
  · rw [weight_iterate_n]
    simp only [PJ.wF0, wadd, wsmul]
    rw [h1, hn, hk]; ring

/- English proof (translation)
Establish `hsz : ∀ w' : WeightFamilies.Wt D j, G * w'.size ≤ max G 0 * w'.size` using `fun w' => mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans (WeightFamilies.Wt.one_le_size w'))`. Conclude with `deepFinal large₂ X h1 h2 ka wL w0 a0 hwt w hw th hthM al hal z hz hW hlat Hm hconj hSM CL AL hLAM (max G 0) Prw Pd (fun σ F => (hS2 j h1 h2 ka F σ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hPd) (sq_nonneg _))) (le_max_right _ _) hPrw mx (fun σ k => (Real.le_exp_log …`.
-/
theorem deepFinal_adm (large₂ : SizeData₂ D) (X : PJ D B P j) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (ka wL w0 : WeightFamilies.Wt D j) (a0 : ℕ) (hwt : wtIter wadd wL w0 a0 = ka) {N ρ : ℕ}
    (w : Fin N → B.Cusp j wL) (hw : ∀ k, w k ∈ B.Mlat j wL) (th : Fin ρ → B.Cusp j w0)
    (hthM : ∀ k, th k ∈ B.Mlat j w0) (al : Fin ρ → Fin (WeightFamilies.dimY D j) → ℕ) (hal : ∀ k, ∑ i, al k i = a0)
    (z : Fin ρ → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka)
    (hz : ∀ k β, X.inc ka (z k β) = (zPoly X w (al k) (th k)).coeff β)
    (hW : ∃ φ : Fin ρ → B.Cusp j ka →ₗ[B.KO] B.KO, detPoly φ z ≠ 0)
    (hlat : WeightAlgebra.adm1 B) {dH : ℕ} (Hm : Herm (fun σ => B.l2NormAlt j ka σ) dH) (hconj : Hm.Conj)
    (hSM : SubMul X) (CL AL CG AG : ℝ) (hLAM : WeightAlgebra.adm5 large₂ B CL AL) (hS2 : WeightFamilies.adm2 large₂ B CG AG)
    (G Prw Pd : ℝ) (hPrw : 0 ≤ Prw)
    (mx : (B.KO →+* ℂ) → ℝ) (hmx : ∀ σ k, Real.log (B.supN j wL σ (w k)) ≤ mx σ)
    (hmxm : (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size)
    (hth : ∀ k, WeightFamilies.meanLogSup B (th k) ≤ G * w0.size)
    (ha : (a0 : ℝ) ≤ ka.size) (hrw : Real.log N ≤ Prw * (wL.size - 1))
    (hd : Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd)
    (hPd : WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd) (hO : OPO large₂ B) :
    Summable (fun la => (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la) ∧
      ∑' la, (gaussC (B.Mlat j ka) z la : ℝ) * X.lN la ≤
        ρ * ((2 * max G 0 + Prw + WeightFamilies.PP0v D large₂ CL AL + (3 / 2) * (Pd + PO D large₂)) * ka.size) := by
  have hsz : ∀ w' : WeightFamilies.Wt D j, G * w'.size ≤ max G 0 * w'.size := fun w' =>
    mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans (WeightFamilies.Wt.one_le_size w'))
  exact deepFinal large₂ X h1 h2 ka wL w0 a0 hwt w hw th hthM al hal z hz hW hlat Hm hconj hSM CL AL hLAM
    (max G 0) Prw Pd
    (fun σ F => (hS2 j h1 h2 ka F σ).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hPd) (sq_nonneg _)))
    (le_max_right _ _) hPrw mx
    (fun σ k => (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (hmx σ k)))
    (hmxm.trans (hsz wL)) (fun k => (hth k).trans (hsz w0)) ha hrw hd hO

end Final

end Formalism.MainNotions.Gaps.SizeBoundsAlt
