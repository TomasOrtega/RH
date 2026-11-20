import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

open Polynomial in

/- English proof (translation)
Use `letI : Algebra F ℂ := τ.toAlgebra`. Establish `hτ : algebraMap F ℂ = τ` using `rfl`. Establish `hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0`. Introduce `k`. Rewrite using `[aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ k) (by simp)`. Establish `hsep : (∏ i, (X - C (r i))).Separable`. Rewrite using `[hr]`. Conclude with `Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen)`. Establish `hinj : Function.Injective r` using `separable_prod_X_sub_C_iff.mp hsep`.

Set `P : Fin δ → (L →+* ℂ)` to `fun k => (pb.lift (r k) (hroot k)).toRingHom`. Establish `hPgen : ∀ k, P k pb.gen = r k` using `fun k => pb.lift_gen (r k) (hroot k)`. Establish `hPinj : Function.Injective P`. Introduce `k l h`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← hPgen, ← hPgen, h]`. Establish `hPτ : ∀ k, (P k).comp (algebraMap F L) = τ`. Introduce `k`. Use extensionality with `x`. Conclude with `(pb.lift (r k) (hroot k)).commutes x`.

Establish `hset : {P : L →+* ℂ | P.comp (algebraMap F L) = τ} = Set.range P`. Use extensionality with `Q`. Prove the components needed by the constructor for the conclusion. Introduce `hQ`. Establish `hQ' : Q.comp (algebraMap F L) = τ` using `hQ`.

Set `Q' : L →ₐ[F] ℂ` to `{ Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }`. Establish `h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0`. Rewrite using `[aeval_algHom_apply, minpoly.aeval, map_zero]`. Rewrite `h0` using `[aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨k, -, hk⟩` from `h0`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hk' : Q' pb.gen = r k` using `by simpa [sub_eq_zero] using hk`. Establish `: pb.lift (r k) (hroot k) = Q'`. Apply `pb.algHom_ext` to reduce the goal to its premises. Rewrite using `[pb.lift_gen, hk']`.

Use `show (pb.lift (r k) (hroot k)).toRingHom = Q`. Rewrite using `[this]`. Introduce and unpack `⟨k, rfl⟩`. Conclude with `hPτ k`. Rewrite using `[hset, finsum_mem_range hPinj, finsum_eq_sum_of_fintype]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hg _ (hPτ k), hPgen]`.
-/
theorem finsum_embeddings_over_eq_sum_roots {F L : Type} [Field F] [Field L] [Algebra F L]
    [Algebra.IsSeparable F L] (pb : PowerBasis F L) (τ : F →+* ℂ) {δ : ℕ} (r : Fin δ → ℂ)
    (hr : ∏ i, (X - C (r i)) = (minpoly F pb.gen).map τ) (g : (L →+* ℂ) → ℝ) (g' : ℂ → ℝ)
    (hg : ∀ P : L →+* ℂ, P.comp (algebraMap F L) = τ → g P = g' (P pb.gen)) :
    ∑ᶠ P ∈ {P : L →+* ℂ | P.comp (algebraMap F L) = τ}, g P = ∑ k, g' (r k) := by
  classical
  letI : Algebra F ℂ := τ.toAlgebra
  have hτ : algebraMap F ℂ = τ := rfl
  have hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0 := by
    intro k
    rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hsep : (∏ i, (X - C (r i))).Separable := by
    rw [hr]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen)
  have hinj : Function.Injective r := separable_prod_X_sub_C_iff.mp hsep
  let P : Fin δ → (L →+* ℂ) := fun k => (pb.lift (r k) (hroot k)).toRingHom
  have hPgen : ∀ k, P k pb.gen = r k := fun k => pb.lift_gen (r k) (hroot k)
  have hPinj : Function.Injective P := by
    intro k l h
    apply hinj
    rw [← hPgen, ← hPgen, h]
  have hPτ : ∀ k, (P k).comp (algebraMap F L) = τ := by
    intro k
    ext x
    exact (pb.lift (r k) (hroot k)).commutes x
  have hset : {P : L →+* ℂ | P.comp (algebraMap F L) = τ} = Set.range P := by
    ext Q
    constructor
    · intro hQ
      have hQ' : Q.comp (algebraMap F L) = τ := hQ
      let Q' : L →ₐ[F] ℂ := { Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }
      have h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0 := by
        rw [aeval_algHom_apply, minpoly.aeval, map_zero]
      rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod, Finset.prod_eq_zero_iff] at h0
      obtain ⟨k, -, hk⟩ := h0
      refine ⟨k, ?_⟩
      have hk' : Q' pb.gen = r k := by simpa [sub_eq_zero] using hk
      have : pb.lift (r k) (hroot k) = Q' := by
        apply pb.algHom_ext
        rw [pb.lift_gen, hk']
      show (pb.lift (r k) (hroot k)).toRingHom = Q
      rw [this]
    · rintro ⟨k, rfl⟩
      exact hPτ k
  rw [hset, finsum_mem_range hPinj, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hg _ (hPτ k), hPgen]

/- English proof (translation)
Introduce `hρ K _ _ σ _ L _ _ _ sg m b Nf hNf`. Use `set R := MvPolynomial σ K with hR`. Use `set F := FractionRing R with hF`. Use `haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)`. Set `pb : PowerBasis F L` to `Field.powerBasisOfFiniteOfSeparable F L`.

Take `⟨ρ, hρm, hρ⟩` from `hρ pb.dim`. Use `choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z`. Set `ev : F → (σ → ℂ) → ℂ` to `fun f t => MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)`. Establish `hpm : ∀ p : R, Measurable fun t : σ → ℂ => MvPolynomial.eval₂ sg t p`. Introduce `p`.

Repeatedly rewrite using `[MvPolynomial.eval₂_eq_eval_map]`. Conclude with `(MvPolynomial.continuous_eval _).measurable`. Establish `hev : ∀ f, Measurable (ev f)` using `fun f => (hpm _).div (hpm _)`. Set `cf : (σ → ℂ) → Fin pb.dim → ℂ` to `fun t i => ev ((minpoly F pb.gen).coeff i) t`. Establish `hcf : Measurable cf` using `measurable_pi_lambda _ fun i => hev _`.

Set `G : (σ → ℂ) → ℂ → ℝ` to `fun t z => Nf fun i => ∑ l : Fin pb.dim, ev (pb.basis.repr (b i) l) t * z ^ (l : ℕ)`. Use `⟨fun t => ∑ k, G t (ρ (cf t) k), ?_, ?_⟩` and prove the remaining obligations. Use `Finset.measurable_sum _ fun k _ => hNf.comp (measurable_pi_lambda _ fun i => ?_)` and prove the remaining obligations. Use `Finset.measurable_sum _ fun l _ => (hev _).mul (Measurable.pow_const ?_ _)` and prove the remaining obligations. Conclude with `(measurable_pi_apply k).comp (hρm.comp hcf)`.

Introduce `t ht`. Establish `hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`. Assume the negation of the conclusion as `h`.

Conclude with `ht p h hp`. Set `τ : F →+* ℂ` to `IsFractionRing.lift hinj`. Establish `hτa : ∀ p : R, τ (algebraMap R F p) = MvPolynomial.eval₂ sg t p` using `fun p => IsFractionRing.lift_algebraMap hinj p`. Establish `hτ : ∀ f, τ f = ev f t`. Introduce `f`.

Use `conv_lhs => rw [← hfr f]`. Rewrite using `[map_div₀, hτa, hτa]`. Establish `hset : {P : L →+* ℂ | ∀ p : R, P (algebraMap F L (algebraMap R F p)) = MvPolynomial.eval₂ sg t p} = {P : L →+* ℂ | P.comp (algebraMap F L) = τ}`. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion.

Introduce `hP`. Apply `IsFractionRing.ringHom_ext (A := R)` to reduce the goal to its premises. Introduce `p`. Rewrite using `[hτa]`. Conclude with `hP p`.

Introduce `hP p`. Establish `hP' : P.comp (algebraMap F L) = τ` using `hP`. Rewrite using `[← hτa, ← hP']`. Both sides reduce to the same expression. Rewrite using `[hset]`.

Use `symm`. Use `finsum_embeddings_over_eq_sum_roots pb τ (ρ (cf t)) ?_ _ (G t) ?_` and prove the remaining obligations. Rewrite using `[hρ]`. Establish `hmon : (minpoly F pb.gen).Monic` using `minpoly.monic pb.isIntegral_gen`. Use `conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]`.

Rewrite using `[Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum, Finset.sum_range]`. Simplify using `[cf, hτ]`. Introduce `P hP show Nf _ = Nf _`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use `conv_lhs => rw [← pb.basis.sum_repr (b i)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, ← hτ, ← hP]`. Both sides reduce to the same expression.
-/
theorem measurable_sum_embeddings_over_generic_point :
    (∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ, ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) = Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) → ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i)) := by
  intro hρ K _ _ σ _ L _ _ _ sg m b Nf hNf
  classical
  set R := MvPolynomial σ K with hR
  set F := FractionRing R with hF
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨ρ, hρm, hρ⟩ := hρ pb.dim
  choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z
  let ev : F → (σ → ℂ) → ℂ := fun f t =>
    MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)
  have hpm : ∀ p : R, Measurable fun t : σ → ℂ => MvPolynomial.eval₂ sg t p := by
    intro p
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.continuous_eval _).measurable
  have hev : ∀ f, Measurable (ev f) := fun f => (hpm _).div (hpm _)
  let cf : (σ → ℂ) → Fin pb.dim → ℂ := fun t i => ev ((minpoly F pb.gen).coeff i) t
  have hcf : Measurable cf := measurable_pi_lambda _ fun i => hev _
  let G : (σ → ℂ) → ℂ → ℝ := fun t z =>
    Nf fun i => ∑ l : Fin pb.dim, ev (pb.basis.repr (b i) l) t * z ^ (l : ℕ)
  refine ⟨fun t => ∑ k, G t (ρ (cf t) k), ?_, ?_⟩
  · refine Finset.measurable_sum _ fun k _ => hNf.comp (measurable_pi_lambda _ fun i => ?_)
    refine Finset.measurable_sum _ fun l _ => (hev _).mul (Measurable.pow_const ?_ _)
    exact (measurable_pi_apply k).comp (hρm.comp hcf)
  · intro t ht
    have hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ) := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra h
      exact ht p h hp
    let τ : F →+* ℂ := IsFractionRing.lift hinj
    have hτa : ∀ p : R, τ (algebraMap R F p) = MvPolynomial.eval₂ sg t p := fun p =>
      IsFractionRing.lift_algebraMap hinj p
    have hτ : ∀ f, τ f = ev f t := by
      intro f
      conv_lhs => rw [← hfr f]
      rw [map_div₀, hτa, hτa]
    have hset : {P : L →+* ℂ | ∀ p : R, P (algebraMap F L (algebraMap R F p)) =
        MvPolynomial.eval₂ sg t p} = {P : L →+* ℂ | P.comp (algebraMap F L) = τ} := by
      ext P
      constructor
      · intro hP
        apply IsFractionRing.ringHom_ext (A := R)
        intro p
        rw [hτa]
        exact hP p
      · intro hP p
        have hP' : P.comp (algebraMap F L) = τ := hP
        rw [← hτa, ← hP']
        rfl
    rw [hset]
    symm
    refine finsum_embeddings_over_eq_sum_roots pb τ (ρ (cf t)) ?_ _ (G t) ?_
    · rw [hρ]
      have hmon : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
      conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
        Finset.sum_range]
      simp [cf, hτ]
    · intro P hP
      show Nf _ = Nf _
      congr 1
      funext i
      conv_lhs => rw [← pb.basis.sum_repr (b i)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, ← hτ, ← hP]
      rfl

end GlobalTheory
