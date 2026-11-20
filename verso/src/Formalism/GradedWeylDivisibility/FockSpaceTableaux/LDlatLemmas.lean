import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[rowAct, aeval_X, AlgHom.id_apply]`. Rewrite using `[Finset.sum_eq_single v.1 (fun b _ hb => by simp [Matrix.one_apply_ne (Ne.symm hb)]) (by simp)]`. Simplify using the standard rewrite rules.
-/
lemma ldlat_rowAct_one {R : Type*} [CommRing R] {k n : ℕ} :
    rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1 (fun b _ hb => by simp [Matrix.one_apply_ne (Ne.symm hb)]) (by simp)]
  simp

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, h K k n g g⁻¹, Matrix.nonsing_inv_mul g hg, ldlat_rowAct_one, AlgHom.id_apply]`.
-/
lemma ldlat_rowAct_inv_left (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g (rowAct K g⁻¹ x) = x := by
  rw [← AlgHom.comp_apply, h K k n g g⁻¹, Matrix.nonsing_inv_mul g hg, ldlat_rowAct_one, AlgHom.id_apply]

/- English proof (translation)
Rewrite using `[← AlgHom.comp_apply, h K k n g⁻¹ g, Matrix.mul_nonsing_inv g hg, ldlat_rowAct_one, AlgHom.id_apply]`.
-/
lemma ldlat_rowAct_inv_right (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g⁻¹ (rowAct K g x) = x := by
  rw [← AlgHom.comp_apply, h K k n g⁻¹ g, Matrix.mul_nonsing_inv g hg, ldlat_rowAct_one, AlgHom.id_apply]

/- English proof (translation)
Unfold `bideterminant initMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[show (map φ : MvPolynomial (Fin r × Fin n) R → _) = ((map φ : MvPolynomial _ R →+* MvPolynomial _ S)) from rfl, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `p q`. Simplify using `[RingHom.mapMatrix_apply]`.
-/
lemma ldlat_map_bidet {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (map φ : MvPolynomial (Fin r × Fin n) R → _) = ((map φ : MvPolynomial _ R →+* MvPolynomial _ S)) from rfl,
    RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

/- English proof (translation)
Introduce `m hm`. Apply `hf` to reduce the goal to its premises. Introduce `h0`. Apply `hm` to reduce the goal to its premises. Rewrite using `[coeff_map, h0, map_zero]`.
-/
lemma ldlat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] {w : σ → M} {f : MvPolynomial σ R} {μ : M}
    (hf : IsWeightedHomogeneous w f μ) : IsWeightedHomogeneous w (map φ f) μ := by
  intro m hm
  apply hf
  intro h0
  apply hm
  rw [coeff_map, h0, map_zero]

/- English proof (translation)
Rewrite `hv`, the goal using `[linearIndependent_iff']`. Introduce `s c hsum i hi`. Set `B` to `Module.Free.chooseBasis F K`. Apply `B.ext_elem` to reduce the goal to its premises. Introduce `j`.

Establish `key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0`. Use extensionality with `m`. Establish `h1` using `congrArg (coeff m) hsum`. Simplify using `only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul, coeff_zero] at h1 ⊢`. Establish `h2` using `congrArg (fun x => B.repr x j) h1`.

Simplify using `only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]`. Use `hv s (fun i => B.repr (c i) j) key i hi` as an intermediate fact.

Simplify using `using this`.
-/
lemma ldlat_linInd_field {F K : Type*} [Field F] [Field K] [Algebra F K] {σ ι : Type*}
    {v : ι → MvPolynomial σ F} (hv : LinearIndependent F v) :
    LinearIndependent K (fun i => map (algebraMap F K) (v i)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (coeff m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul, coeff_zero] at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1
    simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero,
      Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

/- English proof (translation)
Use `letI : Algebra (FractionRing R) K := (IsFractionRing.lift hinj).toAlgebra`. Establish `h1 : LinearIndependent R (fun i => map (algebraMap R (FractionRing R)) (b i))`. Use `hb.map' (mapAlgHom (Algebra.ofId R (FractionRing R))).toLinearMap (by` as an intermediate fact. Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `x y hxy`.

Conclude with `map_injective _ (IsFractionRing.injective R (FractionRing R)) hxy)`. Conclude with `this`. Establish `h2 : LinearIndependent (FractionRing R) (fun i => map (algebraMap R (FractionRing R)) (b i))` using `(LinearIndependent.iff_fractionRing R (FractionRing R)).mp h1`. Establish `h3` using `ldlat_linInd_field (K := K) h2`. Establish `hc : (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)) = algebraMap R K`.

Use extensionality with `r`. Simplify using `[RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]`. Use `h3 using 2 with i` and compare the differences between its conclusion and the goal. Rewrite using `[map_map, hc]`.
-/
lemma ldlat_linInd_base {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) {σ ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : LinearIndependent R b) : LinearIndependent K (fun i => map (algebraMap R K) (b i)) := by
  letI : Algebra (FractionRing R) K := (IsFractionRing.lift hinj).toAlgebra
  have h1 : LinearIndependent R (fun i => map (algebraMap R (FractionRing R)) (b i)) := by
    have := hb.map' (mapAlgHom (Algebra.ofId R (FractionRing R))).toLinearMap (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact map_injective _ (IsFractionRing.injective R (FractionRing R)) hxy)
    exact this
  have h2 : LinearIndependent (FractionRing R) (fun i => map (algebraMap R (FractionRing R)) (b i)) :=
    (LinearIndependent.iff_fractionRing R (FractionRing R)).mp h1
  have h3 := ldlat_linInd_field (K := K) h2
  have hc : (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)) = algebraMap R K := by
    ext r
    simp [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
  convert h3 using 2 with i
  rw [map_map, hc]

end Formalism.GradedWeylDivisibility
