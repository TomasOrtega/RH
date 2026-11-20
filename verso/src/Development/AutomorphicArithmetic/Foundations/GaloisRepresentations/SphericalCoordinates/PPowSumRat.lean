import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

/- English proof (translation)
Establish `hu : IsUnit Sb.det` using `isUnit_iff_ne_zero.mpr hS`. Establish `hinv : Sb * Sb⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `hM : M = Sb * Matrix.diagonal d * Sb⁻¹`. Rewrite using `[← h, Matrix.mul_assoc, hinv, Matrix.mul_one]`. Rewrite using `[hM, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.trace_diagonal]`.
-/
private lemma trace_of_diag {g : ℕ} (M Sb : Matrix (Fin g) (Fin g) ℂ) (d : Fin g → ℂ) (hS : Sb.det ≠ 0)
    (h : M * Sb = Sb * Matrix.diagonal d) : M.trace = ∑ i, d i := by
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hS
  have hinv : Sb * Sb⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hM : M = Sb * Matrix.diagonal d * Sb⁻¹ := by
    rw [← h, Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hM, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.trace_diagonal]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Establish `: (fun i => e i ^ 0) = fun _ => (1 : ℂ)` using `by funext i; simp`. Rewrite using `[this]`. Simplify using `[Matrix.diagonal_one]`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`. Use `congr 2`.
-/
private lemma pow_mul_diag {g : ℕ} (H Sb : Matrix (Fin g) (Fin g) ℂ) (e : Fin g → ℂ)
    (h : H * Sb = Sb * Matrix.diagonal e) (j : ℕ) :
    H ^ j * Sb = Sb * Matrix.diagonal (fun i => e i ^ j) := by
  induction j with
  | zero =>
    have : (fun i => e i ^ 0) = fun _ => (1 : ℂ) := by funext i; simp
    rw [this]
    simp [Matrix.diagonal_one]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    congr 2

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, h, ih, Matrix.mulVec_mulVec]`.
-/
private lemma per_pow {L : Type} {O : Type} [Ring O] [AddCommGroup L] [Module O L] {g : ℕ}
    (P : L →+ (Fin g → ℂ)) (ga : L →ₗ[O] L) (H : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x, P (ga x) = H *ᵥ P x) (j : ℕ) (x : L) : P ((ga ^ j) x) = (H ^ j) *ᵥ P x := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, h, ih, Matrix.mulVec_mulVec]

open scoped Classical in
/- English proof (translation)
Unfold `evAt`. Rewrite using `[Multiset.map_map, ← Finset.sum_filter]`. Both sides reduce to the same expression.
-/
private lemma sum_evAt {F : Type} [Field F] {g : ℕ} (ty : Fin g → (F →+* ℂ)) (e : Fin g → ℂ)
    (τ : F →+* ℂ) (u : ℂ → ℂ) :
    ((evAt ty e τ).map u).sum = ∑ i, if ty i = τ then u (e i) else 0 := by
  unfold evAt
  rw [Multiset.map_map, ← Finset.sum_filter]
  rfl

open scoped Classical in
/- English proof (translation)
Establish `cc : ∀ φ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ` using `fun φ => RingHom.ext fun y => by simp [ComplexEmbedding.conjugate_coe_eq]`. Establish `h1 : ∑ τ : F →+* ℂ, τ x * ((evAt ty e τ).map fun r => r ^ j).sum = ∑ i, ty i x * e i ^ j`. Repeatedly rewrite using `[sum_evAt, Finset.mul_sum, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Establish `h2 : ∑ τ : F →+* ℂ, τ x * (((evAt ty e (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ)).map fun r => r ^ j).sum = (starRingEnd ℂ) (∑ i, ty i x * e i ^ j)`. Repeatedly rewrite using `[Multiset.map_map, sum_evAt, Finset.mul_sum, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_comm, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (ComplexEmbedding.conjugate (ty i))]`. Rewrite using `[if_pos (cc _).symm, ComplexEmbedding.conjugate_coe_eq]`. Simplify using the standard rewrite rules. Introduce `τ _ hτ`.

Rewrite using `[if_neg]`. Introduce `hc`. Apply `hτ` to reduce the goal to its premises. Rewrite using `[hc, cc]`. Introduce `hn`.

Conclude with `absurd (Finset.mem_univ _) hn`. Repeatedly rewrite using `[evFull, Multiset.map_add, Multiset.sum_add, mul_add]`. Rewrite using `[Finset.sum_add_distrib, h1, h2]`.
-/
private lemma sum_evFull {F : Type} [Field F] [NumberField F] {g : ℕ} (ty : Fin g → (F →+* ℂ))
    (e : Fin g → ℂ) (j : ℕ) (x : F) :
    ∑ τ : F →+* ℂ, τ x * ((evFull ty e τ).map fun r => r ^ j).sum =
      (∑ i, ty i x * e i ^ j) + (starRingEnd ℂ) (∑ i, ty i x * e i ^ j) := by
  have cc : ∀ φ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => RingHom.ext fun y => by simp [ComplexEmbedding.conjugate_coe_eq]
  have h1 : ∑ τ : F →+* ℂ, τ x * ((evAt ty e τ).map fun r => r ^ j).sum = ∑ i, ty i x * e i ^ j := by
    simp_rw [sum_evAt, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∑ τ : F →+* ℂ, τ x *
      (((evAt ty e (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ)).map fun r => r ^ j).sum =
      (starRingEnd ℂ) (∑ i, ty i x * e i ^ j) := by
    simp_rw [Multiset.map_map, sum_evAt, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (ComplexEmbedding.conjugate (ty i))]
    · rw [if_pos (cc _).symm, ComplexEmbedding.conjugate_coe_eq]
      simp
    · intro τ _ hτ
      rw [if_neg]
      intro hc
      apply hτ
      rw [hc, cc]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  simp_rw [evFull, Multiset.map_add, Multiset.sum_add, mul_add]
  rw [Finset.sum_add_distrib, h1, h2]

/- English proof (translation)
Introduce `hL hD F _ _ O _ bar g ρ a D P₀ hP ga H hga Sb ty ev hd j`. Take `⟨hS, hρ, hH⟩` from `hd`. Use `hD F (fun τ => ((evFull ty ev τ).map fun r => r ^ j).sum) ?_` and prove the remaining obligations. Introduce `c`. Set `f : D.La →ₗ[ℤ] D.La` to `(AddMonoidHom.mk' (fun x => a c • (ga ^ j) x) (by intro x y; simp [smul_add])).toIntLinearMap`.

Establish `hf : ∀ x, P₀ (f x) = (ρ (a c) * H ^ j) *ᵥ P₀ x`. Introduce `x`. Use `show P₀ (a c • (ga ^ j) x) = _`. Rewrite using `[hP.1, per_pow P₀ ga H hga, Matrix.mulVec_mulVec]`. Use `⟨LinearMap.trace ℤ D.La f, ?_⟩` and prove the remaining obligations.

Rewrite using `[hL D.La g P₀ hP.2.1 hP.2.2.1 hP.2.2.2.1 f _ hf]`. Establish `htr : (ρ (a c) * H ^ j).trace = ∑ i, ty i (c : F) * ev i ^ j`. Use `trace_of_diag _ Sb (fun i => ty i (c : F) * ev i ^ j) hS ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, pow_mul_diag H Sb ev hH j, ← Matrix.mul_assoc, hρ c, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]`. Rewrite using `[htr]`.

Conclude with `sum_evFull ty ev j (c : F)`.
-/
theorem UpperTheory.Gal.W2.powSumRat_of :
    UpperTheory.Gal.W2.TraceLat → UpperTheory.Gal.W2.TraceDual → UpperTheory.Gal.W2.PowSumRat := by
  intro hL hD F _ _ O _ bar g ρ a D P₀ hP ga H hga Sb ty ev hd j
  obtain ⟨hS, hρ, hH⟩ := hd
  refine hD F (fun τ => ((evFull ty ev τ).map fun r => r ^ j).sum) ?_
  intro c
  let f : D.La →ₗ[ℤ] D.La :=
    (AddMonoidHom.mk' (fun x => a c • (ga ^ j) x) (by intro x y; simp [smul_add])).toIntLinearMap
  have hf : ∀ x, P₀ (f x) = (ρ (a c) * H ^ j) *ᵥ P₀ x := by
    intro x
    show P₀ (a c • (ga ^ j) x) = _
    rw [hP.1, per_pow P₀ ga H hga, Matrix.mulVec_mulVec]
  refine ⟨LinearMap.trace ℤ D.La f, ?_⟩
  rw [hL D.La g P₀ hP.2.1 hP.2.2.1 hP.2.2.2.1 f _ hf]
  have htr : (ρ (a c) * H ^ j).trace = ∑ i, ty i (c : F) * ev i ^ j := by
    refine trace_of_diag _ Sb (fun i => ty i (c : F) * ev i ^ j) hS ?_
    rw [Matrix.mul_assoc, pow_mul_diag H Sb ev hH j, ← Matrix.mul_assoc, hρ c, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
  rw [htr]
  exact sum_evFull ty ev j (c : F)
