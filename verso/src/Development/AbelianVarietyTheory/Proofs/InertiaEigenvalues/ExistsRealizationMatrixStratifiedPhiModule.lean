import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEvWIsUnitInjectiveDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RealMatrix

section Alg

variable {R R' : Type} [CommRing R] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul_hom (f : R →+* R') (c : R) (M : Matrix n n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

/- English proof (translation)
Establish `h1 : F v * (e * t) = 1` using `by rw [← ht, ← map_mul, hv, map_one]`. Establish `h2 : e * F v = v` using `by linear_combination v * h1 - (e * F v) * hv`. Establish `h3 : e ^ (a + N) * F v ^ N = v ^ N * e ^ a`. Rewrite using `[pow_add, mul_assoc, ← mul_pow, h2, mul_comm]`. Rewrite using `[map_smul_hom, map_pow, smul_smul, h3, ← smul_smul, h, Matrix.smul_mul]`.
-/
theorem frobenius_matrix_equation_inverse_scaling (F : R →+* R) (e t v : R) (hv : v * t = 1) (ht : F t = e * t) (a N : ℕ) (Y A : Matrix n n R)
    (h : e ^ a • Y.map F = Y * A) : e ^ (a + N) • (v ^ N • Y).map F = (v ^ N • Y) * A := by
  have h1 : F v * (e * t) = 1 := by rw [← ht, ← map_mul, hv, map_one]
  have h2 : e * F v = v := by linear_combination v * h1 - (e * F v) * hv
  have h3 : e ^ (a + N) * F v ^ N = v ^ N * e ^ a := by
    rw [pow_add, mul_assoc, ← mul_pow, h2, mul_comm]
  rw [map_smul_hom, map_pow, smul_smul, h3, ← smul_smul, h, Matrix.smul_mul]

/- English proof (translation)
Establish `h1 : G v * G t = 1` using `by rw [← map_mul, hv, map_one]`. Establish `h2` using `congrArg (fun M => (v ^ N * G v ^ N) • M) h`. Establish `h3 : v ^ N * G v ^ N * t ^ N = G v ^ N`. Rewrite using `[mul_right_comm, ← mul_pow, hv, one_pow, one_mul]`. Establish `h4 : v ^ N * G v ^ N * G t ^ N = v ^ N`.

Rewrite using `[mul_assoc, ← mul_pow, h1, one_pow, mul_one]`. Simplify using `only [smul_smul, h3, h4] at h2`. Rewrite using `[map_smul_hom, map_pow, Matrix.mul_smul, h2, Matrix.smul_mul]`.
-/
theorem galois_matrix_equation_inverse_scaling (G : R →+* R) (t v : R) (hv : v * t = 1) (N : ℕ) (P Y ε : Matrix n n R)
    (h : t ^ N • (P * Y.map G) = G t ^ N • (Y * ε)) : P * (v ^ N • Y).map G = (v ^ N • Y) * ε := by
  have h1 : G v * G t = 1 := by rw [← map_mul, hv, map_one]
  have h2 := congrArg (fun M => (v ^ N * G v ^ N) • M) h
  have h3 : v ^ N * G v ^ N * t ^ N = G v ^ N := by
    rw [mul_right_comm, ← mul_pow, hv, one_pow, one_mul]
  have h4 : v ^ N * G v ^ N * G t ^ N = v ^ N := by
    rw [mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  simp only [smul_smul, h3, h4] at h2
  rw [map_smul_hom, map_pow, Matrix.mul_smul, h2, Matrix.smul_mul]

/- English proof (translation)
Apply `Matrix.map_injective hf` to reduce the goal to its premises. Simplify using `only []`. Rewrite using `[map_smul_hom, map_smul_hom, map_pow, map_pow, Matrix.map_mul, h]`.
-/
theorem descend (f : R →+* R') (hf : Function.Injective f) (x y : R) (N : ℕ) (M Y ε : Matrix n n R)
    (h : f x ^ N • M.map f = f y ^ N • (Y.map f * ε.map f)) : x ^ N • M = y ^ N • (Y * ε) := by
  apply Matrix.map_injective hf
  simp only []
  rw [map_smul_hom, map_smul_hom, map_pow, map_pow, Matrix.map_mul, h]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← map_pow, ← map_pow, ← map_smul_hom, ← map_smul_hom, h]`.
-/
theorem push (f : R →+* R') (x y : R) (N : ℕ) (P Q Y ε : Matrix n n R) (h : x ^ N • (P * Q) = y ^ N • (Y * ε)) :
    f x ^ N • (P.map f * Q.map f) = f y ^ N • (Y.map f * ε.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_pow, ← map_pow, ← map_smul_hom, ← map_smul_hom, h]

end Alg

/- English proof (translation)
Introduce `l _ K bk d ρ τ s ht hτ S ha hA hrel`. Take `⟨u, hu⟩` from `(GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ).1`. Establish `hv : (↑u⁻¹ : WCb l) * inclW l τ = 1` using `by rw [← hu, Units.inv_mul]`. Take `⟨ι, ⟨tb⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Establish `hinj : Function.Injective bk.iA` using `(GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1`.

Use `⟨(↑u⁻¹ : WCb l) ^ s.N • ht.Y.map (inclW l), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `(((Units.isUnit _).pow _).map _).mul ht.unit`. Rewrite using `[ha, hA]`. Use `frobenius_matrix_equation_inverse_scaling (frobW l : WCb l →+* WCb l) (bk.evW bk.E) (inclW l τ) _ hv ?_ _ _ _ _ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ`. Rewrite using `[frobW_inclW, hτ.1, map_mul]`. Apply the tactic sequence `have h := congrArg (fun M => M.map (inclW l)) ht.φ try beta_reduce at h`. Rewrite `h` using `[map_smul_hom, map_pow, Matrix.map_mul]`. Use `Eq.trans ?_ h` and prove the remaining obligations.

Use `congr 1`. Use `ext1 i j`. Conclude with `frobW_inclW _`. Introduce `g`. Establish `h0` using `descend bk.iA hinj _ _ _ _ _ _ (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g _ (hrel g))`.

Establish `h` using `push (inclW l) _ _ _ _ _ _ _ h0`. Rewrite `h` using `[← galW_inclW]`. Use `galois_matrix_equation_inverse_scaling (galW l (g : GQ l) : WCb l →+* WCb l) (inclW l τ) _ hv _ _ _ _ ?_` and prove the remaining obligations. Use `Eq.trans ?_ h` and prove the remaining obligations. Use `congr 2`.

Use `ext1 i j`. Conclude with `((inclWA l).commutes _).symm`. Use `ext1 i j`. Conclude with `galW_inclW _ _`.
-/
theorem exists_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ S : Strat bk d, S.a = ht.a + s.N → S.A = ht.A → (∀ g : ↥(GK K), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA)) → ∃ T : Matrix (Fin d) (Fin d) (WCb l), MReal S ρ T := by
  intro l _ K bk d ρ τ s ht hτ S ha hA hrel
  obtain ⟨u, hu⟩ := (GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ).1
  have hv : (↑u⁻¹ : WCb l) * inclW l τ = 1 := by rw [← hu, Units.inv_mul]
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine ⟨(↑u⁻¹ : WCb l) ^ s.N • ht.Y.map (inclW l), ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (((Units.isUnit _).pow _).map _).mul ht.unit
  · rw [ha, hA]
    refine frobenius_matrix_equation_inverse_scaling (frobW l : WCb l →+* WCb l) (bk.evW bk.E) (inclW l τ) _ hv ?_ _ _ _ _ ?_
    · change frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ
      rw [frobW_inclW, hτ.1, map_mul]
    · have h := congrArg (fun M => M.map (inclW l)) ht.φ
      try beta_reduce at h
      rw [map_smul_hom, map_pow, Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext1 i j
      exact frobW_inclW _
  · intro g
    have h0 := descend bk.iA hinj _ _ _ _ _ _ (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g _ (hrel g))
    have h := push (inclW l) _ _ _ _ _ _ _ h0
    rw [← galW_inclW] at h
    refine galois_matrix_equation_inverse_scaling (galW l (g : GQ l) : WCb l →+* WCb l) (inclW l τ) _ hv _ _ _ _ ?_
    refine Eq.trans ?_ h
    congr 2
    · ext1 i j
      exact ((inclWA l).commutes _).symm
    · ext1 i j
      exact galW_inclW _ _

end GlobalTheory.BSP.RealMatrix
