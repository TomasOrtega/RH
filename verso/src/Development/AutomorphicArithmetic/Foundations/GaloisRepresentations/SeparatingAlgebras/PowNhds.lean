import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen
open Topology Filter

section
variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]

/- English proof (translation)
Use `(hasStrictFDerivAt_pow' (𝕜 := 𝕜) N (x := (1 : R))).congr_fderiv ?_` and prove the remaining obligations. Simplify using `only [one_pow, MulOpposite.op_one, one_smul, Finset.sum_const, Finset.card_range]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.
-/
private lemma strict_pow (N : ℕ) :
    HasStrictFDerivAt (fun x : R => x ^ N) ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R) (1 : R) := by
  refine (hasStrictFDerivAt_pow' (𝕜 := 𝕜) N (x := (1 : R))).congr_fderiv ?_
  simp only [one_pow, MulOpposite.op_one, one_smul, Finset.sum_const, Finset.card_range]
  rw [Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Establish `hN' : (N : 𝕜) ≠ 0` using `Nat.cast_ne_zero.mpr hN`. Set `e : R ≃L[𝕜] R` to `ContinuousLinearEquiv.equivOfInverse ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R) ((N : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 R) (fun x => by simp [smul_smul, hN']) (fun x => by simp [smul_smul, hN'])`. Establish `hf : HasStrictFDerivAt (fun x : R => x ^ N) (e : R →L[𝕜] R) 1` using `strict_pow (𝕜 := 𝕜) N`. Simplify using `using hf.map_nhds_eq_of_equiv`.
-/
private lemma map_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0) :
    map (fun x : R => x ^ N) (𝓝 1) = 𝓝 1 := by
  have hN' : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let e : R ≃L[𝕜] R := ContinuousLinearEquiv.equivOfInverse ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R)
    ((N : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 R) (fun x => by simp [smul_smul, hN'])
    (fun x => by simp [smul_smul, hN'])
  have hf : HasStrictFDerivAt (fun x : R => x ^ N) (e : R →L[𝕜] R) 1 := strict_pow (𝕜 := 𝕜) N
  simpa using hf.map_nhds_eq_of_equiv

/- English proof (translation)
Establish `he` using `Units.isOpenEmbedding_val (R := R)`. Establish `h1 : ((↑) : Rˣ → R) '' V ∈ 𝓝 (1 : R)`. Simplify using `using he.image_mem_nhds.mpr hV`. Establish `h2 : (fun x : R => x ^ N) '' (((↑) : Rˣ → R) '' V) ∈ 𝓝 (1 : R)`. Rewrite using `[← map_pow_nhds (𝕜 := 𝕜) hN]`.

Conclude with `image_mem_map h1`. Rewrite using `[← he.image_mem_nhds]`. Rewrite using `[Set.image_image, Units.val_one]`. Rewrite `h2` using `[Set.image_image]`. Simplify using `using h2`.
-/
private lemma units_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0)
    {V : Set Rˣ} (hV : V ∈ 𝓝 (1 : Rˣ)) : (fun x => x ^ N) '' V ∈ 𝓝 (1 : Rˣ) := by
  have he := Units.isOpenEmbedding_val (R := R)
  have h1 : ((↑) : Rˣ → R) '' V ∈ 𝓝 (1 : R) := by
    simpa using he.image_mem_nhds.mpr hV
  have h2 : (fun x : R => x ^ N) '' (((↑) : Rˣ → R) '' V) ∈ 𝓝 (1 : R) := by
    rw [← map_pow_nhds (𝕜 := 𝕜) hN]
    exact image_mem_map h1
  rw [← he.image_mem_nhds]
  rw [Set.image_image, Units.val_one]
  rw [Set.image_image] at h2
  simpa using h2
end

/- English proof (translation)
Introduce `E _ _ w a N hN V hV`. Use `letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective`. Use `letI : NormedRing (Matrix (Fin a) (Fin a) (w.adicCompletion E)) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra (w.adicCompletion E) (Matrix (Fin a) (Fin a) (w.adicCompletion E)) := Matrix.linftyOpNormedAlgebra`.

Use `haveI : @CompleteSpace (Matrix (Fin a) (Fin a) (w.adicCompletion E)) (@Matrix.linftyOpNormedRing (Fin a) (w.adicCompletion E) _ _ _).toUniformSpace := inferInstanceAs (CompleteSpace (Fin a → Fin a → w.adicCompletion E))`. Conclude with `units_pow_nhds (𝕜 := w.adicCompletion E) hN hV`.
-/
theorem UpperTheory.Gal.Gen.powNhds_pf :
    UpperTheory.Gal.Gen.PowNhds := by
  intro E _ _ w a N hN V hV
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  letI : NormedRing (Matrix (Fin a) (Fin a) (w.adicCompletion E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra (w.adicCompletion E) (Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin a) (Fin a) (w.adicCompletion E))
      (@Matrix.linftyOpNormedRing (Fin a) (w.adicCompletion E) _ _ _).toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin a → Fin a → w.adicCompletion E))
  exact units_pow_nhds (𝕜 := w.adicCompletion E) hN hV
