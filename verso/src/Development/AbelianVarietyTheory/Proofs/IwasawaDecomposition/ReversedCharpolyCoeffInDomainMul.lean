import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff

noncomputable section

open CategoryTheory Polynomial TensorProduct

namespace GlobalTheory.NormalDescent

/- English proof (translation)
Set `e` to `Module.finBasis K V`. Rewrite using `[← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly, Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]`. Generalize the expression as in `LinearMap.toMatrix e e f = M`. Use `congr 1`. Rewrite using `[Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]`.

Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij] <;> ring`.
-/
theorem charpoly_reverse_coeff_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (c : K) (k : ℕ) :
    (c • f).charpoly.reverse.coeff k = c ^ k * f.charpoly.reverse.coeff k := by
  classical
  let e := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly,
    Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]
  generalize LinearMap.toMatrix e e f = M
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j <;> simp [hij] <;> ring

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `haveI : Module.Finite A B := hφ`. Set `K` to `FractionRing A`. Set `Ω` to `AlgebraicClosure K`. Set `ι` to `algebraMap K Ω`.

Set `V` to `K ⊗[A] B`. Use `haveI : Module.Free K V := Module.Free.of_divisionRing _ _`. Set `e` to `Module.finBasis K V`. Set `Mx` to `Algebra.leftMulMatrix e ((1 : K) ⊗ₜ[A] b)`. Establish `hg : charK φ hφ K b = Mx.charpoly` using `by show (Algebra.lmul K V ((1 : K) ⊗ₜ[A] b)).charpoly = _ show _ = (Algebra.leftMulMatrix e _).charpoly`.

Rewrite using `[Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]`. Establish `hb : IsIntegral A b` using `Algebra.IsIntegral.isIntegral b`. Establish `h1 : IsIntegral A ((1 : K) ⊗ₜ[A] b)` using `hb.map (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B)`. Establish `h2 : IsIntegral A Mx` using `h1.map ((Algebra.leftMulMatrix e).restrictScalars A)`. Establish `h3 : IsIntegral A (Mx.map ι)` using `h2.map (AlgHom.mapMatrix (IsScalarTower.toAlgHom A K Ω))`.

Take `⟨p, hpm, hp⟩` from `h3`. Establish `hroot : ∀ μ ∈ (Mx.charpoly.map ι).roots, IsIntegral A μ`. Introduce `μ hμ`. Establish `hs : μ ∈ spectrum Ω (Mx.map ι)`. Rewrite using `[Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]`.

Conclude with `isRoot_of_mem_roots hμ`. Establish `h4` using `spectrum.subset_polynomial_aeval (Mx.map ι) (p.map (algebraMap A Ω)) ⟨μ, hs, rfl⟩`. Establish `h5 : aeval (Mx.map ι) (p.map (algebraMap A Ω)) = 0`. Rewrite using `[aeval_map_algebraMap, aeval_def]`. Conclude with `hp`.

Rewrite `h4` using `[h5]`. Use `⟨p, hpm, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def, ← aeval_map_algebraMap Ω]`. Assume the negation of the conclusion as `hne`. Conclude with `(spectrum.mem_iff.1 h4) (by`.

Simplify using `using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) Ω)))`. Establish `hl : Mx.charpoly.map ι ∈ Polynomial.lifts (integralClosure A Ω).val.toRingHom` using `(IsAlgClosed.splits _).mem_lift_of_roots_mem_range ((Matrix.charpoly_monic _).map _) _ fun μ hμ => ⟨⟨μ, hroot μ hμ⟩, rfl⟩`. Rewrite `hl` using `[lifts_iff_coeff_lifts]`. Take `⟨s, hs⟩` from `hl n`. Establish `hc : IsIntegral A (Mx.charpoly.coeff n)`.

Use `(isIntegral_algHom_iff (IsScalarTower.toAlgHom A K Ω) ι.injective).1 ?_` and prove the remaining obligations. Use `show IsIntegral A (ι _)`. Rewrite using `[← coeff_map, ← hs]`. Conclude with `s.2`. Rewrite using `[hg]`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.1 hc`.
-/
theorem exists_charK_coeff {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (n : ℕ) :
    ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).coeff n := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  let K := FractionRing A
  let Ω := AlgebraicClosure K
  let ι := algebraMap K Ω
  let V := K ⊗[A] B
  haveI : Module.Free K V := Module.Free.of_divisionRing _ _
  let e := Module.finBasis K V
  let Mx := Algebra.leftMulMatrix e ((1 : K) ⊗ₜ[A] b)
  have hg : charK φ hφ K b = Mx.charpoly := by
    show (Algebra.lmul K V ((1 : K) ⊗ₜ[A] b)).charpoly = _
    show _ = (Algebra.leftMulMatrix e _).charpoly
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  have hb : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have h1 : IsIntegral A ((1 : K) ⊗ₜ[A] b) :=
    hb.map (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B)
  have h2 : IsIntegral A Mx := h1.map ((Algebra.leftMulMatrix e).restrictScalars A)
  have h3 : IsIntegral A (Mx.map ι) := h2.map (AlgHom.mapMatrix (IsScalarTower.toAlgHom A K Ω))
  obtain ⟨p, hpm, hp⟩ := h3
  have hroot : ∀ μ ∈ (Mx.charpoly.map ι).roots, IsIntegral A μ := by
    intro μ hμ
    have hs : μ ∈ spectrum Ω (Mx.map ι) := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
      exact isRoot_of_mem_roots hμ
    have h4 := spectrum.subset_polynomial_aeval (Mx.map ι) (p.map (algebraMap A Ω)) ⟨μ, hs, rfl⟩
    have h5 : aeval (Mx.map ι) (p.map (algebraMap A Ω)) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h5] at h4
    refine ⟨p, hpm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap Ω]
    by_contra hne
    exact (spectrum.mem_iff.1 h4) (by
      simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) Ω)))
  have hl : Mx.charpoly.map ι ∈ Polynomial.lifts (integralClosure A Ω).val.toRingHom :=
    (IsAlgClosed.splits _).mem_lift_of_roots_mem_range ((Matrix.charpoly_monic _).map _) _
      fun μ hμ => ⟨⟨μ, hroot μ hμ⟩, rfl⟩
  rw [lifts_iff_coeff_lifts] at hl
  obtain ⟨s, hs⟩ := hl n
  have hc : IsIntegral A (Mx.charpoly.coeff n) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K Ω) ι.injective).1 ?_
    show IsIntegral A (ι _)
    rw [← coeff_map, ← hs]
    exact s.2
  rw [hg]
  exact IsIntegrallyClosed.isIntegral_iff.1 hc

/- English proof (translation)
Introduce `A B _ _ _ _ φ hφ u b k`. Establish `hrev : ∀ b' : B, ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b').reverse.coeff k` using `fun b' => by rw [coeff_reverse]; exact exists_charK_coeff φ hφ b' _`. Establish `key : (charK φ hφ (FractionRing A) (φ u * b)).reverse.coeff k = (algebraMap A (FractionRing A) u) ^ k * (charK φ hφ (FractionRing A) b).reverse.coeff k`. Use `letI := φ.toAlgebra`. Use `haveI : Module.Finite A B := hφ`.

Use `haveI : Module.Free (FractionRing A) (FractionRing A ⊗[A] B) := Module.Free.of_divisionRing _ _`. Establish `e1 : (1 : FractionRing A) ⊗ₜ[A] (φ u * b) = algebraMap A (FractionRing A) u • ((1 : FractionRing A) ⊗ₜ[A] b)`. Rewrite using `[algebraMap_smul, ← tmul_smul, Algebra.smul_def]`. Both sides reduce to the same expression. Use `show (Algebra.lmul _ _ ((1 : FractionRing A) ⊗ₜ[A] (φ u * b))).charpoly.reverse.coeff k = _`.

Rewrite using `[e1, map_smul]`. Conclude with `charpoly_reverse_coeff_smul _ _ _`. Apply `IsFractionRing.injective A (FractionRing A)` to reduce the goal to its premises. Rewrite using `[map_mul, map_pow, algebraMap_normCoeff _ _ _ _ (hrev _), algebraMap_normCoeff _ _ _ _ (hrev _), key]`.
-/
theorem normCoeff_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  intro A B _ _ _ _ φ hφ u b k
  have hrev : ∀ b' : B, ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b').reverse.coeff k :=
    fun b' => by rw [coeff_reverse]; exact exists_charK_coeff φ hφ b' _
  have key : (charK φ hφ (FractionRing A) (φ u * b)).reverse.coeff k
      = (algebraMap A (FractionRing A) u) ^ k * (charK φ hφ (FractionRing A) b).reverse.coeff k := by
    letI := φ.toAlgebra
    haveI : Module.Finite A B := hφ
    haveI : Module.Free (FractionRing A) (FractionRing A ⊗[A] B) := Module.Free.of_divisionRing _ _
    have e1 : (1 : FractionRing A) ⊗ₜ[A] (φ u * b)
        = algebraMap A (FractionRing A) u • ((1 : FractionRing A) ⊗ₜ[A] b) := by
      rw [algebraMap_smul, ← tmul_smul, Algebra.smul_def]; rfl
    show (Algebra.lmul _ _ ((1 : FractionRing A) ⊗ₜ[A] (φ u * b))).charpoly.reverse.coeff k = _
    rw [e1, map_smul]
    exact charpoly_reverse_coeff_smul _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_mul, map_pow, algebraMap_normCoeff _ _ _ _ (hrev _), algebraMap_normCoeff _ _ _ _ (hrev _), key]

end GlobalTheory.NormalDescent
