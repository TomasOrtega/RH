import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekind

namespace GlobalTheory

namespace FracAlgEtale

/- English proof (translation)
Set `ι : R →+* Q` to `algebraMap R Q`. Use `letI : Algebra B R := ((algebraMap A' R).comp (algebraMap B A')).toAlgebra`. Use `haveI : IsScalarTower B A' R := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `letI : Algebra A' K := (π.comp (ι.comp (algebraMap A' R))).toAlgebra`. Use `letI : Algebra B K := ((algebraMap A' K).comp (algebraMap B A')).toAlgebra`.

Use `haveI : IsScalarTower B A' K := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `F` to `FractionRing B`. Use `haveI : Module.Flat A' R := IsLocalization.flat R (Submonoid.powers (algebraMap B A' f))`. Use `haveI : Module.Flat B R := Module.Flat.trans B A' R`. Establish `hreg : ∀ b ∈ nonZeroDivisors B, algebraMap B R b ∈ nonZeroDivisors R`.

Introduce `b hb`. Establish `hs` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hb`. Rewrite using `[mem_nonZeroDivisors_iff]`. Use `⟨fun x hx => hs ?_, fun x hx => hs ?_⟩` and prove the remaining obligations. Use `show b • x = b • (0 : R)`.

Rewrite using `[smul_zero, Algebra.smul_def]`. Apply the tactic sequence `first | exact hx | (rw [mul_comm]; exact hx)`. Use `show b • x = b • (0 : R)`. Rewrite using `[smul_zero, Algebra.smul_def]`. Apply the tactic sequence `first | exact hx | (rw [mul_comm]; exact hx)`.

Establish `hunitR : ∀ s ∈ nonZeroDivisors R, IsUnit (π (ι s))` using `fun s hs => (IsLocalization.map_units Q (⟨s, hs⟩ : nonZeroDivisors R)).map π`. Establish `hBK : ∀ b : B, algebraMap B K b = π (ι (algebraMap B R b))` using `fun b => rfl`. Establish `hunit : ∀ y : nonZeroDivisors B, IsUnit (algebraMap B K y)` using `fun y => by`. Rewrite using `[hBK]`. Conclude with `hunitR _ (hreg _ y.2)`.

Use `letI : Algebra F K := (IsLocalization.lift (M := nonZeroDivisors B) (S := F) hunit).toAlgebra`. Use `haveI : IsScalarTower B F K := IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq (M := nonZeroDivisors B) (S := F) hunit b).symm`. Use `haveI : Module.Finite F (TensorProduct B F A') := Algebra.FormallyUnramified.finite_of_free F _`. Set `ψ : TensorProduct B F A' →ₐ[F] K` to `Algebra.TensorProduct.lift (Algebra.ofId F K) (IsScalarTower.toAlgHom B A' K) (fun _ _ => Commute.all _ _)`. Establish `hA : ∀ a : A', IsIntegral F (algebraMap A' K a)` using `fun a => by`.

Establish `h1` using `(Algebra.IsIntegral.isIntegral (R := F) ((1 : F) ⊗ₜ[B] a)).map ψ`. Simplify `h1` using `[ψ]`. Establish `hAR : ∀ a : A', π (ι (algebraMap A' R a)) = algebraMap A' K a` using `fun a => rfl`. Establish `hf' : f ∈ nonZeroDivisors B` using `mem_nonZeroDivisors_of_ne_zero hf`. Establish `hR : ∀ x : R, IsIntegral F (π (ι x))`.

Introduce `x`. Take `⟨⟨a, ⟨_, n, rfl⟩⟩, hx⟩` from `IsLocalization.surj (Submonoid.powers (algebraMap B A' f)) x`. Establish `hx'` using `congrArg (fun y => π (ι y)) hx`. Simplify using `only [map_mul, map_pow] at hx'`. Establish `hfK : π (ι (algebraMap A' R (algebraMap B A' f))) = algebraMap F K (algebraMap B F f)`.

Rewrite using `[← IsScalarTower.algebraMap_apply B F K]`. Both sides reduce to the same expression. Rewrite `hx'` using `[hfK, hAR]`. Establish `hu : IsUnit (algebraMap F K (algebraMap B F f))`. Rewrite using `[← IsScalarTower.algebraMap_apply B F K]`.

Conclude with `hunit ⟨f, hf'⟩`. Establish `hne : (algebraMap F K (algebraMap B F f)) ^ n ≠ 0` using `pow_ne_zero _ hu.ne_zero`. Establish `: π (ι x) = algebraMap A' K a * ((algebraMap F K (algebraMap B F f)) ^ n)⁻¹` using `(eq_mul_inv_iff_mul_eq₀ hne).2 hx'`. Rewrite using `[this]`. Conclude with `(hA a).mul ((isIntegral_algebraMap (R := F) (A := K) (x := algebraMap B F f)).pow n).inv`.

Establish `hall : ∀ z : K, IsIntegral F z`. Introduce `z`. Take `⟨q, rfl⟩` from `hπ z`. Take `⟨⟨x, s⟩, hq⟩` from `IsLocalization.surj (nonZeroDivisors R) q`. Establish `hq' : π q * π (ι s) = π (ι x)`.

Rewrite using `[← map_mul]`. Conclude with `congrArg π hq`. Establish `: π q = π (ι x) * (π (ι s))⁻¹` using `(eq_mul_inv_iff_mul_eq₀ (hunitR _ s.2).ne_zero).2 hq'`. Rewrite using `[this]`. Conclude with `(hR x).mul (hR s).inv`.

Use `haveI : Algebra.IsIntegral F K := ⟨hall⟩`. Use `haveI : Algebra.IsAlgebraic F K := inferInstance`. Take `⟨algRF, hRF⟩` from `GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc k B hB`. Use `letI algK : Algebra (RatFunc k) K := ((algebraMap F K).comp (algebraMap (RatFunc k) F)).toAlgebra`. Use `haveI : IsScalarTower (RatFunc k) F K := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Conclude with `⟨algK, Algebra.IsAlgebraic.trans (RatFunc k) F K⟩`.
-/
theorem exists_isAlgebraic_ratFunc_of_ringHom (k B : Type) [Field k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (hB : ¬ IsField B) (f : B)
    (hf : f ≠ 0) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (R : Type)
    [CommRing R] [Algebra A' R] [IsLocalization.Away (algebraMap B A' f) R] (Q : Type)
    [CommRing Q] [Algebra R Q] [IsFractionRing R Q] (K : Type) [Field K] (π : Q →+* K)
    (hπ : Function.Surjective π) :
    ∃ _ : Algebra (RatFunc k) K, Algebra.IsAlgebraic (RatFunc k) K := by
  let ι : R →+* Q := algebraMap R Q
  letI : Algebra B R := ((algebraMap A' R).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra A' K := (π.comp (ι.comp (algebraMap A' R))).toAlgebra
  letI : Algebra B K := ((algebraMap A' K).comp (algebraMap B A')).toAlgebra
  haveI : IsScalarTower B A' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let F := FractionRing B

  haveI : Module.Flat A' R := IsLocalization.flat R (Submonoid.powers (algebraMap B A' f))
  haveI : Module.Flat B R := Module.Flat.trans B A' R
  have hreg : ∀ b ∈ nonZeroDivisors B, algebraMap B R b ∈ nonZeroDivisors R := by
    intro b hb
    have hs := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) hb
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => hs ?_, fun x hx => hs ?_⟩
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
    · show b • x = b • (0 : R)
      rw [smul_zero, Algebra.smul_def]
      first | exact hx | (rw [mul_comm]; exact hx)
  have hunitR : ∀ s ∈ nonZeroDivisors R, IsUnit (π (ι s)) := fun s hs =>
    (IsLocalization.map_units Q (⟨s, hs⟩ : nonZeroDivisors R)).map π
  have hBK : ∀ b : B, algebraMap B K b = π (ι (algebraMap B R b)) := fun b => rfl
  have hunit : ∀ y : nonZeroDivisors B, IsUnit (algebraMap B K y) := fun y => by
    rw [hBK]; exact hunitR _ (hreg _ y.2)
  letI : Algebra F K := (IsLocalization.lift (M := nonZeroDivisors B) (S := F) hunit).toAlgebra
  haveI : IsScalarTower B F K := IsScalarTower.of_algebraMap_eq fun b =>
    (IsLocalization.lift_eq (M := nonZeroDivisors B) (S := F) hunit b).symm

  haveI : Module.Finite F (TensorProduct B F A') := Algebra.FormallyUnramified.finite_of_free F _
  let ψ : TensorProduct B F A' →ₐ[F] K :=
    Algebra.TensorProduct.lift (Algebra.ofId F K) (IsScalarTower.toAlgHom B A' K)
      (fun _ _ => Commute.all _ _)
  have hA : ∀ a : A', IsIntegral F (algebraMap A' K a) := fun a => by
    have h1 := (Algebra.IsIntegral.isIntegral (R := F) ((1 : F) ⊗ₜ[B] a)).map ψ
    simpa [ψ] using h1
  have hAR : ∀ a : A', π (ι (algebraMap A' R a)) = algebraMap A' K a := fun a => rfl
  have hf' : f ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hf
  have hR : ∀ x : R, IsIntegral F (π (ι x)) := by
    intro x
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B A' f)) x
    have hx' := congrArg (fun y => π (ι y)) hx
    simp only [map_mul, map_pow] at hx'
    have hfK : π (ι (algebraMap A' R (algebraMap B A' f))) = algebraMap F K (algebraMap B F f) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; rfl
    rw [hfK, hAR] at hx'
    have hu : IsUnit (algebraMap F K (algebraMap B F f)) := by
      rw [← IsScalarTower.algebraMap_apply B F K]; exact hunit ⟨f, hf'⟩
    have hne : (algebraMap F K (algebraMap B F f)) ^ n ≠ 0 := pow_ne_zero _ hu.ne_zero
    have : π (ι x) = algebraMap A' K a * ((algebraMap F K (algebraMap B F f)) ^ n)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hne).2 hx'
    rw [this]
    exact (hA a).mul ((isIntegral_algebraMap (R := F) (A := K) (x := algebraMap B F f)).pow n).inv
  have hall : ∀ z : K, IsIntegral F z := by
    intro z
    obtain ⟨q, rfl⟩ := hπ z
    obtain ⟨⟨x, s⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors R) q
    have hq' : π q * π (ι s) = π (ι x) := by
      rw [← map_mul]; exact congrArg π hq
    have : π q = π (ι x) * (π (ι s))⁻¹ := (eq_mul_inv_iff_mul_eq₀ (hunitR _ s.2).ne_zero).2 hq'
    rw [this]
    exact (hR x).mul (hR s).inv
  haveI : Algebra.IsIntegral F K := ⟨hall⟩
  haveI : Algebra.IsAlgebraic F K := inferInstance

  obtain ⟨algRF, hRF⟩ := GlobalTheory.FracAlgDedekind.exists_isAlgebraic_ratFunc k B hB
  letI algK : Algebra (RatFunc k) K := ((algebraMap F K).comp (algebraMap (RatFunc k) F)).toAlgebra
  haveI : IsScalarTower (RatFunc k) F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨algK, Algebra.IsAlgebraic.trans (RatFunc k) F K⟩

/- English proof (translation)
Introduce `k B _ _ _ _ _ _ hB f hf A' _ _ _ M`. Use `haveI : M.asIdeal.IsMaximal := M.isMaximal`. Use `letI : Field (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := Ideal.Quotient.field M.asIdeal`. Conclude with `exists_isAlgebraic_ratFunc_of_ringHom k B hB f hf A' (Localization.Away (algebraMap B A' f)) (FractionRing (Localization.Away (algebraMap B A' f))) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) (Ideal.Quotient.mk M.asIdeal) (Ideal.Quotient.mk_surjective (I := …`.
-/
theorem exists_isAlgebraic_ratFunc_residue : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  intro k B _ _ _ _ _ _ hB f hf A' _ _ _ M
  haveI : M.asIdeal.IsMaximal := M.isMaximal
  letI : Field (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) :=
    Ideal.Quotient.field M.asIdeal
  exact exists_isAlgebraic_ratFunc_of_ringHom k B hB f hf A' (Localization.Away (algebraMap B A' f))
    (FractionRing (Localization.Away (algebraMap B A' f)))
    (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) (Ideal.Quotient.mk M.asIdeal)
    (Ideal.Quotient.mk_surjective (I := M.asIdeal))

end FracAlgEtale

end GlobalTheory
