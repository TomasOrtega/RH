import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.LevBij

/- English proof (translation)
Set `ψ : A →ₐ[R] B ⧸ x` to `(Ideal.Quotient.mkₐ R x).comp χ`. Establish `hint : ∀ a, ψ a ∈ (integralClosure K (B ⧸ x)).restrictScalars R` using `fun a => ((Algebra.IsIntegral.isIntegral (R := R) a).map ψ).tower_top (A := K)`. Set `e : K ≃ₐ[K] integralClosure K (B ⧸ x)` to `AlgEquiv.ofBijective (Algebra.ofId K _) IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `ψ₁ : A →ₐ[R] integralClosure K (B ⧸ x)` to `ψ.codRestrict _ hint`. Use `⟨((e.symm : _ →ₐ[K] K).restrictScalars R).comp ψ₁, fun a => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e.symm (ψ₁ a) = 0 ↔ _`. Rewrite using `[map_eq_zero_iff _ e.symm.injective, ← Ideal.Quotient.eq_zero_iff_mem, Subtype.ext_iff]`. Both sides reduce to the same expression.
-/
theorem exists_point {R K A B : Type} [CommRing R] [Field K] [IsAlgClosed K] [Algebra R K] [CommRing A] [Algebra R A]
    [Module.Finite R A] [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B] (χ : A →ₐ[R] B)
    (x : Ideal B) [x.IsPrime] : ∃ χ₀ : A →ₐ[R] K, ∀ a, χ₀ a = 0 ↔ χ a ∈ x := by
  let ψ : A →ₐ[R] B ⧸ x := (Ideal.Quotient.mkₐ R x).comp χ
  have hint : ∀ a, ψ a ∈ (integralClosure K (B ⧸ x)).restrictScalars R := fun a =>
    ((Algebra.IsIntegral.isIntegral (R := R) a).map ψ).tower_top (A := K)
  let e : K ≃ₐ[K] integralClosure K (B ⧸ x) :=
    AlgEquiv.ofBijective (Algebra.ofId K _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ₁ : A →ₐ[R] integralClosure K (B ⧸ x) := ψ.codRestrict _ hint
  refine ⟨((e.symm : _ →ₐ[K] K).restrictScalars R).comp ψ₁, fun a => ?_⟩
  change e.symm (ψ₁ a) = 0 ↔ _
  rw [map_eq_zero_iff _ e.symm.injective, ← Ideal.Quotient.eq_zero_iff_mem, Subtype.ext_iff]
  rfl

/- English proof (translation)
Introduce `R K _ _ _ _ G _ _ N A _ _ _ θ hθ B _ _ _ _`. Take `⟨V, hV⟩` from `hθ.opn`. Use `⟨Set.injOn_univ.1 (hV B).injOn, fun χ => ?_⟩` and prove the remaining obligations. Establish `h : Set.range (spMap (χ : A →+* B)) ⊆ V`. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `hx` using `x.isPrime`. Take `⟨χ₀, hχ₀⟩` from `exists_point (K := K) χ x.asIdeal`. Take `⟨t, ht⟩` from `hθ.gen.2 χ₀`. Establish `h1` using `(hV K).mapsTo (Set.mem_univ t)`. Rewrite `h1` using `[ht]`.

Establish `h2 : PrimeSpectrum.comap (χ₀ : A →+* K) ⟨⊥, Ideal.isPrime_bot⟩ ∈ V` using `h1 ⟨⟨⊥, Ideal.isPrime_bot⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `PrimeSpectrum.comap (χ : A →+* B) x ∈ V`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a`. Conclude with `(hχ₀ a).symm`.

Take `⟨w, -, hw⟩` from `(hV B).surjOn h`. Conclude with `⟨w, hw⟩`.
-/
theorem level_bijective : ∀ (R K : Type) [CommRing R] [Field K] [IsAlgClosed K] [Algebra R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] (θ : TorsPt G N A), IsLevel K θ → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B], Function.Bijective (θ.pt B) := by
  intro R K _ _ _ _ G _ _ N A _ _ _ θ hθ B _ _ _ _
  obtain ⟨V, hV⟩ := hθ.opn
  refine ⟨Set.injOn_univ.1 (hV B).injOn, fun χ => ?_⟩
  have h : Set.range (spMap (χ : A →+* B)) ⊆ V := by
    rintro _ ⟨x, rfl⟩
    have hx := x.isPrime
    obtain ⟨χ₀, hχ₀⟩ := exists_point (K := K) χ x.asIdeal
    obtain ⟨t, ht⟩ := hθ.gen.2 χ₀
    have h1 := (hV K).mapsTo (Set.mem_univ t)
    rw [ht] at h1
    have h2 : PrimeSpectrum.comap (χ₀ : A →+* K) ⟨⊥, Ideal.isPrime_bot⟩ ∈ V := h1 ⟨⟨⊥, Ideal.isPrime_bot⟩, rfl⟩
    change PrimeSpectrum.comap (χ : A →+* B) x ∈ V
    convert h2 using 1
    ext a
    exact (hχ₀ a).symm
  obtain ⟨w, -, hw⟩ := (hV B).surjOn h
  exact ⟨w, hw⟩

end GlobalTheory.GroupBplus.Aff.LevBij
