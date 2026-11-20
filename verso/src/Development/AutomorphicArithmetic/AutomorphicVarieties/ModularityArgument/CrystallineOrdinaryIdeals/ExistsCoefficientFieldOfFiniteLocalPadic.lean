import Mathlib

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ B _ _ _ _`. Establish `hart : IsArtinianRing B` using `IsArtinianRing.of_finite ℚ_[l] B`. Set `g : B →ₐ[ℚ_[l]] ResidueField B` to `Ideal.Quotient.mkₐ ℚ_[l] (maximalIdeal B)`. Establish `het : Algebra.FormallyEtale ℚ_[l] (ResidueField B)` using `Algebra.FormallyEtale.of_isSeparable ℚ_[l] (ResidueField B)`. Establish `hker : RingHom.ker (g : B →+* ResidueField B) = maximalIdeal B` using `Ideal.mk_ker`.

Establish `hnil : IsNilpotent (RingHom.ker (g : B →+* ResidueField B))`. Rewrite using `[hker]`. Conclude with `(IsArtinianRing.isNilpotent_jacobson_bot (R := B)).imp fun n h => by`. Rewrite `h` using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Then use the resulting hypothesis. Establish `hsurj : Function.Surjective g` using `Ideal.Quotient.mk_surjective`.

Set `s : ResidueField B →ₐ[ℚ_[l]] B` to `Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℚ_[l] _) g hsurj hnil`. Establish `hs : ∀ x, g (s x) = x` using `fun x => Algebra.FormallySmooth.liftOfSurjective_apply _ g hsurj hnil x`. Use `letI alg : Algebra (ResidueField B) B := s.toRingHom.toAlgebra`. Establish `tower : IsScalarTower ℚ_[l] (ResidueField B) B`. Use `IsScalarTower.of_algebraMap_eq fun r => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] B r = s (algebraMap ℚ_[l] (ResidueField B) r)`. Conclude with `(s.commutes r).symm`. Set `π : B →ₐ[ResidueField B] ResidueField B` to `{ (g : B →+* ResidueField B) with commutes' := fun x => hs x }`. Use `⟨ResidueField B, inferInstance, inferInstance, inferInstance, alg, tower, π, ?_⟩` and prove the remaining obligations. Introduce `a ha`.

Establish `hmem : a ∈ maximalIdeal B`. Rewrite using `[← hker]`. Conclude with `ha`. Conclude with `Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hmem`.
-/
theorem exists_coefficientField_of_finite_local_padic : ∀ {l : ℕ} [Fact l.Prime] (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B], ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[l] E) (_ : FiniteDimensional ℚ_[l] E) (_ : Algebra E B) (_ : IsScalarTower ℚ_[l] E B) (π : B →ₐ[E] E), ∀ a, π a = 0 → IsNilpotent a := by
  intro l _ B _ _ _ _
  have hart : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  let g : B →ₐ[ℚ_[l]] ResidueField B := Ideal.Quotient.mkₐ ℚ_[l] (maximalIdeal B)
  have het : Algebra.FormallyEtale ℚ_[l] (ResidueField B) :=
    Algebra.FormallyEtale.of_isSeparable ℚ_[l] (ResidueField B)
  have hker : RingHom.ker (g : B →+* ResidueField B) = maximalIdeal B := Ideal.mk_ker
  have hnil : IsNilpotent (RingHom.ker (g : B →+* ResidueField B)) := by
    rw [hker]
    exact (IsArtinianRing.isNilpotent_jacobson_bot (R := B)).imp fun n h => by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  let s : ResidueField B →ₐ[ℚ_[l]] B :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℚ_[l] _) g hsurj hnil
  have hs : ∀ x, g (s x) = x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ g hsurj hnil x
  letI alg : Algebra (ResidueField B) B := s.toRingHom.toAlgebra
  have tower : IsScalarTower ℚ_[l] (ResidueField B) B := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change algebraMap ℚ_[l] B r = s (algebraMap ℚ_[l] (ResidueField B) r)
    exact (s.commutes r).symm
  let π : B →ₐ[ResidueField B] ResidueField B :=
    { (g : B →+* ResidueField B) with
      commutes' := fun x => hs x }
  refine ⟨ResidueField B, inferInstance, inferInstance, inferInstance, alg, tower, π, ?_⟩
  intro a ha
  have hmem : a ∈ maximalIdeal B := by
    rw [← hker]
    exact ha
  exact Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hmem

end GlobalTheory
