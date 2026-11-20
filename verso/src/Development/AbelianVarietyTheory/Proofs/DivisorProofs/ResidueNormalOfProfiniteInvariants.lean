import Mathlib

namespace GlobalTheory

attribute [local instance] Subgroup.finiteIndex_of_finite_quotient

open Polynomial in

/- English proof (translation)
Introduce `A B _ _ _ G _ _ _ _ _ _ _ _ _ _ _ P Q _ _ _`. Use `letI := Ideal.Quotient.field P`. Use `letI := Ideal.Quotient.field Q`. Establish `hint : Algebra.IsIntegral A B` using `Algebra.IsInvariant.isIntegral_of_profinite (G := G)`. Establish `hint' : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q)` using `Ideal.Quotient.algebra_isIntegral_of_liesOver Q P`.

Use `normal_iff.2 fun ξ => ⟨Algebra.IsIntegral.isIntegral ξ, ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective ξ`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (stabilizer_isOpen G b) (one_mem _)`. Set `B'` to `FixedPoints.subalgebra A B N.1.1`. Set `b' : B'` to `⟨b, fun g => hN g.2⟩`.

Set `Q' : Ideal B'` to `Q.under B'`. Establish `hintB : Algebra.IsIntegral B' B` using `Algebra.IsIntegral.tower_top A`. Use `haveI hQ' : Q'.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q`. Use `haveI : Q'.LiesOver P := ⟨by`. Rewrite using `[Ideal.under_under (A := A) (B := B') (C := B)]`.

Conclude with `Ideal.LiesOver.over⟩`. Use `letI := Ideal.Quotient.field Q'`. Establish `hn : Normal (A ⧸ P) (B' ⧸ Q')` using `Ideal.Quotient.normal (G ⧸ N.1.1) P Q'`. Set `f : (B' ⧸ Q') →ₐ[A ⧸ P] B ⧸ Q` to `{ toRingHom := Ideal.quotientMap _ B'.val le_rfl, commutes' := Quotient.ind fun _ ↦ rfl }`. Establish `hf : Function.Injective f` using `f.toRingHom.injective`.

Establish `hfb : f (Ideal.Quotient.mk Q' b') = Ideal.Quotient.mk Q b` using `rfl`. Rewrite using `[← hfb, minpoly.algHom_eq f hf]`. Establish `hs` using `hn.splits (Ideal.Quotient.mk Q' b')`. Use `hs.map f.toRingHom` as an intermediate fact. Rewrite `this` using `[Polynomial.map_map]`.

Establish `hc : (f : (B' ⧸ Q') →+* B ⧸ Q).comp (algebraMap (A ⧸ P) (B' ⧸ Q')) = algebraMap (A ⧸ P) (B ⧸ Q)` using `f.comp_algebraMap`. Simplify `this` using `only [AlgHom.toRingHom_eq_coe, hc]`.
-/
theorem Ideal.Quotient.normal_of_profinite : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal], letI := Ideal.Quotient.field P; letI := Ideal.Quotient.field Q; Normal (A ⧸ P) (B ⧸ Q) := by
  intro A B _ _ _ G _ _ _ _ _ _ _ _ _ _ _ P Q _ _ _
  letI := Ideal.Quotient.field P
  letI := Ideal.Quotient.field Q
  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  have hint' : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  refine normal_iff.2 fun ξ => ⟨Algebra.IsIntegral.isIntegral ξ, ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ξ
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (stabilizer_isOpen G b) (one_mem _)
  let B' := FixedPoints.subalgebra A B N.1.1
  let b' : B' := ⟨b, fun g => hN g.2⟩
  let Q' : Ideal B' := Q.under B'
  have hintB : Algebra.IsIntegral B' B := Algebra.IsIntegral.tower_top A
  haveI hQ' : Q'.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  haveI : Q'.LiesOver P := ⟨by
    rw [Ideal.under_under (A := A) (B := B') (C := B)]
    exact Ideal.LiesOver.over⟩
  letI := Ideal.Quotient.field Q'
  have hn : Normal (A ⧸ P) (B' ⧸ Q') := Ideal.Quotient.normal (G ⧸ N.1.1) P Q'
  let f : (B' ⧸ Q') →ₐ[A ⧸ P] B ⧸ Q :=
    { toRingHom := Ideal.quotientMap _ B'.val le_rfl,
      commutes' := Quotient.ind fun _ ↦ rfl }
  have hf : Function.Injective f := f.toRingHom.injective
  have hfb : f (Ideal.Quotient.mk Q' b') = Ideal.Quotient.mk Q b := rfl
  rw [← hfb, minpoly.algHom_eq f hf]
  have hs := hn.splits (Ideal.Quotient.mk Q' b')
  have := hs.map f.toRingHom
  rw [Polynomial.map_map] at this
  have hc : (f : (B' ⧸ Q') →+* B ⧸ Q).comp (algebraMap (A ⧸ P) (B' ⧸ Q')) = algebraMap (A ⧸ P) (B ⧸ Q) := f.comp_algebraMap
  simpa only [AlgHom.toRingHom_eq_coe, hc] using this

end GlobalTheory
