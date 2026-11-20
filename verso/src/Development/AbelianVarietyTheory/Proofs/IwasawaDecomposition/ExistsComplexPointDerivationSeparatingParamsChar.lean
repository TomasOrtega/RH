import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtDerivSep

open IsLocalRing

/- English proof (translation)
Take `⟨hspan, hdim⟩` from `hf`. Establish `hfm : ∀ i, f i ∈ maximalIdeal R` using `fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩`. Set `v : Fin m → CotangentSpace R` to `fun i => (maximalIdeal R).toCotangent ⟨f i, hfm i⟩`. Establish `hv : Submodule.span (ResidueField R) (Set.range v) = ⊤`. Establish `e : Set.range v = (maximalIdeal R).toCotangent '' Set.range (fun i => (⟨f i, hfm i⟩ : maximalIdeal R))`.

Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e, CotangentSpace.span_image_eq_top_iff]`. Apply `Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`.

Conclude with `hspan`. Establish `hfr : Module.finrank (ResidueField R) (CotangentSpace R) = m`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← finrank_top (ResidueField R) (CotangentSpace R), ← hv]`. Conclude with `(finrank_range_le_card v).trans (by simp)`.

Establish `h1` using `ringKrullDim_le_spanFinrank_maximalIdeal R`. Rewrite `h1` using `[spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hdim]`. Conclude with `h1` after adjusting the coercions. Establish `hli : LinearIndependent (ResidueField R) v` using `linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hfr])`. Set `b` to `Module.Basis.mk hli hv.ge`.

Take `⟨j, hj⟩` from `Function.ne_iff.1 hl`. Set `emb : ResidueField R →+* ℂ` to `ResidueField.lift ψ`. Establish `hemb : ∀ r : R, emb (residue R r) = ψ r` using `fun r => ResidueField.lift_residue_apply ψ r`. Set `g : R ⧸ maximalIdeal R ^ 2 →ₐ[k] ResidueField R` to `Ideal.Quotient.liftₐ (maximalIdeal R ^ 2) (IsScalarTower.toAlgHom k R (ResidueField R)) (fun a ha => (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha))`. Establish `hgr : ∀ r : R, g (Ideal.Quotient.mk _ r) = residue R r` using `fun r => rfl`.

Establish `hg : Function.Surjective g`. Introduce `c`. Take `⟨r, rfl⟩` from `residue_surjective c`. Conclude with `⟨Ideal.Quotient.mk _ r, hgr r⟩`. Establish `hnil : IsNilpotent (RingHom.ker g)`.

Use `⟨2, le_bot_iff.1 ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two (RingHom.ker g), Ideal.mul_le]`. Introduce `x hx y hy`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Establish `hr : r ∈ maximalIdeal R` using `(residue_eq_zero_iff r).1 ((hgr r).symm.trans (RingHom.mem_ker.1 hx))`. Establish `hs : s ∈ maximalIdeal R` using `(residue_eq_zero_iff s).1 ((hgr s).symm.trans (RingHom.mem_ker.1 hy))`. Rewrite using `[← map_mul, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_two]`. Conclude with `Ideal.mul_mem_mul hr hs`. Set `s` to `Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil`.

Establish `hs : ∀ c, g (s c) = c` using `fun c => congrArg (fun φ : ResidueField R →ₐ[k] ResidueField R => φ c) (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil)`. Set `t : ResidueField R → R` to `fun c => Function.surjInv Ideal.Quotient.mk_surjective (s c)`. Establish `ht : ∀ c, Ideal.Quotient.mk (maximalIdeal R ^ 2) (t c) = s c` using `fun c => Function.surjInv_eq Ideal.Quotient.mk_surjective (s c)`. Establish `hrt : ∀ c, residue R (t c) = c` using `fun c => by rw [← hgr, ht, hs]`. Set `e : R → R` to `fun r => r - t (residue R r)`.

Establish `he : ∀ r, e r ∈ maximalIdeal R` using `fun r => (residue_eq_zero_iff _).1 (by simp only [e, map_sub, hrt, sub_self])`. Establish `hmk : ∀ a : R, Ideal.Quotient.mk (maximalIdeal R ^ 2) a = 0 → a ∈ maximalIdeal R ^ 2` using `fun a h => Ideal.Quotient.eq_zero_iff_mem.1 h`. Establish `hcot : ∀ (a a' : R) (ha : a ∈ maximalIdeal R) (ha' : a' ∈ maximalIdeal R), a - a' ∈ maximalIdeal R ^ 2 → (maximalIdeal R).toCotangent ⟨a, ha⟩ = (maximalIdeal R).toCotangent ⟨a', ha'⟩` using `fun a a' ha ha' h => (Ideal.toCotangent_eq _).2 h`. Set `D0 : R → ℂ` to `fun r => emb (b.repr ((maximalIdeal R).toCotangent ⟨e r, he r⟩) j)`. Establish `hadd : ∀ x y, D0 (x + y) = D0 x + D0 y`.

Introduce `x y`. Establish `h1 : (maximalIdeal R).toCotangent ⟨e (x + y), he (x + y)⟩ = (maximalIdeal R).toCotangent ⟨e x + e y, add_mem (he x) (he y)⟩`. Use `hcot _ _ _ _ (hmk _ ?_)` and prove the remaining obligations. Simplify using `only [e, map_sub, map_add, ht]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `map_add (maximalIdeal R).toCotangent ⟨e x, he x⟩ ⟨e y, he y⟩`. Simplify using `only [D0, h1]`. Rewrite using `[show (⟨e x + e y, add_mem (he x) (he y)⟩ : maximalIdeal R) = ⟨e x, he x⟩ + ⟨e y, he y⟩ from rfl, h2, map_add, Finsupp.add_apply, map_add]`. Establish `hmul : ∀ x y, D0 (x * y) = ψ x * D0 y + ψ y * D0 x`. Introduce `x y`.

Establish `hm2 : ∀ a b : R, a ∈ maximalIdeal R → b ∈ maximalIdeal R → a * b ∈ maximalIdeal R ^ 2` using `fun a b ha hb => by rw [pow_two]; exact Ideal.mul_mem_mul ha hb`. Establish `h1 : (maximalIdeal R).toCotangent ⟨e (x * y), he (x * y)⟩ = (maximalIdeal R).toCotangent (t (residue R x) • (⟨e y, he y⟩ : maximalIdeal R) + t (residue R y) • (⟨e x, he x⟩ : maximalIdeal R))`. Use `hcot _ _ _ _ ?_` and prove the remaining obligations. Establish `q : e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) = e x * e y + (t (residue R x) * t (residue R y) - t (residue R (x * y)))`. Simplify using `only [e]`.

Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) ∈ _`. Rewrite using `[q]`. Use `add_mem (hm2 _ _ (he x) (he y)) (hmk _ ?_)` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, ht, ht, ht, map_mul, map_mul, sub_self]`.

Simplify using `only [D0, h1, map_add, map_smul]`. Rewrite using `[← algebraMap_smul (ResidueField R) (t (residue R x)), ← algebraMap_smul (ResidueField R) (t (residue R y)), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, ResidueField.algebraMap_eq, hrt, hrt, h …`. Set `D : R →+ ℂ` to `AddMonoidHom.mk' D0 hadd`. Use `⟨D, fun a => ?_, hmul, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D0 _ = 0`.

Establish `h1 : (maximalIdeal R).toCotangent ⟨e (algebraMap k R a), he _⟩ = (maximalIdeal R).toCotangent ⟨0, zero_mem _⟩`. Use `hcot _ _ _ _ (hmk _ ?_)` and prove the remaining obligations. Establish `r1 : residue R (algebraMap k R a) = algebraMap k (ResidueField R) a` using `(IsScalarTower.algebraMap_apply k R (ResidueField R) a).symm`. Use `show Ideal.Quotient.mk _ (algebraMap k R a - t (residue R (algebraMap k R a)) - 0) = 0`. Rewrite using `[sub_zero, map_sub, ht, r1, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, sub_self]`.

Simplify using `only [D0, h1]`. Rewrite using `[show (⟨0, zero_mem _⟩ : maximalIdeal R) = 0 from rfl, map_zero, map_zero, Finsupp.zero_apply, map_zero]`. Establish `hfi : ∀ i, D0 (f i) = emb (Finsupp.single i 1 j)`. Introduce `i`. Establish `h1 : (maximalIdeal R).toCotangent ⟨e (f i), he _⟩ = b i`.

Rewrite using `[Module.Basis.mk_apply]`. Use `hcot _ _ _ _ (hmk _ ?_)` and prove the remaining obligations. Establish `r0 : residue R (f i) = 0` using `(residue_eq_zero_iff _).2 (hfm i)`. Use `show Ideal.Quotient.mk _ (f i - t (residue R (f i)) - f i) = 0`. Rewrite using `[r0, sub_sub_cancel_left, map_neg, ht, map_zero, neg_zero]`.

Simplify using `only [D0, h1, Module.Basis.repr_self]`. Express the relevant statement in the definitionally equal form `∑ i, l i * D0 (f i) ≠ 0`. Simplify using `only [hfi]`. Rewrite using `[Finset.sum_eq_single j (fun i _ hi => by rw [Finsupp.single_apply, if_neg hi, map_zero, mul_zero]) (fun h => (h (Finset.mem_univ j)).elim), Finsupp.single_eq_same, map_one, _root_.mul_one]`. Conclude with `hj`.
-/
theorem exists_der_of_rsp {k R : Type} [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Algebra.FormallySmooth k (ResidueField R)] (ψ : R →+* ℂ) [IsLocalHom ψ] (m : ℕ)
    (f : Fin m → R) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m f) (l : Fin m → ℂ) (hl : l ≠ 0) :
    ∃ D : R →+ ℂ, (∀ a : k, D (algebraMap k R a) = 0) ∧
      (∀ x y, D (x * y) = ψ x * D y + ψ y * D x) ∧ ∑ i, l i * D (f i) ≠ 0 := by
  classical
  obtain ⟨hspan, hdim⟩ := hf
  have hfm : ∀ i, f i ∈ maximalIdeal R := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨f i, hfm i⟩
  have hv : Submodule.span (ResidueField R) (Set.range v) = ⊤ := by
    have e : Set.range v = (maximalIdeal R).toCotangent '' Set.range
        (fun i => (⟨f i, hfm i⟩ : maximalIdeal R)) := by
      rw [← Set.range_comp]; rfl
    rw [e, CotangentSpace.span_image_eq_top_iff]
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hspan
  have hfr : Module.finrank (ResidueField R) (CotangentSpace R) = m := by
    apply le_antisymm
    · rw [← finrank_top (ResidueField R) (CotangentSpace R), ← hv]
      exact (finrank_range_le_card v).trans (by simp)
    · have h1 := ringKrullDim_le_spanFinrank_maximalIdeal R
      rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hdim] at h1
      exact_mod_cast h1
  have hli : LinearIndependent (ResidueField R) v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hfr])
  let b := Module.Basis.mk hli hv.ge
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hl

  let emb : ResidueField R →+* ℂ := ResidueField.lift ψ
  have hemb : ∀ r : R, emb (residue R r) = ψ r := fun r => ResidueField.lift_residue_apply ψ r
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[k] ResidueField R :=
    Ideal.Quotient.liftₐ (maximalIdeal R ^ 2) (IsScalarTower.toAlgHom k R (ResidueField R))
      (fun a ha => (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha))
  have hgr : ∀ r : R, g (Ideal.Quotient.mk _ r) = residue R r := fun r => rfl
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨Ideal.Quotient.mk _ r, hgr r⟩
  have hnil : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, le_bot_iff.1 ?_⟩
    rw [pow_two (RingHom.ker g), Ideal.mul_le]
    intro x hx y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hr : r ∈ maximalIdeal R := (residue_eq_zero_iff r).1 ((hgr r).symm.trans (RingHom.mem_ker.1 hx))
    have hs : s ∈ maximalIdeal R := (residue_eq_zero_iff s).1 ((hgr s).symm.trans (RingHom.mem_ker.1 hy))
    rw [← map_mul, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hr hs
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil
  have hs : ∀ c, g (s c) = c := fun c =>
    congrArg (fun φ : ResidueField R →ₐ[k] ResidueField R => φ c)
      (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil)
  let t : ResidueField R → R := fun c => Function.surjInv Ideal.Quotient.mk_surjective (s c)
  have ht : ∀ c, Ideal.Quotient.mk (maximalIdeal R ^ 2) (t c) = s c := fun c =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (s c)
  have hrt : ∀ c, residue R (t c) = c := fun c => by rw [← hgr, ht, hs]
  let e : R → R := fun r => r - t (residue R r)
  have he : ∀ r, e r ∈ maximalIdeal R := fun r =>
    (residue_eq_zero_iff _).1 (by simp only [e, map_sub, hrt, sub_self])
  have hmk : ∀ a : R, Ideal.Quotient.mk (maximalIdeal R ^ 2) a = 0 → a ∈ maximalIdeal R ^ 2 :=
    fun a h => Ideal.Quotient.eq_zero_iff_mem.1 h
  have hcot : ∀ (a a' : R) (ha : a ∈ maximalIdeal R) (ha' : a' ∈ maximalIdeal R),
      a - a' ∈ maximalIdeal R ^ 2 →
      (maximalIdeal R).toCotangent ⟨a, ha⟩ = (maximalIdeal R).toCotangent ⟨a', ha'⟩ :=
    fun a a' ha ha' h => (Ideal.toCotangent_eq _).2 h
  let D0 : R → ℂ := fun r => emb (b.repr ((maximalIdeal R).toCotangent ⟨e r, he r⟩) j)
  have hadd : ∀ x y, D0 (x + y) = D0 x + D0 y := by
    intro x y
    have h1 : (maximalIdeal R).toCotangent ⟨e (x + y), he (x + y)⟩ =
        (maximalIdeal R).toCotangent ⟨e x + e y, add_mem (he x) (he y)⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      simp only [e, map_sub, map_add, ht]
      ring
    have h2 := map_add (maximalIdeal R).toCotangent ⟨e x, he x⟩ ⟨e y, he y⟩
    simp only [D0, h1]
    rw [show (⟨e x + e y, add_mem (he x) (he y)⟩ : maximalIdeal R) = ⟨e x, he x⟩ + ⟨e y, he y⟩ from rfl,
      h2, map_add, Finsupp.add_apply, map_add]
  have hmul : ∀ x y, D0 (x * y) = ψ x * D0 y + ψ y * D0 x := by
    intro x y
    have hm2 : ∀ a b : R, a ∈ maximalIdeal R → b ∈ maximalIdeal R → a * b ∈ maximalIdeal R ^ 2 :=
      fun a b ha hb => by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    have h1 : (maximalIdeal R).toCotangent ⟨e (x * y), he (x * y)⟩ =
        (maximalIdeal R).toCotangent (t (residue R x) • (⟨e y, he y⟩ : maximalIdeal R) +
          t (residue R y) • (⟨e x, he x⟩ : maximalIdeal R)) := by
      refine hcot _ _ _ _ ?_
      have q : e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) =
          e x * e y + (t (residue R x) * t (residue R y) - t (residue R (x * y))) := by
        simp only [e]; ring
      change e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) ∈ _
      rw [q]
      refine add_mem (hm2 _ _ (he x) (he y)) (hmk _ ?_)
      rw [map_sub, map_mul, ht, ht, ht, map_mul, map_mul, sub_self]
    simp only [D0, h1, map_add, map_smul]
    rw [← algebraMap_smul (ResidueField R) (t (residue R x)),
      ← algebraMap_smul (ResidueField R) (t (residue R y)), map_smul, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul, ResidueField.algebraMap_eq, hrt, hrt, hemb, hemb]
  let D : R →+ ℂ := AddMonoidHom.mk' D0 hadd
  refine ⟨D, fun a => ?_, hmul, ?_⟩
  · change D0 _ = 0
    have h1 : (maximalIdeal R).toCotangent ⟨e (algebraMap k R a), he _⟩ =
        (maximalIdeal R).toCotangent ⟨0, zero_mem _⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      have r1 : residue R (algebraMap k R a) = algebraMap k (ResidueField R) a :=
        (IsScalarTower.algebraMap_apply k R (ResidueField R) a).symm
      show Ideal.Quotient.mk _ (algebraMap k R a - t (residue R (algebraMap k R a)) - 0) = 0
      rw [sub_zero, map_sub, ht, r1, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, sub_self]
    simp only [D0, h1]
    rw [show (⟨0, zero_mem _⟩ : maximalIdeal R) = 0 from rfl, map_zero, map_zero, Finsupp.zero_apply,
      map_zero]
  · have hfi : ∀ i, D0 (f i) = emb (Finsupp.single i 1 j) := by
      intro i
      have h1 : (maximalIdeal R).toCotangent ⟨e (f i), he _⟩ = b i := by
        rw [Module.Basis.mk_apply]
        refine hcot _ _ _ _ (hmk _ ?_)
        have r0 : residue R (f i) = 0 := (residue_eq_zero_iff _).2 (hfm i)
        show Ideal.Quotient.mk _ (f i - t (residue R (f i)) - f i) = 0
        rw [r0, sub_sub_cancel_left, map_neg, ht, map_zero, neg_zero]
      simp only [D0, h1, Module.Basis.repr_self]
    change ∑ i, l i * D0 (f i) ≠ 0
    simp only [hfi]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [Finsupp.single_apply, if_neg hi, map_zero, mul_zero])
      (fun h => (h (Finset.mem_univ j)).elim), Finsupp.single_eq_same, map_one, _root_.mul_one]
    exact hj

end GlobalTheory.PtDerivSep

namespace GlobalTheory.PtDerivSep

open IsLocalRing

/- English proof (translation)
Introduce `k _ _ Y p n σ hsm x₀ U hy m f hR l hl`. Use `haveI := hsm`. Use `haveI : Smooth p := SmoothOfRelativeDimension.smooth n p`. Set `c : k →+* Γ(Y, U.1)` to `ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1`. Establish `hft : c.FiniteType` using `(p.finiteType_appLE (isAffineOpen_top _) U.2 le_top).comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)`.

Set `germ : Γ(Y, U.1) →+* Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))` to `(Y.presheaf.germ U.1 _ hy).hom`. Establish `hloc : germ.EssFiniteType`. Use `letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)`. Use `haveI := U.2.isLocalization_stalk ⟨_, hy⟩`. Conclude with `Algebra.EssFiniteType.of_isLocalization (Y.presheaf.stalk _) (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl`.

Establish `hnoeth : IsNoetherianRing (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)))`. Use `letI := c.toAlgebra`. Use `haveI : Algebra.FiniteType k Γ(Y, U.1) := hft`. Use `haveI : IsNoetherianRing Γ(Y, U.1) := Algebra.FiniteType.isNoetherianRing k _`. Use `letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)`.

Use `haveI := U.2.isLocalization_stalk ⟨_, hy⟩`. Conclude with `IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl _ inferInstance`. Use `letI : Algebra k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := (germ.comp c).toAlgebra`. Use `haveI : Algebra.EssFiniteType k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := RingHom.essFiniteType_algebraMap.1 (hft.essFiniteType.comp hloc)`. Use `haveI : Algebra.EssFiniteType k (ResidueField (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)))) := .of_surjective (IsScalarTower.toAlgHom k _ _) residue_surjective`.

Set `ψ` to `(Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) x₀.1).hom`. Take `⟨D, h1, h2, h3⟩` from `exists_der_of_rsp (k := k) ψ m _ hR l hl`. Establish `hx : x₀ ∈ CxPts.ptsIn p σ U.1` using `CxPts.mem_ptsIn.2 hy`. Establish `hψ : ∀ g, ψ (germ g) = CxPts.ev p σ U.1 g x₀`. Introduce `g`.

Rewrite using `[CxPts.ev_eq hx, CxPts.evHom, ← GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x₀.1 U.1 hx]`. Both sides reduce to the same expression. Use `⟨D.comp germ.toAddMonoidHom, fun a => h1 a, fun g h => ?_, h3⟩` and prove the remaining obligations. Simplify using `only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul, h2, hψ]`.
-/
theorem exists_ptDer_sep : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ∀ (x₀ : CxPts p σ) (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m (fun i => Y.presheaf.germ U.1 _ hy (f i)) → ∀ l : Fin m → ℂ, l ≠ 0 → ∃ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) ∧ (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) ∧ ∑ i, l i * δ (f i) ≠ 0 := by
  intro k _ _ Y p n σ hsm x₀ U hy m f hR l hl
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  let c : k →+* Γ(Y, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1
  have hft : c.FiniteType := (p.finiteType_appLE (isAffineOpen_top _) U.2 le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let germ : Γ(Y, U.1) →+* Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)) :=
    (Y.presheaf.germ U.1 _ hy).hom
  have hloc : germ.EssFiniteType := by
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact Algebra.EssFiniteType.of_isLocalization (Y.presheaf.stalk _)
      (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl
  have hnoeth : IsNoetherianRing (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := by
    letI := c.toAlgebra
    haveI : Algebra.FiniteType k Γ(Y, U.1) := hft
    haveI : IsNoetherianRing Γ(Y, U.1) := Algebra.FiniteType.isNoetherianRing k _
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl _ inferInstance
  letI : Algebra k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := (germ.comp c).toAlgebra
  haveI : Algebra.EssFiniteType k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) :=
    RingHom.essFiniteType_algebraMap.1 (hft.essFiniteType.comp hloc)
  haveI : Algebra.EssFiniteType k (ResidueField (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)))) :=
    .of_surjective (IsScalarTower.toAlgHom k _ _) residue_surjective
  let ψ := (Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) x₀.1).hom
  obtain ⟨D, h1, h2, h3⟩ := exists_der_of_rsp (k := k) ψ m _ hR l hl
  have hx : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have hψ : ∀ g, ψ (germ g) = CxPts.ev p σ U.1 g x₀ := by
    intro g
    rw [CxPts.ev_eq hx, CxPts.evHom, ← GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x₀.1 U.1 hx]
    rfl
  refine ⟨D.comp germ.toAddMonoidHom, fun a => h1 a, fun g h => ?_, h3⟩
  simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul, h2, hψ]

end GlobalTheory.PtDerivSep
