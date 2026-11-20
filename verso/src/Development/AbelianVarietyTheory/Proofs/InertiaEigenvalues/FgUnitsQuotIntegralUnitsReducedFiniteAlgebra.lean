import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.NormUnits

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `choose S hS using fun i => Group.fg_iff.mp (hG i)`. Use `Group.fg_iff.mpr ⟨⋃ i, Pi.mulSingle i '' S i, ?_, Set.finite_iUnion fun i => (hS i).2.image _⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Rewrite using `[← Finset.univ_prod_mulSingle x]`. Use `Subgroup.prod_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hx : x i ∈ Subgroup.closure (S i)` using `by rw [(hS i).1]; trivial`. Establish `h1 : Pi.mulSingle i (x i) ∈ (Subgroup.closure (S i)).map (MonoidHom.mulSingle G i)` using `⟨x i, hx, rfl⟩`. Rewrite `h1` using `[MonoidHom.map_closure]`.

Conclude with `Subgroup.closure_mono (fun y hy => Set.mem_iUnion.2 ⟨i, hy⟩) h1`.
-/
theorem group_fg_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, CommGroup (G i)]
    (hG : ∀ i, Group.FG (G i)) : Group.FG (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose S hS using fun i => Group.fg_iff.mp (hG i)
  refine Group.fg_iff.mpr ⟨⋃ i, Pi.mulSingle i '' S i, ?_,
    Set.finite_iUnion fun i => (hS i).2.image _⟩
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_prod_mulSingle x]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have hx : x i ∈ Subgroup.closure (S i) := by rw [(hS i).1]; trivial
  have h1 : Pi.mulSingle i (x i) ∈ (Subgroup.closure (S i)).map (MonoidHom.mulSingle G i) :=
    ⟨x i, hx, rfl⟩
  rw [MonoidHom.map_closure] at h1
  exact Subgroup.closure_mono (fun y hy => Set.mem_iUnion.2 ⟨i, hy⟩) h1

/- English proof (translation)
Use `Fintype.ofFinite (MaximalSpectrum A)` as an intermediate fact. Use `choose p hpm hp using hx`. Use `⟨∏ I, p I, monic_prod_of_monic _ _ fun I _ => hpm I, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def]`. Apply `(IsArtinianRing.equivPi A).injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `J`. Rewrite using `[map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply, map_prod, map_prod]`. Use `Finset.prod_eq_zero (Finset.mem_univ J) ?_` and prove the remaining obligations. Establish `h2` using `aeval_algHom_apply (Ideal.Quotient.mkₐ O J.asIdeal) x (p J)`. Rewrite `h2` using `[Ideal.Quotient.mkₐ_eq_mk]`.

Rewrite using `[← h2, aeval_def]`. Conclude with `hp J`.
-/
theorem isIntegral_of_forall_quot {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [IsArtinianRing A] [IsReduced A] (x : A)
    (hx : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal x)) :
    IsIntegral O x := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum A)
  choose p hpm hp using hx
  refine ⟨∏ I, p I, monic_prod_of_monic _ _ fun I _ => hpm I, ?_⟩
  rw [← aeval_def]
  apply (IsArtinianRing.equivPi A).injective
  funext J
  rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply, map_prod, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ J) ?_
  have h2 := aeval_algHom_apply (Ideal.Quotient.mkₐ O J.asIdeal) x (p J)
  rw [Ideal.Quotient.mkₐ_eq_mk] at h2
  rw [← h2, aeval_def]
  exact hp J

/- English proof (translation)
Introduce `K hL A _ _ _ _ _ _`. Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite K.E A`. Use `Fintype.ofFinite (MaximalSpectrum A)` as an intermediate fact. Establish `hfg : ∀ I : MaximalSpectrum A, Group.FG ((A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal))`. Introduce `I`.

Use `haveI := I.isMaximal`. Use `letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal`. Use `haveI : FiniteDimensional K.E (A ⧸ I.asIdeal) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E I.asIdeal).toLinearMap Ideal.Quotient.mk_surjective`. Conclude with `hL (A ⧸ I.asIdeal)`. Establish `hP` using `group_fg_pi (fun I : MaximalSpectrum A => (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) hfg`.

Set `ψ : Aˣ →* ∀ I : MaximalSpectrum A, (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)` to `MonoidHom.pi fun I => (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)`. Establish `hsurj : Function.Surjective ψ`. Introduce `c`. Use `choose u hu using fun I => QuotientGroup.mk'_surjective _ (c I)`. Set `e` to `IsArtinianRing.equivPi A`.

Use `⟨Units.map (e.symm : (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) →* A) (MulEquiv.piUnits.symm u), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `I`. Rewrite using `[← hu I]`. Express the relevant statement in the definitionally equal form `QuotientGroup.mk' _ _ = _`. Use `congr 1`.

Use `ext`. Establish `h3 : ∀ z : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal, Ideal.Quotient.mk I.asIdeal (e.symm z) = z I` using `fun z => by`. Rewrite using `[← IsArtinianRing.equivPi_apply A (e.symm z) I]`. Conclude with `congrFun (e.apply_symm_apply z) I`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`.

Rewrite using `[h3]`. Both sides reduce to the same expression. Establish `hker : ψ.ker ≤ intUnits K.O A`. Introduce `t ht`. Establish `hI : ∀ I : MaximalSpectrum A, Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom t ∈ intUnits K.O (A ⧸ I.asIdeal)` using `fun I => (QuotientGroup.eq_one_iff _).mp (congrFun (MonoidHom.mem_ker.mp ht) I)`.

Use `⟨NormUnits.isIntegral_of_forall_quot _ fun I => (hI I).1, NormUnits.isIntegral_of_forall_quot _ fun I => ?_⟩` and prove the remaining obligations. Use `(hI I).2` as an intermediate fact. Rewrite `this` using `[Units.coe_map_inv]`. Then use the resulting hypothesis. Use `haveI : Group.FG (Aˣ ⧸ ψ.ker) := Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.toMonoidHom) (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.surjective`. Use `Group.fg_of_surjective (f := QuotientGroup.map ψ.ker (intUnits K.O A) (MonoidHom.id _) fun t ht => hker ht) ?_` and prove the remaining obligations.

Introduce `q`. Take `⟨y, rfl⟩` from `QuotientGroup.mk'_surjective _ q`. Conclude with `⟨QuotientGroup.mk y, rfl⟩`.
-/
theorem units_quot_intUnits_fg : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L]
    [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) →
    ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A]
    [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  intro K hL A _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K.E A
  have := Fintype.ofFinite (MaximalSpectrum A)

  have hfg : ∀ I : MaximalSpectrum A,
      Group.FG ((A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K.E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact hL (A ⧸ I.asIdeal)
  have hP := group_fg_pi (fun I : MaximalSpectrum A =>
    (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) hfg
  let ψ : Aˣ →* ∀ I : MaximalSpectrum A, (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal) :=
    MonoidHom.pi fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hsurj : Function.Surjective ψ := by
    intro c
    choose u hu using fun I => QuotientGroup.mk'_surjective _ (c I)
    let e := IsArtinianRing.equivPi A
    refine ⟨Units.map (e.symm : (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) →* A)
      (MulEquiv.piUnits.symm u), ?_⟩
    funext I
    rw [← hu I]
    change QuotientGroup.mk' _ _ = _
    congr 1
    ext
    have h3 : ∀ z : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal,
        Ideal.Quotient.mk I.asIdeal (e.symm z) = z I := fun z => by
      rw [← IsArtinianRing.equivPi_apply A (e.symm z) I]
      exact congrFun (e.apply_symm_apply z) I
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [h3]
    rfl
  have hker : ψ.ker ≤ intUnits K.O A := by
    intro t ht
    have hI : ∀ I : MaximalSpectrum A,
        Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom t ∈ intUnits K.O (A ⧸ I.asIdeal) :=
      fun I => (QuotientGroup.eq_one_iff _).mp (congrFun (MonoidHom.mem_ker.mp ht) I)
    refine ⟨NormUnits.isIntegral_of_forall_quot _ fun I => (hI I).1,
      NormUnits.isIntegral_of_forall_quot _ fun I => ?_⟩
    have := (hI I).2
    rwa [Units.coe_map_inv] at this
  haveI : Group.FG (Aˣ ⧸ ψ.ker) :=
    Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map ψ.ker (intUnits K.O A) (MonoidHom.id _) fun t ht => hker ht) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨QuotientGroup.mk y, rfl⟩

end GlobalTheory.UnitLemma.NormUnits
