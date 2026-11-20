import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelTower
import GroundTheory.TateCohomology.TateResEqZeroOfNsmulEqZero
import GroundTheory.TateCohomology.ResCoresPos
import GroundTheory.TateCohomology.Annihilation
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module IntermediateField

section Sylow

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/- English proof (translation)
Set `e : tateCohomology A (n : ℤ) ≅ groupCohomology A n` to `(TateCohomology.isoGroupCohomology n).app A`. Take `⟨y, hy⟩` from `e.toLinearEquiv.surjective x`. Substitute `hy` using the available equality. It suffices to establish `hy : y = 0 by subst hy; exact map_zero _`. Establish `hidx : ∀ p ∈ (Nat.card G).primeFactors, ∃ P : Sylow p G, (P : Subgroup G).index • y = 0`.

Introduce `p hp`. Take `⟨P, hP⟩` from `h p hp`. Use `⟨P, ?_⟩` and prove the remaining obligations. Establish `hc` using `congrArg (fun f => f.hom y) (GroundTheory.GroupCoh.tateRes_comp_isoGroupCohomology (P : Subgroup G) n A)`. Simplify using `only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc`.

Establish `hres : ((GroundTheory.GroupCoh.tateRes (P : Subgroup G) n).app A).hom y = 0`. Establish `hinj : Function.Injective ((TateCohomology.isoGroupCohomology n).app (Rep.res (P : Subgroup G).subtype A)).toLinearEquiv` using `LinearEquiv.injective _`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `hc.trans hP`.

Rewrite using `[← GroundTheory.GroupCoh.tateCores_app_tateRes_app_apply (P : Subgroup G) A n y, hres, map_zero]`. Establish `hG : Nat.card G • y = 0`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `GroundTheory.GroupCoh.card_smul_tateCohomology A n y`. Assume the negation of the conclusion as `hne`.

Establish `hm1 : addOrderOf y ≠ 1` using `fun h1 => hne (AddMonoid.addOrderOf_eq_one_iff.1 h1)`. Use `set q := (addOrderOf y).minFac`. Establish `hq : q.Prime` using `Nat.minFac_prime hm1`. Establish `hqG : q ∣ Nat.card G` using `(Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hG)`. Establish `hqmem : q ∈ (Nat.card G).primeFactors` using `Nat.mem_primeFactors.2 ⟨hq, hqG, Nat.card_pos.ne'⟩`.

Take `⟨P, hP⟩` from `hidx q hqmem`. Establish `: Fact q.Prime` using `⟨hq⟩`. Conclude with `P.not_dvd_index ((Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hP))`.
-/
theorem eq_zero_of_forall_sylow_map_eq_zero (A : Rep.{u} k G) (n : ℕ) [NeZero n]
    (x : groupCohomology A n)
    (h : ∀ p ∈ (Nat.card G).primeFactors, ∃ P : Sylow p G,
      (groupCohomology.map (P : Subgroup G).subtype (𝟙 _) n).hom x = 0) :
    x = 0 := by
  classical
  let e : tateCohomology A (n : ℤ) ≅ groupCohomology A n :=
    (TateCohomology.isoGroupCohomology n).app A
  obtain ⟨y, hy⟩ := e.toLinearEquiv.surjective x
  subst hy
  suffices hy : y = 0 by subst hy; exact map_zero _

  have hidx : ∀ p ∈ (Nat.card G).primeFactors, ∃ P : Sylow p G, (P : Subgroup G).index • y = 0 := by
    intro p hp
    obtain ⟨P, hP⟩ := h p hp
    refine ⟨P, ?_⟩
    have hc := congrArg (fun f => f.hom y)
      (GroundTheory.GroupCoh.tateRes_comp_isoGroupCohomology (P : Subgroup G) n A)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    have hres : ((GroundTheory.GroupCoh.tateRes (P : Subgroup G) n).app A).hom y = 0 := by
      have hinj : Function.Injective
          ((TateCohomology.isoGroupCohomology n).app (Rep.res (P : Subgroup G).subtype A)).toLinearEquiv :=
        LinearEquiv.injective _
      apply hinj
      rw [map_zero]
      exact hc.trans hP
    rw [← GroundTheory.GroupCoh.tateCores_app_tateRes_app_apply (P : Subgroup G) A n y, hres, map_zero]

  have hG : Nat.card G • y = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact GroundTheory.GroupCoh.card_smul_tateCohomology A n y
  by_contra hne
  have hm1 : addOrderOf y ≠ 1 := fun h1 => hne (AddMonoid.addOrderOf_eq_one_iff.1 h1)
  set q := (addOrderOf y).minFac
  have hq : q.Prime := Nat.minFac_prime hm1
  have hqG : q ∣ Nat.card G := (Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hG)
  have hqmem : q ∈ (Nat.card G).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hq, hqG, Nat.card_pos.ne'⟩
  obtain ⟨P, hP⟩ := hidx q hqmem
  have : Fact q.Prime := ⟨hq⟩
  exact P.not_dvd_index ((Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hP))

end Sylow

section Level

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def groupCohomologyResIdeleClassIso (H : Subgroup Gal(L/K)) (n : ℕ) :
    groupCohomology (Rep.res H.subtype (ideleClassRep K L)) n ≅
      groupCohomology (ideleClassRep (fixedField H) L) n :=
  groupCohomology.mapIso (subgroupEquivGalFixedField H) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

variable [IsGalois K L]

omit [IsGalois K L] in

/- English proof (translation)
The claim follows from `P.isPGroup'.of_equiv (subgroupEquivGalFixedField _)`.
-/
theorem isPGroup_gal_fixedField_sylow {p : ℕ} (P : Sylow p Gal(L/K)) :
    IsPGroup p Gal(L/fixedField (P : Subgroup Gal(L/K))) :=
  P.isPGroup'.of_equiv (subgroupEquivGalFixedField _)

/- English proof (translation)
Rewrite using `[ModuleCat.isZero_iff_subsingleton]`. Establish `hz : ∀ x : groupCohomology (ideleClassRep K L) 1, x = 0` using `fun x => eq_zero_of_forall_sylow_map_eq_zero _ 1 x fun p hp => by`. Establish `: Fact p.Prime` using `⟨Nat.prime_of_mem_primeFactors hp⟩`. Set `P : Sylow p Gal(L/K)` to `Classical.arbitrary _`. Use `⟨P, ?_⟩` and prove the remaining obligations.

Establish `h0` using `(isZero_groupCohomology_one_ideleClassRep_of_isPGroup (isPGroup_gal_fixedField_sylow P)).of_iso (groupCohomologyResIdeleClassIso (P : Subgroup Gal(L/K)) 1)`. Rewrite `h0` using `[ModuleCat.isZero_iff_subsingleton]`. Conclude with `Subsingleton.elim _ _`. Conclude with `⟨fun x y => by rw [hz x, hz y]⟩`.
-/
theorem isZero_groupCohomology_one_ideleClassRep :
    IsZero (groupCohomology (ideleClassRep K L) 1) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hz : ∀ x : groupCohomology (ideleClassRep K L) 1, x = 0 := fun x =>
    eq_zero_of_forall_sylow_map_eq_zero _ 1 x fun p hp => by
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      let P : Sylow p Gal(L/K) := Classical.arbitrary _
      refine ⟨P, ?_⟩
      have h0 := (isZero_groupCohomology_one_ideleClassRep_of_isPGroup
        (isPGroup_gal_fixedField_sylow P)).of_iso
        (groupCohomologyResIdeleClassIso (P : Subgroup Gal(L/K)) 1)
      rw [ModuleCat.isZero_iff_subsingleton] at h0
      exact Subsingleton.elim _ _
  exact ⟨fun x y => by rw [hz x, hz y]⟩

/- English proof (translation)
Use `set n := Nat.card Gal(L/K) with hn`. Establish `hn0 : n ≠ 0` using `Nat.card_pos.ne'`. Establish `hS : ∀ p : n.primeFactors, ∃ _ : Sylow (p : ℕ) Gal(L/K), True` using `fun p => by`. Establish `: Fact (p : ℕ).Prime` using `⟨Nat.prime_of_mem_primeFactors p.2⟩`. Conclude with `⟨Classical.arbitrary _, trivial⟩`.

Use `choose P _ using hS`. Set `Φ : groupCohomology (ideleClassRep K L) 2 →+ ∀ p : n.primeFactors, groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2` to `AddMonoidHom.pi fun p => ((groupCohomologyResIdeleClassIso (P p : Subgroup Gal(L/K)) 2).hom.hom.comp (groupCohomology.map (P p : Subgroup Gal(L/K)).subtype (𝟙 _) 2).hom).toAddMonoidHom`. Establish `hΦ : Function.Injective Φ`. Use `(injective_iff_map_eq_zero Φ).2 fun x hx => ?_` and prove the remaining obligations. Use `eq_zero_of_forall_sylow_map_eq_zero _ 2 x fun p hp => ⟨P ⟨p, hp⟩, ?_⟩` and prove the remaining obligations.

Establish `hxp` using `congrFun hx ⟨p, hp⟩`. Establish `hinj : Function.Injective (groupCohomologyResIdeleClassIso (P ⟨p, hp⟩ : Subgroup Gal(L/K)) 2).toLinearEquiv` using `LinearEquiv.injective _`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `hxp`.

Establish `hdvd : ∀ p : n.primeFactors, Nat.card (groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2) ∣ (p : ℕ) ^ n.factorization p`. Introduce `p`. Establish `: Fact (p : ℕ).Prime` using `⟨Nat.prime_of_mem_primeFactors p.2⟩`. Establish `h` using `natCard_groupCohomology_two_ideleClassRep_dvd_of_isPGroup (isPGroup_gal_fixedField_sylow (P p))`. Rewrite `h` using `[finrank_fixedField_eq_card, Sylow.card_eq_multiplicity]`. Then use the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_coe_sort n.primeFactors (fun p => p ^ n.factorization p)]`. Conclude with `(Nat.prod_primeFactors_pow_factorization hn0).symm`. Use `_ = finrank K L := IsGalois.card_aut_eq_finrank K L`.
-/
theorem natCard_groupCohomology_two_ideleClassRep_dvd :
    Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ finrank K L := by
  classical
  set n := Nat.card Gal(L/K) with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'

  have hS : ∀ p : n.primeFactors, ∃ _ : Sylow (p : ℕ) Gal(L/K), True := fun p => by
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact ⟨Classical.arbitrary _, trivial⟩
  choose P _ using hS

  let Φ : groupCohomology (ideleClassRep K L) 2 →+
      ∀ p : n.primeFactors,
        groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2 :=
    AddMonoidHom.pi fun p =>
      ((groupCohomologyResIdeleClassIso (P p : Subgroup Gal(L/K)) 2).hom.hom.comp
        (groupCohomology.map (P p : Subgroup Gal(L/K)).subtype (𝟙 _) 2).hom).toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    refine eq_zero_of_forall_sylow_map_eq_zero _ 2 x fun p hp => ⟨P ⟨p, hp⟩, ?_⟩
    have hxp := congrFun hx ⟨p, hp⟩
    have hinj : Function.Injective
        (groupCohomologyResIdeleClassIso (P ⟨p, hp⟩ : Subgroup Gal(L/K)) 2).toLinearEquiv :=
      LinearEquiv.injective _
    apply hinj
    rw [map_zero]
    exact hxp

  have hdvd : ∀ p : n.primeFactors,
      Nat.card (groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2) ∣
        (p : ℕ) ^ n.factorization p := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have h := natCard_groupCohomology_two_ideleClassRep_dvd_of_isPGroup
      (isPGroup_gal_fixedField_sylow (P p))
    rwa [finrank_fixedField_eq_card, Sylow.card_eq_multiplicity] at h
  calc Nat.card (groupCohomology (ideleClassRep K L) 2)
      = Nat.card Φ.range := Nat.card_congr (AddMonoidHom.ofInjective hΦ).toEquiv
    _ ∣ Nat.card (∀ p : n.primeFactors,
          groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2) :=
        AddSubgroup.card_addSubgroup_dvd_card _
    _ = ∏ p : n.primeFactors,
          Nat.card (groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2) :=
        Nat.card_pi
    _ ∣ ∏ p : n.primeFactors, (p : ℕ) ^ n.factorization p :=
        Finset.prod_dvd_prod_of_dvd _ _ fun p _ => hdvd p
    _ = n := by
        rw [Finset.prod_coe_sort n.primeFactors (fun p => p ^ n.factorization p)]
        exact (Nat.prod_primeFactors_pow_factorization hn0).symm
    _ = finrank K L := IsGalois.card_aut_eq_finrank K L

/- English proof (translation)
The claim follows from `Nat.finite_of_card_ne_zero fun h => Module.finrank_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ natCard_groupCohomology_two_ideleClassRep_dvd))`.
-/
theorem finite_groupCohomology_two_ideleClassRep :
    Finite (groupCohomology (ideleClassRep K L) 2) :=
  Nat.finite_of_card_ne_zero fun h =>
    Module.finrank_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ natCard_groupCohomology_two_ideleClassRep_dvd))

end Level

end GroundTheory.ProfCoh
