import Mathlib
import GroundTheory.ProfiniteCohomology.FilteredHomology
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Complex

variable {R : Type u} [Ring R] {ι' : Type*} {c : ComplexShape ι'} {ι : Type*}
  {K : HomologicalComplex (ModuleCat.{u} R) c} {L : ι → HomologicalComplex (ModuleCat.{u} R) c}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem homologyMap_pi_bijective (p : ∀ i, K ⟶ L i)
    (hp : ∀ m, Function.Bijective fun (x : K.X m) (i : ι) => ((p i).f m).hom x) (n : ι') :
    Function.Bijective fun (x : K.homology n) (i : ι) =>
      (HomologicalComplex.homologyMap (p i) n).hom x := by
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance (x - y)
    have h0 : ∀ i, (HomologicalComplex.homologyMap (p i) n).hom (x - y) = 0 := fun i => by
      rw [map_sub, sub_eq_zero]
      exact congrFun hxy i
    rw [← hz] at h0 ⊢
    have hw : ∀ i, ∃ w : (L i).X (c.prev n),
        ((L i).d (c.prev n) n).hom w = ((p i).f n).hom ((K.iCycles n).hom z) := fun i => by
      have h := h0 i
      rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply] at h
      exact h
    choose w hw using hw
    obtain ⟨v, hv⟩ := (hp (c.prev n)).2 w
    rw [homologyπ_eq_zero_iff]
    refine ⟨v, (hp n).1 (funext fun i => ?_)⟩
    have hvi : ((p i).f (c.prev n)).hom v = w i := congrFun hv i
    change ((p i).f n).hom ((K.d (c.prev n) n).hom v) = ((p i).f n).hom ((K.iCycles n).hom z)
    rw [hom_f_d_apply, hvi, hw i]
  · intro y
    have hz : ∀ i, ∃ z : (L i).cycles n, ((L i).homologyπ n).hom z = y i := fun i =>
      (ModuleCat.epi_iff_surjective _).1 inferInstance (y i)
    choose z hz using hz
    obtain ⟨x, hx⟩ := (hp n).2 fun i => ((L i).iCycles n).hom (z i)
    have hxi : ∀ i, ((p i).f n).hom x = ((L i).iCycles n).hom (z i) := fun i => congrFun hx i
    have hdx : (K.d n (c.next n)).hom x = 0 := by
      refine (hp (c.next n)).1 (funext fun i => ?_)
      change ((p i).f (c.next n)).hom ((K.d n (c.next n)).hom x) = ((p i).f (c.next n)).hom 0
      rw [map_zero, hom_f_d_apply, hxi]
      exact iCycles_d_apply _ _ _ _
    obtain ⟨w, hw⟩ := exists_iCycles_eq K x hdx
    refine ⟨(K.homologyπ n).hom w, funext fun i => ?_⟩
    change (HomologicalComplex.homologyMap (p i) n).hom ((K.homologyπ n).hom w) = y i
    rw [homologyMap_homologyπ_apply, ← hz i]
    congr 1
    apply (ModuleCat.mono_iff_injective ((L i).iCycles n)).1 inferInstance
    rw [iCycles_cyclesMap_apply, hw, hxi]

end Complex

section GroupCohomology

variable {k G : Type u} [CommRing k] [Group G] {ι : Type*} {P : Rep.{u} k G}
  {A : ι → Rep.{u} k G}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem cochainsMap_pi_bijective (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (m : ℕ) :
    Function.Bijective fun (f : (groupCohomology.inhomogeneousCochains P).X m) (i : ι) =>
      ((groupCohomology.cochainsMap (MonoidHom.id G) (p i)).f m).hom f := by
  constructor
  · intro f f' h
    funext g
    apply hp.1
    funext i
    exact congrFun (congrFun h i) g
  · intro F
    refine ⟨fun g => Function.surjInv hp.2 (fun i => F i g), funext fun i => funext fun g => ?_⟩
    exact congrFun (Function.surjInv_eq hp.2 (fun i => F i g)) i

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem groupCohomology_pi_bijective (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ) :
    Function.Bijective fun (x : groupCohomology P n) (i : ι) =>
      (groupCohomology.map (MonoidHom.id G) (p i) n).hom x :=
  homologyMap_pi_bijective (fun i => groupCohomology.cochainsMap (MonoidHom.id G) (p i))
    (cochainsMap_pi_bijective p hp) n

noncomputable def groupCohomologyPiEquiv (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ) :
    groupCohomology P n ≃ₗ[k] ∀ i, groupCohomology (A i) n :=
  LinearEquiv.ofBijective (LinearMap.pi fun i => (groupCohomology.map (MonoidHom.id G) (p i) n).hom)
    (groupCohomology_pi_bijective p hp n)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem groupCohomologyPiEquiv_apply (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ)
    (x : groupCohomology P n) (i : ι) :
    groupCohomologyPiEquiv p hp n x i = (groupCohomology.map (MonoidHom.id G) (p i) n).hom x :=
  rfl

end GroupCohomology

end GroundTheory.ProfCoh
