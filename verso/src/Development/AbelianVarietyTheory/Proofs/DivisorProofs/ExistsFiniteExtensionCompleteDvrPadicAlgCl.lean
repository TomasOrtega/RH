import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallEqOfIntegralDvr
open IsLocalRing

namespace GlobalTheory.DvrFinExt

/- English proof (translation)
Establish `hb : Function.Bijective (algebraMap K Ω).rangeRestrict` using `⟨(algebraMap K Ω).rangeRestrict.injective, (algebraMap K Ω).rangeRestrict_surjective⟩`. Set `e` to `RingEquiv.ofBijective _ hb`. Set `u : F →+* K` to `e.symm.toRingHom.comp ((algebraMap F Ω).codRestrict _ hQ)`. Establish `hu : (algebraMap K Ω).comp u = (RingHom.id Ω).comp (algebraMap F Ω)`. Use extensionality with `q`.

Establish `h` using `e.apply_symm_apply ((algebraMap F Ω).codRestrict _ hQ q)`. Conclude with `congrArg Subtype.val h`. Establish `hint : ∀ x : Ω, IsIntegral K x` using `fun x => IsIntegral.map_of_comp_eq u (RingHom.id Ω) hu (Algebra.IsIntegral.isIntegral (R := F) x)`. Take `⟨s, hs⟩` from `Algebra.FiniteType.out (R := ℤ) (A := R)`. Use `haveI : Finite (y₀ '' (s : Set R)) := (s.finite_toSet.image y₀).to_subtype`.

Use `⟨IntermediateField.adjoin K (y₀ '' (s : Set R)), IntermediateField.finiteDimensional_adjoin (fun x _ => hint x), fun a => ?_⟩` and prove the remaining obligations. Establish `ha : a ∈ Algebra.adjoin ℤ (s : Set R)` using `hs ▸ Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩`. Consider the case `algebraMap n => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`.
-/
theorem exists_finite_intermediateField (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F Ω]
    [Algebra.IsIntegral F Ω] [Algebra K Ω] (hQ : ∀ q : F, algebraMap F Ω q ∈ (algebraMap K Ω).range)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* Ω) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ a, y₀ a ∈ L := by
  have hb : Function.Bijective (algebraMap K Ω).rangeRestrict :=
    ⟨(algebraMap K Ω).rangeRestrict.injective, (algebraMap K Ω).rangeRestrict_surjective⟩
  let e := RingEquiv.ofBijective _ hb
  let u : F →+* K := e.symm.toRingHom.comp ((algebraMap F Ω).codRestrict _ hQ)
  have hu : (algebraMap K Ω).comp u = (RingHom.id Ω).comp (algebraMap F Ω) := by
    ext q
    have h := e.apply_symm_apply ((algebraMap F Ω).codRestrict _ hQ q)
    exact congrArg Subtype.val h
  have hint : ∀ x : Ω, IsIntegral K x := fun x =>
    IsIntegral.map_of_comp_eq u (RingHom.id Ω) hu (Algebra.IsIntegral.isIntegral (R := F) x)
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  haveI : Finite (y₀ '' (s : Set R)) := (s.finite_toSet.image y₀).to_subtype
  refine ⟨IntermediateField.adjoin K (y₀ '' (s : Set R)),
    IntermediateField.finiteDimensional_adjoin (fun x _ => hint x), fun a => ?_⟩
  have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  | algebraMap n => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/- English proof (translation)
Introduce `p _ V _ _ _ _ hc κ hκ hQ R _ _ y₀`. Use `letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra`. Take `⟨L, hL, hy⟩` from `exists_finite_intermediateField ℚ_[p] (FractionRing V) (PadicAlgCl p) hQ R y₀`. Take `⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩` from `GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L`. Use `haveI : CharZero W := charZero_of_injective_ringHom hinj`.

Set `e` to `FractionRing.algEquiv W L`. Set `κ' : FractionRing W →+* PadicAlgCl p` to `L.val.toRingHom.comp e.toRingEquiv.toRingHom`. Set `fK : FractionRing V →+* FractionRing W` to `e.symm.toRingEquiv.toRingHom.comp (algebraMap (FractionRing V) L)`. Establish `hfK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (algebraMap V W a)`. Introduce `a`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[e.commutes]`. Establish `h` using `congrArg (fun g : V →+* L => g a) hcomp`. Conclude with `(e.apply_symm_apply _).trans h.symm`. Establish `hκ' : κ'.comp fK = κ`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Use `show ((e (e.symm (algebraMap (FractionRing V) L x)) : L) : PadicAlgCl p) = κ x`. Rewrite using `[e.apply_symm_apply]`. Both sides reduce to the same expression. Use `haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W`.

Use `⟨W, inferInstance, inferInstance, inferInstance, hcW, inferInstance, algebraMap V W, fK, κ', hinj, hloc, RingHom.finite_algebraMap.2 hfin, hfK, hκ', GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ κ' (fun v => ?_) hκ, fun a => ⟨e.symm ⟨y₀ a, hy a⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hfK]`. Conclude with `congrArg (fun g : FractionRing V →+* PadicAlgCl p => g (algebraMap V (FractionRing V) v)) hκ'`. Use `show ((e (e.symm ⟨y₀ a, hy a⟩) : L) : PadicAlgCl p) = y₀ a`. Rewrite using `[e.apply_symm_apply]`.
-/
theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by
  intro p _ V _ _ _ _ hc κ hκ hQ R _ _ y₀
  letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  obtain ⟨L, hL, hy⟩ := exists_finite_intermediateField ℚ_[p] (FractionRing V) (PadicAlgCl p) hQ R y₀
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  let e := FractionRing.algEquiv W L
  let κ' : FractionRing W →+* PadicAlgCl p := L.val.toRingHom.comp e.toRingEquiv.toRingHom
  let fK : FractionRing V →+* FractionRing W :=
    e.symm.toRingEquiv.toRingHom.comp (algebraMap (FractionRing V) L)
  have hfK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (algebraMap V W a) := by
    intro a
    apply e.injective
    rw [e.commutes]
    have h := congrArg (fun g : V →+* L => g a) hcomp
    exact (e.apply_symm_apply _).trans h.symm
  have hκ' : κ'.comp fK = κ := by
    refine RingHom.ext fun x => ?_
    show ((e (e.symm (algebraMap (FractionRing V) L x)) : L) : PadicAlgCl p) = κ x
    rw [e.apply_symm_apply]
    rfl
  haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcW, inferInstance, algebraMap V W, fK, κ', hinj, hloc,
    RingHom.finite_algebraMap.2 hfin, hfK, hκ', GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ κ' (fun v => ?_) hκ,
    fun a => ⟨e.symm ⟨y₀ a, hy a⟩, ?_⟩⟩
  · rw [← hfK]
    exact congrArg (fun g : FractionRing V →+* PadicAlgCl p => g (algebraMap V (FractionRing V) v)) hκ'
  · show ((e (e.symm ⟨y₀ a, hy a⟩) : L) : PadicAlgCl p) = y₀ a
    rw [e.apply_symm_apply]

end GlobalTheory.DvrFinExt
