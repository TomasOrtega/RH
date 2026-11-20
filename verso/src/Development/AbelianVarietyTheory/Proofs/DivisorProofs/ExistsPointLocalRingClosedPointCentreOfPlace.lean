import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `κ' _ _ F A hsm hAF hfrac`. Use `haveI : IsFractionRing A κ' := IsFractionRing.of_field A κ' fun z => by`. Take `⟨a, ha, b, hb, hb0, e⟩` from `hfrac z`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [← e, hb0]⟩`. Set `ι : A →+* F.ring` to `(algebraMap A κ').codRestrict F.ring (fun x => hAF x.2)`.

Set `q : Ideal A` to `(IsLocalRing.maximalIdeal F.ring).comap ι`. Establish `hq : q ≠ ⊤`. Introduce `h`. Establish `h1 : (1 : A) ∈ q` using `h ▸ Submodule.mem_top`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 (show ι 1 ∈ _ from h1) (by simp)`.

Take `⟨n, hn, hqn⟩` from `Ideal.exists_le_maximal q hq`. Establish `hinv : ∀ s ∈ n.primeCompl, ((s : A) : κ')⁻¹ ∈ F.ring`. Introduce `s hs`. Establish `hs' : ι s ∉ IsLocalRing.maximalIdeal F.ring` using `fun h => hs (hqn h)`. Establish `hu : IsUnit (ι s)`.

Assume the negation of the conclusion as `h`. Conclude with `hs' ((IsLocalRing.mem_maximalIdeal _).2 h)`. Take `⟨u, hu⟩` from `hu.exists_right_inv`. Establish `e : ((s : A) : κ') * (u : κ') = 1` using `congrArg Subtype.val hu`. Rewrite using `[← eq_inv_of_mul_eq_one_right e]`.

Conclude with `u.2`. Establish `hle : n.primeCompl ≤ nonZeroDivisors A` using `n.primeCompl_le_nonZeroDivisors`. Set `B0 : Subalgebra A κ'` to `Localization.subalgebra.ofField κ' n.primeCompl hle`. Use `haveI : IsLocalization.AtPrime B0 n := Localization.subalgebra.isLocalization_ofField κ' _ hle`. Establish `hAB : A.toSubring ≤ B0.toSubring` using `fun x hx => B0.algebraMap_mem (⟨x, hx⟩ : A)`.

Establish `hc : ∀ a, algebraMap ℂ κ' a ∈ B0.toSubring` using `fun a => hAB (A.algebraMap_mem a)`. Use `letI : Algebra ℂ B0 := ((algebraMap A B0).comp (algebraMap ℂ A)).toAlgebra`. Use `haveI : IsScalarTower ℂ A B0 := IsScalarTower.of_algebraMap_eq' rfl`. Establish `hloc : IsLocalRing B0` using `IsLocalization.AtPrime.isLocalRing B0 n`. Use `⟨B0.toSubring, ⟨hc, hloc, ?_, ?_⟩, ?_, hAB, ?_, ?_⟩` and prove the remaining obligations.

Use `show (algebraMap ℂ B0).EssFiniteType`. Use `RingHom.EssFiniteType.comp ?_ ?_` and prove the remaining obligations. Conclude with `RingHom.essFiniteType_algebraMap.2 inferInstance`. Conclude with `RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization B0 n.primeCompl)`. Introduce `f`.

Take `⟨a, ha, b, hb, hb0, e⟩` from `hfrac f`. Conclude with `⟨a, hAB ha, b, hAB hb, hb0, e⟩`. Introduce `r hr`. Set `r' : B0` to `⟨r, hr⟩`. Use `letI : Field (A ⧸ n) := Ideal.Quotient.field n`.

Use `haveI : Module.Finite ℂ (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ n)`. Establish `hsurj : Function.Surjective (algebraMap ℂ (A ⧸ n))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral.2`. Set `e` to `IsLocalization.AtPrime.equivQuotMaximalIdeal n B0`. Take `⟨x, hx⟩` from `Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ r'))`. Take `⟨a, ha⟩` from `hsurj (Ideal.Quotient.mk n x)`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Set `z : B0` to `algebraMap A B0 (algebraMap ℂ A a)`. Establish `hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0) z = Ideal.Quotient.mk _ r'`. Rewrite using `[← e.apply_symm_apply (Ideal.Quotient.mk _ r'), ← hx, ← ha]`. Conclude with `(IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk n B0 (algebraMap ℂ A a)).symm`.

Establish `hm : r' - z ∈ IsLocalRing.maximalIdeal B0` using `Ideal.Quotient.eq.1 hz.symm`. Establish `hnu` using `(nonUnit_iff (R := B0.toSubring) (r' - z)).2 ((IsLocalRing.mem_maximalIdeal _).1 hm)`. Conclude with `hnu`. Introduce and unpack `x ⟨a, s, hs, rfl⟩`. Conclude with `F.ring.toSubring.mul_mem (hAF a.2) (hinv s hs)`.

Use `show (algebraMap ℂ B0).FormallySmooth haveI : Algebra.FormallyEtale A B0 := Algebra.FormallyEtale.of_isLocalization n.primeCompl haveI : Algebra.FormallySmooth ℂ B0 := Algebra.FormallySmooth.comp ℂ A B0`. Conclude with `RingHom.formallySmooth_algebraMap.2 inferInstance`.
-/
theorem exists_locRing_closedPoint_centre : ∀ {κ' : Type} [Field κ'] [Algebra ℂ κ'] (F : Place (algebraMap ℂ κ')) (A : Subalgebra ℂ κ'),
    Algebra.Smooth ℂ A → A.toSubring ≤ F.ring.toSubring →
    (∀ f : κ', ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (B : Subring κ') (hB : IsLocModel (algebraMap ℂ κ') B), RatRes (algebraMap ℂ κ') B ∧
      A.toSubring ≤ B ∧ B ≤ F.ring.toSubring ∧
      ((algebraMap ℂ κ').codRestrict B hB.const_mem).FormallySmooth := by
  intro κ' _ _ F A hsm hAF hfrac
  haveI : IsFractionRing A κ' := IsFractionRing.of_field A κ' fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by simp [← e, hb0]⟩
  let ι : A →+* F.ring := (algebraMap A κ').codRestrict F.ring (fun x => hAF x.2)
  let q : Ideal A := (IsLocalRing.maximalIdeal F.ring).comap ι
  have hq : q ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ q := h ▸ Submodule.mem_top
    exact (IsLocalRing.mem_maximalIdeal _).1 (show ι 1 ∈ _ from h1) (by simp)
  obtain ⟨n, hn, hqn⟩ := Ideal.exists_le_maximal q hq
  have hinv : ∀ s ∈ n.primeCompl, ((s : A) : κ')⁻¹ ∈ F.ring := by
    intro s hs
    have hs' : ι s ∉ IsLocalRing.maximalIdeal F.ring := fun h => hs (hqn h)
    have hu : IsUnit (ι s) := by
      by_contra h
      exact hs' ((IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    have e : ((s : A) : κ') * (u : κ') = 1 := congrArg Subtype.val hu
    rw [← eq_inv_of_mul_eq_one_right e]
    exact u.2
  have hle : n.primeCompl ≤ nonZeroDivisors A := n.primeCompl_le_nonZeroDivisors
  let B0 : Subalgebra A κ' := Localization.subalgebra.ofField κ' n.primeCompl hle
  haveI : IsLocalization.AtPrime B0 n := Localization.subalgebra.isLocalization_ofField κ' _ hle
  have hAB : A.toSubring ≤ B0.toSubring := fun x hx => B0.algebraMap_mem (⟨x, hx⟩ : A)
  have hc : ∀ a, algebraMap ℂ κ' a ∈ B0.toSubring := fun a => hAB (A.algebraMap_mem a)
  letI : Algebra ℂ B0 := ((algebraMap A B0).comp (algebraMap ℂ A)).toAlgebra
  haveI : IsScalarTower ℂ A B0 := IsScalarTower.of_algebraMap_eq' rfl
  have hloc : IsLocalRing B0 := IsLocalization.AtPrime.isLocalRing B0 n
  refine ⟨B0.toSubring, ⟨hc, hloc, ?_, ?_⟩, ?_, hAB, ?_, ?_⟩
  · show (algebraMap ℂ B0).EssFiniteType
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 inferInstance
    · exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization B0 n.primeCompl)
  · intro f
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
    exact ⟨a, hAB ha, b, hAB hb, hb0, e⟩
  · intro r hr
    let r' : B0 := ⟨r, hr⟩
    letI : Field (A ⧸ n) := Ideal.Quotient.field n
    haveI : Module.Finite ℂ (A ⧸ n) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ n)
    have hsurj : Function.Surjective (algebraMap ℂ (A ⧸ n)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2
    let e := IsLocalization.AtPrime.equivQuotMaximalIdeal n B0
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ r'))
    obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk n x)
    refine ⟨a, ?_⟩
    let z : B0 := algebraMap A B0 (algebraMap ℂ A a)
    have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0) z = Ideal.Quotient.mk _ r' := by
      rw [← e.apply_symm_apply (Ideal.Quotient.mk _ r'), ← hx, ← ha]
      exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk n B0 (algebraMap ℂ A a)).symm
    have hm : r' - z ∈ IsLocalRing.maximalIdeal B0 := Ideal.Quotient.eq.1 hz.symm
    have hnu := (nonUnit_iff (R := B0.toSubring) (r' - z)).2 ((IsLocalRing.mem_maximalIdeal _).1 hm)
    exact hnu
  · rintro x ⟨a, s, hs, rfl⟩
    exact F.ring.toSubring.mul_mem (hAF a.2) (hinv s hs)
  · show (algebraMap ℂ B0).FormallySmooth
    haveI : Algebra.FormallyEtale A B0 := Algebra.FormallyEtale.of_isLocalization n.primeCompl
    haveI : Algebra.FormallySmooth ℂ B0 := Algebra.FormallySmooth.comp ℂ A B0
    exact RingHom.formallySmooth_algebraMap.2 inferInstance

end GlobalTheory.FieldPair
