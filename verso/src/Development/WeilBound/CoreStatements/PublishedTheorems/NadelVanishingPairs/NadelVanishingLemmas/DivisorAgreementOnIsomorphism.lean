import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAndMultiplicityPullbackIsIsoOpenStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.PullDiv

/- English proof (translation)
Take `⟨m, i, hi, rfl⟩` from `h`. Use `isProper_str R m` as an intermediate fact. Establish `: IsProper (i ≫ PSpace.str R m)` using `inferInstance`. Conclude with `QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)`.
-/
theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

/- English proof (translation)
Introduce `k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hP U hU H`. Establish `: CompactSpace Y₁` using `compactSpace_of_isProjOver hP`. Establish `: Smooth q` using `SmoothOfRelativeDimension.smooth n q`. Establish `: Smooth (t ≫ q)` using `SmoothOfRelativeDimension.smooth n (t ≫ q)`. Establish `hinj : ∀ w₁ w₂ : Y₁, t w₁ ∈ U → t w₂ ∈ U → t w₁ = t w₂ → w₁ = w₂`.

Introduce `w₁ w₂ h₁ h₂ e`. Establish `hb : Function.Injective (t ∣_ U)` using `((ConcreteCategory.bijective_of_isIso ((t ∣_ U).base))).1`. Use `@hb ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ (Subtype.ext ((morphismRestrict_base_coe t U _).trans (e.trans (morphismRestrict_base_coe t U ⟨w₂, h₂⟩).symm)))` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Set `c : Y₀ → ℤ` to `fun z => if h : ∃ w, t w = z ∧ z ∈ U then H.mult h.choose else 0`.

Establish `hc : ∀ w, t w ∈ U → c (t w) = H.mult w`. Introduce `w hw`. Establish `h : ∃ w', t w' = t w ∧ t w ∈ U` using `⟨w, rfl, hw⟩`. Simplify using `only [c, dif_pos h]`. Establish `e` using `h.choose_spec`.

Rewrite using `[hinj _ _ (by rw [e.1]; exact hw) hw e.1]`. Establish `hsupp : Function.support c ⊆ t '' Function.support H.mult`. Introduce `z hz`. Distinguish the cases in `h : ∃ w, t w = z ∧ z ∈ U`. Take `⟨w, rfl, hw⟩` from `h`.

Conclude with `⟨w, by simpa [hc w hw] using hz, rfl⟩`. Conclude with `(hz (by simp only [c]; exact dif_neg h)).elim`. Establish `hfin : (Function.support c).Finite` using `(H.finite_support_mult.image _).subset hsupp`. Establish `hcod : ∀ z, c z ≠ 0 → Order.coheight z = 1`. Introduce `z hz`.

Distinguish the cases in `h : ∃ w, t w = z ∧ z ∈ U`. Take `⟨w, rfl, hw⟩` from `h`. Rewrite `hz` using `[hc w hw]`. Rewrite using `[← (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU w hw).1]`. Conclude with `CartierDiv.coheight_eq_one_of_mult_ne_zero hz`.

Conclude with `(hz (by simp only [c]; exact dif_neg h)).elim`. Take `⟨H₀, hH₀⟩` from `GlobalTheory.T.exists_cartier_with_multiplicities Y₀ (fun x => AbelianProjective.ufd_stalk q x) c hfin hcod`. Use `⟨H₀, fun y hy hmem => ?_⟩` and prove the remaining obligations. Establish `: GlobalTheory.IsNormalScheme Y₁` using `(isNormalScheme_iff Y₁).mpr fun x => ⟨inferInstance, have := AbelianProjective.ufd_stalk (t ≫ q) x UniqueFactorizationMonoid.instIsIntegrallyClosed⟩`. Take `⟨z, hzy, hz⟩` from `((GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (H - pullCart t H₀)).2.1 y).1 hmem`.

Establish `hzU : t z ∈ U` using `(hzy.map t.continuous).mem_open U.isOpen hy`. Apply `hz` to reduce the goal to its premises. Establish `hm` using `CartierDiv.mult_add (H - pullCart t H₀) (pullCart t H₀) z`. Rewrite `hm` using `[sub_add_cancel, (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU z hzU).2 H₀, hH₀, hc z hzU]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_pullCart_agree : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hP U hU H
  classical
  have : CompactSpace Y₁ := compactSpace_of_isProjOver hP
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)

  have hinj : ∀ w₁ w₂ : Y₁, t w₁ ∈ U → t w₂ ∈ U → t w₁ = t w₂ → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ e
    have hb : Function.Injective (t ∣_ U) :=
      ((ConcreteCategory.bijective_of_isIso ((t ∣_ U).base))).1
    have := @hb ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ (Subtype.ext ((morphismRestrict_base_coe t U _).trans
      (e.trans (morphismRestrict_base_coe t U ⟨w₂, h₂⟩).symm)))
    exact congrArg Subtype.val this
  let c : Y₀ → ℤ := fun z => if h : ∃ w, t w = z ∧ z ∈ U then H.mult h.choose else 0
  have hc : ∀ w, t w ∈ U → c (t w) = H.mult w := by
    intro w hw
    have h : ∃ w', t w' = t w ∧ t w ∈ U := ⟨w, rfl, hw⟩
    simp only [c, dif_pos h]
    have e := h.choose_spec
    rw [hinj _ _ (by rw [e.1]; exact hw) hw e.1]
  have hsupp : Function.support c ⊆ t '' Function.support H.mult := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      exact ⟨w, by simpa [hc w hw] using hz, rfl⟩
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  have hfin : (Function.support c).Finite := (H.finite_support_mult.image _).subset hsupp
  have hcod : ∀ z, c z ≠ 0 → Order.coheight z = 1 := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      rw [hc w hw] at hz
      rw [← (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU w hw).1]
      exact CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_cartier_with_multiplicities Y₀ (fun x => AbelianProjective.ufd_stalk q x) c hfin hcod
  refine ⟨H₀, fun y hy hmem => ?_⟩
  have : GlobalTheory.IsNormalScheme Y₁ := (isNormalScheme_iff Y₁).mpr fun x =>
    ⟨inferInstance, have := AbelianProjective.ufd_stalk (t ≫ q) x
      UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  obtain ⟨z, hzy, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (H - pullCart t H₀)).2.1 y).1 hmem
  have hzU : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  apply hz
  have hm := CartierDiv.mult_add (H - pullCart t H₀) (pullCart t H₀) z
  rw [sub_add_cancel, (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU z hzU).2 H₀, hH₀, hc z hzU] at hm
  omega

end GlobalTheory.PullDiv
