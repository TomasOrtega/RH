import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionTorusExtensionAbelianVarietyLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIsQuotOfFinrankEqZeroStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateProperness

/- English proof (translation)
Introduce `k _ _ p _ _ G _ hG g hg m hm s hs hcard`. Take `⟨N, _, ν, hN, hνmon, hνci, hpdiv, hlift, -, hdim⟩` from `GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG`. Take `⟨g', hg', hiso⟩` from `hdim g hg`. Take `⟨X, _, _, _, B, _, i, q, hq, hB, hdimB⟩` from `GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient k p N hN hpdiv`. Take `⟨a, ha, hga⟩` from `hdimB g' hg'`.

Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (by simp)`. Establish `hcop : m.Coprime p`. Establish `hnd : ¬ p ∣ m` using `fun h => hm ((CharP.cast_eq_zero_iff k p m).mpr h)`.

Conclude with `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hnd)`. Establish `hmono : Mono ν.left` using `inferInstance`. Establish `hinj : ∀ y y' : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = y' ≫ ν → y = y'`. Introduce `y y' h`. Use `ext1`.

Conclude with `(cancel_mono ν.left).mp (by simpa using congrArg CommaMorphism.left h)`. Establish `hlift' : ∀ x ∈ s, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ m = 1`. Introduce `x hx`. Take `⟨y, hy⟩` from `hlift x m hcop hm0 (hs x hx)`. Use `⟨y, hy, hinj _ _ ?_⟩` and prove the remaining obligations.

Rewrite using `[MonObj.pow_comp, hy, hs x hx, MonObj.one_comp]`. Use `choose! f hf1 hf2 using hlift'`. Establish `hfinj : Set.InjOn f s`. Introduce `x hx x' hx' h`. Rewrite using `[← hf1 x hx, ← hf1 x' hx', h]`.

Establish `hcardN : (s.image f).card ≤ m ^ (Module.finrank ℤ X + 2 * a)`. Use `GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le k N hN.1 X B i q hq hB a ha m hm (s.image f) ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp hy`. Conclude with `hf2 x hx`.

Rewrite `hcardN` using `[Finset.card_image_of_injOn hfinj]`. Establish `hpt : Nonempty (𝟙_ (Over (Sp k))).left`. Express the relevant statement in the definitionally equal form `Nonempty (Sp k)`. Use `first`. Consider the case `infer_instance`.

Consider the case `exact ⟨IsLocalRing.closedPoint k⟩`. Establish `hne : Nonempty N.left` using `⟨(1 : 𝟙_ (Over (Sp k)) ⟶ N).left hpt.some⟩`. Establish `hgle : g' ≤ g` using `GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion k N G ν hνci hne g g' hg hg'`. Establish `hm1 : 1 < m`. Break down `Nat.lt_or_ge 1 m with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Establish `: m = 1` using `by omega`. Substitute `this` using the available equality. Simplify using `at hcard hcardN`.

Use linear arithmetic over natural numbers and integers. Establish `hlt : m ^ (2 * g) < m ^ (Module.finrank ℤ X + 2 * a + 1)`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp` using `(Nat.pow_lt_pow_iff_right (by omega)).mp hlt`. Establish `ht : Module.finrank ℤ X = 0` using `by omega`.

Establish `hgg : g ≤ g'` using `by omega`. Use `haveI hP : IsProper N.hom := GlobalTheory.T.isProper_of_isQuot_abelian_of_finrank_eq_zero k N X B i q hq hB ht`. Use `haveI : IsIso ν.left := by haveI := hiso hgg`. Conclude with `Functor.map_isIso (Over.forget (Sp k)) ν`. Establish `hw : G.hom = inv ν.left ≫ N.hom`.

Rewrite using `[← Over.w ν]`. Simplify using the standard rewrite rules. Rewrite using `[hw]`. Use `infer_instance`.
-/
theorem main : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ p _ _ G _ hG g hg m hm s hs hcard
  classical
  obtain ⟨N, _, ν, hN, hνmon, hνci, hpdiv, hlift, -, hdim⟩ :=
    GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG
  obtain ⟨g', hg', hiso⟩ := hdim g hg
  obtain ⟨X, _, _, _, B, _, i, q, hq, hB, hdimB⟩ :=
    GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient k p N hN hpdiv
  obtain ⟨a, ha, hga⟩ := hdimB g' hg'

  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hcop : m.Coprime p := by
    have hnd : ¬ p ∣ m := fun h => hm ((CharP.cast_eq_zero_iff k p m).mpr h)
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hnd)

  have hmono : Mono ν.left := inferInstance
  have hinj : ∀ y y' : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = y' ≫ ν → y = y' := by
    intro y y' h
    ext1
    exact (cancel_mono ν.left).mp (by simpa using congrArg CommaMorphism.left h)

  have hlift' : ∀ x ∈ s, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ m = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hlift x m hcop hm0 (hs x hx)
    refine ⟨y, hy, hinj _ _ ?_⟩
    rw [MonObj.pow_comp, hy, hs x hx, MonObj.one_comp]
  choose! f hf1 hf2 using hlift'
  have hfinj : Set.InjOn f s := by
    intro x hx x' hx' h
    rw [← hf1 x hx, ← hf1 x' hx', h]
  have hcardN : (s.image f).card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
    refine GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le k N hN.1 X B i q hq hB a ha m hm (s.image f) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf2 x hx
  rw [Finset.card_image_of_injOn hfinj] at hcardN

  have hpt : Nonempty (𝟙_ (Over (Sp k))).left := by
    change Nonempty (Sp k)
    first
    | infer_instance
    | exact ⟨IsLocalRing.closedPoint k⟩
  have hne : Nonempty N.left := ⟨(1 : 𝟙_ (Over (Sp k)) ⟶ N).left hpt.some⟩
  have hgle : g' ≤ g := GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion k N G ν hνci hne g g' hg hg'

  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge 1 m with h | h
    · exact h
    · exfalso
      have : m = 1 := by omega
      subst this
      simp at hcard hcardN
      omega
  have hlt : m ^ (2 * g) < m ^ (Module.finrank ℤ X + 2 * a + 1) := by
    calc m ^ (2 * g) < m * s.card := hcard
      _ ≤ m * m ^ (Module.finrank ℤ X + 2 * a) := Nat.mul_le_mul_left m hcardN
      _ = m ^ (Module.finrank ℤ X + 2 * a + 1) := by ring
  have hexp := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  have ht : Module.finrank ℤ X = 0 := by omega
  have hgg : g ≤ g' := by omega
  haveI hP : IsProper N.hom := GlobalTheory.T.isProper_of_isQuot_abelian_of_finrank_eq_zero k N X B i q hq hB ht
  haveI : IsIso ν.left := by
    haveI := hiso hgg
    exact Functor.map_isIso (Over.forget (Sp k)) ν
  have hw : G.hom = inv ν.left ≫ N.hom := by
    rw [← Over.w ν]
    simp
  rw [hw]
  infer_instance

end GlobalTheory.SerreTateProperness
