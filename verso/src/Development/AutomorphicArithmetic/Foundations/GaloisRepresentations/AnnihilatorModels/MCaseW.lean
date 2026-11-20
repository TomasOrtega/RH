import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `hSame hFrob hComp hKer hIso hImg hRead`. Introduce `p _ D O _ _ _ _ f b N r w _ hstd M j j₁ hj T T' κ _ _ _ φ hφ x β hx hβ o₁ m₁ y y' hy hy' P P' hrep hrep' hcard hiff`. Substitute `hj` using the available equality. Establish `hpp : p.Prime` using `Fact.out`. Establish `hfinR : Finite (IsLocalRing.ResidueField O)` using `Nat.finite_of_card_ne_zero (by rw [hstd.card]; exact pow_ne_zero _ hpp.ne_zero)`.

Establish `hq : ∀ a : O, β a ^ (p ^ f) = β a`. Introduce `a`. Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField O)`. Establish `h1 : (IsLocalRing.residue O a) ^ (p ^ f) = IsLocalRing.residue O a`. Rewrite using `[← hstd.card, Nat.card_eq_fintype_card]`.

Conclude with `FiniteField.pow_card _`. Establish `h2 : a ^ (p ^ f) - a ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h1, sub_self]`. Establish `h3` using `hβ _ h2`. Rewrite `h3` using `[map_sub, map_pow, sub_eq_zero]`.

Conclude with `h3`. Establish `hfix : spMap φ ≫ spMap β = spMap β`. Establish `hc : φ.comp β = β` using `RingHom.ext fun a => by rw [RingHom.comp_apply, hφ, hq]`. Rewrite using `[spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]`. Establish `hf : 0 < f`.

Break down `Nat.eq_zero_or_pos f with h0 | h0` into its components or cases. It suffices to derive a contradiction. Establish `hc` using `hstd.card`. Rewrite `hc` using `[h0, pow_zero]`. Use `Finite.one_lt_card (α := IsLocalRing.ResidueField O)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Establish `hw : w ≠ ⊤` using `Ideal.IsMaximal.ne_top ‹_›`. Establish `hβw : ∀ (i : Fin D.a), ∀ z ∈ w, β ((b.t i) z) = 0` using `fun i z hz => hβ _ (hstd.tw i z hz)`. Take `⟨o'', mF, F, hFi, hFa, hFk⟩` from `hFrob p D O b N f κ (spMap β) φ hφ hfix P'.o'`.

Establish `hcomp` using `hComp p D O b N (Sp κ) (spMap β) _ _ o₁ P'.o' o'' P'.ψ F P'.isog hFi`. Establish `hexp : p ^ (f * j) * p ^ f = p ^ (f * (j + 1))`. Rewrite using `[← pow_add]`. Put the polynomial expressions in normal form. Rewrite `hcomp` using `[hexp]`.

Establish `he : f * (j + 1) - 1 + 1 = f * (j + 1)` using `Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hf (Nat.succ_pos j)).ne')`. Establish `hcard1 : Nat.card { g // UKer r o₁ P.ψ (𝟙_ (Over (Sp κ))) g } = (p ^ f) ^ j`. Rewrite using `[← hcard]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight hiff)`. Establish `hU` using `hSame p D O b N hstd.m1 hstd.a1 r w hw hstd.ule f κ β hβw o₁ P.o' P'.o' o'' P.ψ P'.ψ F (f * (j + 1) - 1) (by rw [he]; exact P.isog) P'.isog.2.1 (by rw [he]; exact hcomp) hFk ((p ^ f) ^ j) (pow_pos (pow_pos hpp.pos _) _) (by rw [← pow_succ']; exact hrep) hcard1 hrep' hcard hiff`.

Establish `hK1` using `hKer p D O b N r w hw hstd.ule κ (spMap β) _ o₁ P.o' o'' P.ψ (P'.ψ ≫ F) P.isog hcomp hU`. Establish `hK2` using `hKer p D O b N r w hw hstd.ule κ (spMap β) _ o₁ o'' P.o' (P'.ψ ≫ F) P.ψ hcomp P.isog (fun T g => (hU T g).symm)`. Take `⟨m₂, hm₂⟩` from `hIso p D O b N κ (spMap β) _ o₁ P.o' o'' P.ψ (P'.ψ ≫ F) P.isog hcomp (fun T g => ⟨hK1 T g, hK2 T g⟩)`. Take `⟨n₁, hn₁⟩` from `GlobalTheory.HTQuotRigid.objMap_comp_φ P.m' T.mt`. Take `⟨n₂a, hn₂a⟩` from `GlobalTheory.HTQuotRigid.objMap_comp_φ P'.m' T'.mt`.

Take `⟨n₂, hn₂⟩` from `GlobalTheory.HTQuotRigid.objMap_comp_φ mF n₂a`. Establish `h₁ : (y ≫ T.t) ≫ M.s = spMap β`. Rewrite using `[Category.assoc, ← T.st, ← Category.assoc, hy, hx]`. Establish `h₂ : (spMap φ ≫ y' ≫ T'.t) ≫ M.s = spMap β`. Simplify using `only [Category.assoc]`.

Rewrite using `[← T'.st, ← Category.assoc y', hy', hx, hfix]`. Take `⟨ht, hφeq⟩` from `hImg p D O b N hstd.three hstd.cop M (Sp κ) (spMap β) P.o' o'' (y ≫ T.t) (spMap φ ≫ y' ≫ T'.t) h₁ h₂ n₁ n₂ m₂`. Use `⟨ht, ?_⟩` and prove the remaining obligations. Introduce `a h h'`. Choose the witnesses or unpack the hypotheses as in `⟨a₀, ha₀⟩ : ∃ a₀ : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, Over.Hom.left a₀ ≫ m₁.φ = a := by`.

Use `⟨Over.homMk (m₁.cart.1.lift a (𝟙 _) (by rw [Category.id_comp, h, hy])) ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Substitute `ha₀` using the available equality. Rewrite using `[(hRead p D O b N M r w (j + 1) _ T (Sp κ) x (spMap β) o₁ m₁ y hy P a₀).2 h, (hRead p D O b N M r w j _ T' (Sp κ) x (spMap β) o₁ m₁ y' hy' P' a₀).2 h', ← hn₁, ← hφeq, hn₂, hn₂a]`.

Establish `key` using `hFa (a₀ ≫ P'.ψ)`. Simplify using `only [Over.comp_left, Category.assoc] at key hm₂ ⊢`. Rewrite using `[reassoc_of% hm₂, reassoc_of% key]`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.caseW_of :
    SameW → FrobIsog → IsogComp → KerFromU → IsoOfKer → ImgEq → PulledRead → CaseW := by
  intro hSame hFrob hComp hKer hIso hImg hRead
  intro p _ D O _ _ _ _ f b N r w _ hstd M j j₁ hj T T' κ _ _ _ φ hφ x β hx hβ o₁ m₁ y y' hy hy' P P' hrep hrep' hcard hiff
  subst hj
  have hpp : p.Prime := Fact.out
  have hfinR : Finite (IsLocalRing.ResidueField O) :=
    Nat.finite_of_card_ne_zero (by rw [hstd.card]; exact pow_ne_zero _ hpp.ne_zero)
  have hq : ∀ a : O, β a ^ (p ^ f) = β a := by
    intro a
    letI := Fintype.ofFinite (IsLocalRing.ResidueField O)
    have h1 : (IsLocalRing.residue O a) ^ (p ^ f) = IsLocalRing.residue O a := by
      rw [← hstd.card, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card _
    have h2 : a ^ (p ^ f) - a ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h1, sub_self]
    have h3 := hβ _ h2
    rw [map_sub, map_pow, sub_eq_zero] at h3
    exact h3
  have hfix : spMap φ ≫ spMap β = spMap β := by
    have hc : φ.comp β = β := RingHom.ext fun a => by rw [RingHom.comp_apply, hφ, hq]
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have hc := hstd.card
      rw [h0, pow_zero] at hc
      have := Finite.one_lt_card (α := IsLocalRing.ResidueField O)
      omega
    · exact h0
  have hw : w ≠ ⊤ := Ideal.IsMaximal.ne_top ‹_›
  have hβw : ∀ (i : Fin D.a), ∀ z ∈ w, β ((b.t i) z) = 0 := fun i z hz => hβ _ (hstd.tw i z hz)
  obtain ⟨o'', mF, F, hFi, hFa, hFk⟩ := hFrob p D O b N f κ (spMap β) φ hφ hfix P'.o'
  have hcomp := hComp p D O b N (Sp κ) (spMap β) _ _ o₁ P'.o' o'' P'.ψ F P'.isog hFi
  have hexp : p ^ (f * j) * p ^ f = p ^ (f * (j + 1)) := by
    rw [← pow_add]
    ring_nf
  rw [hexp] at hcomp
  have he : f * (j + 1) - 1 + 1 = f * (j + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hf (Nat.succ_pos j)).ne')
  have hcard1 : Nat.card { g // UKer r o₁ P.ψ (𝟙_ (Over (Sp κ))) g } = (p ^ f) ^ j := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have hU := hSame p D O b N hstd.m1 hstd.a1 r w hw hstd.ule f κ β hβw o₁ P.o' P'.o' o'' P.ψ P'.ψ F
    (f * (j + 1) - 1) (by rw [he]; exact P.isog) P'.isog.2.1 (by rw [he]; exact hcomp) hFk ((p ^ f) ^ j)
    (pow_pos (pow_pos hpp.pos _) _) (by rw [← pow_succ']; exact hrep) hcard1 hrep' hcard hiff
  have hK1 := hKer p D O b N r w hw hstd.ule κ (spMap β) _ o₁ P.o' o'' P.ψ (P'.ψ ≫ F) P.isog hcomp hU
  have hK2 := hKer p D O b N r w hw hstd.ule κ (spMap β) _ o₁ o'' P.o' (P'.ψ ≫ F) P.ψ hcomp P.isog
    (fun T g => (hU T g).symm)
  obtain ⟨m₂, hm₂⟩ := hIso p D O b N κ (spMap β) _ o₁ P.o' o'' P.ψ (P'.ψ ≫ F) P.isog hcomp
    (fun T g => ⟨hK1 T g, hK2 T g⟩)
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P.m' T.mt
  obtain ⟨n₂a, hn₂a⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P'.m' T'.mt
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ mF n₂a
  have h₁ : (y ≫ T.t) ≫ M.s = spMap β := by
    rw [Category.assoc, ← T.st, ← Category.assoc, hy, hx]
  have h₂ : (spMap φ ≫ y' ≫ T'.t) ≫ M.s = spMap β := by
    simp only [Category.assoc]
    rw [← T'.st, ← Category.assoc y', hy', hx, hfix]
  obtain ⟨ht, hφeq⟩ := hImg p D O b N hstd.three hstd.cop M (Sp κ) (spMap β) P.o' o''
    (y ≫ T.t) (spMap φ ≫ y' ≫ T'.t) h₁ h₂ n₁ n₂ m₂
  refine ⟨ht, ?_⟩
  intro a h h'
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, Over.Hom.left a₀ ≫ m₁.φ = a := by
    refine ⟨Over.homMk (m₁.cart.1.lift a (𝟙 _) (by rw [Category.id_comp, h, hy])) ?_, ?_⟩
    · simp
    · simp
  subst ha₀
  rw [(hRead p D O b N M r w (j + 1) _ T (Sp κ) x (spMap β) o₁ m₁ y hy P a₀).2 h,
    (hRead p D O b N M r w j _ T' (Sp κ) x (spMap β) o₁ m₁ y' hy' P' a₀).2 h',
    ← hn₁, ← hφeq, hn₂, hn₂a]
  have key := hFa (a₀ ≫ P'.ψ)
  simp only [Over.comp_left, Category.assoc] at key hm₂ ⊢
  rw [reassoc_of% hm₂, reassoc_of% key]
