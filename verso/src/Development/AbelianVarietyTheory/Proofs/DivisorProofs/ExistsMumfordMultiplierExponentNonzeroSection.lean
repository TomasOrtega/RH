import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.MumMult

/- English proof (translation)
Set `y : (𝟙_ (Over (Sp R))).left` to `(IsLocalRing.closedPoint R : PrimeSpectrum R)`. Use `⟨(η[D.toPre.P.A]).left y, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, Over.w (η[D.toPre.P.A])]`. Both sides reduce to the same expression.
-/
theorem exists_closedFibre_pt (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) :
    ∃ x : D.toPre.P.A.left, D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) := by
  let y : (𝟙_ (Over (Sp R))).left := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  refine ⟨(η[D.toPre.P.A]).left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, Over.w (η[D.toPre.P.A])]
  rfl

/- English proof (translation)
Introduce `R _ _ _ hR D a a' h h' hE`. Use `D.toPre.P.isAb.proper` as an intermediate fact. Establish `hP` using `D.toPre.P.isLB`. Take `⟨N₀, hN₀, -, hκ⟩` from `GlobalTheory.Mum.PosMult.exists_pos_mult R hR.1 D a a' h h' hE`. Take `⟨N₁, hN₁⟩` from `GlobalTheory.Mum.PosMult.eventually_relAmple R D.toPre.P a`.

Establish `hA : IsAmpleLB D.toPre.P.L` using `isAmpleLB_of_relAmple_of_isAffine D.toPre.P.A hP D.toPre.P.ample`. Establish `hNb` using `LB.isLB_linComb hP (K := Fin 1) ![a.left] ![1]`. Take `⟨N₂, hN₂⟩` from `Filter.eventually_atTop.1 (GlobalTheory.AmpleDominates.eventually_isGenerated D.toPre.P.A.hom hA hNb)`. Use `set N := max N₀ (max N₁ N₂) with hNdef`. Establish `hN0 : N₀ ≤ N` using `le_max_left _ _`.

Establish `hN1 : N₁ ≤ N` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `hN2 : N₂ ≤ N` using `(le_max_right _ _).trans (le_max_right _ _)`. Establish `hL'` using `LB.isLB_linComb hP (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]`. Establish `hG` using `hN₂ N hN2`. Establish `hD` using `LB.isLB_div (isLB_lbPow hP N) hNb`.

Establish `hGen : IsGenerated (LB.LinComb D.toPre.P.L (K` using `Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) := by`. Use `hG.of_lbIso hL' ((cls_eq_iff hL' hD).1 ?_)` and prove the remaining obligations. Rewrite using `[cls_linComb hP, cls_div (isLB_lbPow hP N) hNb, cls_lbPow hP, cls_linComb hP]`. Simplify using `[Fin.sum_univ_two, GlobalTheory.CechPic.pull_id]`. Normalize the expressions using the abelian group laws.

Use `⟨N, le_trans hN₀ hN0, ⟨hN₁ N hN1, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `κ hs h0 hc hint hb y`. Take `⟨r, hr⟩` from `hκ κ hs h0 hc hint hb y`. Take `⟨r', hr'⟩` from `hint y`. Use `⟨r' ^ (N - N₀) * r, ?_⟩` and prove the remaining obligations.

Establish `hsplit : (κ y : FractionRing R) ^ N = (κ y : FractionRing R) ^ (N - N₀) * (κ y : FractionRing R) ^ N₀`. Rewrite using `[← pow_add, Nat.sub_add_cancel hN0]`. Establish `hr0 : ((κ y ^ N₀ : (FractionRing R)ˣ) : FractionRing R) = (κ y : FractionRing R) ^ N₀` using `Units.val_pow_eq_pow_val _ _`. Rewrite using `[Units.val_pow_eq_pow_val, hsplit, ← hr0, hr, map_mul, map_pow, ← hr']`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨x, hx⟩` from `exists_closedFibre_pt R D`. Take `⟨σ₀, hσ⟩` from `hGen.exists_mem x`. Use `⟨σ₀, x, hx, fun j hj => ?_⟩` and prove the remaining obligations. Conclude with `(mem_nonzeroLocus_iff_basicOpen σ₀ hj).1 hσ`.
-/
theorem exists_N_sec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ GlobalTheory.MumMult.PosN D a h h' N ∧ ∃ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧ GlobalTheory.MumMult.NonzeroAt D a N σ₀ x := by
  intro R _ _ _ hR D a a' h h' hE
  have := D.toPre.P.isAb.proper
  have hP := D.toPre.P.isLB
  obtain ⟨N₀, hN₀, -, hκ⟩ := GlobalTheory.Mum.PosMult.exists_pos_mult R hR.1 D a a' h h' hE
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.Mum.PosMult.eventually_relAmple R D.toPre.P a
  have hA : IsAmpleLB D.toPre.P.L := isAmpleLB_of_relAmple_of_isAffine D.toPre.P.A hP D.toPre.P.ample
  have hNb := LB.isLB_linComb hP (K := Fin 1) ![a.left] ![1]
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (GlobalTheory.AmpleDominates.eventually_isGenerated D.toPre.P.A.hom hA hNb)
  set N := max N₀ (max N₁ N₂) with hNdef
  have hN0 : N₀ ≤ N := le_max_left _ _
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hL' := LB.isLB_linComb hP (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]
  have hG := hN₂ N hN2
  have hD := LB.isLB_div (isLB_lbPow hP N) hNb
  have hGen : IsGenerated (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) := by
    refine hG.of_lbIso hL' ((cls_eq_iff hL' hD).1 ?_)
    rw [cls_linComb hP, cls_div (isLB_lbPow hP N) hNb, cls_lbPow hP, cls_linComb hP]
    simp [Fin.sum_univ_two, GlobalTheory.CechPic.pull_id]
    abel
  refine ⟨N, le_trans hN₀ hN0, ⟨hN₁ N hN1, ?_⟩, ?_⟩
  · intro κ hs h0 hc hint hb y
    obtain ⟨r, hr⟩ := hκ κ hs h0 hc hint hb y
    obtain ⟨r', hr'⟩ := hint y
    refine ⟨r' ^ (N - N₀) * r, ?_⟩
    have hsplit : (κ y : FractionRing R) ^ N = (κ y : FractionRing R) ^ (N - N₀) * (κ y : FractionRing R) ^ N₀ := by
      rw [← pow_add, Nat.sub_add_cancel hN0]
    have hr0 : ((κ y ^ N₀ : (FractionRing R)ˣ) : FractionRing R) = (κ y : FractionRing R) ^ N₀ := Units.val_pow_eq_pow_val _ _
    rw [Units.val_pow_eq_pow_val, hsplit, ← hr0, hr, map_mul, map_pow, ← hr']
    ring
  · obtain ⟨x, hx⟩ := exists_closedFibre_pt R D
    obtain ⟨σ₀, hσ⟩ := hGen.exists_mem x
    refine ⟨σ₀, x, hx, fun j hj => ?_⟩
    exact (mem_nonzeroLocus_iff_basicOpen σ₀ hj).1 hσ

end GlobalTheory.MumMult
