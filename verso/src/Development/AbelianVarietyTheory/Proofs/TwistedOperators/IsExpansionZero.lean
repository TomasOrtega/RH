import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRealSSmulTwoSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryBaseVacuaLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaRealUpToTwistLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosetsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFlatAsm

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

/- English proof (translation)
Simplify using `only [evT]`. Rewrite using `[← mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : 2 * k < D.R.m` using `by have := Finset.mem_range.1 hk; omega`.

Simplify using `only [combC]`. Rewrite using `[h _ (even_two_mul k) hk', GlobalTheory.SeeSaw.Scale.biComb_smul]`. Both sides reduce to the same expression.
-/
theorem evT_combC_smul (c : Combs G) (a : ℕ → ℂ) (C C' : BiFam G) (h : ∀ j, Even j → j < D.R.m → C j = a j • C' j)
    (f : SchRow G) (u : ColPt G) (y : RowPt G) :
    evT (combC W c C) f u y = (∏ k ∈ Finset.range (D.R.m / 2), a (2 * k)) * evT (combC W c C') f u y := by
  simp only [evT]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k < D.R.m := by have := Finset.mem_range.1 hk; omega
  simp only [combC]
  rw [h _ (even_two_mul k) hk', GlobalTheory.SeeSaw.Scale.biComb_smul]
  rfl

/- English proof (translation)
Introduce `j hj hm` and use `⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ (h j hj hm).1, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ (h j hj hm).2⟩`.
-/
theorem isRealFam_smul (a : ℕ → ℂ) {C : BiFam G} (h : IsRealFam W C) : IsRealFam W fun j => a j • C j :=
  fun j hj hm => ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ (h j hj hm).1, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ (h j hj hm).2⟩

/- English proof (translation)
Establish `hm : 0 ∈ Finset.range (D.R.m / 2)` using `by have := D.R.two_le_m; exact Finset.mem_range.2 (by omega)`. Rewrite using `[Finset.prod_eq_single_of_mem 0 hm fun k _ hk => if_neg (by omega)]`. Conclude with `if_pos rfl`.
-/
theorem prod_ite_zero (κ : ℂ) :
    ∏ k ∈ Finset.range (D.R.m / 2), (if 2 * k = 0 then κ else 1) = κ := by
  have hm : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; exact Finset.mem_range.2 (by omega)
  rw [Finset.prod_eq_single_of_mem 0 hm fun k _ hk => if_neg (by omega)]
  exact if_pos rfl

variable {W} in

/- English proof (translation)
Take `⟨e, he, -, -⟩` from `h`. Use `⟨e, he, fun d hd => by simp at hd, fun x y _ _ => ?_⟩` and prove the remaining obligations. Simplify using `only [GridChoice.supp, Set.mem_setOf_eq, not_forall, unfSupport, not_not] at hβ`. Take `⟨w, hw⟩` from `hβ`. Rewrite using `[Finsupp.sum_zero_index]`.

Use `(Finset.prod_eq_zero (Finset.mem_univ w) ?_).symm` and prove the remaining obligations. Simplify using `only [GridChoice.term]`. Rewrite using `[hw]`. Both sides reduce to the same expression.
-/
theorem isExpansion_zero {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (hβ : β ∉ S.supp t Φ)
    {τ : PureDat G t →₀ ℂ} (h : S.IsExpansion t Φ β τ) : S.IsExpansion t Φ β 0 := by
  obtain ⟨e, he, -, -⟩ := h
  refine ⟨e, he, fun d hd => by simp at hd, fun x y _ _ => ?_⟩
  simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall, unfSupport, not_not] at hβ
  obtain ⟨w, hw⟩ := hβ
  rw [Finsupp.sum_zero_index]
  refine (Finset.prod_eq_zero (Finset.mem_univ w) ?_).symm
  simp only [GridChoice.term]
  rw [hw]
  rfl

end Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

/- English proof (translation)
Take `⟨κ, z₁, hz₁, hl⟩` from `hl`. Take `⟨hb, z₂, hz₂, hv⟩` from `hv`. Use `⟨fun t => z₁ t * (∏ k ∈ Finset.range (D.R.m / 2), z₂ t (2 * k))⁻¹, fun t => mul_mem (hz₁ t) (inv_mem (prod_mem fun k _ => hz₂ t _)), fun P p hp => ?_⟩` and prove the remaining obligations. Take `⟨C₀, hC₀, hC⟩` from `hv P p hp`. Use `⟨fun j => (if j = 0 then κ else 1) • C₀ j, isRealFam_smul ch.W _ hC₀, fun t Φ τ hτ M hM β b hβ τ' c hτ' hc => ?_⟩` and prove the remaining obligations.

Take `⟨b₀, hb₀⟩` from `hb t`. Distinguish the cases in `hs : Stair t β`. Use `⟨_, fun _ => rfl, fun u y => ?_⟩` and prove the remaining obligations. Take `⟨ζ, hζ, e⟩` from `hl t Φ τ hτ M hM β b b₀ hβ hb₀ τ' c hτ' hc`. Rewrite using `[e P p hp u y, hζ hs, Finsupp.mul_sum, Finsupp.mul_sum]`.

Use `Finsupp.sum_congr fun d _ => ?_` and prove the remaining obligations. Rewrite using `[evT_combC_smul ch.W (c d) (fun j => (z₂ t j : ℂ)) _ C₀ (hC t M hM b₀ hb₀), evT_combC_smul ch.W (c d) (fun j => if j = 0 then κ else 1) _ C₀ (fun _ _ _ => rfl), prod_ite_zero]`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_prod, _root_.mul_inv_rev, inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨0, fun h => absurd h hs, fun u y => ?_⟩` and prove the remaining obligations.

Take `⟨ζ, -, e⟩` from `hl t Φ τ hτ M hM β b b₀ hβ hb₀ 0 c (isExpansion_zero _ t Φ β (fun h => hs (ho t Φ β h)) hτ') (fun d hd => by simp at hd)`. Rewrite using `[e P p hp u y, Finsupp.sum_zero_index, mul_zero, zero_mul]`.
-/
theorem flatAt_of (s : ℤˣ) (hl : LocAt ch s) (hv : VacAt ch) (ho : OneAt ch) : FlatAt ch s := by
  obtain ⟨κ, z₁, hz₁, hl⟩ := hl
  obtain ⟨hb, z₂, hz₂, hv⟩ := hv
  refine ⟨fun t => z₁ t * (∏ k ∈ Finset.range (D.R.m / 2), z₂ t (2 * k))⁻¹,
    fun t => mul_mem (hz₁ t) (inv_mem (prod_mem fun k _ => hz₂ t _)), fun P p hp => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hv P p hp
  refine ⟨fun j => (if j = 0 then κ else 1) • C₀ j, isRealFam_smul ch.W _ hC₀,
    fun t Φ τ hτ M hM β b hβ τ' c hτ' hc => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hb t
  by_cases hs : Stair t β
  · refine ⟨_, fun _ => rfl, fun u y => ?_⟩
    obtain ⟨ζ, hζ, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ τ' c hτ' hc
    rw [e P p hp u y, hζ hs, Finsupp.mul_sum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [evT_combC_smul ch.W (c d) (fun j => (z₂ t j : ℂ)) _ C₀ (hC t M hM b₀ hb₀),
      evT_combC_smul ch.W (c d) (fun j => if j = 0 then κ else 1) _ C₀ (fun _ _ _ => rfl), prod_ite_zero]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_prod, _root_.mul_inv_rev, inv_inv]
    ring
  · refine ⟨0, fun h => absurd h hs, fun u y => ?_⟩
    obtain ⟨ζ, -, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ 0 c
      (isExpansion_zero _ t Φ β (fun h => hs (ho t Φ β h)) hτ') (fun d hd => by simp at hd)
    rw [e P p hp u y, Finsupp.sum_zero_index, mul_zero, zero_mul]

/- English proof (translation)
The claim follows from `big_mono (fun ch ⟨⟨⟨s, hl⟩, hv⟩, ho⟩ => ⟨s, flatAt_of ch s hl hv ho⟩) ((GlobalTheory.T.flat_dictionary_base_vacua_large_depth.and GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth).and GlobalTheory.T.rowTest_support_families_staircase_cosets)`.
-/
theorem flatAt_big : Big fun ch => ∃ s, FlatAt ch s :=
  big_mono (fun ch ⟨⟨⟨s, hl⟩, hv⟩, ho⟩ => ⟨s, flatAt_of ch s hl hv ho⟩) ((GlobalTheory.T.flat_dictionary_base_vacua_large_depth.and GlobalTheory.T.unfolded_vacua_real_up_to_twist_large_depth).and GlobalTheory.T.rowTest_support_families_staircase_cosets)

end GlobalTheory.RowFlatAsm

end
