import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePairStatement

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlatAnyLevel
section Span
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
end Span
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
section Laws
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end Laws
section Chain
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
section Cancel
open Filter Topology
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}
end Cancel
end Chain
end GlobalTheory.FlatAnyLevel
end
section Cover
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.FlatCore GlobalTheory.FlatLine GlobalTheory.AllWt in
/- English proof (translation)
Introduce `_ D T j Y e o hG _`. Use `⟨1, one_pos, fun Z τ => ?_⟩` and prove the remaining obligations. Take `⟨A⟩` from `GlobalTheory.FlatAnyLevel.archEx (GlobalTheory.FlatAnyLevel.neatUnf_of_good D T j Y e o hG) (xiR D) Z τ`. Simplify using `only [Nat.cast_one, one_smul]`. Use `⟨A.sig, A.inv, A.sig_mem, A.inv_mem, A.idem_sig, A.idem_inv, A.mul_inv, fun σ hσ => ?_⟩` and prove the remaining obligations.

Establish `hg : goodOf Y.d.c₂ σ = σ` using `if_pos hσ`. Establish `hn` using `A.norm_inf σ`. Rewrite `hn` using `[hg]`. Use `⟨max (A.cInf σ) (A.cInf σ)⁻¹, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hs : homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0) A.sig z = A.cInf σ`.

Use `hn ▸ Set.mem_image_of_mem _ hz` as an intermediate fact. Conclude with `this`. Take `⟨hdom, hlies⟩` from `hz`. Establish `hpos` using `A.cInf_pos σ`. Establish `ht` using `tested_of_homN_ne (U := Y.U σ) (x := xiR D) hdom (hs.trans_ne hpos.ne')`.

Establish `hi` using `homN_idem (U := Y.U σ) (x := xiR D) hdom hlies ht`. Establish `hm` using `homN_mul (Y.U σ) (xiR D) (G := wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0) (G' := -(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) ⟨0, by simp [wtOf_snd]⟩ ⟨0, by simp [wtOf_snd]⟩ A.sig A.inv z hdom`. Rewrite `hm` using `[add_neg_cancel, A.mul_inv, hi, hs]`. Use `⟨hs ▸ le_max_left _ _, ?_⟩` and prove the remaining obligations. Establish `: homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) A.inv z = (A.cInf σ)⁻¹`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this]`. Conclude with `le_max_right _ _`.
-/
theorem GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ s i : Rul Y.d.Xo₂ Y.d.c₂, s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C) := by
  intro _ D T j Y e o hG _
  refine ⟨1, one_pos, fun Z τ => ?_⟩
  obtain ⟨A⟩ := GlobalTheory.FlatAnyLevel.archEx (GlobalTheory.FlatAnyLevel.neatUnf_of_good D T j Y e o hG) (xiR D) Z τ
  simp only [Nat.cast_one, one_smul]
  refine ⟨A.sig, A.inv, A.sig_mem, A.inv_mem, A.idem_sig, A.idem_inv, A.mul_inv, fun σ hσ => ?_⟩
  have hg : goodOf Y.d.c₂ σ = σ := if_pos hσ
  have hn := A.norm_inf σ
  rw [hg] at hn
  refine ⟨max (A.cInf σ) (A.cInf σ)⁻¹, fun z hz => ?_⟩
  have hs : homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0) A.sig z = A.cInf σ := by
    have := hn ▸ Set.mem_image_of_mem _ hz
    exact this
  obtain ⟨hdom, hlies⟩ := hz
  have hpos := A.cInf_pos σ
  have ht := tested_of_homN_ne (U := Y.U σ) (x := xiR D) hdom (hs.trans_ne hpos.ne')
  have hi := homN_idem (U := Y.U σ) (x := xiR D) hdom hlies ht
  have hm := homN_mul (Y.U σ) (xiR D) (G := wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)
    (G' := -(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) ⟨0, by simp [wtOf_snd]⟩ ⟨0, by simp [wtOf_snd]⟩ A.sig A.inv z hdom
  rw [add_neg_cancel, A.mul_inv, hi, hs] at hm
  refine ⟨hs ▸ le_max_left _ _, ?_⟩
  have : homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (flatWt (T.Q.Dw j) τ) 0)) A.inv z = (A.cInf σ)⁻¹ := by
    field_simp
    linarith
  rw [this]; exact le_max_right _ _
end Cover
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | exact _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | (intros; apply _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.flat_unit_exists_at_every_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ s i : Rul Y.d.Xo₂ Y.d.c₂, s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) ((N : ℤ) • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C) := by
  first | exact @_root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | exact _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level | (intros; apply _root_.GlobalTheory.FlatAnyLevel.exists_flat_unit_bounded_any_level <;> assumption)
end
