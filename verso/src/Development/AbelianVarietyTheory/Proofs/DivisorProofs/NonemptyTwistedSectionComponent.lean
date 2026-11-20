import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.KeyTwDeep

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.KeyRootTw in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg`. Take `⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩` from `GlobalTheory.KeyFamClosing.keyFam_one`. Set `e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)` to `(Fintype.equivFin _).symm`. Take `⟨K, hKmem, hKval⟩` from `GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq`. Establish `hσ0` using `goodEmb_goodOf c c.F.val.toRingHom`.

Take `⟨⟨ρ, hρmem⟩, hρ⟩` from `GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval`. Establish `hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ`. Use `⟨?_, k₂, k₃, k₄, ?_⟩` and prove the remaining obligations. Simplify `k₁` using `only [GlobalTheory.KeyCl.Homog, mul_one]`. Simplify `k₅` using `only [GlobalTheory.KeyCl.ArchNorm, mul_one]`.

Establish `hval` using `GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval`. Establish `hC` using `fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval`. Use `choose C hCpos hClog hCeq using hC`. Establish `hgE` using `card_frame_index Dw e`. Establish `hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))`.

Simplify using `[Fintype.card_sigma]`. Establish `hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m` using `wtOf_zero_fst E H Dw`. Establish `hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw`. Use function extensionality and compare the values at `i`. Break down `i with _ | ⟨τ, i⟩` into its components or cases.

Both sides reduce to the same expression. Simplify using `only [exZ, keyEx, Pi.neg_apply]`. Conclude with `hwt 1 τ i i.2`. Establish `hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0`. Rewrite using `[← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]`.

Introduce `Z`. Take `⟨a, ha, haK⟩` from `hρ Z`. Establish `hP : HasPts U Z` using `hasPts U hpq hg hU Z`. Use `set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs`. Use `set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'`.

Establish `hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1))`. Use `mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)` as an intermediate fact. Rewrite `this` using `[zero_add, ← hex]`. Then use the resulting hypothesis. Establish `hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1)))`. Use `mul_mem_secZ (idem_mem_secZ Z) hρmem` as an intermediate fact.

Establish `h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw`. Establish `h3` using `exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))`. Rewrite `h3` using `[hadd, hex]`. Apply the tactic sequence `have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl`. Rewrite `h3` using `[h4]`.

Conclude with `(neg_add_eq_zero.1 h3.symm).symm`. Rewrite `this` using `[zero_add, ← h2]`. Then use the resulting hypothesis. Establish `hsupp : s ∈ suppOn Z` using `by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)`. Establish `hsupp' : s' ∈ suppOn Z` using `by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)`. Establish `hnorm` using `fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) => homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz ((hP.1 σ).2 z hz)`.

Establish `hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ` using `fun σ h => if_pos h`. Establish `hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i)` using `fun m τ i j hij hj => by`. Rewrite using `[hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]`. Establish `hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D`. Introduce `σ hσ`.

Use `⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `hnorm σ`. Rewrite `h1` using `[hgood σ hσ]`. Conclude with `(h1 z hz).1.le`. Establish `hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D`.

Introduce `σ hσ`. Use `⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `hnorm σ`. Rewrite `h1` using `[hgood σ hσ]`. Conclude with `(h1 z hz).2.le`.

Set `B : HeightOneSpectrum (𝓞 c.F) → ℝ` to `fun w => ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)`. Establish `hbnd` using `fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) => val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1 (hval w v (valOn_subset Z w hv)).2`. Set `t : TwSec U x Z (wtOf Dw 0 1)` to `{ even := even_wtOf _ _ sig := s inv := s' sig_mem := hsm inv_mem := by`. Establish `h5` using `exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)`. Establish `h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1)` using `neg_eq_of_add_eq_zero_right hadd`.

Rewrite using `[← h5, h6]`. Conclude with `hsm'`. Use `idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]`. Use `idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]`. Use `mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]`.

Use `cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)`. Use `cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _`. Use `norm_inf := fun σ z hz => by`. Rewrite using `[(hnorm σ z hz).1, norm_goodOf]`. Use `cusp_sig := fun G hG f hf => GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf`.

Use `cusp_inv := fun G hG f hf => by`. Establish `h7` using `GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1)) hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf`. Rewrite `h7` using `[add_assoc, hadd, add_zero]`. Then use the resulting hypothesis. Use `lo := fun w => -(vAdd w a : ℝ) / 4 - B w`. Use `hi := fun w => -(vAdd w a : ℝ) / 4`.

Use `lo_le := fun w v hv => (hbnd w v hv).1`. Use `le_hi := fun w v hv => (hbnd w v hv).2`. Use `finite_lo := by`. Use `((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Simplify using `only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn`. Apply `hw` to reduce the goal to its premises. Simplify using `[B, hn.1, hn.2]`. Use `finite_hi := by`. Use `(finite_vAdd ha).subset fun w hw => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Simplify using `only [Function.mem_support, not_not] at hn`. Apply `hw` to reduce the goal to its premises. Simplify using `[hn]`. Use `pts := hP }`.

Conclude with `⟨t⟩`.
-/
theorem twSec_keyRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) →
    FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) →
    ∀ Z : Comp Xo c, Nonempty (TwSec U x Z (wtOf Dw 0 1)) := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨⟨ρ, hρmem⟩, hρ⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := by
    simp [Fintype.card_sigma]
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  have hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  intro Z
  obtain ⟨a, ha, haK⟩ := hρ Z
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hρmem
    have h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw := by
      have h3 := exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))
      rw [hadd, hex] at h3
      have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl
      rw [h4] at h3
      exact (neg_add_eq_zero.1 h3.symm).symm
    rwa [zero_add, ← h2] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hnorm := fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) =>
    homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz
      ((hP.1 σ).2 z hz)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hbnd := fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) =>
    val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1
      (hval w v (valOn_subset Z w hv)).2
  let t : TwSec U x Z (wtOf Dw 0 1) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by
        have h5 := exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)
        have h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1) := neg_eq_of_add_eq_zero_right hadd
        rw [← h5, h6]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]
      idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]
      mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]
      cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)
      cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _
      norm_inf := fun σ z hz => by
        rw [(hnorm σ z hz).1, norm_goodOf]
      cusp_sig := fun G hG f hf =>
        GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1))
          hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun w => -(vAdd w a : ℝ) / 4 - B w
      hi := fun w => -(vAdd w a : ℝ) / 4
      lo_le := fun w v hv => (hbnd w v hv).1
      le_hi := fun w v hv => (hbnd w v hv).2
      finite_lo := by
        refine ((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_
        by_contra hn
        simp only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn
        apply hw
        simp [B, hn.1, hn.2]
      finite_hi := by
        refine (finite_vAdd ha).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, not_not] at hn
        apply hw
        simp [hn]
      pts := hP }
  exact ⟨t⟩

/- English proof (translation)
Introduce `_ D T hT j hp _ _ hj Y e o hG _ _ Z`. Establish `hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p` using `Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne`. Establish `hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p` using `GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0`. Conclude with `twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z`.
-/
theorem exists_twSec_keyRoot_deep : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (GlobalTheory.FlatTw.TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 1)) := by
  intro _ D T hT j hp _ _ hj Y e o hG _ _ Z
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0
  exact twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z

end GlobalTheory.KeyTwDeep
