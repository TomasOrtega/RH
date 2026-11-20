import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackMemCuspFormSupLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramedPointRestrictCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverLaUnder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum

/- English proof (translation)
Rewrite `hf` using `[cuspW_wtZ]`. Conclude with `cusp_le_sec Xo c U a n hf`.
-/
theorem mem_sec_of_mem_cuspW_wtZ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U (wtZ a n)) : f ∈ sec Xo c a n := by
  rw [cuspW_wtZ] at hf
  exact cusp_le_sec Xo c U a n hf

/- English proof (translation)
Introduce `D T j Y e o hJ hj hG a n hD cst q hq`. Establish `hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q`. Take `⟨hp, hq', -⟩` from `hJ.pins.2.2.2 j hj`. Take `⟨h1, h2⟩` from `hj`. Establish `h3` using `D.R.m_add_three_le_k`.

Rewrite using `[hp, hq']`. Simplify using `only [Ranks.sigW]`. Use linear arithmetic over natural numbers and integers. Establish `hL` using `GlobalTheory.LevGeo.laws_core D T j hJ hj`. Establish `hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q`.

Take `⟨hp, hq', -⟩` from `hL.dat`. Take `⟨h1, h2⟩` from `hj`. Establish `hk` using `D.R.m_add_three_le_k`. Rewrite using `[hp, hq']`. Simplify using `only [Ranks.sigW]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[refExp_vp_le_iff]`. Introduce `la₂ S io₂ e₂ ho₂ y₂ ha₂ φ hφ`. Take `⟨y', ha', hφ', hv'⟩` from `GlobalTheory.CoverDown.exists_intFr_below _ _ _ _ (T.Q.Xo j) Y.c' Y.d hpq hG.lev.1 (Or.inl ⟨hne, hL.levA⟩) S io₂ y₂ ha₂`. Take `⟨y, ha, hφy, hv⟩` from `GlobalTheory.T.integralFramedPoint_restrict_coefficient_field _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle S _ y' ha'`.

Take `⟨la', e', hq', ho'⟩` from `GlobalTheory.PlaceBelow.exists_overLa_under Y.c'.F Y.d.c₂.F (Y.d.eF : Y.c'.F →+* Y.d.c₂.F) q la₂.1 hq la₂.2 S io₂ e₂ ho₂`. Take `⟨la, e₀, hq₀, ho⟩` from `GlobalTheory.PlaceBelow.exists_overLa_under T.Q.c.F Y.c'.F (IntermediateField.inclusion Y.hle).toRingHom q la' hq hq' S _ e' ho'`. Use `le_trans ?_ (refExp_vp_le_iff (T.U j) |>.1 le_rfl ⟨la, hq₀⟩ S _ e₀ ho y ha φ (hφy φ (hφ' φ hφ)))` and prove the remaining obligations. Use `le_iInf₂ fun f hf => ?_` and prove the remaining obligations. Take `⟨g, ⟨hg, hP⟩, -⟩` from `GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover D T j Y e o hJ hj hG hG.unit hG.modelW a n hD f.1 f.2`.

Establish `hgl` using `(GlobalTheory.T.pullback_mem_cuspFormSupLattice_iff D T j Y e o hJ hj hG a n f ⟨g, hg⟩ hP).2 hf`. Establish `hfs : f.1 ∈ sec (T.Q.Xo j) T.Q.c a n` using `mem_sec_of_mem_cuspW_wtZ f.2`. Establish `hP'` using `((GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW).2.2 a n f.1 hfs g).1 hP`. Establish `hbc` using `((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f.1 hfs).1`. Establish `hval : evI y₂ g = evI y f.1` using `(hv' a n _ hbc g (mem_sec_of_mem_cuspW_wtZ hg) hP').trans (hv a n f.1 hfs)`.

Use `(iInf₂_le (⟨g, hg⟩ : Y.V (wtZ a n)) hgl).trans (le_of_eq ?_)` and prove the remaining obligations. Conclude with `congrArg _ hval`.
-/
theorem refExp_vp_cover_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtZ a n) q ≤ refExp_vp (T.U j) cst (wtZ a n) q := by
  intro D T j Y e o hJ hj hG a n hD cst q hq
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hJ.pins.2.2.2 j hj
    obtain ⟨h1, h2⟩ := hj
    have h3 := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  have hL := GlobalTheory.LevGeo.laws_core D T j hJ hj
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  rw [refExp_vp_le_iff]
  intro la₂ S io₂ e₂ ho₂ y₂ ha₂ φ hφ
  obtain ⟨y', ha', hφ', hv'⟩ := GlobalTheory.CoverDown.exists_intFr_below _ _ _ _ (T.Q.Xo j) Y.c' Y.d hpq hG.lev.1
    (Or.inl ⟨hne, hL.levA⟩) S io₂ y₂ ha₂
  obtain ⟨y, ha, hφy, hv⟩ := GlobalTheory.T.integralFramedPoint_restrict_coefficient_field _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle S _ y' ha'
  obtain ⟨la', e', hq', ho'⟩ := GlobalTheory.PlaceBelow.exists_overLa_under Y.c'.F Y.d.c₂.F (Y.d.eF : Y.c'.F →+* Y.d.c₂.F) q la₂.1 hq la₂.2 S io₂ e₂ ho₂
  obtain ⟨la, e₀, hq₀, ho⟩ := GlobalTheory.PlaceBelow.exists_overLa_under T.Q.c.F Y.c'.F (IntermediateField.inclusion Y.hle).toRingHom q la' hq hq' S _ e' ho'
  refine le_trans ?_ (refExp_vp_le_iff (T.U j) |>.1 le_rfl ⟨la, hq₀⟩ S _ e₀ ho y ha φ (hφy φ (hφ' φ hφ)))
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨g, ⟨hg, hP⟩, -⟩ := GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover D T j Y e o hJ hj hG hG.unit hG.modelW a n hD f.1 f.2
  have hgl := (GlobalTheory.T.pullback_mem_cuspFormSupLattice_iff D T j Y e o hJ hj hG a n f ⟨g, hg⟩ hP).2 hf
  have hfs : f.1 ∈ sec (T.Q.Xo j) T.Q.c a n := mem_sec_of_mem_cuspW_wtZ f.2
  have hP' := ((GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW).2.2 a n f.1 hfs g).1 hP
  have hbc := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f.1 hfs).1
  have hval : evI y₂ g = evI y f.1 :=
    (hv' a n _ hbc g (mem_sec_of_mem_cuspW_wtZ hg) hP').trans (hv a n f.1 hfs)
  refine (iInf₂_le (⟨g, hg⟩ : Y.V (wtZ a n)) hgl).trans (le_of_eq ?_)
  exact congrArg _ hval

end GlobalTheory.RefSum

end
