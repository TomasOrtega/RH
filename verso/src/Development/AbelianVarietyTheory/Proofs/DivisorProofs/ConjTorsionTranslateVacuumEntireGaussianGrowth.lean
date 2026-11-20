import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings

namespace GlobalTheory.ConjTranslate

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

/- English proof (translation)
Establish `hg` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨b, κ, hb, -, rfl⟩` from `hG`. Take `⟨-, ⟨hd, hinv⟩, -⟩` from `GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a d _ _ (Or.inl ⟨_, b, hb, rfl⟩) (Or.inr ⟨L, L', h1, h2, rfl⟩) _ (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D hg cc δ t0 hc ht b hb.1)`. Use `⟨hd.const_mul κ, fun x hx z => ?_⟩` and prove the remaining obligations. Use `hinv x hx z` as an intermediate fact.

Simplify using `only [U] at this ⊢`. Rewrite using `[show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_Th (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a d _ _
    (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _ (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D hg cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

/- English proof (translation)
Take `⟨hg, hperm⟩` from `GlobalTheory.InducedType.induced_type D`. Establish `hGT` using `mem_Th D cc δ t0 hc ht a d L L' h1 h2 G hG`. Take `⟨hdata, htors⟩` from `(GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc`. Take `⟨hA, hAU, -⟩` from `GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG`. Take `⟨hTh, -⟩` from `GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA`.

Take `⟨t', ht'⟩` from `(GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2`. Take `⟨hN, -⟩` from `GlobalTheory.ConjNorm.useNorm_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'`. Take `⟨cc', δ', hc', -, hΛ⟩` from `GlobalTheory.ConjCurve.galCurve_holds D cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos`. Take `⟨π, hπ⟩` from `hperm Qbar ρ hρ hdata.1`. Establish `hne : fnConj D Qbar ρ G ≠ 0`.

Introduce `h`. Rewrite `hN` using `[h, hΛ]`. Rewrite `ht'` using `[hΛ]`. Use `pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hg cc' δ' t' hc' ht') (hN.symm.trans ?_)` and prove the remaining obligations. Simplify using `[normSq]`.

Take `⟨m, hm, hmy⟩` from `id hy`. Take `⟨y', hy', -⟩` from `GlobalTheory.GalExist.galEx_all D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy (by omega)`. Establish `hgal` using `(GlobalTheory.GalTheta.gal_all D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA) (by rw [comb_one]; exact hAU y hy)).1`. Rewrite `hgal` using `[comb_one]`. Rewrite using `[hgal]`.

Use `⟨U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1, U_ne_zero D _ _ _ hne, fun z => ?_⟩` and prove the remaining obligations. Use `sup_perm D hg cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _ hTh y' z` as an intermediate fact. Rewrite `this` using `[Hf_re, ← mul_div_assoc]`. Conclude with `this`.
-/
theorem conj_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  obtain ⟨hg, hperm⟩ := GlobalTheory.InducedType.induced_type D
  have hGT := mem_Th D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc Qbar ρ hρ hdata.2.1
    hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hperm Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hg cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := GlobalTheory.GalExist.galEx_all D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y
    (2 * m) hy (by omega)
  have hgal := (GlobalTheory.GalTheta.gal_all D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1)
    (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
    (by rw [comb_one]; exact hAU y hy)).1
  rw [comb_one] at hgal
  rw [hgal]
  refine ⟨U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1, U_ne_zero D _ _ _ hne, fun z => ?_⟩
  have := sup_perm D hg cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
    hTh y' z
  rw [Hf_re, ← mul_div_assoc] at this
  exact this

/- English proof (translation)
Establish `hg` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨hdata, -⟩` from `(GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc`. Take `⟨hA, -⟩` from `GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG`. Take `⟨hfix | hfix, htor, hbar⟩` from `GlobalTheory.ThetaConj.useBar_holds D cc δ hc Qbar ρ hdata`. Conclude with `conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy ρ hfix`.

Take `⟨hd, hne, hle⟩` from `conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy (rhoBar Qbar ρ) hfix`. Take `⟨hTh, -⟩` from `GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA`. Establish `hn2` using `((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0`. Rewrite `hn2` using `[U_zero]`. Establish `hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) = (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom` using `congrArg Tor.abelian₂ htor`.

Rewrite `hle` using `[(hbar a d L L' G).1, htor, hn2, hL, area_conj]`. Rewrite `hd`, `hne`, `hle` using `[(hbar a d L L' _).1]`. Use `⟨?_, fun h => hne ?_, fun z => ?_⟩` and prove the remaining obligations. Use `GlobalTheory.ThetaConj.differentiable_cBar hd` as an intermediate fact. Rewrite `this` using `[GlobalTheory.ThetaConj.cBar_cBar]`. Then use the resulting hypothesis.

Rewrite using `[h]`. Use function extensionality and compare the values at `z`. Simplify using `[cBar]`. Use `hle (vBar D z)` as an intermediate fact. Rewrite `this` using `[cBar, GlobalTheory.ThetaConj.vBar_invol]`.

Simplify `this` using `only [vBar, Complex.norm_conj]`.
-/
theorem conj_any (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ hc Qbar ρ hdata
  · exact conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy ρ hfix
  · obtain ⟨hd, hne, hle⟩ := conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy
      (rhoBar Qbar ρ) hfix
    obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ
      hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [(hbar a d L L' G).1, htor, hn2, hL, area_conj] at hle
    rw [(hbar a d L L' _).1] at hd hne hle
    refine ⟨?_, fun h => hne ?_, fun z => ?_⟩
    · have := GlobalTheory.ThetaConj.differentiable_cBar hd
      rwa [GlobalTheory.ThetaConj.cBar_cBar] at this
    · rw [h]
      funext z
      simp [cBar]
    · have := hle (vBar D z)
      rw [cBar, GlobalTheory.ThetaConj.vBar_invol] at this
      simpa only [vBar, Complex.norm_conj] using this

end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

/- English proof (translation)
Introduce `D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ`. Take `⟨-, hAU, -⟩` from `GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF`. Take `⟨hd, hne, hle⟩` from `conj_any D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ`. Conclude with `⟨GlobalTheory.ConjJet.U_diff D _ y F (mem_Th D cc dl t0 hc ht a b L L' h1 h2 F hF).1, hAU y hy, _, hd, (GlobalTheory.ConjSeries.taylor_fnConj D a b _ ρ _ hd hne).1, hle⟩`.
-/
theorem conj_translate : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ F : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → ∀ y, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl))) := by
  intro D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  obtain ⟨-, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF
  obtain ⟨hd, hne, hle⟩ := conj_any D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  exact ⟨GlobalTheory.ConjJet.U_diff D _ y F (mem_Th D cc dl t0 hc ht a b L L' h1 h2 F hF).1, hAU y hy,
    _, hd, (GlobalTheory.ConjSeries.taylor_fnConj D a b _ ρ _ hd hne).1, hle⟩

end GlobalTheory.ConjTranslate
