import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPairStatement

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.SplitParLeft
open GlobalTheory.DblVacLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hT hunr _ _ d' hd' dd omd hdc hws R hR0 hRv p hp`. Use `set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef`. Establish `hΨ : Ψ ∈ schA F _` using `hRv.2`. Establish `hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _` using `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)`. Establish `hV` using `hTr.geo.hM'.vac v`.

Take `⟨y, hy⟩` from `Function.ne_iff.mp hV.2.1`. Establish `hΨne : Ψ ≠ 0`. Introduce `h0`. Set `x : Fin a' × Fin (a + a') → AF F` to `fun i => GlobalTheory.LatVac.liftV v (y i)`. Establish `hRx : R x = R 0`.

Use `hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)` as an intermediate fact. Simplify using `using this`. Establish `h1` using `congrFun h0 x`. Simplify using `only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1`. Conclude with `mul_ne_zero hy hR0 h1`.

Take `⟨c, hc⟩` from `dblFun_eigen_left hTr.base hTr.geo v hunr d' hd' dd omd hdc hws.2.1 R hRv p hp.1`. Take `⟨l, hl, hinv, hl0⟩` from `GlobalTheory.DblDiagForm.exists_form F _ Ψ hΨ hΨne`. Take `⟨t, ht⟩` from `hp.2`. Establish `hS` using `hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ`. Establish `htp` using `GlobalTheory.InertDbl.parD_diag_action F E σ G.V' v p hp t ht`.

Establish `hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ∉ above E (X.T : Set (Pl F))` using `fun w h hm => hT (h ▸ hm)`. Establish `ha : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1`. Rewrite using `[MonoidHom.div_apply, chr_det_eq_one G.V' hTr.geo.hV'.lat v X.α (fun w h => hTr.chars.unrα w (hw w h)) t htp.1 htp.2, chr_det_eq_one G.V' hTr.geo.hV'.lat v X.β (fun w h => hTr.chars.unrβ w (hw w h)) t htp.1 htp.2, div_one]`. Establish `hb` using `GlobalTheory.IntegralDetModule.modu_norm_det G.V' hTr.geo.hV'.lat v t htp.1 htp.2`. Rewrite `hS` using `[ha, hb]`.

Rewrite `hS` using `[hc, map_smul, smul_eq_mul]`. Simplify using `only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS`. Establish `h1 : c = 1` using `(mul_eq_right₀ hl0).mp hS`. Rewrite using `[hc, h1, one_smul]`.
-/
theorem splitParallel_derivative_fixes_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.V' v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hT hunr _ _ d' hd' dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hV.2.1
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := dblFun_eigen_left hTr.base hTr.geo v hunr d' hd' dd omd hdc hws.2.1 R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.DblDiagForm.exists_form F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.InertDbl.parD_diag_action F E σ G.V' v p hp t ht
  have hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ∉ above E (X.T : Set (Pl F)) :=
    fun w h hm => hT (h ▸ hm)
  have ha : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
    rw [MonoidHom.div_apply,
      chr_det_eq_one G.V' hTr.geo.hV'.lat v X.α (fun w h => hTr.chars.unrα w (hw w h)) t htp.1 htp.2,
      chr_det_eq_one G.V' hTr.geo.hV'.lat v X.β (fun w h => hTr.chars.unrβ w (hw w h)) t htp.1 htp.2, div_one]
  have hb := GlobalTheory.IntegralDetModule.modu_norm_det G.V' hTr.geo.hV'.lat v t htp.1 htp.2
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]
end GlobalTheory.SplitParLeft
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | exact _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | (intros; apply _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.split_parallel_derivative_left_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.V' v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @_root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | exact _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | (intros; apply _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left <;> assumption)
end
