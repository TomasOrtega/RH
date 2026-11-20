import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledUnitaryVacuumTensorEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDblPar

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv p hp`. Use `set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef`. Establish `hΨ : Ψ ∈ schA F _` using `hRv.2`. Establish `hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _` using `GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.star_mem_schA_main _ Ψ hΨ)`. Establish `hV` using `hTr.geo.hM'.vac v`.

Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hV.2.1 (funext h)`. Establish `hΨne : Ψ ≠ 0`.

Introduce `h0`. Set `x : Fin a' × Fin (a + a') → AF F` to `fun i => GlobalTheory.LatVac.liftV v (y i)`. Establish `hRx : R x = R 0`. Use `hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)` as an intermediate fact. Simplify using `using this`.

Establish `h1` using `congrFun h0 x`. Simplify using `only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1`. Conclude with `mul_ne_zero hy hR0 h1`. Take `⟨c, hc⟩` from `GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen F E σ B a a' G X om om' hTr v w hin dd omd hdc hws R hRv p hp.1`. Take `⟨l, hl, hinv, hl0⟩` from `GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero F _ Ψ hΨ hΨne`.

Take `⟨t, ht⟩` from `hp.2`. Establish `hS` using `hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ`. Establish `htp` using `GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ G.W v p hp t ht`. Establish `ha` using `GlobalTheory.T.comparisonCharacter_det_eq_one_inertPlace F E σ B a a' G X om om' hTr v w hin hT t htp`. Establish `hb` using `GlobalTheory.T.local_theta_integral_at_inert_place F E σ B a a' G X om om' hTr v w hin hT t htp`.

Rewrite `hS` using `[ha, hb]`. Rewrite `hS` using `[hc, map_smul, smul_eq_mul]`. Simplify using `only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS`. Establish `h1 : c = 1` using `(mul_eq_right₀ hl0).mp hS`. Rewrite using `[hc, h1, one_smul]`.
-/
theorem parD_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.star_mem_schA_main _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hV.2.1 (funext h)
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen F E σ B a a' G X om om' hTr v w hin dd omd hdc hws R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ G.W v p hp t ht
  have ha := GlobalTheory.T.comparisonCharacter_det_eq_one_inertPlace F E σ B a a' G X om om' hTr v w hin hT t htp
  have hb := GlobalTheory.T.local_theta_integral_at_inert_place F E σ B a a' G X om om' hTr v w hin hT t htp
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]

end GlobalTheory.InertDblPar

end
