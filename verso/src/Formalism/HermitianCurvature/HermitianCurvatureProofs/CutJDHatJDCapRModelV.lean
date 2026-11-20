import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

/- English proof (translation)
Take `⟨hp, -, hc, hci, -⟩` from `hL`. Establish `hT : (fun σ => Wd.Ts σ y) ∘ MA.siteA P (MA.DQ P) = L.Tl y`. Use function extensionality and compare the values at `l`. Simplify using `only [Function.comp_apply]`. Unfold `R.LevelData.Tl`.

Rewrite using `[hp, hc, hci]`. Both sides reduce to the same expression. Unfold `Wd.v0 MA.sites R.LevelData.Tprod`. Rewrite using `[List.map_reverse, List.map_ofFn, hT]`.
-/
theorem site_vector_eq_tensor_product (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (b : Fin 2) : Wd.v0 (MA.sites P (MA.DQ P)) y b = L.Tprod y b 0 := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hT : (fun σ => Wd.Ts σ y) ∘ MA.siteA P (MA.DQ P) = L.Tl y := by
    funext l
    simp only [Function.comp_apply]
    unfold R.LevelData.Tl
    rw [hp, hc, hci]
    rfl
  unfold Wd.v0 MA.sites R.LevelData.Tprod
  rw [List.map_reverse, List.map_ofFn, hT]

/- English proof (translation)
Establish `hL'` using `hL`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL'`. Establish `sp : ∀ l, star (L.p l) = -L.pb l` using `fun l => by`. Rewrite using `[hp, hpb]`. Use `show star (MA.sc P (MA.DQ P) ((MA.DQ P).pP l)) = -MA.sc P (MA.DQ P) ((MA.DQ P).pbP l)`.

Rewrite using `[Formalism.FourierDecayAlt.P.MAx3.F.star_sc, Formalism.FourierDecayAlt.P.MAx3.F.star_pP]`. Unfold `MA.sc`. Simplify using the standard rewrite rules. Establish `sc : ∀ l, star (L.c l) = L.cb l` using `fun l => by`. Rewrite using `[hc, hcb]`.

Use `show star (MA.sc P (MA.DQ P) ((MA.DQ P).cP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbP l)`. Rewrite using `[Formalism.FourierDecayAlt.P.MAx3.F.star_sc]`. Both sides reduce to the same expression. Establish `sci : ∀ l, star (L.ci l) = L.cbi l` using `fun l => by`. Rewrite using `[hci, hcbi]`.

Use `show star (MA.sc P (MA.DQ P) ((MA.DQ P).ciP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbiP l)`. Rewrite using `[Formalism.FourierDecayAlt.P.MAx3.F.star_sc]`. Both sides reduce to the same expression. Establish `h` using `congrArg (fun M => M 0 a) (Formalism.FourierDecayAlt.P.TLB.star_Tprod_gen L sp sc sci y)`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h`.

Rewrite using `[site_vector_eq_tensor_product P L hL y a]`. Conclude with `h`.
-/
theorem star_site_vector_eq_tensor (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (a : Fin 2) :
    star (Wd.v0 (MA.sites P (MA.DQ P)) y a) = L.Tvprod (starRingEnd ℂ y) a 0 := by
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL'
  have sp : ∀ l, star (L.p l) = -L.pb l := fun l => by
    rw [hp, hpb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).pP l)) = -MA.sc P (MA.DQ P) ((MA.DQ P).pbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc, Formalism.FourierDecayAlt.P.MAx3.F.star_pP]
    unfold MA.sc
    simp
  have sc : ∀ l, star (L.c l) = L.cb l := fun l => by
    rw [hc, hcb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).cP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have sci : ∀ l, star (L.ci l) = L.cbi l := fun l => by
    rw [hci, hcbi]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).ciP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbiP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have h := congrArg (fun M => M 0 a) (Formalism.FourierDecayAlt.P.TLB.star_Tprod_gen L sp sc sci y)
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h
  rw [site_vector_eq_tensor_product P L hL y a]
  exact h

/- English proof (translation)
Introduce `P L hL y`. Use `⟨fun b => site_vector_eq_tensor_product P L hL (y : ℂ) b, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[star_site_vector_eq_tensor P L hL (y : ℂ) a, Complex.conj_ofReal]`.
-/
theorem mirror_residue_model_holds : JDRModelV := by
  intro P L hL y
  refine ⟨fun b => site_vector_eq_tensor_product P L hL (y : ℂ) b, fun a => ?_⟩
  rw [star_site_vector_eq_tensor P L hL (y : ℂ) a, Complex.conj_ofReal]

end

end Formalism.FourierDecayAlt.P.CutMP
