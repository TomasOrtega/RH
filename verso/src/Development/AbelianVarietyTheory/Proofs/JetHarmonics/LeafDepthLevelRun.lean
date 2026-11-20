import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRowsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthParamsPlusMinusCountsEqKappaStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunDepthDataLawsAndFiniteLocalDepthStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RamificationIndexGeOfResCharDvdLevelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegreeStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

/- English proof (translation)
Introduce `D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF`. Establish `hL` using `(GlobalTheory.T.runDepthData_laws_and_finite_local_depth D L Pm Tp hK T EX hM hR.star_eq).1`. Use `DepthTie.leafDepthLevel_core T (depOf T EX Tp hK) O ι N (numOf D L) hL hR.E_eq hR.σ_eq hR.nn_eq hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.conj (fun j => GlobalTheory.T.depthParams_plusMinusCounts_eq_kappa D L Pm Tp hK (ι j) …` and prove the remaining obligations. Introduce `j`. Establish `h1 : DF (T.Q.Dw (ι j)) ((depOf T EX Tp hK).aL (ι j)) = WeightAlgebra.DF (lR Tp hK (ι j))` using `(GlobalTheory.T.weightExponents_embeddings_degree D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1`.

Establish `h2` using `(GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2`. Simplify using `only [h1, hR.T_eq]`. Conclude with `h2` after adjusting the coercions. Introduce `j`. Establish `h` using `(GlobalTheory.T.degree_weightKappa_le_pageBound D L Pm Tp hK hx hb (ι j) (hR.inR j)).2`.

Rewrite using `[hR.jets_eq_fact, hR.g2_eq]`. Conclude with `⟨h 0, h 1⟩`. Introduce `w _ hw`. Establish `key : ∀ v : HeightOneSpectrum (𝓞 K), plc v = plc w → (plc w : ℝ) - 1 ≤ DepthTie.e2 T.Q.c v`. Introduce `v hv`.

Establish `hc : resCharOf (placeBelow (K` using `T.Q.c.F) v) = plc w := (DepthTie.resChar_below v).trans hv`. Establish `hd : resCharOf (placeBelow (K` using `T.Q.c.F) v) ∣ T.Q.l.M := by`. Rewrite using `[hc, level_M T hM]`. Break down `hw with h | h` into its components or cases. Rewrite using `[h, hR.jets_eq_fact]`.

Conclude with `Dvd.intro _ rfl`. Rewrite using `[h, hR.g2_eq]`. Conclude with `Dvd.intro_left _ rfl`. Establish `h` using `GlobalTheory.T.ramificationIndex_ge_of_resChar_dvd_level _ _ T.Q.l T.Q.c _ hd`. Rewrite `h` using `[hc]`.

Establish `h' : plc w ≤ DepthTie.e2 T.Q.c v + 1` using `by unfold DepthTie.e2; omega`. Establish `h'' : (plc w : ℝ) ≤ (DepthTie.e2 T.Q.c v : ℝ) + 1` using `by exact_mod_cast h'`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨key w rfl, key _ (plc_conjPl w)⟩`.
-/
theorem leafDepthLevel_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthLevel N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hL := (GlobalTheory.T.runDepthData_laws_and_finite_local_depth D L Pm Tp hK T EX hM hR.star_eq).1
  refine DepthTie.leafDepthLevel_core T (depOf T EX Tp hK) O ι N (numOf D L) hL hR.E_eq hR.σ_eq hR.nn_eq hR.T_eq
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.conj (fun j => GlobalTheory.T.depthParams_plusMinusCounts_eq_kappa D L Pm Tp hK (ι j) (hR.inR j)) hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) ?_ ?_ ?_
  · intro j
    have h1 : DF (T.Q.Dw (ι j)) ((depOf T EX Tp hK).aL (ι j)) = WeightAlgebra.DF (lR Tp hK (ι j)) :=
      (GlobalTheory.T.weightExponents_embeddings_degree D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    simp only [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h := (GlobalTheory.T.degree_weightKappa_le_pageBound D L Pm Tp hK hx hb (ι j) (hR.inR j)).2
    rw [hR.jets_eq_fact, hR.g2_eq]
    exact ⟨h 0, h 1⟩
  · intro w _ hw
    have key : ∀ v : HeightOneSpectrum (𝓞 K), plc v = plc w → (plc w : ℝ) - 1 ≤ DepthTie.e2 T.Q.c v := by
      intro v hv
      have hc : resCharOf (placeBelow (K := T.Q.c.F) v) = plc w := (DepthTie.resChar_below v).trans hv
      have hd : resCharOf (placeBelow (K := T.Q.c.F) v) ∣ T.Q.l.M := by
        rw [hc, level_M T hM]
        rcases hw with h | h
        · rw [h, hR.jets_eq_fact]; exact Dvd.intro _ rfl
        · rw [h, hR.g2_eq]; exact Dvd.intro_left _ rfl
      have h := GlobalTheory.T.ramificationIndex_ge_of_resChar_dvd_level _ _ T.Q.l T.Q.c _ hd
      rw [hc] at h
      have h' : plc w ≤ DepthTie.e2 T.Q.c v + 1 := by unfold DepthTie.e2; omega
      have h'' : (plc w : ℝ) ≤ (DepthTie.e2 T.Q.c v : ℝ) + 1 := by exact_mod_cast h'
      linarith
    exact ⟨key w rfl, key _ (plc_conjPl w)⟩

end GlobalTheory.RunDepth
