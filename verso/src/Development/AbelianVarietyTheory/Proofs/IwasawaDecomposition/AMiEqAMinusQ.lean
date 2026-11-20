import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarmonicCoefficientMapAtWeights

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RecordWeightVec

/- English proof (translation)
Establish `hi` using `i.2`. Establish `h1 : DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n`. Unfold `DV.sigPar Formalism.L2.NTheta.lamAt`. Both sides reduce to the same expression. Establish `h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i`.

Unfold `DV.eQ`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression. Rewrite using `[GlobalTheory.CoefMapRecord.aPl_cast D i τ n hn, DV.aPlusQ_eq, h1, h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aPl_eq_aPlusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) = DV.aPlusQ D ((i : ℕ) + 1) τ n := by
  have hi := i.2
  have h1 : DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n := by
    unfold DV.sigPar Formalism.L2.NTheta.lamAt
    rfl
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aPl_cast D i τ n hn, DV.aPlusQ_eq, h1, h2]
  push_cast
  ring

/- English proof (translation)
Establish `hi` using `i.2`. Establish `h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i`. Unfold `DV.eQ`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression.

Rewrite using `[GlobalTheory.CoefMapRecord.aMi_cast D i τ q n c hq hn, DV.aMinusQ, dif_pos (by omega), h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aMi_eq_aMinusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (q n c : ℕ) (hq : i + 1 + q = D.R.m)
    (hn : n + c + 1 = q) : (aMi D i (D.R.k + i) q τ n : ℚ) = DV.aMinusQ D ((i : ℕ) + 1) τ c := by
  have hi := i.2
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dif_pos ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aMi_cast D i τ q n c hq hn, DV.aMinusQ, dif_pos (by omega), h2]
  ring

/- English proof (translation)
Introduce `D hK i`. Establish `hi` using `i.2`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1)` using `fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _`. Establish `hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i`.

Simplify using `only [Ranks.sigW]`. Use linear arithmetic over natural numbers and integers. Establish `hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m`. Simplify using `only [Ranks.sigW]`. Use linear arithmetic over natural numbers and integers.

Use `⟨rfl, Formalism.L2.Geo.wtOf_eq_kapW _ (fun τ a => ?_) (fun τ c => ?_) rfl⟩` and prove the remaining obligations. Establish `h` using `(hK _ (inR i).1 (inR i).2 τ).1 a`. Establish `h'` using `aPl_eq_aPlusQ D i τ a (hp ▸ a.2)`. Rewrite using `[(kapIs_kapTop D i τ).1 a, hs τ]`. Rewrite `h'` using `[← h, ← hp]`.

Conclude with `h'` after adjusting the coercions. Establish `h` using `(hK _ (inR i).1 (inR i).2 τ).2 (Fin.rev c)`. Establish `hc` using `c.2`. Establish `h'` using `aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)`. Rewrite using `[(kapIs_kapTop D i τ).2.1 c, hs τ]`.

Rewrite `h'` using `[← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h]`. Conclude with `h'` after adjusting the coercions.
-/
theorem wtOf_kapTop : ∀ D : D7, DV.KapDef D → ∀ i : Fin D.R.m,
    (kapTop D i).n = D.R.nV ∧ Formalism.L2.Geo.wtOf (kapTop D i) = DV.kapW D ((i : ℕ) + 1) := by
  intro D hK i
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ =>
    D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  refine ⟨rfl, Formalism.L2.Geo.wtOf_eq_kapW _ (fun τ a => ?_) (fun τ c => ?_) rfl⟩
  · have h := (hK _ (inR i).1 (inR i).2 τ).1 a
    have h' := aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    rw [(kapIs_kapTop D i τ).1 a, hs τ]
    rw [← h, ← hp] at h'
    exact_mod_cast h'
  · have h := (hK _ (inR i).1 (inR i).2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    rw [(kapIs_kapTop D i τ).2.1 c, hs τ]
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h] at h'
    exact_mod_cast h'

end GlobalTheory.RecordWeightVec
