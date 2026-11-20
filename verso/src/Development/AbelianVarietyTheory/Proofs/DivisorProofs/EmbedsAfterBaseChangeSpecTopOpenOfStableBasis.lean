import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat.EmbedsBC
/- English proof (translation)
Introduce `Rg _ B _ M k mB bB hAb hM hVA hBC`. Establish `: UniversallyClosed B.hom`. Use `hAb.proper` as an intermediate fact. Use `infer_instance`. Set `x : Sp Rg ⟶ (topS Rg).left` to `(Sp Rg).topIso.inv`.

Establish `hx : IsIso x` using `inferInstanceAs (IsIso (Sp Rg).topIso.inv)`. Use `choose b' hb' using fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_isPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i)`. Use `⟨x, b', hx, hb', ?_⟩` and prove the remaining obligations. Establish `hsp` using `(hBC Rg x b' hb').2`. Conclude with `GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) x b' hsp`.
-/
theorem embeds_bc : ∀ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k : ℕ) {mB : ℕ} (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → VeryAmpleAt B M k → IsBCBasis B M k bB → ∃ (x : Sp Rg ⟶ (topS Rg).left) (b' : Fin mB → LB.Sec (LPow B M (k : ℤ) (baseAt x))), IsIso x ∧ (∀ i, IsPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i) (b' i)) ∧ GlobalTheory.AmpleSpan.EmbedsBy (fst (baseAt x) B).left b' := by
  intro Rg _ B _ M k mB bB hAb hM hVA hBC
  have : UniversallyClosed B.hom := by
    have := hAb.proper
    infer_instance
  let x : Sp Rg ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  have hx : IsIso x := inferInstanceAs (IsIso (Sp Rg).topIso.inv)
  choose b' hb' using fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_isPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i)
  refine ⟨x, b', hx, hb', ?_⟩
  have hsp := (hBC Rg x b' hb').2
  exact GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) x b' hsp
end GlobalTheory.HomFixMat.EmbedsBC
