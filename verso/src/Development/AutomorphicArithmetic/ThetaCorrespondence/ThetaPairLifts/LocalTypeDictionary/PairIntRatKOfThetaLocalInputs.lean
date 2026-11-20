import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntegralRatioOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WildAKer

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open GlobalTheory.SumSize.TopInt
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
/- English proof (translation)
Introduce `hP hI hD`. Take `⟨C1, hC1, hPL⟩` from `_root_.UpperTheory.WildA.ker_wild_ramification_map`. Take `⟨C0, hC0, hS⟩` from `UpperTheory.WildA.lossOne C1 hC1`. Take `⟨CF2, hD⟩` from `hD`. Use `⟨CF2, fun CF hCF => ?_⟩` and prove the remaining obligations.

Take `⟨C02, hD⟩` from `hD CF hCF`. Use `⟨max C0 C02, fun ε C hC => ?_⟩` and prove the remaining obligations. Take `⟨x2, hD⟩` from `hD ε C (le_of_max_le_right hC)`. Use `⟨x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩` and prove the remaining obligations. Establish `dict : DictAt ch` using `hD D large₂ he hx Γ Pl0 T A Ks R F hs ch hch hsc hfo`.

Take `⟨S, δ, hL⟩` from `(GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1`. Establish `hgap : ch.sc.cGap = 1`. Establish `e : ch.sc = ⟨1, CF, large₂.sc.b⟩` using `hsc`. Rewrite using `[e]`. Take `⟨S', h, hE, hh⟩` from `hS (G := ch.G) large₂ hs.size hs.host hgap S δ hL`.

Take `⟨l1, l2, l3⟩` from `UpperTheory.WildA.expLoss D S' h _ hE`. Take `⟨-, -, -, -, hm2, -, -, h12⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs.size`. Use `⟨_, ⟨l1, l2, fun s => (l3 s).trans ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hlog : 0 ≤ Real.log large₂.sc.b` using `Real.log_nonneg (by linarith)`. Establish `hsig : 0 ≤ sig ch.G` using `Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`.

Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Establish `hCC : C0 ≤ C` using `le_of_max_le_left hC`. Establish `h1 : C0 ≤ C * D.R.m` using `by nlinarith`. Establish `h2 : (0 : ℝ) ≤ D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b`. Establish `: (0 : ℝ) ≤ large₂.sc.b` using `by linarith`.

Check the signs of the components of the expression. Use `mul_le_mul_of_nonneg_right h1 h2` as an intermediate fact. Unfold `bOne`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `t p hp w hw k d hk hcos hz hPl hdep x y hr a v hv`.

Establish `key` using `hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t p hp k d hk hcos hz hPl x y hr w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv`. Use `inLat_mono key ?_` and prove the remaining obligations. Establish `h1` using `kerLoss_mono ch.G δ C1 large₂.sc.b p.small p.big (primeUnder w) (hdep _ (primeUnder_prime w) (primeUnder_mem w))`. Establish `h2` using `(mul_le_mul_of_nonneg_left h1 hC1.le).trans (hh p hp _ (primeUnder_prime w))`. Establish `h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ)` using `by exact_mod_cast vw_natCast_nonneg w _`.

Establish `h3` using `mul_le_mul_of_nonneg_left h2 h0`. Rewrite using `[mul_assoc]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → GlobalTheory.SumSize.PairInt.PairIntRatK := by
  intro hP hI hD
  obtain ⟨C1, hC1, hPL⟩ := _root_.UpperTheory.WildA.ker_wild_ramification_map
  obtain ⟨C0, hC0, hS⟩ := UpperTheory.WildA.lossOne C1 hC1
  obtain ⟨CF2, hD⟩ := hD
  refine ⟨CF2, fun CF hCF => ?_⟩
  obtain ⟨C02, hD⟩ := hD CF hCF
  refine ⟨max C0 C02, fun ε C hC => ?_⟩
  obtain ⟨x2, hD⟩ := hD ε C (le_of_max_le_right hC)
  refine ⟨x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩
  have dict : DictAt ch := hD D large₂ he hx Γ Pl0 T A Ks R F hs ch hch hsc hfo
  obtain ⟨S, δ, hL⟩ := (GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1
  have hgap : ch.sc.cGap = 1 := by
    have e : ch.sc = ⟨1, CF, large₂.sc.b⟩ := hsc
    rw [e]
  obtain ⟨S', h, hE, hh⟩ := hS (G := ch.G) large₂ hs.size hs.host hgap S δ hL
  obtain ⟨l1, l2, l3⟩ := UpperTheory.WildA.expLoss D S' h _ hE
  obtain ⟨-, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs.size
  refine ⟨_, ⟨l1, l2, fun s => (l3 s).trans ?_⟩, ?_⟩
  · have hlog : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hCC : C0 ≤ C := le_of_max_le_left hC
    have h1 : C0 ≤ C * D.R.m := by nlinarith
    have h2 : (0 : ℝ) ≤ D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have : (0 : ℝ) ≤ large₂.sc.b := by linarith
      positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    unfold bOne
    linarith
  · intro t p hp w hw k d hk hcos hz hPl hdep x y hr a v hv
    have key := hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t p hp k d hk hcos hz hPl x y hr
      w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv
    refine inLat_mono key ?_
    have h1 := kerLoss_mono ch.G δ C1 large₂.sc.b p.small p.big (primeUnder w)
      (hdep _ (primeUnder_prime w) (primeUnder_mem w))
    have h2 := (mul_le_mul_of_nonneg_left h1 hC1.le).trans (hh p hp _ (primeUnder_prime w))
    have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast vw_natCast_nonneg w _
    have h3 := mul_le_mul_of_nonneg_left h2 h0
    rw [mul_assoc]
    linarith
end
