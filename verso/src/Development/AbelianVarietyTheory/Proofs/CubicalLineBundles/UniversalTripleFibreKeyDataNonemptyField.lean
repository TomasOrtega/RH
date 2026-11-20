import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT

namespace GlobalTheory.LamT

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo K _ x hpq`. Establish `hT : Out.SecTwistSt` using `GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Take `⟨U, hU, hg⟩` from `exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ`. Choose the witnesses or unpack the hypotheses as in `⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp K), Nonempty (SABMap t Xo.univ.t x) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull x Xo.univ.t`.

Conclude with `⟨_, ⟨m⟩⟩`. Take `⟨⟨T, rfl, hTg⟩, -⟩` from `PAT.exists_of_sabMap E H _ _ x U t (hU ▸ m)`. Establish `hpos : 1 ≤ Module.finrank ℚ E / 2`. Establish `h1` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Rewrite `h1` using `[Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]`.

Establish `h2 : 0 < Module.finrank ℚ (maximalRealSubfield E)` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers. Take `⟨b, hb⟩` from `principalPolarisation_exists_unique_section hT T.pol`. Take `⟨a, -, hu⟩` from `hb b`. Take `⟨v, hv⟩` from `KeyPow.exists_isLieBasis T.t.G T.dim`.

Use `⟨⟨T, m, ?_, b, KeyPow.exists_mem_nonzeroLocus T.pol b ?_, v, hv⟩⟩` and prove the remaining obligations. Rewrite using `[hTg, hg]`. Conclude with `Nat.mul_pos hpos hpq`. Assume the negation of the conclusion as `hn push Not at hn`. Conclude with `zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)`.
-/
theorem nonempty_fibKey : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → Nonempty (FibKey Xo K x) := by
  intro E _ _ _ H Dw l Xo K _ x hpq
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨U, hU, hg⟩ := exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp K), Nonempty (SABMap t Xo.univ.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT T.pol
  obtain ⟨a, -, hu⟩ := hb b
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis T.t.G T.dim
  refine ⟨⟨T, m, ?_, b, KeyPow.exists_mem_nonzeroLocus T.pol b ?_, v, hv⟩⟩
  · rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  · by_contra hn
    push Not at hn
    exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

end GlobalTheory.LamT
