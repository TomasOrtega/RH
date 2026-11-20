import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedSectionCorrespondenceExistsUniqueNonva
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

/- English proof (translation)
Establish `h1` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ))) (fun τ => τ (H.rt : E) = H.rt0)`. Rewrite `h1` using `[Finset.card_univ, Embeddings.card]`. Establish `h2` using `GlobalTheory.PeriodCoord.card_cmType H`. Rewrite `h2` using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Establish `h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E)`.

Rewrite using `[← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]`. Establish `h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2`. Use linear arithmetic over natural numbers and integers. Establish `h5 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2`. Use linear arithmetic over natural numbers and integers.

Establish `h6` using `Fintype.card_congr e`. Rewrite `h6` using `[Fintype.card_fin, Fintype.card_sigma]`. Rewrite `h6` using `[Fintype.card_fin, Datum.mult]`. Rewrite `h6` using `[Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h5, smul_eq_mul, smul_eq_mul]`. Rewrite using `[h6, mul_add]`.
-/
theorem card_frame_index {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = g := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h5 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h6 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at h6
  simp_rw [Fintype.card_fin, Datum.mult] at h6
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h5, smul_eq_mul, smul_eq_mul] at h6
  rw [h6, mul_add]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c g e S _ _ _ y hpq`. Take `⟨U, hU, hg⟩` from `GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ`. Choose the witnesses or unpack the hypotheses as in `⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Xo.univ.t y.x) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull y.x Xo.univ.t`. Conclude with `⟨_, ⟨m⟩⟩`.

Take `⟨⟨T, rfl, hTg⟩, -⟩` from `GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U t (hU ▸ m)`. Establish `hpos : 1 ≤ Module.finrank ℚ E / 2`. Establish `h1` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Rewrite `h1` using `[Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]`. Establish `h2 : 0 < Module.finrank ℚ (maximalRealSubfield E)` using `Module.finrank_pos`.

Use linear arithmetic over natural numbers and integers. Establish `hgp : 1 ≤ T.g`. Rewrite using `[hTg, hg]`. Conclude with `Nat.mul_pos hpos hpq`. Take `rfl : T.g = g` from `hTg.trans (hg.trans (card_frame_index Dw e))`.

Take `⟨-, h₁, h₂⟩` from `SecTieEx.secTie_exists_unique E H Dw l Xo S y.x T.t m`. Take `⟨th, ht⟩` from `h₁ y.s`. Establish `hne` using `(h₂ th _ ht).2.1 (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo S _ _ y.gen)`. Establish `hB` using `(GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u T.g e y.tan y.eig).1 y.basis`. Take `⟨hl, hb⟩` from `GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo S y.x T.t.G m.φ m.cart`.

Use `choose v hv using fun j => hl _ (y.tan (e j).1 (e j).2)`. Use `⟨⟨T, m, hgp, th, hne, v, (hb _ v).2 ?_⟩, ht, rfl, hv⟩` and prove the remaining obligations. Rewrite using `[funext hv]`. Conclude with `hB`.
-/
theorem exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  intro E _ _ _ H Dw l Xo c g e S _ _ _ y hpq
  obtain ⟨U, hU, hg⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Xo.univ.t y.x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y.x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hgp : 1 ≤ T.g := by
    rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  obtain rfl : T.g = g := hTg.trans (hg.trans (card_frame_index Dw e))
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo S y.x T.t m
  obtain ⟨th, ht⟩ := h₁ y.s
  have hne := (h₂ th _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo S _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u T.g e y.tan y.eig).1 y.basis
  obtain ⟨hl, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo S y.x T.t.G m.φ m.cart
  choose v hv using fun j => hl _ (y.tan (e j).1 (e j).2)
  refine ⟨⟨T, m, hgp, th, hne, v, (hb _ v).2 ?_⟩, ht, rfl, hv⟩
  rw [funext hv]
  exact hB

end GlobalTheory.KeyFourth
