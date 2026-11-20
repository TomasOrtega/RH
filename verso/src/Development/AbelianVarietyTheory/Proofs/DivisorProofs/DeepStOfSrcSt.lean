import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanGeTransferDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatumFieldContainmentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalSystemOfSiegelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnStabilizerTrivial

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.CovHt.DeepOfSrc

open GlobalTheory.ShFam

def SrcAt (C : ℝ) : Prop := ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ),
  N - j < j → j < N → 2 < D.R.f * (N - 1) → κ.primes.card ≤ 15 →
    MeanAll (Xo := s.Xo) (c := κ.c) (r := N) (fun σ => GlobalTheory.ThetaDictCompare.toU (s.U σ)) (xiR D) (ell D) C

/- English proof (translation)
Take `⟨κ, rfl⟩` from `(exists_lv_iff A l).2 ⟨hg, hL⟩`. Establish `hX` using `fun l => GlobalTheory.Moduli.moduli_scheme_exists _ A.H Dw l (by omega)`. Take `⟨X, hXo⟩ : ∃ X : ∀ l : Level A.H, Moduli Dw l, X κ.l = Xo` from `⟨Function.update (fun l => (hX l).some) κ.l Xo, Function.update_self ..⟩`. Substitute `hXo` using the available equality. Take `⟨s, ⟨t⟩⟩` from `hx _ A.H Dw (by omega) X`.

Set `S : Sig A N Dw.p` to `⟨Dw, rfl, hN, by omega, X, s, t⟩`. Take `⟨z⟩` from `nonempty_src_of_sig S κ`. Conclude with `⟨κ.c, κ.F_eq, z.unif, hS D A N Dw.p S κ z (by omega) (by omega) hf hc⟩`.
-/
theorem mean_of_large {C : ℝ} (hS : SrcAt C) (hx : SysExSt) (D : D7) (A : Amb D) (Dw : Datum A.H) (l : Level A.H)
    (Xo : Moduli Dw l) (N : ℕ) (hN : Dw.p + Dw.q = N) (hq : Dw.q < Dw.p) (hq0 : 0 < Dw.q) (hf : 2 < D.R.f * (N - 1))
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hL : IsLargeFor A l.M')
    (hc : l.M'.primeFactors.card ≤ 15) :
    ∃ c' : Coeff l, c'.F = fieldLL D ∧ ∃ U' : UnfFam Xo c' N (-D.host.xi0),
      MeanAll (fun σ => GlobalTheory.ThetaDictCompare.toU (U'.U σ)) (xiR D) (ell D) C := by
  obtain ⟨κ, rfl⟩ := (exists_lv_iff A l).2 ⟨hg, hL⟩
  have hX := fun l => GlobalTheory.Moduli.moduli_scheme_exists _ A.H Dw l (by omega)
  obtain ⟨X, hXo⟩ : ∃ X : ∀ l : Level A.H, Moduli Dw l, X κ.l = Xo :=
    ⟨Function.update (fun l => (hX l).some) κ.l Xo, Function.update_self ..⟩
  subst hXo
  obtain ⟨s, ⟨t⟩⟩ := hx _ A.H Dw (by omega) X
  let S : Sig A N Dw.p := ⟨Dw, rfl, hN, by omega, X, s, t⟩
  obtain ⟨z⟩ := nonempty_src_of_sig S κ
  exact ⟨κ.c, κ.F_eq, z.unif, hS D A N Dw.p S κ z (by omega) (by omega) hf hc⟩

/- English proof (translation)
Take `⟨H, h1, h2, h3⟩` from `A`. Establish `key` using `mean_of_large hS hx D'`. Consider the cases of `D`. Consider the cases of `D'`. Consider the cases of `eR`.

Consider the cases of `e`. Conclude with `key ⟨H, h1, h2, h3⟩ Dw l Xo N hN hq hq0 hf hg ⟨hz, hL⟩ hc`.
-/
theorem mean_of_large' {C : ℝ} (hS : SrcAt C) (hx : SysExSt) (D D' : D7) (eR : D'.R = D.R) (e : HEq D'.host D.host)
    (A : Amb D) (Dw : Datum A.H) (l : Level A.H)
    (Xo : Moduli Dw l) (N : ℕ) (hN : Dw.p + Dw.q = N) (hq : Dw.q < Dw.p) (hq0 : 0 < Dw.q) (hf : 2 < D.R.f * (N - 1))
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hz : zeta l.M' ∈ fieldLL D') (hL : GlobalTheory.CompRat.CurveOver A.H (fieldLL D') l.M')
    (hc : l.M'.primeFactors.card ≤ 15) :
    ∃ c' : Coeff l, c'.F = fieldLL D' ∧ ∃ U' : UnfFam Xo c' N (-D.host.xi0),
      MeanAll (fun σ => GlobalTheory.ThetaDictCompare.toU (U'.U σ)) (xiR D) (ell D) C := by
  obtain ⟨H, h1, h2, h3⟩ := A
  have key := mean_of_large hS hx D'
  cases D
  cases D'
  cases eR
  cases e
  exact key ⟨H, h1, h2, h3⟩ Dw l Xo N hN hq hq0 hf hg ⟨hz, hL⟩ hc

/- English proof (translation)
Establish `hM0 : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `key : ∀ c : ℕ, c.Prime → c ∣ l.M → c ≠ p → 3 ≤ l.M / p ^ l.M.factorization p` using `fun c hc hd hn => by`. Establish `h3 : 3 ≤ c`. Establish `h2` using `hc.two_le`. Take `⟨t, ht⟩` from `l.odd.of_dvd_nat hd`.

Use linear arithmetic over natural numbers and integers. Conclude with `h3.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd fun h => hn ((Nat.prime_dvd_prime_iff_eq hp hc).1 h).symm))`. Distinguish the cases in `h : a = p`. Conclude with `key b hb h2 fun h' => hab (h.trans h'.symm)`. Conclude with `key a ha h1 h`.
-/
theorem goodAt_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H)
    {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) (h1 : a ∣ l.M) (h2 : b ∣ l.M) (p : ℕ) (hp : p.Prime) :
    l.GoodAt p := by
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have key : ∀ c : ℕ, c.Prime → c ∣ l.M → c ≠ p → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn => by
    have h3 : 3 ≤ c := by
      have h2 := hc.two_le
      obtain ⟨t, ht⟩ := l.odd.of_dvd_nat hd
      omega
    exact h3.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd
      fun h => hn ((Nat.prime_dvd_prime_iff_eq hp hc).1 h).symm))
  by_cases h : a = p
  · exact key b hb h2 fun h' => hab (h.trans h'.symm)
  · exact key a ha h1 h

/- English proof (translation)
Introduce and unpack `- hH ⟨C, hC, hS⟩`. Use `⟨C, hC, fun D T hT j hj1 hjm Y e o hY hc u g hg => ?_⟩` and prove the remaining obligations. Establish `hQ` using `hT.pins`. Establish `hx : SysExSt` using `GlobalTheory.T.toroidal_system_of_siegel hH.sieg hH.fan`. Establish `hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd` using `by rw [hY.lev.1.2.1, hQ.2.1.1]`.

Establish `hM0 : 0 < Y.d.l₂.M'` using `Nat.lcm_pos (lt_of_lt_of_le (by norm_num) Y.d.l₂.three_le) Y.d.l₂.A_pos`. Take `⟨F₀, hfin, hF₀⟩` from `GlobalTheory.CurveField.exists_curveOver T.Q.H hM0`. Use `haveI := Y.d.c₂.fin`. Take `⟨D', eR, eH, hK⟩` from `GlobalTheory.T.exists_datum_field_containment D (Y.d.c₂.F ⊔ F₀) inferInstance`. Establish `h1 : Y.d.c₂.F ≤ fieldLL D'` using `le_sup_left.trans hK`.

Establish `h2 : F₀ ≤ fieldLL D'` using `le_sup_right.trans hK`. Take `⟨hp, hq, -⟩` from `hQ.2.2.2 j ⟨hj1, hjm.le⟩`. Establish `a1` using `D.R.two_le_m`. Establish `a2` using `D.R.m_add_three_le_k`. Establish `a3 : 2 ≤ D.R.f` using `a1.trans D.R.m_le_f`.

Simplify using `only [Ranks.sigW] at hp hq`. Establish `hr : 5 ≤ D.R.r - 1` using `by unfold Ranks.r; omega`. Take `⟨c', hc', U', hU⟩` from `mean_of_large' hS hx D D' eR eH ⟨T.Q.H, hQ.1.1, hQ.1.2.1, hQ.1.2.2.1⟩ (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ D.R.r (by unfold Ranks.r; dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by nlinarith) (goodAt_of_dvd _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne (hM ▸ (dvd_ …`. Establish `hE : 2 < Module.finrank ℚ D.host.E / 2`. Establish `h4 : 2 ^ 2 ≤ 2 ^ D.R.e` using `Nat.pow_le_pow_right (by norm_num) D.host.two_le_e`.

Establish `h5 : 2 ^ D.R.e ≤ D.R.ord` using `Nat.le_of_dvd D.R.toFrame.ord_pos D.R.toFrame.two_pow_dvd_ord`. Rewrite using `[GlobalTheory.Proof.ColumnStabilizerTrivial.finrank_E]`. Unfold `Ranks.f Ranks.n`. Use linear arithmetic over natural numbers and integers. Conclude with `GlobalTheory.T.mean_ge_transfer_dictionary D T.toCore j Y e o hY hE c' (hc' ▸ h1) U' u _ _ hg.2.1 (hU u g hg)`.
-/
theorem deepSt_of_srcSt : Hypotheses2 → HypothesesH → SrcSt → DeepSt := by
  rintro - hH ⟨C, hC, hS⟩
  refine ⟨C, hC, fun D T hT j hj1 hjm Y e o hY hc u g hg => ?_⟩
  have hQ := hT.pins
  have hx : SysExSt := GlobalTheory.T.toroidal_system_of_siegel hH.sieg hH.fan
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hQ.2.1.1]
  have hM0 : 0 < Y.d.l₂.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) Y.d.l₂.three_le) Y.d.l₂.A_pos
  obtain ⟨F₀, hfin, hF₀⟩ := GlobalTheory.CurveField.exists_curveOver T.Q.H hM0
  haveI := Y.d.c₂.fin
  obtain ⟨D', eR, eH, hK⟩ := GlobalTheory.T.exists_datum_field_containment D (Y.d.c₂.F ⊔ F₀) inferInstance
  have h1 : Y.d.c₂.F ≤ fieldLL D' := le_sup_left.trans hK
  have h2 : F₀ ≤ fieldLL D' := le_sup_right.trans hK
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j ⟨hj1, hjm.le⟩
  have a1 := D.R.two_le_m
  have a2 := D.R.m_add_three_le_k
  have a3 : 2 ≤ D.R.f := a1.trans D.R.m_le_f
  simp only [Ranks.sigW] at hp hq
  have hr : 5 ≤ D.R.r - 1 := by unfold Ranks.r; omega
  obtain ⟨c', hc', U', hU⟩ := mean_of_large' hS hx D D' eR eH ⟨T.Q.H, hQ.1.1, hQ.1.2.1, hQ.1.2.2.1⟩ (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂
    D.R.r (by unfold Ranks.r; dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by nlinarith)
    (goodAt_of_dvd _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
      (hM ▸ (dvd_mul_right _ _).mul_right _) (hM ▸ (dvd_mul_left _ _).mul_right _))
    (h1 Y.d.c₂.zeta_mem) (fun τ hτ => hF₀ τ fun x hx => hτ x (h2 hx)) hc
  have hE : 2 < Module.finrank ℚ D.host.E / 2 := by
    have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) D.host.two_le_e
    have h5 : 2 ^ D.R.e ≤ D.R.ord :=
      Nat.le_of_dvd D.R.toFrame.ord_pos D.R.toFrame.two_pow_dvd_ord
    rw [GlobalTheory.Proof.ColumnStabilizerTrivial.finrank_E]
    unfold Ranks.f Ranks.n
    omega
  exact GlobalTheory.T.mean_ge_transfer_dictionary D T.toCore j Y e o hY hE c' (hc' ▸ h1) U' u _ _ hg.2.1 (hU u g hg)

end GlobalTheory.CovHt.DeepOfSrc
