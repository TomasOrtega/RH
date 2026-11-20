import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatakeBound

/- English proof (translation)
Introduce `h10 h11 h11b h12 g1 g2 g3 g4 E _ _ _ a π hU w B hB α hα`. Take `⟨L, rfl⟩ : ∃ L : List ℂˣ, (L : Multiset ℂˣ) = B` from `⟨B.toList, Multiset.coe_toList B⟩`. Establish `hcard : L.length = a` using `by simpa using hB.card`. Substitute `hcard` using the available equality. Establish `hBz : (L : Multiset ℂˣ) = Finset.univ.val.map L.get` using `by rw [Fin.univ_val_map, List.ofFn_get]`.

Take `⟨i, rfl⟩ : ∃ i, L.get i = α` from `List.mem_iff_get.1 (Multiset.mem_coe.1 hα)`. Establish `ha : 1 ≤ L.length` using `Fin.pos i`. Proceed by induction on `π using Quotient.inductionOn with | _ π => ?_`. Use `set z := L.get with hz`. Set `F` to `w.adicCompletion E`.

Use `letI : MeasurableSpace F := borel F`. Use `haveI : BorelSpace F := ⟨rfl⟩`. Establish `hB' : HasSatGL w (π.locRep w) (Finset.univ.val.map z)` using `by rw [← hBz]; exact hB`. Take `⟨ψ, hψ, l, hl0, hW⟩` from `g4 E L.length ha π w`. Take `⟨v, g, hv, hlv⟩` from `g2 E L.length π w _ hB' l hl0`.

Take `⟨Bf, hBf⟩` from `g1 E L.length π hU w`. Establish `hs` using `g3 E L.length π w`. Take `⟨hq, h12'⟩` from `h12 E w`. Establish `hH : Heig (π.locRep w) v z` using `h12' L.length π.V (π.locRep w) v z hv`. Establish `hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ)` using `by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w`.

Establish `hpair` using `h11b L.length z (h11 F L.length π.V (π.locRep w) Bf hBf v z hv.1 hH)`. Establish `hup : ∀ j, ‖(z j : ℂ)‖ < Real.sqrt (Ideal.absNorm w.asIdeal : ℝ)`. Introduce `j`. Break down `Nat.lt_or_ge 1 L.length with h2 | h1` into its components or cases. Use `h10 F Measure.addHaar ψ hψ L.length π.V (π.locRep w) hs h2 l Bf hW hBf v z hH ⟨g, hlv⟩ j` as an intermediate fact.

Rewrite `this` using `[hq]`. Then use the resulting hypothesis. Take `⟨k, hk⟩` from `hpair j`. Establish `hkj : k = j` using `Fin.ext (by have := k.2; have := j.2; omega)`. Substitute `hkj` using the available equality. Establish `h0 : ‖(z k : ℂ)‖ = 1`.

Establish `h00 : 0 ≤ ‖(z k : ℂ)‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[h0, Real.lt_sqrt zero_le_one]`. Simplify using `using hq1`. Take `⟨k, hk⟩` from `hpair i`.

Establish `hkpos : 0 < ‖(z k : ℂ)‖` using `norm_pos_iff.2 (Units.ne_zero _)`. Establish `hi : ‖(z i : ℂ)‖ = ‖(z k : ℂ)‖⁻¹` using `eq_inv_of_mul_eq_one_right hk`. Establish `hsq : (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (Ideal.absNorm w.asIdeal : ℝ)` using `(Real.sqrt_eq_rpow _).symm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_neg (by positivity), hsq, hi]`.

Conclude with `inv_strictAnti₀ hkpos (hup k)`. Rewrite using `[hsq]`. Conclude with `hup i`.
-/
theorem jacquetShalikaBound_of_steps : ParameterUpperBound → liftZP_unit → ParameterAbsoluteValues → lift_levelP_alt₂ → G1 → G2 → G3 → G4 → GlobalTheory.Published.JacquetShalikaBound := by
  intro h10 h11 h11b h12 g1 g2 g3 g4 E _ _ _ a π hU w B hB α hα
  obtain ⟨L, rfl⟩ : ∃ L : List ℂˣ, (L : Multiset ℂˣ) = B := ⟨B.toList, Multiset.coe_toList B⟩
  have hcard : L.length = a := by simpa using hB.card
  subst hcard
  have hBz : (L : Multiset ℂˣ) = Finset.univ.val.map L.get := by rw [Fin.univ_val_map, List.ofFn_get]
  obtain ⟨i, rfl⟩ : ∃ i, L.get i = α := List.mem_iff_get.1 (Multiset.mem_coe.1 hα)
  have ha : 1 ≤ L.length := Fin.pos i
  induction π using Quotient.inductionOn with | _ π => ?_
  set z := L.get with hz
  let F := w.adicCompletion E
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  have hB' : HasSatGL w (π.locRep w) (Finset.univ.val.map z) := by rw [← hBz]; exact hB
  obtain ⟨ψ, hψ, l, hl0, hW⟩ := g4 E L.length ha π w
  obtain ⟨v, g, hv, hlv⟩ := g2 E L.length π w _ hB' l hl0
  obtain ⟨Bf, hBf⟩ := g1 E L.length π hU w
  have hs := g3 E L.length π w
  obtain ⟨hq, h12'⟩ := h12 E w
  have hH : Heig (π.locRep w) v z := h12' L.length π.V (π.locRep w) v z hv
  have hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hpair := h11b L.length z (h11 F L.length π.V (π.locRep w) Bf hBf v z hv.1 hH)
  have hup : ∀ j, ‖(z j : ℂ)‖ < Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) := by
    intro j
    rcases Nat.lt_or_ge 1 L.length with h2 | h1
    · have := h10 F Measure.addHaar ψ hψ L.length π.V (π.locRep w) hs h2 l Bf hW hBf v z hH ⟨g, hlv⟩ j
      rwa [hq] at this
    · obtain ⟨k, hk⟩ := hpair j
      have hkj : k = j := Fin.ext (by have := k.2; have := j.2; omega)
      subst hkj
      have h0 : ‖(z k : ℂ)‖ = 1 := by
        have h00 : 0 ≤ ‖(z k : ℂ)‖ := norm_nonneg _
        nlinarith
      rw [h0, Real.lt_sqrt zero_le_one]
      simpa using hq1
  obtain ⟨k, hk⟩ := hpair i
  have hkpos : 0 < ‖(z k : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hi : ‖(z i : ℂ)‖ = ‖(z k : ℂ)‖⁻¹ := eq_inv_of_mul_eq_one_right hk
  have hsq : (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) :=
    (Real.sqrt_eq_rpow _).symm
  refine ⟨?_, ?_⟩
  · rw [Real.rpow_neg (by positivity), hsq, hi]
    exact inv_strictAnti₀ hkpos (hup k)
  · rw [hsq]; exact hup i

end GlobalTheory.CompanionTheory.SatakeBound

end
