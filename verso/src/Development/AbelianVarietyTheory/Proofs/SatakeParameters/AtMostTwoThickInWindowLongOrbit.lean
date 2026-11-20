import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.LongWindow

/- English proof (translation)
Unfold `Thick Host.thickPlaces at hg`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, e⟩ : ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by`. Simplify `hg` using `[Finset.mem_image]`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `e2 : (plc g).2 = g.2` using `UpperTheory.KStar.Words.placeOf_snd g`.

Rewrite using `[← e2, ← e]`. Both sides reduce to the same expression.
-/
theorem thick_inTranslate {R : Ranks} (H : Host R) (g : R.GG) (hg : Thick H g) :
    R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv g.2) := by
  unfold Thick Host.thickPlaces at hg
  obtain ⟨s, hs, e⟩ : ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    simpa [Finset.mem_image] using hg
  refine ⟨s, hs, ?_⟩
  have e2 : (plc g).2 = g.2 := UpperTheory.KStar.Words.placeOf_snd g
  rw [← e2, ← e]
  rfl

/- English proof (translation)
Unfold `letter`. Rewrite using `[UpperTheory.KStar.Words.pow_val_add, natCast_zsmul]`. Both sides reduce to the same expression.
-/
theorem letter_snd {fr : Formalism.HC.Frame} (τ φ : fr.GG) (i : ZMod (orderOf φ)) (k : ℕ) :
    fr.iotaInv (letter τ φ (i + k)).2 = fr.iotaInv τ.2 + (((i.val + k : ℕ) : ℤ)) • fr.iotaInv φ.2 := by
  unfold letter
  rw [UpperTheory.KStar.Words.pow_val_add, natCast_zsmul]
  rfl

open Classical in
/- English proof (translation)
Introduce `R H τ φ hord i a b c hab hbc hcL ⟨ha, hb, hc⟩`. Establish `hO` using `((R.toFrame.hostThickOrbit H.T2 H.second_set_range H.second_set_no_relation H.u0 (R.iotaInv τ.2) (R.iotaInv φ.2)).1 (by rw [R.toFrame.addOrderOf_iotaInv]; exact hord) (i.val : ℤ))`. Establish `mem : ∀ k : ℕ, k < H.Lw → Thick H (letter τ φ (i + k)) → ((i.val + k : ℕ) : ℤ) ∈ (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2))`. Introduce `k hk ht`. Rewrite using `[Finset.mem_filter, Finset.mem_Ico]`.

Use `⟨⟨by push_cast; omega, by push_cast; omega⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← letter_snd]`. Conclude with `thick_inTranslate H _ ht`. Establish `hsub : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ) ⊆ (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2))`. Introduce `x hx`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `mem a (by omega) ha`. Conclude with `mem b (by omega) hb`. Conclude with `mem c hcL hc`.

Establish `h3 : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ).card = 3`. Rewrite using `[Finset.card_insert_of_notMem, Finset.card_pair]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_insert, Finset.mem_singleton]`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Use `Finset.card_le_card hsub` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem main : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 →
    WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  intro R H τ φ hord i a b c hab hbc hcL ⟨ha, hb, hc⟩
  have hO := ((R.toFrame.hostThickOrbit H.T2 H.second_set_range H.second_set_no_relation H.u0 (R.iotaInv τ.2) (R.iotaInv φ.2)).1
    (by rw [R.toFrame.addOrderOf_iotaInv]; exact hord) (i.val : ℤ))
  have mem : ∀ k : ℕ, k < H.Lw → Thick H (letter τ φ (i + k)) →
      ((i.val + k : ℕ) : ℤ) ∈ (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro k hk ht
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by push_cast; omega, by push_cast; omega⟩, ?_⟩
    rw [← letter_snd]
    exact thick_inTranslate H _ ht
  have hsub : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ) ⊆
      (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem a (by omega) ha
    · exact mem b (by omega) hb
    · exact mem c hcL hc
  have h3 : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push_cast; omega
  have := Finset.card_le_card hsub
  omega

end GlobalTheory.HTW.LongWindow
