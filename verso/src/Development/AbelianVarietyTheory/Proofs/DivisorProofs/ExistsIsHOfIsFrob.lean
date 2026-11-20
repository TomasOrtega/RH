import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehlerStatement
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Introduce `K Kt _ _ p _ _ π F F' hL hF hF'`. Establish `hex : ∀ z, ∃ w, F' z = F z + p * w`. Introduce `z`. Take `⟨w, hw⟩` from `(hL.ker (F' z - F z)).1 (by rw [map_sub, hF, hF', sub_self])`. Conclude with `⟨w, by rw [← hw]; ring⟩`.

Establish `huniq : ∀ z w w', F' z = F z + p * w → F' z = F z + p * w' → π w = π w'`. Introduce `z w w' h1 h2`. Establish `h3 : (p : Kt) * (w - w') = 0` using `by rw [mul_sub]; linear_combination h2 - h1`. Establish `h4` using `(hL.ann (w - w')).1 h3`. Rewrite `h4` using `[map_sub]`.

Conclude with `sub_eq_zero.1 h4`. Set `g : Kt → K` to `fun z => π (Classical.choose (hex z))`. Establish `hg : ∀ z w, F' z = F z + p * w → g z = π w` using `fun z w hw => huniq z _ w (Classical.choose_spec (hex z)) hw`. Establish `hgadd : ∀ z z', g (z + z') = g z + g z'`. Introduce `z z'`.

Take `⟨w, h1⟩` from `hex z`. Take `⟨w', h2⟩` from `hex z'`. Rewrite using `[hg z w h1, hg z' w' h2, hg (z + z') (w + w') (by rw [map_add, map_add, h1, h2]; ring), map_add]`. Establish `hgp : ∀ y, g (p * y) = 0`. Introduce `y`.

Take `⟨w, h1⟩` from `hex y`. Rewrite using `[hg (p * y) (p * w) (by rw [map_mul, map_mul, map_natCast, map_natCast, h1]; ring), map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]`. Establish `hgmul : ∀ z z', g (z * z') = π z' ^ p * g z + π z ^ p * g z'`. Introduce `z z'`. Take `⟨w, h1⟩` from `hex z`.

Take `⟨w', h2⟩` from `hex z'`. Rewrite using `[hg z w h1, hg z' w' h2, hg (z * z') (w * F z' + F z * w' + p * w * w') (by rw [map_mul, map_mul, h1, h2]; ring)]`. Simplify using `only [map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]`. Rewrite using `[hF z, hF z']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hwd : ∀ z z', π z = π z' → g z = g z'`. Introduce `z z' hzz`. Take `⟨y, hy⟩` from `(hL.ker (z - z')).1 (by rw [map_sub, hzz, sub_self])`. Establish `: z = z' + p * y` using `by rw [← hy]; ring`. Rewrite using `[this, hgadd, hgp, add_zero]`.

Set `φ : K →+ K` to `AddMonoidHom.mk' (fun x => g (Function.surjInv hL.surj x)) (by`. Introduce `a b`. Use `show g _ = g _ + g _`. Rewrite using `[← hgadd]`. Apply `hwd` to reduce the goal to its premises.

Rewrite using `[map_add, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])`. Establish `hφ : ∀ z, φ (π z) = g z`. Introduce `z`. Use `show g _ = g _`. Conclude with `hwd _ _ (Function.surjInv_eq hL.surj _)`.

Take `⟨f, hfs, hfD⟩` from `GlobalTheory.T.frobeniusDerivation_factors_through_kaehler (M := K) p φ (by`. Introduce `a b`. Take `⟨z, rfl⟩` from `hL.surj a`. Take `⟨z', rfl⟩` from `hL.surj b`. Rewrite using `[← map_mul, hφ, hφ, hφ, hgmul, smul_eq_mul, smul_eq_mul]`.

Use the proof step `ring)`. Use `⟨f, fun c v => by rw [hfs, smul_eq_mul], fun z w hzw => ?_⟩` and prove the remaining obligations. Rewrite using `[hfD, hφ, hg z w hzw]`.
-/
theorem exists_isH_of_isFrob : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F F' : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → IsFrob p π F' →
    ∃ h, IsH p π F F' h := by
  intro K Kt _ _ p _ _ π F F' hL hF hF'
  have hex : ∀ z, ∃ w, F' z = F z + p * w := by
    intro z
    obtain ⟨w, hw⟩ := (hL.ker (F' z - F z)).1 (by rw [map_sub, hF, hF', sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have huniq : ∀ z w w', F' z = F z + p * w → F' z = F z + p * w' → π w = π w' := by
    intro z w w' h1 h2
    have h3 : (p : Kt) * (w - w') = 0 := by rw [mul_sub]; linear_combination h2 - h1
    have h4 := (hL.ann (w - w')).1 h3
    rw [map_sub] at h4
    exact sub_eq_zero.1 h4
  let g : Kt → K := fun z => π (Classical.choose (hex z))
  have hg : ∀ z w, F' z = F z + p * w → g z = π w := fun z w hw =>
    huniq z _ w (Classical.choose_spec (hex z)) hw
  have hgadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z + z') (w + w') (by rw [map_add, map_add, h1, h2]; ring), map_add]
  have hgp : ∀ y, g (p * y) = 0 := by
    intro y
    obtain ⟨w, h1⟩ := hex y
    rw [hg (p * y) (p * w) (by rw [map_mul, map_mul, map_natCast, map_natCast, h1]; ring), map_mul,
      map_natCast, CharP.cast_eq_zero, zero_mul]
  have hgmul : ∀ z z', g (z * z') = π z' ^ p * g z + π z ^ p * g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z * z') (w * F z' + F z * w' + p * w * w')
      (by rw [map_mul, map_mul, h1, h2]; ring)]
    simp only [map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
    rw [hF z, hF z']
    ring
  have hwd : ∀ z z', π z = π z' → g z = g z' := by
    intro z z' hzz
    obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, hzz, sub_self])
    have : z = z' + p * y := by rw [← hy]; ring
    rw [this, hgadd, hgp, add_zero]
  let φ : K →+ K := AddMonoidHom.mk' (fun x => g (Function.surjInv hL.surj x)) (by
    intro a b
    show g _ = g _ + g _
    rw [← hgadd]
    apply hwd
    rw [map_add, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])
  have hφ : ∀ z, φ (π z) = g z := by
    intro z
    show g _ = g _
    exact hwd _ _ (Function.surjInv_eq hL.surj _)
  obtain ⟨f, hfs, hfD⟩ := GlobalTheory.T.frobeniusDerivation_factors_through_kaehler (M := K) p φ (by
    intro a b
    obtain ⟨z, rfl⟩ := hL.surj a
    obtain ⟨z', rfl⟩ := hL.surj b
    rw [← map_mul, hφ, hφ, hφ, hgmul, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨f, fun c v => by rw [hfs, smul_eq_mul], fun z w hzw => ?_⟩
  rw [hfD, hφ, hg z w hzw]

end GlobalTheory.DI
