import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Introduce `hD hI hC G A _ _ K N N' ι c Q d h t t' hbi hfin hle hι hsplit hK hnorm hc hQ hidx hex hconj hdc`. Take `⟨-, e1⟩` from `hD G A K N N' ι h t hfin hle hι hsplit hK hnorm`. Take `⟨f2, e2⟩` from `hD G A K N N' ι h t' hfin hle hι hsplit hK hnorm`. Establish `hcomm : ∀ a, t' * ι a = ι ((c ^ d) a) * t'` using `fun a => by`. Rewrite using `[← hconj a]`.

Use `group`. Establish `key` using `hC A (K.comap ι) c Q d (fun v => cellSum K N' h (t' * ι v)) hc hQ hidx hex (by`. Introduce `v hv a`. Use `hI G K N' h (t' * ι a) (ι ((c ^ d) v)) 1 hbi hv K.one_mem (by simp) (by simp)` as an intermediate fact. Use `show cellSum K N' h (t' * ι (v * a)) = cellSum K N' h (t' * ι a)`.

Rewrite using `[← this, map_mul, ← mul_assoc, hcomm v, mul_one, mul_assoc])`. Use the proof step `(by`. Introduce `u hu a`. Use `hI G K N' h (t' * ι a) 1 (ι u) hbi K.one_mem hu (hnorm u) (fun w hw => by simpa using hnorm u⁻¹ w hw)` as an intermediate fact. Use `show cellSum K N' h (t' * ι (a * u)) = cellSum K N' h (t' * ι a)`.

Rewrite using `[← this, map_mul, one_mul, mul_assoc])`. Use `f2`. Rewrite using `[e1, e2, ← key]`. Use `finsum_congr fun y => ?_` and prove the remaining obligations. Take `⟨k₁, hk₁, k₂, hk₂, n1, n2, e⟩` from `hdc y.out`.

Establish `hcc : (c ^ d) ((c ^ (-d)) y.out) = y.out`. Rewrite using `[← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply]`. Rewrite using `[hcomm, map_inv, hcc, map_inv, e, hI G K N' h _ k₁ k₂ hbi hk₁ hk₂ n1 n2]`.
-/
theorem rankOne_of_steps : Descent → CellInv → ChainSum → RankOne := by
  intro hD hI hC G A _ _ K N N' ι c Q d h t t' hbi hfin hle hι hsplit hK hnorm hc hQ hidx hex hconj hdc
  obtain ⟨-, e1⟩ := hD G A K N N' ι h t hfin hle hι hsplit hK hnorm
  obtain ⟨f2, e2⟩ := hD G A K N N' ι h t' hfin hle hι hsplit hK hnorm
  have hcomm : ∀ a, t' * ι a = ι ((c ^ d) a) * t' := fun a => by
    rw [← hconj a]; group
  have key := hC A (K.comap ι) c Q d (fun v => cellSum K N' h (t' * ι v)) hc hQ hidx hex
    (by
      intro v hv a
      have := hI G K N' h (t' * ι a) (ι ((c ^ d) v)) 1 hbi hv K.one_mem (by simp) (by simp)
      show cellSum K N' h (t' * ι (v * a)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, ← mul_assoc, hcomm v, mul_one, mul_assoc])
    (by
      intro u hu a
      have := hI G K N' h (t' * ι a) 1 (ι u) hbi K.one_mem hu (hnorm u)
        (fun w hw => by simpa using hnorm u⁻¹ w hw)
      show cellSum K N' h (t' * ι (a * u)) = cellSum K N' h (t' * ι a)
      rw [← this, map_mul, one_mul, mul_assoc])
    f2
  rw [e1, e2, ← key]
  refine finsum_congr fun y => ?_
  obtain ⟨k₁, hk₁, k₂, hk₂, n1, n2, e⟩ := hdc y.out
  have hcc : (c ^ d) ((c ^ (-d)) y.out) = y.out := by
    rw [← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply]
  rw [hcomm, map_inv, hcc, map_inv, e, hI G K N' h _ k₁ k₂ hbi hk₁ hk₂ n1 n2]

end GlobalTheory.SatakeWeyl
