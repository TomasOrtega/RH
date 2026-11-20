import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

/- English proof (translation)
Introduce `b L`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr T`. Express the relevant statement in the definitionally equal form `T.pdPow r.toNat = ⊤`. Rewrite using `[Int.toNat_of_nonpos hr]`.

Conclude with `T.pdPow_zero`. Introduce `T`. Express the relevant statement in the definitionally equal form `T.pdPow (1 : ℤ).toNat = T.J`. Conclude with `le_antisymm (dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one`. Introduce `r r' h T`.

Conclude with `T.pdPow_anti (Int.toNat_le_toNat h)`. Introduce `r r' T x y hx hy`. Establish `hx' : (show T.B from x) ∈ pdP T.δ r`. Establish `: (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat)` using `hx`. Rewrite `this` using `[Int.toNat_natCast]`.

Conclude with `this`. Establish `hy' : (show T.B from y) ∈ pdP T.δ r'`. Establish `: (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat)` using `hy`. Rewrite `this` using `[Int.toNat_natCast]`. Conclude with `this`.

Establish `h` using `dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')`. Express the relevant statement in the definitionally equal form `_ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)`. Rewrite using `[Int.toNat_natCast]`. Conclude with `h`. Introduce `k T x hx`.

Express the relevant statement in the definitionally equal form `_ ∈ T.pdPow ((k : ℤ).toNat)`. Rewrite using `[Int.toNat_natCast]`. Conclude with `dpow_mem_pdP T.δ k hx`.
-/
theorem isFil_thFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  intro b L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.pdPow_zero
  · intro T
    change T.pdPow (1 : ℤ).toNat = T.J
    exact le_antisymm (dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one
  · intro r r' h T
    exact T.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.B from x) ∈ pdP T.δ r := by
      have : (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.B from y) ∈ pdP T.δ r' := by
      have : (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.δ k hx

end GlobalTheory.CompanionTheory.DPFil
