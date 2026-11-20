import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdempotent

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `G V W _ _ _ _ _ _ _ _ _ _ ρ σ hρ hσ hne`. Take `⟨μ, h1, h2⟩` from `centralIdem_mul ρ σ hσ`. Establish `hirrρ : ρ.IsIrreducible` using `isIrreducible_of ρ hρ`. Establish `hirrσ : σ.IsIrreducible` using `isIrreducible_of σ hσ`. Establish `hc0 : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`.

Establish `: Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)`. Establish `hno : ¬ Nonempty (Representation.Equiv ρ σ)`. Introduce and unpack `⟨φ⟩`. Conclude with `hne ⟨φ.toLinearEquiv, fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x⟩`. Establish `horth` using `Representation.char_orthonormal σ ρ`.

Rewrite `horth` using `[if_neg hno, Nat.card_eq_fintype_card]`. Establish `h3 : ∑ g, ρ.character g⁻¹ * σ.character g = 0`. Establish `e : ∑ g, ρ.character g⁻¹ * σ.character g = ∑ g, σ.character g * ρ.character g⁻¹` using `Finset.sum_congr rfl fun g _ => mul_comm _ _`. Rewrite using `[e]`. Simplify using `using horth`.

Rewrite `h1` using `[h3]`. Establish `hd : (Module.finrank ℂ W : ℂ) ≠ 0`. Conclude with `(Module.finrank_pos (R := ℂ) (M := W)).ne'` after adjusting the coercions. Establish `hμ : μ = 0` using `(mul_eq_zero.mp h1).resolve_right hd`. Rewrite using `[h2, hμ, mul_zero, zero_smul]`.
-/
theorem central_idempotents_orthogonal : CentralIdemOrthogonal := by
  intro G V W _ _ _ _ _ _ _ _ _ _ ρ σ hρ hσ hne
  obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ σ hσ
  have hirrρ : ρ.IsIrreducible := isIrreducible_of ρ hρ
  have hirrσ : σ.IsIrreducible := isIrreducible_of σ hσ
  have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hno : ¬ Nonempty (Representation.Equiv ρ σ) := by
    rintro ⟨φ⟩
    exact hne ⟨φ.toLinearEquiv, fun g x => LinearMap.congr_fun (φ.isIntertwining' g) x⟩
  have horth := Representation.char_orthonormal σ ρ
  rw [if_neg hno, Nat.card_eq_fintype_card] at horth
  have h3 : ∑ g, ρ.character g⁻¹ * σ.character g = 0 := by
    have e : ∑ g, ρ.character g⁻¹ * σ.character g = ∑ g, σ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => mul_comm _ _
    rw [e]
    simpa using horth
  rw [h3] at h1
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  have hμ : μ = 0 := (mul_eq_zero.mp h1).resolve_right hd
  rw [h2, hμ, mul_zero, zero_smul]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
