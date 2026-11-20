import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

/- English proof (translation)
Unfold `gap gapX`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem gap_eq_weight_sub_next {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap lam p = lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0 := by
  unfold gap gapX
  split_ifs <;> simp

/- English proof (translation)
Establish `hab : (a : ℕ) + 1 < N` using `hb ▸ b.2`. Establish `hbe : (⟨(a : ℕ) + 1, hab⟩ : Fin N) = b` using `Fin.ext hb.symm`. Establish `hu : gap lam (τ, a) = lam (τ, a) - lam (τ, b)`. Rewrite using `[gap_eq_weight_sub_next]`. Simplify using `only [hab, dif_pos, hbe]`.

Establish `hsw : ∀ q : Ψ × Fin N, (lam ∘ Equiv.swap (τ, a) (τ, b)) q = lam q + (if q.1 = τ then (if (q.2 : ℕ) = a + 1 then 1 else 0) - (if (q.2 : ℕ) = a then 1 else 0) else 0) * (lam (τ, a) - lam (τ, b))`. Introduce and unpack `⟨σ, i⟩`. Distinguish the cases in `h1 : (σ, i) = (τ, a)`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj h1`. Simplify using the standard rewrite rules.

Distinguish the cases in `h2 : (σ, i) = (τ, b)`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj h2`. Simplify using `[hb]`. Rewrite using `[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]`. Distinguish the cases in `hσ : σ = τ`.

Substitute `hσ` using the available equality. Establish `e1 : (i : ℕ) ≠ a` using `fun h => h1 (by rw [Fin.ext h])`. Establish `e2 : (i : ℕ) ≠ a + 1` using `fun h => h2 (by rw [Fin.ext (h.trans hb.symm)])`. Simplify using `[e1, e2]`. Simplify using `[hσ]`.

Take `⟨σ, i⟩` from `p`. Rewrite using `[hu, gap_eq_weight_sub_next, gap_eq_weight_sub_next]`. Simplify using `only [hsw, xiCoef, Fin.ext_iff]`. Establish `hi` using `i.2`. Apply the tactic sequence `split_ifs <;> first | omega | (push_cast; ring)`.
-/
theorem gap_comp_swap {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (hb : (b : ℕ) = a + 1)
    (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = gap lam p + gap lam (τ, a) * (xiCoef τ a p : ℝ) := by
  have hab : (a : ℕ) + 1 < N := hb ▸ b.2
  have hbe : (⟨(a : ℕ) + 1, hab⟩ : Fin N) = b := Fin.ext hb.symm
  have hu : gap lam (τ, a) = lam (τ, a) - lam (τ, b) := by
    rw [gap_eq_weight_sub_next]; simp only [hab, dif_pos, hbe]
  have hsw : ∀ q : Ψ × Fin N, (lam ∘ Equiv.swap (τ, a) (τ, b)) q =
      lam q + (if q.1 = τ then (if (q.2 : ℕ) = a + 1 then 1 else 0) - (if (q.2 : ℕ) = a then 1 else 0) else 0)
        * (lam (τ, a) - lam (τ, b)) := by
    rintro ⟨σ, i⟩
    by_cases h1 : (σ, i) = (τ, a)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      simp
    by_cases h2 : (σ, i) = (τ, b)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      simp [hb]
    rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
    by_cases hσ : σ = τ
    · subst hσ
      have e1 : (i : ℕ) ≠ a := fun h => h1 (by rw [Fin.ext h])
      have e2 : (i : ℕ) ≠ a + 1 := fun h => h2 (by rw [Fin.ext (h.trans hb.symm)])
      simp [e1, e2]
    · simp [hσ]
  obtain ⟨σ, i⟩ := p
  rw [hu, gap_eq_weight_sub_next, gap_eq_weight_sub_next]
  simp only [hsw, xiCoef, Fin.ext_iff]
  have hi := i.2
  split_ifs <;> first | omega | (push_cast; ring)

/- English proof (translation)
Introduce `Ψ _ N τ a b hb lam u c`. Use `⟨?_, fun p => ?_, fun p => ?_⟩` and prove the remaining obligations. Simplify using `only [c, u, xiCoef]`. Simplify using the standard rewrite rules. Simplify using `only [c]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[gap_comp_swap τ a b hb]`. Simplify using `only [c, u]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gap_swap_decomp : ∀ (Ψ : Type) [DecidableEq Ψ] (N : ℕ) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ∀ lam : Ψ × Fin N → ℝ, let u := gap lam (τ, a); let c := fun p => gap lam p + u / 2 * (xiCoef τ a p : ℝ); c (τ, a) = 0 ∧ (∀ p, gap lam p = c p - u / 2 * (xiCoef τ a p : ℝ)) ∧ ∀ p, gap (lam ∘ Equiv.swap (τ, a) (τ, b)) p = c p + u / 2 * (xiCoef τ a p : ℝ) := by
  intro Ψ _ N τ a b hb lam u c
  refine ⟨?_, fun p => ?_, fun p => ?_⟩
  · simp only [c, u, xiCoef]
    simp
  · simp only [c]; ring
  · rw [gap_comp_swap τ a b hb]
    simp only [c, u]; ring

end GlobalTheory.CompanionTheory.Ar.PB
