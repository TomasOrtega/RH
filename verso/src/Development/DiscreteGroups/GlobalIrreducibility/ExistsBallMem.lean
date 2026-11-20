import Development.DiscreteGroups.GlobalIrreducibility.MulMemBall

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Introduce `h hh`. Use `mul_mem_ball hξ hh` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Conclude with `hc.eq_one this`.
-/
theorem psi_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) : ∀ h ∈ ball s, ψ (ξ * h) = 1 := by
  intro h hh
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one this

/- English proof (translation)
Use `mul_mem_ball hξ hh` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Conclude with `hc.eq_one (neg_mem this)`.
-/
theorem psi_neg_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) {h : k} (hh : h ∈ ball s) : ψ (-(ξ * h)) = 1 := by
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one (neg_mem this)

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.
-/
theorem card_ne_zero (s t : kˣ) : ((Fintype.card (Q (k := k) s t) : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

/- English proof (translation)
Distinguish the cases in `h : a = 0`. Conclude with `⟨1, by rw [h]; exact (ball 1).zero_mem⟩`. Conclude with `⟨Units.mk0 a h, mem_ball.2 le_rfl⟩`.
-/
theorem exists_ball_mem (a : k) : ∃ t : kˣ, a ∈ ball t := by
  by_cases h : a = 0
  · exact ⟨1, by rw [h]; exact (ball 1).zero_mem⟩
  · exact ⟨Units.mk0 a h, mem_ball.2 le_rfl⟩

/- English proof (translation)
Break down `le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h` into its components or cases. Conclude with `⟨s1, le_rfl, h⟩`. Conclude with `⟨s2, h, le_rfl⟩`.
-/
theorem exists_min (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s : k) ≤ valuation k (s1 : k) ∧
    valuation k (s : k) ≤ valuation k (s2 : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s1, le_rfl, h⟩
  · exact ⟨s2, h, le_rfl⟩

/- English proof (translation)
Break down `le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h` into its components or cases. Conclude with `⟨s2, h, le_rfl⟩`. Conclude with `⟨s1, le_rfl, h⟩`.
-/
theorem exists_max (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s1 : k) ≤ valuation k (s : k) ∧
    valuation k (s2 : k) ≤ valuation k (s : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s2, h, le_rfl⟩
  · exact ⟨s1, le_rfl, h⟩

section Fourier

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)

/- English proof (translation)
Establish `h1 : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) • σ ((Quotient.out q : ↥(ball t)) : k) z = z` using `fun q => by`. Rewrite using `[hz _ (out_mem q), smul_smul, ch_neg_mul, one_smul]`. Simplify using `only [avg, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_const, Finset.card_univ]`. Conclude with `(Nat.cast_smul_eq_nsmul ℂ _ _).symm`.
-/
theorem avg_of_eigen {s t : kˣ} {ξ : k} {z : V}
    (hz : ∀ b ∈ ball t, σ b z = ((ψ (ξ * b) : Circle) : ℂ) • z) :
    avg ψ σ s t ξ z = ((Fintype.card (Q s t) : ℕ) : ℂ) • z := by
  have h1 : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) z = z := fun q => by
    rw [hz _ (out_mem q), smul_smul, ch_neg_mul, one_smul]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

include hadd

/- English proof (translation)
Establish `hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1` using `fun h hh => hξ h (ball_mono hss0 hh)`. Establish `hxs : ∀ h ∈ ball s, σ h x = x` using `fun h hh => hx h (ball_mono hss0 hh)`. Establish `e1 : avg ψ σ s0 t ξ (avg ψ σ s t ξ x) = ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x` using `avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξs hxs hb)`. Establish `e2 : avg ψ σ s t ξ (avg ψ σ s0 t ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x` using `avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx hb)`. Rewrite using `[← e1, ← e2, ← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]`.
-/
theorem avg_level {s s0 t : kˣ} {ξ : k} (hss0 : valuation k (s : k) ≤ valuation k (s0 : k))
    (hξ : ∀ h ∈ ball s0, ψ (ξ * h) = 1) {x : V} (hx : ∀ h ∈ ball s0, σ h x = x) :
    ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x := by
  have hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1 := fun h hh => hξ h (ball_mono hss0 hh)
  have hxs : ∀ h ∈ ball s, σ h x = x := fun h hh => hx h (ball_mono hss0 hh)
  have e1 : avg ψ σ s0 t ξ (avg ψ σ s t ξ x) = ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξs hxs hb)
  have e2 : avg ψ σ s t ξ (avg ψ σ s0 t ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx hb)
  rw [← e1, ← e2, ← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]

/- English proof (translation)
Establish `e : avg ψ σ s t ξ (avg ψ σ s t' ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s t' ξ x` using `avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx (ball_mono htt' hb))`. Establish `hm : avg ψ σ s t ξ (avg ψ σ s t' ξ x) ∈ W`. Rewrite using `[← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]`. Conclude with `avg_mem ψ σ W hW _ _ _ h`. Rewrite `hm` using `[e]`.

Conclude with `(W.smul_mem_iff (card_ne_zero s t)).1 hm`.
-/
theorem avg_mono_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) {s t t' : kˣ}
    (htt' : valuation k (t : k) ≤ valuation k (t' : k)) {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    {x : V} (hx : ∀ h ∈ ball s, σ h x = x) (h : avg ψ σ s t ξ x ∈ W) : avg ψ σ s t' ξ x ∈ W := by
  have e : avg ψ σ s t ξ (avg ψ σ s t' ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s t' ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx (ball_mono htt' hb))
  have hm : avg ψ σ s t ξ (avg ψ σ s t' ξ x) ∈ W := by
    rw [← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]
    exact avg_mem ψ σ W hW _ _ _ h
  rw [e] at hm
  exact (W.smul_mem_iff (card_ne_zero s t)).1 hm

end Fourier

end DiscreteGroups.sglob.LConvGenF
