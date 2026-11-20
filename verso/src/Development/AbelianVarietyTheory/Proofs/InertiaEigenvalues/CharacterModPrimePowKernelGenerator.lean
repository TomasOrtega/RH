import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Use `haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Establish `hcast : ∀ x : ℤ, ((x : ZMod (p ^ r)) = 0 ↔ (p : ℤ) ^ r ∣ x)`. Introduce `x`. Conclude with `ZMod.intCast_zmod_eq_zero_iff_dvd x (p ^ r)` after adjusting the coercions. Establish `hmul : ∀ σ τ, ((a (σ * τ) : ZMod (p ^ r))) = (a σ : ZMod (p ^ r)) + (a τ : ZMod (p ^ r))`.

Introduce `σ τ`. Use `(hcast _).2 (hadd σ τ)` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`. Establish `hone : ((a 1 : ℤ) : ZMod (p ^ r)) = 0`.

Use `hmul 1 1` as an intermediate fact. Simplify using `only [mul_one] at this`. Take the linear combination `-this`. Set `f : G →* Multiplicative (ZMod (p ^ r))` to `{ toFun := fun σ => Multiplicative.ofAdd (a σ : ZMod (p ^ r)) map_one' := by simp only [hone, ofAdd_zero] map_mul' := fun σ τ => by simp only [hmul, ofAdd_add] }`. Establish `hfx : ∀ σ, f σ = Multiplicative.ofAdd (a σ : ZMod (p ^ r))` using `fun _ => rfl`.

Establish `hker : ∀ σ, σ ∈ f.ker ↔ (p : ℤ) ^ r ∣ a σ`. Introduce `σ`. Rewrite using `[MonoidHom.mem_ker, hfx, ofAdd_eq_one, hcast]`. Take `⟨g, hg⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := f.range)`. Take `⟨σ₁, hσ₁⟩` from `g.2`.

Use `set x : ZMod (p ^ r) := (a σ₁ : ZMod (p ^ r)) with hxdef`. Establish `hidx : f.ker.index = addOrderOf x`. Establish `h1 : f.ker.index = Nat.card f.range` using `Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv`. Rewrite using `[h1, ← hg, ← Subgroup.orderOf_coe, ← hσ₁, hfx, orderOf_ofAdd_eq_addOrderOf]`. Establish `hsm : ∀ k : ℕ, k • x = 0 ↔ (p : ℤ) ^ r ∣ (k : ℤ) * a σ₁`.

Introduce `k`. Rewrite using `[← hcast]`. Use `push_cast`. Rewrite using `[nsmul_eq_mul]`. Establish `hdvd : addOrderOf x ∣ p ^ r` using `(addOrderOf_dvd_natCard x).trans (by rw [Nat.card_zmod])`.

Take `⟨s, hsr, hs⟩` from `(Nat.dvd_prime_pow hp).1 hdvd`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Take `⟨τ, hτ⟩` from `hne`. Establish `: f.ker = ⊤` using `Subgroup.index_eq_one.1 (by rw [hidx, hs, pow_zero])`.

Conclude with `hτ ((hker τ).1 (this ▸ Subgroup.mem_top τ))`. Take `⟨c, hc⟩` from `(hsm (addOrderOf x)).1 (addOrderOf_nsmul_eq_zero x)`. Use `⟨f.ker, inferInstance, σ₁, c, hker, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hidx, hc]`. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨d, rfl⟩`. Establish `hp0 : (p : ℤ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `key : (p : ℤ) ^ r ∣ ((p ^ (s - 1) : ℕ) : ℤ) * a σ₁`. Use `⟨d, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises.

Establish `hs' : (p : ℤ) ^ s = p * p ^ (s - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use `hc` as an intermediate fact.

Rewrite `this` using `[hs]`. Move the coercions through the operations in `at this ⊢`. Rewrite `this` using `[hs']`. Take the linear combination `this`. Establish `h2 : addOrderOf x ∣ p ^ (s - 1)` using `addOrderOf_dvd_of_nsmul_eq_zero ((hsm _).2 key)`.

Rewrite `h2` using `[hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt]`. Use linear arithmetic over natural numbers and integers.
-/
theorem character_kernel_generator (G : Type) [Group G] (p r : ℕ) (a : G → ℤ) (hp : p.Prime)
    (hadd : ∀ σ τ, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ) (hne : ∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) :
    ∃ (J : Subgroup G) (_ : J.Normal) (σ₁ : G) (c : ℤ), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧
      c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ ∧ ¬ (p : ℤ) ∣ c := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcast : ∀ x : ℤ, ((x : ZMod (p ^ r)) = 0 ↔ (p : ℤ) ^ r ∣ x) := by
    intro x
    exact_mod_cast ZMod.intCast_zmod_eq_zero_iff_dvd x (p ^ r)
  have hmul : ∀ σ τ, ((a (σ * τ) : ZMod (p ^ r))) = (a σ : ZMod (p ^ r)) + (a τ : ZMod (p ^ r)) := by
    intro σ τ
    have := (hcast _).2 (hadd σ τ)
    push_cast at this
    linear_combination this
  have hone : ((a 1 : ℤ) : ZMod (p ^ r)) = 0 := by
    have := hmul 1 1
    simp only [mul_one] at this
    linear_combination -this
  let f : G →* Multiplicative (ZMod (p ^ r)) :=
    { toFun := fun σ => Multiplicative.ofAdd (a σ : ZMod (p ^ r))
      map_one' := by simp only [hone, ofAdd_zero]
      map_mul' := fun σ τ => by simp only [hmul, ofAdd_add] }
  have hfx : ∀ σ, f σ = Multiplicative.ofAdd (a σ : ZMod (p ^ r)) := fun _ => rfl
  have hker : ∀ σ, σ ∈ f.ker ↔ (p : ℤ) ^ r ∣ a σ := by
    intro σ
    rw [MonoidHom.mem_ker, hfx, ofAdd_eq_one, hcast]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := f.range)
  obtain ⟨σ₁, hσ₁⟩ := g.2
  set x : ZMod (p ^ r) := (a σ₁ : ZMod (p ^ r)) with hxdef
  have hidx : f.ker.index = addOrderOf x := by
    have h1 : f.ker.index = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [h1, ← hg, ← Subgroup.orderOf_coe, ← hσ₁, hfx, orderOf_ofAdd_eq_addOrderOf]
  have hsm : ∀ k : ℕ, k • x = 0 ↔ (p : ℤ) ^ r ∣ (k : ℤ) * a σ₁ := by
    intro k
    rw [← hcast]
    push_cast
    rw [nsmul_eq_mul]
  have hdvd : addOrderOf x ∣ p ^ r :=
    (addOrderOf_dvd_natCard x).trans (by rw [Nat.card_zmod])
  obtain ⟨s, hsr, hs⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hs0 : s ≠ 0 := by
    rintro rfl
    obtain ⟨τ, hτ⟩ := hne
    have : f.ker = ⊤ := Subgroup.index_eq_one.1 (by rw [hidx, hs, pow_zero])
    exact hτ ((hker τ).1 (this ▸ Subgroup.mem_top τ))
  obtain ⟨c, hc⟩ := (hsm (addOrderOf x)).1 (addOrderOf_nsmul_eq_zero x)
  refine ⟨f.ker, inferInstance, σ₁, c, hker, ?_, ?_⟩
  · rw [hidx, hc]; ring
  · rintro ⟨d, rfl⟩
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have key : (p : ℤ) ^ r ∣ ((p ^ (s - 1) : ℕ) : ℤ) * a σ₁ := by
      refine ⟨d, ?_⟩
      apply mul_left_cancel₀ hp0
      have hs' : (p : ℤ) ^ s = p * p ^ (s - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := hc
      rw [hs] at this
      push_cast at this ⊢
      rw [hs'] at this
      linear_combination this
    have h2 : addOrderOf x ∣ p ^ (s - 1) :=
      addOrderOf_dvd_of_nsmul_eq_zero ((hsm _).2 key)
    rw [hs, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
    omega

end GlobalTheory.PMon.Ram
