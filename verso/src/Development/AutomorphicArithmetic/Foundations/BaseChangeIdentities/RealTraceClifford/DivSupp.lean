import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Establish `hρ : StrictAnti (rhoV n)` using `(rearr n).2.2.1`. Establish `hsupp : ∀ v, cf χ v ≠ 0 ↔ v ∈ χ.coeff.support`. Introduce `v`. Simplify using `[cf, Finsupp.mem_support_iff]`. Take `⟨μ, hμ, hmax⟩` from `Finset.exists_max_image χ.coeff.support (fun v => ∑ a, x a * v a) ⟨ξ, (hsupp ξ).1 hξ⟩`.

Establish `hμ' : cf χ μ ≠ 0` using `(hsupp μ).2 hμ`. Establish `hcoef : cf (alt (rhoV n) * χ) (rhoV n + μ) = cf χ μ`. Rewrite using `[(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Establish `e : rhoV n + μ - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = μ`. Use function extensionality and compare the values at `a`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Simplify using `[sg]`. Introduce `w _ hw`. Establish `hz : cf χ (rhoV n + μ - rhoV n ∘ ⇑w) = 0`.

Assume the negation of the conclusion as `hc`. Establish `h1` using `hmax _ ((hsupp _).1 hc)`. Establish `h2` using `(rearr n).1 x (rhoV n) hx.antitone hρ.antitone w`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1`. Conclude with `hw (h2.2 hx hρ (by linarith [h2.1]))`.

Rewrite using `[hz, mul_zero]`. Introduce `h1`. Conclude with `absurd (Finset.mem_univ _) h1`. Rewrite `hcoef` using `[h]`. Take `⟨w, hw⟩` from `(cfBasic n).2.2.2.2.2.2.2.2.2.2.1 (κ + rhoV n) (rhoV n + μ) (by rw [hcoef]; exact hμ')`.

Establish `hanti : Antitone (κ + rhoV n)` using `hκ.add hρ.antitone`. Establish `h2` using `((rearr n).1 x (κ + rhoV n) hx.antitone hanti w).1`. Establish `e : ∑ a, x a * (rhoV n + μ) a = ∑ a, x a * (κ + rhoV n) (w a)`. Rewrite using `[hw]`. Both sides reduce to the same expression.

Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at e h2`. Establish `h4 : ∑ a, x a * ξ a ≤ ∑ a, x a * μ a` using `hmax ξ ((hsupp ξ).1 hξ)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem character_support_pairing_le_of_strict_anti {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : StrictAnti x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  classical
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have hsupp : ∀ v, cf χ v ≠ 0 ↔ v ∈ χ.coeff.support := by
    intro v
    simp [cf, Finsupp.mem_support_iff]
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image χ.coeff.support
    (fun v => ∑ a, x a * v a) ⟨ξ, (hsupp ξ).1 hξ⟩
  have hμ' : cf χ μ ≠ 0 := (hsupp μ).2 hμ
  have hcoef : cf (alt (rhoV n) * χ) (rhoV n + μ) = cf χ μ := by
    rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · have e : rhoV n + μ - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = μ := by
        funext a
        simp
      rw [e]
      simp [sg]
    · intro w _ hw
      have hz : cf χ (rhoV n + μ - rhoV n ∘ ⇑w) = 0 := by
        by_contra hc
        have h1 := hmax _ ((hsupp _).1 hc)
        have h2 := (rearr n).1 x (rhoV n) hx.antitone hρ.antitone w
        simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
          Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
        exact hw (h2.2 hx hρ (by linarith [h2.1]))
      rw [hz, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  rw [h] at hcoef
  obtain ⟨w, hw⟩ := (cfBasic n).2.2.2.2.2.2.2.2.2.2.1 (κ + rhoV n) (rhoV n + μ)
    (by rw [hcoef]; exact hμ')
  have hanti : Antitone (κ + rhoV n) := hκ.add hρ.antitone
  have h2 := ((rearr n).1 x (κ + rhoV n) hx.antitone hanti w).1
  have e : ∑ a, x a * (rhoV n + μ) a = ∑ a, x a * (κ + rhoV n) (w a) := by
    rw [hw]
    rfl
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at e h2
  have h4 : ∑ a, x a * ξ a ≤ ∑ a, x a * μ a := hmax ξ ((hsupp ξ).1 hξ)
  linarith

/- English proof (translation)
Establish `hρ : StrictAnti (rhoV n)` using `(rearr n).2.2.1`. Establish `key : ∀ ε : ℝ, 0 < ε → ∑ a, x a * ξ a - ∑ a, x a * κ a ≤ ε * (∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a)`. Introduce `ε hε`. Establish `hs : StrictAnti (fun a => x a + ε * rhoV n a)`. Introduce `a b hab`.

Establish `h1` using `hρ hab`. Establish `h2` using `hx hab.le`. Use the polynomial consequences of the given equalities and inequalities. Use `character_support_pairing_le_of_strict_anti κ χ hκ h _ hs ξ hξ` as an intermediate fact. Simplify using `only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `set A := ∑ a, x a * ξ a - ∑ a, x a * κ a with hA`. Use `set B := ∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a with hB`.

Establish `hA0 : 0 < A` using `by rw [hA]; linarith`. Establish `ht : 0 < |B| + 1` using `by positivity`. Establish `hε : 0 < A / (2 * (|B| + 1))` using `by positivity`. Establish `k` using `key _ hε`. Establish `hle : A / (2 * (|B| + 1)) * B ≤ A / (2 * (|B| + 1)) * (|B| + 1)` using `mul_le_mul_of_nonneg_left (by linarith [le_abs_self B]) hε.le`.

Establish `heq : A / (2 * (|B| + 1)) * (|B| + 1) = A / 2`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem character_support_pairing_le_of_antitone {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : Antitone x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have key : ∀ ε : ℝ, 0 < ε →
      ∑ a, x a * ξ a - ∑ a, x a * κ a ≤ ε * (∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a) := by
    intro ε hε
    have hs : StrictAnti (fun a => x a + ε * rhoV n a) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hx hab.le
      nlinarith
    have := character_support_pairing_le_of_strict_anti κ χ hκ h _ hs ξ hξ
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at this
    linarith
  by_contra hc
  push_neg at hc
  set A := ∑ a, x a * ξ a - ∑ a, x a * κ a with hA
  set B := ∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a with hB
  have hA0 : 0 < A := by rw [hA]; linarith
  have ht : 0 < |B| + 1 := by positivity
  have hε : 0 < A / (2 * (|B| + 1)) := by positivity
  have k := key _ hε
  have hle : A / (2 * (|B| + 1)) * B ≤ A / (2 * (|B| + 1)) * (|B| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self B]) hε.le
  have heq : A / (2 * (|B| + 1)) * (|B| + 1) = A / 2 := by
    field_simp
  linarith

/- English proof (translation)
Introduce `n κ χ hκ h`. Establish `hρ : StrictAnti (rhoV n)` using `(rearr n).2.2.1`. Use `⟨?_, fun ξ hξ x hx => character_support_pairing_le_of_antitone κ χ hκ h x hx ξ hξ, ?_⟩` and prove the remaining obligations. Establish `hs : StrictAnti (κ + rhoV n)`. Introduce `a b hab`.

Establish `h1` using `hρ hab`. Establish `h2` using `hκ hab.le`. Simplify using `only [Pi.add_apply]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcoef : cf (alt (rhoV n) * χ) (κ + rhoV n) = cf χ κ`.

Rewrite using `[(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Establish `e : κ + rhoV n - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = κ`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Simplify using `[sg]`. Introduce `w _ hw`. Establish `hz : cf χ (κ + rhoV n - rhoV n ∘ ⇑w) = 0`. Assume the negation of the conclusion as `hc`. Establish `h1` using `character_support_pairing_le_of_strict_anti κ χ hκ h (rhoV n) hρ _ hc`.

Establish `h2` using `(rearr n).1 (rhoV n) (rhoV n) hρ.antitone hρ.antitone w`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1`. Conclude with `hw (h2.2 hρ hρ (by linarith [h2.1]))`. Rewrite using `[hz, mul_zero]`. Introduce `h1`.

Conclude with `absurd (Finset.mem_univ _) h1`. Rewrite using `[← hcoef, h]`. Conclude with `((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 _ hs).1`. Introduce `hS ξ hξ`. Take `⟨w, hw⟩` from `((rearr n).2.1 ξ).2.1`.

Establish `hanti : Antitone (domC ξ)` using `((rearr n).2.1 ξ).1`. Establish `hc : cf χ (domC ξ) ≠ 0`. Rewrite using `[hw, hS w ξ]`. Conclude with `hξ`. Establish `h1` using `character_support_pairing_le_of_antitone κ χ hκ h (domC ξ) hanti (domC ξ) hc`.

Establish `h2` using `((rearr n).2.2.2.2.2 (domC ξ) κ (by`. Simplify using `only [nsq, sq]`. Conclude with `h1)).1`. Rewrite `h2` using `[((rearr n).2.1 ξ).2.2.2.2]`. Conclude with `h2`.
-/
theorem UpperTheory.RealTr.divSupp :
    ∀ (n : ℕ) (κ : Wt n) (χ : FR n), Antitone κ → alt (rhoV n) * χ = alt (κ + rhoV n) → cf χ κ = 1 ∧ (∀ ξ, cf χ ξ ≠ 0 → Maj ξ κ) ∧
      (Sym χ → ∀ ξ, cf χ ξ ≠ 0 → nsq ξ ≤ nsq κ) := by
  intro n κ χ hκ h
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  refine ⟨?_, fun ξ hξ x hx => character_support_pairing_le_of_antitone κ χ hκ h x hx ξ hξ, ?_⟩
  · have hs : StrictAnti (κ + rhoV n) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hκ hab.le
      simp only [Pi.add_apply]
      linarith
    have hcoef : cf (alt (rhoV n) * χ) (κ + rhoV n) = cf χ κ := by
      rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · have e : κ + rhoV n - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = κ := by
          funext a
          simp
        rw [e]
        simp [sg]
      · intro w _ hw
        have hz : cf χ (κ + rhoV n - rhoV n ∘ ⇑w) = 0 := by
          by_contra hc
          have h1 := character_support_pairing_le_of_strict_anti κ χ hκ h (rhoV n) hρ _ hc
          have h2 := (rearr n).1 (rhoV n) (rhoV n) hρ.antitone hρ.antitone w
          simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
            Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
          exact hw (h2.2 hρ hρ (by linarith [h2.1]))
        rw [hz, mul_zero]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    rw [← hcoef, h]
    exact ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 _ hs).1
  · intro hS ξ hξ
    obtain ⟨w, hw⟩ := ((rearr n).2.1 ξ).2.1
    have hanti : Antitone (domC ξ) := ((rearr n).2.1 ξ).1
    have hc : cf χ (domC ξ) ≠ 0 := by
      rw [hw, hS w ξ]
      exact hξ
    have h1 := character_support_pairing_le_of_antitone κ χ hκ h (domC ξ) hanti (domC ξ) hc
    have h2 := ((rearr n).2.2.2.2.2 (domC ξ) κ (by
      simp only [nsq, sq]
      exact h1)).1
    rw [((rearr n).2.1 ξ).2.2.2.2] at h2
    exact h2
