import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

/- English proof (translation)
Establish `hx : ∃ x, 0 < f x`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonpos fun z _ => hc z).1 h0 z (Finset.mem_univ _))`. Establish `hy : ∃ y, f y < 0`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hc z).1 h0 z (Finset.mem_univ _))`. Take `⟨x, hx⟩` from `hx`. Take `⟨y, hy⟩` from `hy`.

Establish `hxy : x ≠ y` using `fun e => by rw [e] at hx; omega`. Establish `e1 : ∀ (g : α → ℤ), ∑ z, g z * eps x y z = g y - g x`. Introduce `g`. Establish `: ∀ z, g z * eps x y z = (if z = y then g y else 0) - (if z = x then g x else 0)`. Introduce `z`.

Unfold `eps`. Distinguish the cases in `a : z = x`. Substitute `a` using the available equality. Simplify using `[hxy]`. Distinguish the cases in `b : z = y`.

Substitute `b` using the available equality. Simplify using `[a]`. Simplify using `[a, b]`. Simplify using `[this, Finset.sum_sub_distrib]`. Establish `ex : eps x y x = -1` using `by simp [eps]`.

Establish `ey : eps x y y = 1` using `by simp [eps, hxy.symm]`. Use `⟨x, y, hxy, ?_, ?_⟩` and prove the remaining obligations. Use `e1 fun _ => 1` as an intermediate fact. Simplify using `only [one_mul] at this`. Rewrite using `[Finset.sum_add_distrib, h0, this]`.

Simplify using the standard rewrite rules. Establish `a` using `e1 f`. Establish `b` using `e1 (eps x y)`. Establish `: ∑ z, (f z + eps x y z) ^ 2 = ∑ z, f z ^ 2 + 2 * ∑ z, f z * eps x y z + ∑ z, eps x y z * eps x y z`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun z _ => by ring`. Rewrite using `[this, a, b, ex, ey]`. Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.PMon.arith {α : Type} [Fintype α] [DecidableEq α] (f : α → ℤ) (h0 : ∑ z, f z = 0) (hf : f ≠ 0) :
    ∃ x y, x ≠ y ∧ ∑ z, (f z + eps x y z) = 0 ∧ ∑ z, (f z + eps x y z) ^ 2 < ∑ z, f z ^ 2 := by
  have hx : ∃ x, 0 < f x := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonpos fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  have hy : ∃ y, f y < 0 := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hxy : x ≠ y := fun e => by rw [e] at hx; omega
  have e1 : ∀ (g : α → ℤ), ∑ z, g z * eps x y z = g y - g x := by
    intro g
    have : ∀ z, g z * eps x y z = (if z = y then g y else 0) - (if z = x then g x else 0) := by
      intro z
      unfold eps
      by_cases a : z = x
      · subst a; simp [hxy]
      · by_cases b : z = y
        · subst b; simp [a]
        · simp [a, b]
    simp [this, Finset.sum_sub_distrib]
  have ex : eps x y x = -1 := by simp [eps]
  have ey : eps x y y = 1 := by simp [eps, hxy.symm]
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have := e1 fun _ => 1
    simp only [one_mul] at this
    rw [Finset.sum_add_distrib, h0, this]; simp
  · have a := e1 f
    have b := e1 (eps x y)
    have : ∑ z, (f z + eps x y z) ^ 2 = ∑ z, f z ^ 2 + 2 * ∑ z, f z * eps x y z + ∑ z, eps x y z * eps x y z := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this, a, b, ex, ey]
    omega

/- English proof (translation)
Introduce `hF hT hS hR hM l _ P AI T`. It suffices to establish `H : ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = N → ∀ (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ from fun n _ _ K r ρ => H _ n rfl K r ρ`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N IH`.

Introduce `n _ _ hn K r ρ hρ hd`. Take `⟨w, hw⟩` from `(hF l P AI T n K r ρ hρ).1 hd`. Take `⟨K', r', ρ', w', h1, h2, h3, h4⟩` from `hT l P AI T n K r ρ w hρ hw`. Apply `h4` to reduce the goal to its premises. It suffices to establish `G : ∀ (S : ℕ) (σ : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (v : Fin r' → n → ℤ), IsRat r' σ → Framed P σ v → ∑ z : Fin r' × n, v z.1 z.2 = 0 → (∑ z : Fin r' × n, v z.1 z.2 ^ 2).toNat = S → AdmSt P σ from G _ ρ' w' h1 h2 (by rw [Fintype.sum_prod_type]; exact h3) rfl`.

Introduce `S`. Proceed by induction on `S using Nat.strong_induction_on with`. Consider the case `_ S IS`. Introduce `σ v a1 a2 a3 a4`. Distinguish the cases in `hv : (fun z : Fin r' × n => v z.1 z.2) = 0`.

Establish `: v = 0` using `funext fun m => funext fun j => congrFun hv (m, j)`. Substitute `this` using the available equality. Conclude with `hS l P AI T n K' r' σ a1 a2`. Distinguish the cases in `hs : Splits r' σ`. Conclude with `hR l P AI T n K' r' σ a1 ((hF l P AI T n K' r' σ a1).2 ⟨v, a2⟩) hs fun a _ _ ha τ b1 b2 => IH _ (hn ▸ ha) a rfl K' r' τ b1 b2`.

Take `⟨x, y, hxy, c1, c2⟩` from `GlobalTheory.PMon.arith _ a3 hv`. Take `⟨τ, b1, b2, b3⟩` from `hM l P AI T n K' r' σ v x y hxy a1 a2 hs`. Use `b3 (IS _ ?_ τ _ b1 b2 c1 rfl)` and prove the remaining obligations. Establish `p : 0 ≤ ∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2` using `Finset.sum_nonneg fun z _ => sq_nonneg _`. Use `show (∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2).toNat < S`.

Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.PMon.matThm_of_steps : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  intro hF hT hS hR hM l _ P AI T
  suffices H : ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = N →
      ∀ (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ from
    fun n _ _ K r ρ => H _ n rfl K r ρ
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro n _ _ hn K r ρ hρ hd
  obtain ⟨w, hw⟩ := (hF l P AI T n K r ρ hρ).1 hd
  obtain ⟨K', r', ρ', w', h1, h2, h3, h4⟩ := hT l P AI T n K r ρ w hρ hw
  apply h4
  suffices G : ∀ (S : ℕ) (σ : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (v : Fin r' → n → ℤ), IsRat r' σ → Framed P σ v →
      ∑ z : Fin r' × n, v z.1 z.2 = 0 → (∑ z : Fin r' × n, v z.1 z.2 ^ 2).toNat = S → AdmSt P σ from
    G _ ρ' w' h1 h2 (by rw [Fintype.sum_prod_type]; exact h3) rfl
  intro S
  induction S using Nat.strong_induction_on with
  | _ S IS =>
  intro σ v a1 a2 a3 a4
  by_cases hv : (fun z : Fin r' × n => v z.1 z.2) = 0
  · have : v = 0 := funext fun m => funext fun j => congrFun hv (m, j)
    subst this
    exact hS l P AI T n K' r' σ a1 a2
  by_cases hs : Splits r' σ
  · exact hR l P AI T n K' r' σ a1 ((hF l P AI T n K' r' σ a1).2 ⟨v, a2⟩) hs
      fun a _ _ ha τ b1 b2 => IH _ (hn ▸ ha) a rfl K' r' τ b1 b2
  obtain ⟨x, y, hxy, c1, c2⟩ := GlobalTheory.PMon.arith _ a3 hv
  obtain ⟨τ, b1, b2, b3⟩ := hM l P AI T n K' r' σ v x y hxy a1 a2 hs
  refine b3 (IS _ ?_ τ _ b1 b2 c1 rfl)
  have p : 0 ≤ ∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  show (∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2).toNat < S
  omega
