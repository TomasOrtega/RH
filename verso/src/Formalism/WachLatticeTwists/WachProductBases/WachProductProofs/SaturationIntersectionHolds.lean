import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.AffineLineLocalAcyclicityOfStrictHenselianPoints

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Finset

section Eig

variable {L : Type} [CommRing L] {P : Type} [AddCommGroup P] [Module L P]

end Eig

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact ⟨fun a b h => by simpa using h, fun b => ⟨b, by simp⟩⟩`. Consider the case `succ j ih`. Establish `: (fun x : P => t ^ (j + 1) • x) = (fun x : P => t ^ j • x) ∘ (fun x : P => t • x)`. Use function extensionality and compare the values at `x`.

Simplify using `[pow_succ, mul_smul]`. Rewrite using `[this]`. Conclude with `ih.comp h`.
-/
theorem pow_smul_bij {R P : Type} [CommRing R] [AddCommGroup P] [Module R P] (t : R)
    (h : Function.Bijective (fun x : P => t • x)) (j : ℕ) :
    Function.Bijective (fun x : P => t ^ j • x) := by
  induction j with
  | zero => exact ⟨fun a b h => by simpa using h, fun b => ⟨b, by simp⟩⟩
  | succ j ih =>
    have : (fun x : P => t ^ (j + 1) • x) = (fun x : P => t ^ j • x) ∘ (fun x : P => t • x) := by
      funext x; simp [pow_succ, mul_smul]
    rw [this]; exact ih.comp h

/- English proof (translation)
Introduce `A _ Δ _ _ N _ _ κ _ b ρ γ π π' hρ hb hγρ hγ hring x hx`. Take `⟨x', hx'⟩` from `hγ x`. Establish `hinv : ∀ d, ρ d (π • x') = π • x'`. Introduce `d`. Rewrite using `[← hx', map_sub, ← hγρ, hx d]`.

Establish `hcoord : ∀ d v k, b.repr (ρ d v) k = d • b.repr v k`. Introduce `d v k`. Use `conv_lhs => rw [← b.sum_repr v]`. Rewrite using `[map_sum]`. Simplify using `only [hρ, hb]`.

Rewrite using `[b.repr_sum_self]`. Establish `hk : ∀ k (d : Δ), d • (π * b.repr x' k) = π * b.repr x' k`. Introduce `k d`. Use `congrArg (fun v => b.repr v k) (hinv d)` as an intermediate fact. Simplify using `only [hcoord, map_smul, Finsupp.smul_apply, smul_eq_mul] at this`.

Conclude with `this`. Use `choose a' ha'inv ha' using fun k => hring (b.repr x' k) (hk k)`. Use `⟨∑ k, a' k • b k, ?_, ?_⟩` and prove the remaining obligations. Introduce `d`. Rewrite using `[map_sum]`.

Simplify using `only [hρ, hb, ha'inv]`. Rewrite using `[hx', smul_sum] conv_lhs => rw [← b.sum_repr x', smul_sum]`. Use `sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, ha']`.
-/
theorem gamma_sub_one_pi_invariants : GammaSubOnePiInvariants := by
  intro A _ Δ _ _ N _ _ κ _ b ρ γ π π' hρ hb hγρ hγ hring x hx
  obtain ⟨x', hx'⟩ := hγ x
  have hinv : ∀ d, ρ d (π • x') = π • x' := by
    intro d
    rw [← hx', map_sub, ← hγρ, hx d]
  have hcoord : ∀ d v k, b.repr (ρ d v) k = d • b.repr v k := by
    intro d v k
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [hρ, hb]
    rw [b.repr_sum_self]
  have hk : ∀ k (d : Δ), d • (π * b.repr x' k) = π * b.repr x' k := by
    intro k d
    have := congrArg (fun v => b.repr v k) (hinv d)
    simp only [hcoord, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    exact this
  choose a' ha'inv ha' using fun k => hring (b.repr x' k) (hk k)
  refine ⟨∑ k, a' k • b k, ?_, ?_⟩
  · intro d
    rw [map_sum]
    simp only [hρ, hb, ha'inv]
  · rw [hx', smul_sum]
    conv_lhs => rw [← b.sum_repr x', smul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [smul_smul, smul_smul, ha']

end Formalism.RepresentationBoundsCohomology.N1
