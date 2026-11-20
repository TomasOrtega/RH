import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusChainCarry
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalCharacterIdealPowers
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.Xgn.A_xgr_r_om

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
  {F : Type} [Field F]

/- English proof (translation)
Rewrite using `[xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]`. Establish `he : (r • fun a : F => algebraMap R C (χ a)) = fun a => algebraMap R C (r * χ a)`. Use function extensionality and compare the values at `a`. Simplify using `[Algebra.smul_def, map_mul]`. Rewrite using `[he]`.
-/
theorem mem_x_ideal_iff (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  rw [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have he : (r • fun a : F => algebraMap R C (χ a)) = fun a => algebraMap R C (r * χ a) := by
    funext a
    simp [Algebra.smul_def, map_mul]
  rw [he]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_aug (M : Submodule R (F → C)) (g : F → C) :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

/- English proof (translation)
Conclude with `hv.le_of_dvd (Ideal.mem_span_singleton.mp h)`.
-/
theorem v_le_of_mem (hv : v.Integers R) {a b : R} (h : a ∈ Ideal.span {b}) :
    v (algebraMap R C a) ≤ v (algebraMap R C b) := by
  exact hv.le_of_dvd (Ideal.mem_span_singleton.mp h)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `v_le_of_mem hv` to reduce the goal to its premises. Rewrite using `[← h]`. Conclude with `Ideal.mem_span_singleton_self a`. Apply `v_le_of_mem hv` to reduce the goal to its premises.

Rewrite using `[h]`. Conclude with `Ideal.mem_span_singleton_self b`.
-/
theorem v_eq_of_span (hv : v.Integers R) {a b : R} (h : Ideal.span {a} = Ideal.span {b}) :
    v (algebraMap R C a) = v (algebraMap R C b) := by
  apply le_antisymm
  · apply v_le_of_mem hv
    rw [← h]
    exact Ideal.mem_span_singleton_self a
  · apply v_le_of_mem hv
    rw [h]
    exact Ideal.mem_span_singleton_self b

/- English proof (translation)
Establish `key : ∀ x y : X → C, v (l x) ≤ b → v (l y) ≤ b → v (l (x + y)) ≤ b`. Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `le_trans (v.map_add _ _) (max_le hx hy)`. Establish `ksm : ∀ (r : R) (x : X → C), v (l x) ≤ b → v (l (r • x)) ≤ b`.

Introduce `r x hx`. Rewrite using `[map_smul, Algebra.smul_def, map_mul]`. Conclude with `le_trans (mul_le_of_le_one_left (by positivity) (hv.map_le_one r)) hx`. Establish `k0 : v (l 0) ≤ b` using `by simp`. Establish `step : ∀ g ∈ Submodule.span R s, ∀ g' ∈ Submodule.span R s, v (l (g * g')) ≤ b`.

Introduce `g hg g' hg'`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`. Proceed by induction on `hg' using Submodule.span_induction with`. Consider the case `mem y hy => exact h x hx y hy`.

Consider the case `zero => simpa using k0`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `key _ _ hy hz`. Consider the case `smul r y _ hy => rw [mul_smul_comm]`. Conclude with `ksm r _ hy`.

Consider the case `zero => simpa using k0`. Consider the case `add x z _ _ hx hz => rw [add_mul]`. Conclude with `key _ _ hx hz`. Consider the case `smul r x _ hx => rw [smul_mul_assoc]`. Conclude with `ksm r _ hx`.

Introduce `g hg`. Unfold `sqIdeal at hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, f', hf', rfl⟩` from `hx`.

Conclude with `step f hf f' hf'`. Consider the case `zero => exact k0`. Consider the case `add x z _ _ hx hz => exact key _ _ hx hz`. Consider the case `smul r x _ hx => exact ksm r _ hx`.
-/
theorem sq_bound (hv : v.Integers R) {X : Type} (s : Set (X → C)) (l : (X → C) →ₗ[R] C)
    (b : NNReal) (h : ∀ g ∈ s, ∀ g' ∈ s, v (l (g * g')) ≤ b) :
    ∀ g ∈ sqIdeal (Submodule.span R s), v (l g) ≤ b := by
  have key : ∀ x y : X → C, v (l x) ≤ b → v (l y) ≤ b → v (l (x + y)) ≤ b := by
    intro x y hx hy
    rw [map_add]
    exact le_trans (v.map_add _ _) (max_le hx hy)
  have ksm : ∀ (r : R) (x : X → C), v (l x) ≤ b → v (l (r • x)) ≤ b := by
    intro r x hx
    rw [map_smul, Algebra.smul_def, map_mul]
    exact le_trans (mul_le_of_le_one_left (by positivity) (hv.map_le_one r)) hx
  have k0 : v (l 0) ≤ b := by simp
  have step : ∀ g ∈ Submodule.span R s, ∀ g' ∈ Submodule.span R s, v (l (g * g')) ≤ b := by
    intro g hg g' hg'
    induction hg using Submodule.span_induction with
    | mem x hx =>
      induction hg' using Submodule.span_induction with
      | mem y hy => exact h x hx y hy
      | zero => simpa using k0
      | add y z _ _ hy hz => rw [mul_add]; exact key _ _ hy hz
      | smul r y _ hy => rw [mul_smul_comm]; exact ksm r _ hy
    | zero => simpa using k0
    | add x z _ _ hx hz => rw [add_mul]; exact key _ _ hx hz
    | smul r x _ hx => rw [smul_mul_assoc]; exact ksm r _ hx
  intro g hg
  unfold sqIdeal at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, f', hf', rfl⟩ := hx
    exact step f hf f' hf'
  | zero => exact k0
  | add x z _ _ hx hz => exact key _ _ hx hz
  | smul r x _ hx => exact ksm r _ hx

variable [Fintype F] [DecidableEq F]

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_aug]`. Use `⟨?_, by simp [Pi.pow_apply, hg.2]⟩` and prove the remaining obligations. Proceed by induction on `k with`. Consider the case `zero => simpa using hg.1`. Consider the case `succ n ih => rw [pow_succ]`.

Conclude with `AA.mul_mem _ _ ih hg.1`.
-/
theorem pow_mem_aug (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ augIdeal AA.carrier)
    (k : ℕ) : g ^ (k + 1) ∈ augIdeal AA.carrier := by
  rw [mem_aug] at hg ⊢
  refine ⟨?_, by simp [Pi.pow_apply, hg.2]⟩
  induction k with
  | zero => simpa using hg.1
  | succ n ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg.1

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, k = j + 2` from `⟨k - 2, by omega⟩`. Establish `hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier`. Rewrite using `[mem_aug]`. Use `⟨(mem_x_ideal_iff _ χ c).mp hc, ?_⟩` and prove the remaining obligations. Simplify using `[MulChar.map_nonunit χ not_isUnit_zero]`.

Establish `he : (fun a => algebraMap R C (c ^ (j + 2) * (χ ^ (j + 2)) a)) = (fun a => algebraMap R C (c * χ a)) * (fun a => algebraMap R C (c * χ a)) ^ (j + 1)`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.mul_apply, Pi.pow_apply, MulChar.pow_apply' χ (by omega : j + 2 ≠ 0), map_pow, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`.

Unfold `sqIdeal`. Conclude with `Submodule.subset_span ⟨_, hg, _, pow_mem_aug AA hg j, rfl⟩`.
-/
theorem pow_mem_sq (AA : HopfOrder (C := C) R F) (χ : MulChar F R) {c : R}
    (hc : c ∈ xIdeal AA.carrier χ) {k : ℕ} (hk : 2 ≤ k) :
    (fun a => algebraMap R C (c ^ k * (χ ^ k) a)) ∈ sqIdeal (augIdeal AA.carrier) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hg : (fun a => algebraMap R C (c * χ a)) ∈ augIdeal AA.carrier := by
    rw [mem_aug]
    refine ⟨(mem_x_ideal_iff _ χ c).mp hc, ?_⟩
    simp [MulChar.map_nonunit χ not_isUnit_zero]
  have he : (fun a => algebraMap R C (c ^ (j + 2) * (χ ^ (j + 2)) a)) =
      (fun a => algebraMap R C (c * χ a)) * (fun a => algebraMap R C (c * χ a)) ^ (j + 1) := by
    funext a
    simp only [Pi.mul_apply, Pi.pow_apply, MulChar.pow_apply' χ (by omega : j + 2 ≠ 0), map_pow,
      map_mul]
    ring
  rw [he]
  unfold sqIdeal
  exact Submodule.subset_span ⟨_, hg, _, pow_mem_aug AA hg j, rfl⟩

/- English proof (translation)
Unfold `sqIdeal`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `h ⟨f, hf, f', hf', rfl⟩`. Conclude with `AA.mul_mem f f' ((mem_aug _ f).mp hf).1 ((mem_aug _ f').mp hf').1`.
-/
theorem sq_le (AA : HopfOrder (C := C) R F) : sqIdeal (augIdeal AA.carrier) ≤ AA.carrier := by
  unfold sqIdeal
  rw [Submodule.span_le]
  rintro h ⟨f, hf, f', hf', rfl⟩
  exact AA.mul_mem f f' ((mem_aug _ f).mp hf).1 ((mem_aug _ f').mp hf').1

omit [Fintype F] [DecidableEq F] in
/- English proof (translation)
Simplify using `only [smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eig_fun (χ : MulChar F R) (r : R) (a x : F) :
    algebraMap R C (r * χ (a • x)) = algebraMap R C (χ a) * algebraMap R C (r * χ x) := by
  simp only [smul_eq_mul, map_mul]; ring

end

/- English proof (translation)
Establish `hp : 0 < p`. Break down `Nat.eq_zero_or_pos p with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Apply the tactic sequence `rcases f with _ | f <;> simp at h2 <;> omega`. Conclude with `h0`.

Establish `key : ∀ (g : ℕ) (m : ℕ), m < p ^ g → ∃ d : Fin g → Fin p, ∑ n : Fin g, (d n : ℕ) * p ^ (n : ℕ) = m`. Introduce `g`. Proceed by induction on `g with`. Consider the case `zero`. Introduce `m hm`.

Use `⟨Fin.elim0, ?_⟩` and prove the remaining obligations. Simplify using `at hm`. Simplify using `[hm]`. Consider the case `succ g ih`. Introduce `m hm`.

Take `⟨d', hd'⟩` from `ih (m / p) (by`. Rewrite using `[Nat.div_lt_iff_lt_mul hp, ← pow_succ]`. Conclude with `hm)`. Use `⟨Fin.cons ⟨m % p, Nat.mod_lt _ hp⟩ d', ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]`. Establish `hs : ∑ x : Fin g, (d' x : ℕ) * p ^ ((x : ℕ) + 1) = (∑ x : Fin g, (d' x : ℕ) * p ^ (x : ℕ)) * p`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl (fun x _ => by ring)`. Rewrite using `[hs, hd']`.

Conclude with `Nat.mod_add_div' m p`. Take `⟨d, hd⟩` from `key f m h2`. Use `⟨d, ?_, hd⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `hz : ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0` using `Finset.sum_eq_zero (fun n _ => by simp [hne n])`. Use linear arithmetic over natural numbers and integers.
-/
theorem digits {p f m : ℕ} (h1 : 1 ≤ m) (h2 : m < p ^ f) :
    ∃ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) ∧ ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = m := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0
      rcases f with _ | f <;> simp at h2 <;> omega
    · exact h0
  have key : ∀ (g : ℕ) (m : ℕ), m < p ^ g →
      ∃ d : Fin g → Fin p, ∑ n : Fin g, (d n : ℕ) * p ^ (n : ℕ) = m := by
    intro g
    induction g with
    | zero =>
      intro m hm
      refine ⟨Fin.elim0, ?_⟩
      simp at hm
      simp [hm]
    | succ g ih =>
      intro m hm
      obtain ⟨d', hd'⟩ := ih (m / p) (by
        rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]
        exact hm)
      refine ⟨Fin.cons ⟨m % p, Nat.mod_lt _ hp⟩ d', ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
      have hs : ∑ x : Fin g, (d' x : ℕ) * p ^ ((x : ℕ) + 1) =
          (∑ x : Fin g, (d' x : ℕ) * p ^ (x : ℕ)) * p := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      rw [hs, hd']
      exact Nat.mod_add_div' m p
  obtain ⟨d, hd⟩ := key f m h2
  refine ⟨d, ?_, hd⟩
  by_contra hne
  push_neg at hne
  have hz : ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 :=
    Finset.sum_eq_zero (fun n _ => by simp [hne n])
  omega

/- English proof (translation)
Use `⟨1, fun _ => δ, ⟨?_⟩, by simp⟩` and prove the remaining obligations. Conclude with `((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm`.
-/
theorem hasLen_quot {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) {M : Type} [AddCommGroup M] [Module R M] (φ : R →ₗ[R] M)
    (hφ : Function.Surjective φ) (δ : R) (hk : LinearMap.ker φ = Ideal.span {δ}) :
    HasLen v R M (v (algebraMap R C δ)) := by
  refine ⟨1, fun _ => δ, ⟨?_⟩, by simp⟩
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    (LinearEquiv.funUnique (Fin 1) R (R ⧸ Ideal.span {δ})).symm

end PositivityTheory.Xgn.A_xgr_r_om
