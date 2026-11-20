import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.SmGL.Segment

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[mem_carrier]`. Use `show (∃ a : ℕ, a < Δ.len ∧ (Δ.first.nu s).nu a = x) ↔ _`. Simplify using `only [IrrGL.nu_nu]`.
-/
theorem mem_carrier_nu {Δ : Segment k} {s : ℂ} {x : IrrGL k} :
    x ∈ (Δ.nu s).carrier ↔ ∃ a : ℕ, a < Δ.len ∧ Δ.first.nu (s + a) = x := by
  rw [mem_carrier]
  show (∃ a : ℕ, a < Δ.len ∧ (Δ.first.nu s).nu a = x) ↔ _
  simp only [IrrGL.nu_nu]

/- English proof (translation)
Establish `hd : 0 < Δ.first.1` using `Δ.isCusp_first.1`. Establish `inj : ∀ r s : ℝ, Δ.first.nu (r : ℂ) = Δ.first.nu (s : ℂ) → r = s` using `fun r s h => (IrrGL.nu_ofReal_inj hd).1 h`. Use `⟨⟨ofFirst (Δ.first.nu ((t - 1 : ℝ) : ℂ)) (Δ.isCusp_first.nu _) (Δ.len + 1) (Nat.succ_pos _), ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[Set.mem_union, mem_carrier_nu, mem_carrier_nu, mem_carrier]`.

Simplify using `only [first_ofFirst, len_ofFirst, IrrGL.nu_nu]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Break down `Nat.lt_succ_iff_lt_or_eq.1 ha with h | h` into its components or cases. Conclude with `Or.inr ⟨a, h, rfl⟩`.

Use `Or.inl ⟨a - 1, by have := Δ.len_pos; omega, ?_⟩` and prove the remaining obligations. Use `congr 1`. Establish `h1 : ((a - 1 : ℕ) : ℂ) = (a : ℂ) - 1`. Rewrite using `[Nat.cast_sub (by have := Δ.len_pos; omega)]; simp`. Rewrite using `[h1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `(⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)`. Use `⟨a + 1, by omega, ?_⟩` and prove the remaining obligations. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨a, by omega, rfl⟩`. Introduce `hsub`. Establish `hm : Δ.first.nu ((t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ)) ∈ (Δ.nu (t : ℂ)).carrier` using `mem_carrier_nu.2 ⟨Δ.len - 1, by have := Δ.len_pos; omega, rfl⟩`.

Take `⟨a, ha, he⟩` from `mem_carrier_nu.1 (hsub hm)`. Establish `e1 : ((t - 1 : ℝ) : ℂ) + (a : ℂ) = ((t - 1 + a : ℝ) : ℂ)` using `by push_cast; ring`. Establish `e2 : (t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ) = ((t + ((Δ.len - 1 : ℕ) : ℝ) : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `he` using `[e1, e2]`. Establish `h3` using `inj _ _ he`.

Establish `h4 : (a : ℝ) = ((Δ.len - 1 : ℕ) : ℝ) + 1` using `by linarith`. Establish `h5 : a = Δ.len - 1 + 1` using `by exact_mod_cast h4`. Use `Δ.len_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `hsub`.

Establish `hm : Δ.first.nu (((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ)) ∈ (Δ.nu ((t - 1 : ℝ) : ℂ)).carrier` using `mem_carrier_nu.2 ⟨0, Δ.len_pos, rfl⟩`. Take `⟨a, ha, he⟩` from `mem_carrier_nu.1 (hsub hm)`. Establish `e1 : (t : ℂ) + (a : ℂ) = ((t + a : ℝ) : ℂ)` using `by push_cast; ring`. Establish `e2 : ((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ) = ((t - 1 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `he` using `[e1, e2]`.

Establish `h3` using `inj _ _ he`. Establish `h4 : (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem linked_nu_nu_sub_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ) :
    (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  have hd : 0 < Δ.first.1 := Δ.isCusp_first.1
  have inj : ∀ r s : ℝ, Δ.first.nu (r : ℂ) = Δ.first.nu (s : ℂ) → r = s :=
    fun r s h => (IrrGL.nu_ofReal_inj hd).1 h
  refine ⟨⟨ofFirst (Δ.first.nu ((t - 1 : ℝ) : ℂ)) (Δ.isCusp_first.nu _) (Δ.len + 1) (Nat.succ_pos _), ?_⟩, ?_, ?_⟩
  · ext x
    rw [Set.mem_union, mem_carrier_nu, mem_carrier_nu, mem_carrier]
    simp only [first_ofFirst, len_ofFirst, IrrGL.nu_nu]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
      · exact Or.inr ⟨a, h, rfl⟩
      · refine Or.inl ⟨a - 1, by have := Δ.len_pos; omega, ?_⟩
        congr 1
        have h1 : ((a - 1 : ℕ) : ℂ) = (a : ℂ) - 1 := by
          rw [Nat.cast_sub (by have := Δ.len_pos; omega)]; simp
        rw [h1]; push_cast; ring
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · refine ⟨a + 1, by omega, ?_⟩
        congr 1; push_cast; ring
      · exact ⟨a, by omega, rfl⟩
  · intro hsub
    have hm : Δ.first.nu ((t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ)) ∈ (Δ.nu (t : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨Δ.len - 1, by have := Δ.len_pos; omega, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : ((t - 1 : ℝ) : ℂ) + (a : ℂ) = ((t - 1 + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : (t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ) = ((t + ((Δ.len - 1 : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (a : ℝ) = ((Δ.len - 1 : ℕ) : ℝ) + 1 := by linarith
    have h5 : a = Δ.len - 1 + 1 := by exact_mod_cast h4
    have := Δ.len_pos
    omega
  · intro hsub
    have hm : Δ.first.nu (((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ)) ∈ (Δ.nu ((t - 1 : ℝ) : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨0, Δ.len_pos, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : (t : ℂ) + (a : ℂ) = ((t + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ) = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith

end GlobalTheory.SmGL.Segment
