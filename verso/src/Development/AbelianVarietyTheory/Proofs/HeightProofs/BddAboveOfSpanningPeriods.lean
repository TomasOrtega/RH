import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `P : AddSubgroup R` to `{ carrier := {p | ∀ x, g (x + p) = g x} zero_mem' := fun x => by simp add_mem' := fun {a b} ha hb x => by`. Rewrite using `[← add_assoc, hb, ha]`. Use the proof step `neg_mem' := fun {a} ha x => by`. Use `ha (x + -a)` as an intermediate fact. Rewrite using `[← this]`.

Simplify using `}`. Establish `hP : Submodule.span ℝ (P : Set R) = ⊤`. Rewrite using `[eq_top_iff, ← hS, Submodule.span_le]`. Introduce `s hs`. Take `⟨N, hN, h⟩` from `hper s hs`.

Establish `h1 : (N : ℝ) • s ∈ Submodule.span ℝ (P : Set R)` using `Submodule.subset_span h`. Establish `h2` using `Submodule.smul_mem _ ((N : ℝ)⁻¹) h1`. Establish `hN' : (N : ℝ) ≠ 0` using `by exact_mod_cast hN.ne'`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hN', one_smul]`. Then use the resulting hypothesis. Take `⟨t, htP, hspan, hli⟩` from `exists_linearIndependent ℝ (P : Set R)`.

Establish `hfin : Finite t` using `hli.finite`. Use `letI : Fintype t := Fintype.ofFinite t`. Set `b : Module.Basis t ℝ R` to `Module.Basis.mk hli (by`. Rewrite using `[Subtype.range_coe, hspan, hP])`. Establish `hb : Submodule.span ℤ (Set.range b) ≤ AddSubgroup.toIntSubmodule P`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: b i = (i : R)` using `by simp [b]`. Rewrite using `[this]`. Conclude with `htP i.2`.

Establish `hK : IsCompact (Metric.closedBall (0 : R) (∑ i, ‖b i‖))` using `isCompact_closedBall _ _`. Take `⟨C, hC⟩` from `hK.bddAbove_image hg.continuousOn`. Use `⟨C, fun x => ?_⟩` and prove the remaining obligations. Establish `hfl : ((ZSpan.floor b x : R)) ∈ P` using `hb (ZSpan.floor b x).2`. Establish `hx : g x = g (ZSpan.fract b x)`.

Use `hfl (ZSpan.fract b x)` as an intermediate fact. Rewrite using `[← this, ZSpan.fract_apply]`. Simplify using the standard rewrite rules. Rewrite using `[hx]`. Apply `hC` to reduce the goal to its premises.

Conclude with `⟨_, by simpa using ZSpan.norm_fract_le b x, rfl⟩`.
-/
theorem bddAbove_of_spanning_periods (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (g : R → ℝ) (hg : Continuous g) (S : Set R)
    (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) :
    ∃ C : ℝ, ∀ x, g x ≤ C := by
  classical
  let P : AddSubgroup R :=
    { carrier := {p | ∀ x, g (x + p) = g x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by
        rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by
        have := ha (x + -a)
        rw [← this]; simp }
  have hP : Submodule.span ℝ (P : Set R) = ⊤ := by
    rw [eq_top_iff, ← hS, Submodule.span_le]
    intro s hs
    obtain ⟨N, hN, h⟩ := hper s hs
    have h1 : (N : ℝ) • s ∈ Submodule.span ℝ (P : Set R) := Submodule.subset_span h
    have h2 := Submodule.smul_mem _ ((N : ℝ)⁻¹) h1
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rwa [smul_smul, inv_mul_cancel₀ hN', one_smul] at h2
  obtain ⟨t, htP, hspan, hli⟩ := exists_linearIndependent ℝ (P : Set R)
  have hfin : Finite t := hli.finite
  letI : Fintype t := Fintype.ofFinite t
  let b : Module.Basis t ℝ R := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, hP])
  have hb : Submodule.span ℤ (Set.range b) ≤ AddSubgroup.toIntSubmodule P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i = (i : R) := by simp [b]
    rw [this]
    exact htP i.2
  have hK : IsCompact (Metric.closedBall (0 : R) (∑ i, ‖b i‖)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hfl : ((ZSpan.floor b x : R)) ∈ P := hb (ZSpan.floor b x).2
  have hx : g x = g (ZSpan.fract b x) := by
    have := hfl (ZSpan.fract b x)
    rw [← this, ZSpan.fract_apply]; simp
  rw [hx]
  apply hC
  exact ⟨_, by simpa using ZSpan.norm_fract_le b x, rfl⟩

end GlobalTheory
