import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Use `set I : Ideal O := RingHom.ker ev with hI`. Use `set N : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun l => D ℂ L (t l : L)) with hN`. Use `set M : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun w : O => D ℂ L (w : L)) with hM`. Establish `hvM : D ℂ L (v : L) ∈ M` using `Submodule.subset_span ⟨v, rfl⟩`. It suffices to establish `hMN : M ≤ N from hMN hvM`.

Apply `Submodule.le_of_le_smul_of_le_jacobson_bot (I := I)` to reduce the goal to its premises. Take `⟨s, hs⟩` from `(inferInstance : Algebra.FiniteType ℂ B).out set G : Submodule O (Ω[L⁄ℂ]) := Submodule.span O ((fun b : B => D ℂ L (b : L)) '' (s : Set B)) with hG`. Establish `hB : ∀ b : B, D ℂ L (b : L) ∈ G`. Introduce `b`. Establish `hb : b ∈ Algebra.adjoin ℂ (s : Set B)` using `hs ▸ Algebra.mem_top`.

Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `algebraMap r => simp`. Consider the case `add y z _ _ hy hz`. Rewrite using `[Subalgebra.coe_add, map_add]`.

Conclude with `Submodule.add_mem _ hy hz`. Consider the case `mul y z _ _ hy hz`. Rewrite using `[Subalgebra.coe_mul, Derivation.leibniz]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem G (⟨y, hBO y.2⟩ : O) hz) (Submodule.smul_mem G (⟨z, hBO z.2⟩ : O) hy)`. Establish `hGM : M = G`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[hM, Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Take `⟨b, hb0, hbw⟩` from `hden w`. Take `⟨u, hu⟩` from `hunit _ hb0`.

Establish `h1 : D ℂ L ((b : L) * (w : L)) ∈ G` using `hB ⟨_, hbw⟩`. Rewrite `h1` using `[Derivation.leibniz]`. Establish `h2 : (⟨b, hBO b.2⟩ : O) • D ℂ L (w : L) ∈ G`. Establish `h4` using `Submodule.sub_mem G h1 (Submodule.smul_mem G w (hB b))`. Use `h4 using 1` and compare the differences between its conclusion and the goal.

Simplify using `[Subalgebra.smul_def]`. Establish `h3` using `Submodule.smul_mem G (↑u⁻¹ : O) h2`. Rewrite `h3` using `[← hu, smul_smul, Units.inv_mul, one_smul]`. Conclude with `h3`. Rewrite using `[hG, Submodule.span_le]`.

Introduce and unpack `_ ⟨b, _, rfl⟩`. Conclude with `Submodule.subset_span ⟨⟨b, hBO b.2⟩, rfl⟩`. Rewrite using `[hGM]`. Conclude with `Submodule.fg_span (s.finite_toSet.image _)`. Introduce `y hy`.

Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `z`. Apply `hunit` to reduce the goal to its premises. Establish `hy0 : ev y = 0` using `hy`. Simplify using `[hy0]`.

Rewrite using `[hM, Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Take `⟨a, ha⟩` from `hmax (w - algebraMap ℂ O (ev w)) (by simp)`. Establish `hD : D ℂ L (w : L) = ∑ l, ((a l : O) • D ℂ L (t l : L) + (t l : O) • D ℂ L (a l : L))`. Establish `h1 : (w : L) = algebraMap ℂ L (ev w) + ∑ l, (a l : L) * (t l : L)`.

Establish `h5` using `congrArg (fun u : O => (u : L)) ha`. Move the coercions through the operations in `at h5`. Take the linear combination `h5`. Rewrite using `[h1, map_add, Derivation.map_algebraMap, zero_add, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Derivation.leibniz]`. Both sides reduce to the same expression. Use `show D ℂ L (w : L) ∈ _`. Rewrite using `[hD]`. Use `Submodule.sum_mem _ fun l _ => Submodule.add_mem _ ?_ ?_` and prove the remaining obligations.

Conclude with `Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises. Apply `Submodule.smul_mem_smul` to reduce the goal to its premises. Use `show ev (t l) = 0`. Conclude with `ht l`.

Conclude with `Submodule.subset_span ⟨a l, rfl⟩`.
-/
private theorem locOne_nak {L : Type} [Field L] [Algebra ℂ L] (B O : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (hBO : B ≤ O) (ev : O →ₐ[ℂ] ℂ) (hunit : ∀ u : O, ev u ≠ 0 → IsUnit u)
    (hden : ∀ v : O, ∃ b : B, ev ⟨b, hBO b.2⟩ ≠ 0 ∧ (b : L) * v ∈ B)
    {d : ℕ} (t : Fin d → O) (ht : ∀ l, ev (t l) = 0)
    (hmax : ∀ v : O, ev v = 0 → ∃ a : Fin d → O, v = ∑ l, a l * t l) (v : O) :
    D ℂ L (v : L) ∈ Submodule.span O (Set.range fun l => D ℂ L (t l : L)) := by
  classical
  set I : Ideal O := RingHom.ker ev with hI
  set N : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun l => D ℂ L (t l : L)) with hN
  set M : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun w : O => D ℂ L (w : L)) with hM
  have hvM : D ℂ L (v : L) ∈ M := Submodule.subset_span ⟨v, rfl⟩
  suffices hMN : M ≤ N from hMN hvM
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := I)
  · obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ B).out
    set G : Submodule O (Ω[L⁄ℂ]) := Submodule.span O ((fun b : B => D ℂ L (b : L)) '' (s : Set B)) with hG
    have hB : ∀ b : B, D ℂ L (b : L) ∈ G := by
      intro b
      have hb : b ∈ Algebra.adjoin ℂ (s : Set B) := hs ▸ Algebra.mem_top
      induction hb using Algebra.adjoin_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | algebraMap r => simp
      | add y z _ _ hy hz =>
        rw [Subalgebra.coe_add, map_add]
        exact Submodule.add_mem _ hy hz
      | mul y z _ _ hy hz =>
        rw [Subalgebra.coe_mul, Derivation.leibniz]
        exact Submodule.add_mem _ (Submodule.smul_mem G (⟨y, hBO y.2⟩ : O) hz)
          (Submodule.smul_mem G (⟨z, hBO z.2⟩ : O) hy)
    have hGM : M = G := by
      apply le_antisymm
      · rw [hM, Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        obtain ⟨b, hb0, hbw⟩ := hden w
        obtain ⟨u, hu⟩ := hunit _ hb0
        have h1 : D ℂ L ((b : L) * (w : L)) ∈ G := hB ⟨_, hbw⟩
        rw [Derivation.leibniz] at h1
        have h2 : (⟨b, hBO b.2⟩ : O) • D ℂ L (w : L) ∈ G := by
          have h4 := Submodule.sub_mem G h1 (Submodule.smul_mem G w (hB b))
          convert h4 using 1
          simp [Subalgebra.smul_def]
        have h3 := Submodule.smul_mem G (↑u⁻¹ : O) h2
        rw [← hu, smul_smul, Units.inv_mul, one_smul] at h3
        exact h3
      · rw [hG, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact Submodule.subset_span ⟨⟨b, hBO b.2⟩, rfl⟩
    rw [hGM]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    apply hunit
    have hy0 : ev y = 0 := hy
    simp [hy0]
  · rw [hM, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, ha⟩ := hmax (w - algebraMap ℂ O (ev w)) (by simp)
    have hD : D ℂ L (w : L) = ∑ l, ((a l : O) • D ℂ L (t l : L) + (t l : O) • D ℂ L (a l : L)) := by
      have h1 : (w : L) = algebraMap ℂ L (ev w) + ∑ l, (a l : L) * (t l : L) := by
        have h5 := congrArg (fun u : O => (u : L)) ha
        push_cast at h5
        linear_combination h5
      rw [h1, map_add, Derivation.map_algebraMap, zero_add, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.leibniz]
      rfl
    show D ℂ L (w : L) ∈ _
    rw [hD]
    refine Submodule.sum_mem _ fun l _ => Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
    · apply Submodule.mem_sup_right
      apply Submodule.smul_mem_smul
      · show ev (t l) = 0
        exact ht l
      · exact Submodule.subset_span ⟨a l, rfl⟩

/- English proof (translation)
Introduce `hMax hVal F L _ _ _ _ _ _ d x hc hred e v hv`. Take `⟨hle, ⟨ev, hev⟩, hbv, hinv⟩` from `hVal L (rB ℂ L (xv x) {0}) e.1`. Use `haveI := hc.smooth 0`. Use `haveI : Algebra.FiniteType ℂ (rB ℂ L (xv x) {0}) := inferInstance`. Establish `hevB : ∀ b : rB ℂ L (xv x) {0}, ev ⟨b, hle b.2⟩ = e.1 b`.

Introduce `b`. Take `⟨h, hb⟩` from `(hev _ _).1 (hbv b)`. Conclude with `hb`. Establish `hunit : ∀ u : loc (rB ℂ L (xv x) {0}) e.1, ev u ≠ 0 → IsUnit u`. Introduce `u hu`.

Take `⟨h0, h1⟩` from `hinv u (ev u) ((hev _ _).2 ⟨u.2, rfl⟩) hu`. Conclude with `IsUnit.of_mul_eq_one (⟨_, h1⟩ : loc (rB ℂ L (xv x) {0}) e.1) (Subtype.ext (mul_inv_cancel₀ h0))`. Establish `hden : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ∃ b : rB ℂ L (xv x) {0}, ev ⟨b, hle b.2⟩ ≠ 0 ∧ (b : L) * v ∈ rB ℂ L (xv x) {0}`. Introduce `v`. Take `⟨b, hb, hbv'⟩` from `v.2`.

Conclude with `⟨b, by rw [hevB]; exact hb, hbv'⟩`. Set `t : Fin d → loc (rB ℂ L (xv x) {0}) e.1` to `fun l => ⟨tt L x l, hle (tco_mem ℂ L (xv x) l)⟩`. Establish `ht : ∀ l, ev (t l) = 0` using `fun l => (hevB ⟨_, tco_mem ℂ L (xv x) l⟩).trans (e.2 l)`. Establish `hmax : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ev v = 0 → ∃ a : Fin d → loc (rB ℂ L (xv x) {0}) e.1, v = ∑ l, a l * t l`. Introduce `v h0`.

Take `⟨a, ha, hv'⟩` from `hMax F L d x hc hred e v ((hev _ _).2 ⟨v.2, h0⟩)`. Use `⟨fun l => ⟨a l, ha l⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hv', AddSubmonoidClass.coe_finset_sum]`. Both sides reduce to the same expression. Establish `hmem` using `locOne_nak _ _ hle ev hunit hden t ht hmax ⟨v, hv⟩`.

Take `⟨c, hc'⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hmem`. Conclude with `⟨fun l => c l, fun l => (c l).2, hc'.symm⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.locOne_of :
    LocMax → ValBasic → LocOne := by
  intro hMax hVal F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨hle, ⟨ev, hev⟩, hbv, hinv⟩ := hVal L (rB ℂ L (xv x) {0}) e.1
  haveI := hc.smooth 0
  haveI : Algebra.FiniteType ℂ (rB ℂ L (xv x) {0}) := inferInstance
  have hevB : ∀ b : rB ℂ L (xv x) {0}, ev ⟨b, hle b.2⟩ = e.1 b := by
    intro b
    obtain ⟨h, hb⟩ := (hev _ _).1 (hbv b)
    exact hb
  have hunit : ∀ u : loc (rB ℂ L (xv x) {0}) e.1, ev u ≠ 0 → IsUnit u := by
    intro u hu
    obtain ⟨h0, h1⟩ := hinv u (ev u) ((hev _ _).2 ⟨u.2, rfl⟩) hu
    exact IsUnit.of_mul_eq_one (⟨_, h1⟩ : loc (rB ℂ L (xv x) {0}) e.1)
      (Subtype.ext (mul_inv_cancel₀ h0))
  have hden : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ∃ b : rB ℂ L (xv x) {0},
      ev ⟨b, hle b.2⟩ ≠ 0 ∧ (b : L) * v ∈ rB ℂ L (xv x) {0} := by
    intro v
    obtain ⟨b, hb, hbv'⟩ := v.2
    exact ⟨b, by rw [hevB]; exact hb, hbv'⟩
  let t : Fin d → loc (rB ℂ L (xv x) {0}) e.1 := fun l => ⟨tt L x l, hle (tco_mem ℂ L (xv x) l)⟩
  have ht : ∀ l, ev (t l) = 0 := fun l =>
    (hevB ⟨_, tco_mem ℂ L (xv x) l⟩).trans (e.2 l)
  have hmax : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ev v = 0 → ∃ a : Fin d → loc (rB ℂ L (xv x) {0}) e.1,
      v = ∑ l, a l * t l := by
    intro v h0
    obtain ⟨a, ha, hv'⟩ := hMax F L d x hc hred e v ((hev _ _).2 ⟨v.2, h0⟩)
    refine ⟨fun l => ⟨a l, ha l⟩, Subtype.ext ?_⟩
    rw [hv', AddSubmonoidClass.coe_finset_sum]
    rfl
  have hmem := locOne_nak _ _ hle ev hunit hden t ht hmax ⟨v, hv⟩
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  exact ⟨fun l => c l, fun l => (c l).2, hc'.symm⟩
