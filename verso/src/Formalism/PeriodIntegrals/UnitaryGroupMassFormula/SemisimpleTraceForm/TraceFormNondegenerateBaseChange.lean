import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep

namespace PI.SSAscent.UnitaryGroupMassFormula

open Matrix

/- English proof (translation)
Introduce `K L _ _ _ a S hK`. Use `set f : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) L := (algebraMap K L).mapMatrix with hf`. Use `set P : Submodule K (Matrix (Fin a) (Fin a) K) := Subalgebra.toSubmodule (Algebra.adjoin K S) with hP`. Set `b` to `Module.finBasis K P`. Use `set m := Module.finrank K P`.

Set `β : Fin m → Matrix (Fin a) (Fin a) K` to `fun i => (b i : Matrix (Fin a) (Fin a) K)`. Establish `hβA : ∀ i, β i ∈ Algebra.adjoin K S` using `fun i => (b i).2`. Establish `hspanA : ∀ x ∈ Algebra.adjoin K S, ∃ d : Fin m → K, ∑ i, d i • β i = x`. Introduce `x hx`. Use `⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : P))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h1`. Conclude with `h1`. Establish `hli : LinearIndependent K β` using `b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)`. Set `G : Matrix (Fin m) (Fin m) K` to `Matrix.of fun i j => Matrix.trace (β i * β j)`.

Establish `hG : G.det ≠ 0`. Introduce `h0`. Take `⟨d, hd0, hd⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr h0`. Apply `hd0` to reduce the goal to its premises. Establish `hz : ∑ i, d i • β i = 0`.

Apply `hK` to reduce the goal to its premises. Conclude with `Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hβA i) _`. Introduce `y hy`. Take `⟨e, rfl⟩` from `hspanA y hy`. Rewrite using `[Finset.mul_sum, trace_sum]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Establish `hj : (d ᵥ* G) j = 0` using `by rw [hd]; rfl`. Rewrite using `[mul_smul_comm, trace_smul, Finset.sum_mul, trace_sum]`. Simplify using `only [smul_mul_assoc, trace_smul, smul_eq_mul]`.

Simplify using `only [vecMul, dotProduct, G, Matrix.of_apply] at hj`. Rewrite using `[hj, mul_zero]`. Use function extensionality and compare the values at `i`. Conclude with `(Fintype.linearIndependent_iff.mp hli) d hz i`. Establish `hfA : ∀ y ∈ Algebra.adjoin K S, f y ∈ Algebra.adjoin L (f '' S)`.

Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩`. Consider the case `algebraMap r`. Establish `: f (algebraMap K _ r) = algebraMap L (Matrix (Fin a) (Fin a) L) (algebraMap K L r)`.

Use extensionality with `i j`. Rewrite using `[hf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[this]`. Conclude with `Subalgebra.algebraMap_mem _ _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Establish `hfsmul : ∀ (c : K) (M : Matrix (Fin a) (Fin a) K), f (c • M) = algebraMap K L c • f M`.

Introduce `c M`. Use extensionality with `i j`. Simplify using `[hf]`. Establish `hBspan : ∀ x ∈ Algebra.adjoin L (f '' S), x ∈ Submodule.span L (Set.range fun i => f (β i))`. Introduce `x hx`.

Establish `hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin L (f '' S))` using `hx`. Rewrite `hx'` using `[Algebra.adjoin_eq_span]`. Use `(Submodule.span_le.mpr ?_) hx'` and prove the remaining obligations. Establish `hcl : (Submonoid.closure (f '' S) : Set (Matrix (Fin a) (Fin a) L)) ⊆ (Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L) (Algebra.adjoin K S).toSubmonoid : Set _)`. Establish `: Submonoid.closure (f '' S) ≤ Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L) (Algebra.adjoin K S).toSubmonoid`.

Rewrite using `[Submonoid.closure_le]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `⟨s, Algebra.subset_adjoin hs, rfl⟩`. Conclude with `this`. Introduce `z hz`.

Take `⟨y, hy, rfl⟩` from `hcl hz`. Take `⟨d, rfl⟩` from `hspanA y hy`. Use `show f (∑ i, d i • β i) ∈ _`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hfsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `x hx hxy`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun L).mp (hBspan x hx)`. Establish `hG' : (G.map (algebraMap K L)).det ≠ 0`.

Use `RingHom.map_det (algebraMap K L) G` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← this]`. Conclude with `(map_ne_zero _).mpr hG`. Establish `hc : c ᵥ* G.map (algebraMap K L) = 0`.

Use function extensionality and compare the values at `j`. Establish `h1` using `hxy (f (β j)) (hfA _ (hβA j))`. Rewrite `h1` using `[Finset.sum_mul, trace_sum]`. Simplify using `only [vecMul, dotProduct, Matrix.map_apply, G, Matrix.of_apply, Pi.zero_apply]`. Rewrite using `[← h1]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, trace_smul, smul_eq_mul, ← map_mul, AddMonoidHom.map_trace]`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hne (by simp)`. Conclude with `hG' (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc0, hc⟩)`.
-/
theorem traceFormNondegenerate_baseChange : AscendStep := by
  intro K L _ _ _ a S hK
  classical
  set f : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) L :=
    (algebraMap K L).mapMatrix with hf
  set P : Submodule K (Matrix (Fin a) (Fin a) K) :=
    Subalgebra.toSubmodule (Algebra.adjoin K S) with hP
  let b := Module.finBasis K P
  set m := Module.finrank K P
  let β : Fin m → Matrix (Fin a) (Fin a) K := fun i => (b i : Matrix (Fin a) (Fin a) K)
  have hβA : ∀ i, β i ∈ Algebra.adjoin K S := fun i => (b i).2
  have hspanA : ∀ x ∈ Algebra.adjoin K S, ∃ d : Fin m → K, ∑ i, d i • β i = x := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr (⟨x, hx⟩ : P))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1
  have hli : LinearIndependent K β :=
    b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  let G : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => Matrix.trace (β i * β j)
  have hG : G.det ≠ 0 := by
    intro h0
    obtain ⟨d, hd0, hd⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hd0
    have hz : ∑ i, d i • β i = 0 := by
      apply hK
      · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hβA i) _
      · intro y hy
        obtain ⟨e, rfl⟩ := hspanA y hy
        rw [Finset.mul_sum, trace_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hj : (d ᵥ* G) j = 0 := by rw [hd]; rfl
        rw [mul_smul_comm, trace_smul, Finset.sum_mul, trace_sum]
        simp only [smul_mul_assoc, trace_smul, smul_eq_mul]
        simp only [vecMul, dotProduct, G, Matrix.of_apply] at hj
        rw [hj, mul_zero]
    funext i
    exact (Fintype.linearIndependent_iff.mp hli) d hz i

  have hfA : ∀ y ∈ Algebra.adjoin K S, f y ∈ Algebra.adjoin L (f '' S) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
        have : f (algebraMap K _ r) = algebraMap L (Matrix (Fin a) (Fin a) L) (algebraMap K L r) := by
          ext i j
          rw [hf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply,
            Matrix.algebraMap_matrix_apply]
          split_ifs <;> simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hfsmul : ∀ (c : K) (M : Matrix (Fin a) (Fin a) K), f (c • M) = algebraMap K L c • f M := by
    intro c M
    ext i j
    simp [hf]

  have hBspan : ∀ x ∈ Algebra.adjoin L (f '' S),
      x ∈ Submodule.span L (Set.range fun i => f (β i)) := by
    intro x hx
    have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin L (f '' S)) := hx
    rw [Algebra.adjoin_eq_span] at hx'
    refine (Submodule.span_le.mpr ?_) hx'
    have hcl : (Submonoid.closure (f '' S) : Set (Matrix (Fin a) (Fin a) L)) ⊆
        (Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
          (Algebra.adjoin K S).toSubmonoid : Set _) := by
      have : Submonoid.closure (f '' S) ≤
          Submonoid.map (f : Matrix (Fin a) (Fin a) K →* Matrix (Fin a) (Fin a) L)
            (Algebra.adjoin K S).toSubmonoid := by
        rw [Submonoid.closure_le]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨s, Algebra.subset_adjoin hs, rfl⟩
      exact this
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hcl hz
    obtain ⟨d, rfl⟩ := hspanA y hy
    show f (∑ i, d i • β i) ∈ _
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hfsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro x hx hxy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp (hBspan x hx)
  have hG' : (G.map (algebraMap K L)).det ≠ 0 := by
    have := RingHom.map_det (algebraMap K L) G
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero _).mpr hG
  have hc : c ᵥ* G.map (algebraMap K L) = 0 := by
    funext j
    have h1 := hxy (f (β j)) (hfA _ (hβA j))
    rw [Finset.sum_mul, trace_sum] at h1
    simp only [vecMul, dotProduct, Matrix.map_apply, G, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, trace_smul, smul_eq_mul, ← map_mul, AddMonoidHom.map_trace]
    rfl
  by_contra hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  exact hG' (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc0, hc⟩)

end PI.SSAscent.UnitaryGroupMassFormula
