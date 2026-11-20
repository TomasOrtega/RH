import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich.Sep

open NumberField Matrix

/- English proof (translation)
Take `⟨T, hT⟩ : ∃ T, T = Algebra.traceMatrix ℤ ω` from `⟨_, rfl⟩`. Establish `hTsymm : ∀ j k, T j k = T k j` using `fun j k => by`. Simplify using `only [hT, Algebra.traceMatrix_apply, Algebra.traceForm_apply]`. Rewrite using `[mul_comm]`. Establish `hAT : T.adjugate * T = Algebra.discr ℤ ω • (1 : Matrix ι ι ℤ)`.

Rewrite using `[Matrix.adjugate_mul, Algebra.discr_def, hT]`. Establish `e1 : ∀ (c : ℤ) (y : 𝓞 E), Algebra.trace ℤ (𝓞 E) ((c : 𝓞 E) * y) = c * Algebra.trace ℤ (𝓞 E) y`. Introduce `c y`. Rewrite using `[← zsmul_eq_mul, map_zsmul, smul_eq_mul]`. Establish `htrω : ∀ z : 𝓞 E, ∀ k, Algebra.trace ℤ (𝓞 E) (z * ω k) = ∑ j, ω.repr z j * T j k`.

Introduce `z k`. Use `conv_lhs => rw [← ω.sum_repr z]`. Rewrite using `[Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_zsmul, smul_eq_mul, hT, Algebra.traceMatrix_apply, Algebra.traceForm_apply]`.

Take `⟨b, hb⟩ : ∃ b : ι → 𝓞 E, b = fun i => ∑ k, (T.adjugate i k : 𝓞 E) * ω k` from `⟨_, rfl⟩`. Establish `hDB : ∀ z : 𝓞 E, ∀ i, Algebra.trace ℤ (𝓞 E) (z * b i) = Algebra.discr ℤ ω * ω.repr z i`. Introduce `z i`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hb, Finset.mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, e1]`. Use `_ = ∑ k, T.adjugate i k * ∑ j, ω.repr z j * T j k := by simp only [htrω]`. Use `_ = ∑ j, ω.repr z j * (T.adjugate * T) i j := by`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hTsymm j k]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = Algebra.discr ℤ ω * ω.repr z i := by`.

Rewrite using `[hAT]`. Simplify using `[Matrix.smul_apply, Matrix.one_apply]`. Apply the tactic sequence `try ring`. Establish `hnd : ∀ s : 𝓞 E, (∀ l, Algebra.trace ℤ (𝓞 E) (s * ω l) = 0) → s = 0`. Introduce `s hs`.

Establish `hb0 : ∀ i, Algebra.trace ℤ (𝓞 E) (s * b i) = 0`. Introduce `i`. Simplify using `only [hb, Finset.mul_sum, map_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, e1, hs, mul_zero]`.

Establish `hr : ∀ i, ω.repr s i = 0` using `fun i => by`. Establish `h` using `hDB s i`. Rewrite `h` using `[hb0 i]`. Conclude with `(mul_eq_zero.mp h.symm).resolve_left hd`. Rewrite using `[← ω.sum_repr s]`.

Simplify using `[hr]`. Establish `htr : ∀ y : 𝓞 E, Algebra.trace ℤ (𝓞 E) y = ∑ i, ω.repr (y * ω i) i`. Introduce `y`. Rewrite using `[Algebra.trace_eq_matrix_trace ω, Matrix.trace]`. Simplify using `[Algebra.leftMulMatrix_eq_repr_mul]`.

Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `hnd` to reduce the goal to its premises. Introduce `l`. Rewrite using `[sub_mul, map_sub, Finset.sum_mul, map_sum, e1, htr (ω l)]`.

Establish `h : ∀ i, Algebra.trace ℤ (𝓞 E) (ω i * b i * ω l) = Algebra.discr ℤ ω * ω.repr (ω l * ω i) i` using `fun i => by`. Rewrite using `[mul_right_comm, hDB, mul_comm (ω i)]`. Simplify using `only [h, Finset.mul_sum, sub_self]`. Introduce `x i`. Apply `sub_eq_zero.mp` to reduce the goal to its premises.

Apply `hnd` to reduce the goal to its premises. Introduce `l`. Rewrite using `[sub_mul, map_sub, Finset.sum_mul, map_sum]`. Establish `h1 : Algebra.trace ℤ (𝓞 E) (x * b i * ω l) = Algebra.discr ℤ ω * ω.repr (x * ω l) i`. Rewrite using `[mul_right_comm, hDB]`.

Establish `h2 : ∀ j, Algebra.trace ℤ (𝓞 E) (((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j * ω l) = ω.repr (x * ω j) i * (Algebra.discr ℤ ω * ω.repr (ω l) j)` using `fun j => by`. Rewrite using `[mul_assoc, e1, mul_comm (b j), hDB]`. Simplify using `only [h1, h2, ω.repr_self, Finsupp.single_apply]`. Simplify using the standard rewrite rules. Apply the tactic sequence `try ring`.
-/
private theorem exists_discr_dual_basis_of_discr_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (E : Type) [Field E]
    [NumberField E] (ω : Module.Basis ι ℤ (𝓞 E)) (hd : Algebra.discr ℤ ω ≠ 0) :
    ∃ b : ι → 𝓞 E, ∑ i, ω i * b i = ((Algebra.discr ℤ ω : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∀ i, x * b i = ∑ j, ((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j := by
  obtain ⟨T, hT⟩ : ∃ T, T = Algebra.traceMatrix ℤ ω := ⟨_, rfl⟩
  have hTsymm : ∀ j k, T j k = T k j := fun j k => by
    simp only [hT, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [mul_comm]
  have hAT : T.adjugate * T = Algebra.discr ℤ ω • (1 : Matrix ι ι ℤ) := by
    rw [Matrix.adjugate_mul, Algebra.discr_def, hT]

  have e1 : ∀ (c : ℤ) (y : 𝓞 E), Algebra.trace ℤ (𝓞 E) ((c : 𝓞 E) * y) =
      c * Algebra.trace ℤ (𝓞 E) y := by
    intro c y
    rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul]
  have htrω : ∀ z : 𝓞 E, ∀ k, Algebra.trace ℤ (𝓞 E) (z * ω k) = ∑ j, ω.repr z j * T j k := by
    intro z k
    conv_lhs => rw [← ω.sum_repr z]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_zsmul, smul_eq_mul, hT, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]

  obtain ⟨b, hb⟩ : ∃ b : ι → 𝓞 E, b = fun i => ∑ k, (T.adjugate i k : 𝓞 E) * ω k := ⟨_, rfl⟩
  have hDB : ∀ z : 𝓞 E, ∀ i, Algebra.trace ℤ (𝓞 E) (z * b i) = Algebra.discr ℤ ω * ω.repr z i := by
    intro z i
    calc Algebra.trace ℤ (𝓞 E) (z * b i)
        = ∑ k, T.adjugate i k * Algebra.trace ℤ (𝓞 E) (z * ω k) := by
          simp only [hb, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_left_comm, e1]
      _ = ∑ k, T.adjugate i k * ∑ j, ω.repr z j * T j k := by simp only [htrω]
      _ = ∑ j, ω.repr z j * (T.adjugate * T) i j := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hTsymm j k]
          ring
      _ = Algebra.discr ℤ ω * ω.repr z i := by
          rw [hAT]
          simp [Matrix.smul_apply, Matrix.one_apply]
          try ring
  have hnd : ∀ s : 𝓞 E, (∀ l, Algebra.trace ℤ (𝓞 E) (s * ω l) = 0) → s = 0 := by
    intro s hs
    have hb0 : ∀ i, Algebra.trace ℤ (𝓞 E) (s * b i) = 0 := by
      intro i
      simp only [hb, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [mul_left_comm, e1, hs, mul_zero]
    have hr : ∀ i, ω.repr s i = 0 := fun i => by
      have h := hDB s i
      rw [hb0 i] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hd
    rw [← ω.sum_repr s]
    simp [hr]
  have htr : ∀ y : 𝓞 E, Algebra.trace ℤ (𝓞 E) y = ∑ i, ω.repr (y * ω i) i := by
    intro y
    rw [Algebra.trace_eq_matrix_trace ω, Matrix.trace]
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  refine ⟨b, ?_, ?_⟩
  · apply sub_eq_zero.mp
    apply hnd
    intro l
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum, e1, htr (ω l)]
    have h : ∀ i, Algebra.trace ℤ (𝓞 E) (ω i * b i * ω l) =
        Algebra.discr ℤ ω * ω.repr (ω l * ω i) i := fun i => by
      rw [mul_right_comm, hDB, mul_comm (ω i)]
    simp only [h, Finset.mul_sum, sub_self]
  · intro x i
    apply sub_eq_zero.mp
    apply hnd
    intro l
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    have h1 : Algebra.trace ℤ (𝓞 E) (x * b i * ω l) = Algebra.discr ℤ ω * ω.repr (x * ω l) i := by
      rw [mul_right_comm, hDB]
    have h2 : ∀ j, Algebra.trace ℤ (𝓞 E) (((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j * ω l) =
        ω.repr (x * ω j) i * (Algebra.discr ℤ ω * ω.repr (ω l) j) := fun j => by
      rw [mul_assoc, e1, mul_comm (b j), hDB]
    simp only [h1, h2, ω.repr_self, Finsupp.single_apply]
    simp
    try ring

/- English proof (translation)
Set `ω` to `(RingOfIntegers.basis E).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))`. Establish `hdisc : Algebra.discr ℤ ω = discr E`. Simplify using `only [ω, Module.Basis.coe_reindex]`. Rewrite using `[Algebra.discr_reindex]`. Take `⟨b, hsum, hb⟩` from `exists_discr_dual_basis_of_discr_ne_zero E ω (by rw [hdisc]; exact discr_ne_zero E)`.

Use `⟨_, ω, b, by rw [← hdisc]; exact hsum, fun x => ⟨fun i j => ω.repr (x * ω i) j, fun i => ?_, fun i => hb x i⟩⟩` and prove the remaining obligations. Use `conv_lhs => rw [← ω.sum_repr (x * ω i)]`. Simplify using `[zsmul_eq_mul]`.
-/
theorem exists_sep_element (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∑ i, a i * b i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∃ m : Matrix (Fin n) (Fin n) ℤ, (∀ i, x * a i = ∑ j, (m i j : 𝓞 E) * a j) ∧
        ∀ i, x * b i = ∑ j, (m j i : 𝓞 E) * b j := by
  classical
  let ω := (RingOfIntegers.basis E).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))
  have hdisc : Algebra.discr ℤ ω = discr E := by
    simp only [ω, Module.Basis.coe_reindex]
    rw [Algebra.discr_reindex]
  obtain ⟨b, hsum, hb⟩ := exists_discr_dual_basis_of_discr_ne_zero E ω (by rw [hdisc]; exact discr_ne_zero E)
  refine ⟨_, ω, b, by rw [← hdisc]; exact hsum, fun x =>
    ⟨fun i j => ω.repr (x * ω i) j, fun i => ?_, fun i => hb x i⟩⟩
  conv_lhs => rw [← ω.sum_repr (x * ω i)]
  simp [zsmul_eq_mul]

/- English proof (translation)
Take `⟨n, a, b, hsum, hm⟩` from `exists_sep_element E`. Use `⟨n, a, b, fun R _ V _ _ ρ σ => ⟨fun v => ?_, fun v hv => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eigSp, Submodule.mem_iInf]`. Introduce `x`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]`.

Take `⟨m, hma, hmb⟩` from `hm x`. Establish `L : ∀ i, ρ x (ρ (a i) v) = ∑ j, (m i j : R) • ρ (a j) v` using `fun i => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hma i, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]`.

Establish `Rr : ∀ j, σ x * σ (b j) = ∑ i, (m i j : R) * σ (b i)` using `fun j => by`. Rewrite using `[← map_mul, hmb j, map_sum]`. Simplify using `[map_mul, map_intCast]`. Rewrite using `[map_sum, Finset.smul_sum]`. Simplify using `only [map_smul, L, Finset.smul_sum, smul_smul, Rr, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `hv' : ∀ x, ρ x v = σ x • v`. Introduce `x`.

Rewrite `hv` using `[eigSp, Submodule.mem_iInf]`. Establish `h` using `hv x`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using h`. Simplify using `only [hv', smul_smul, ← Finset.sum_smul]`.

Use `congr 1`. Rewrite using `[← map_intCast σ, ← hsum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_comm]`.
-/
theorem exists_eigen_op_discr (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (ρ : 𝓞 E →+* Module.End R V) (σ : 𝓞 E →+* R),
      (∀ v, ∑ i, σ (b i) • ρ (a i) v ∈ eigSp ρ σ) ∧
        ∀ v ∈ eigSp ρ σ, ∑ i, σ (b i) • ρ (a i) v = ((discr E : ℤ) : R) • v := by
  obtain ⟨n, a, b, hsum, hm⟩ := exists_sep_element E
  refine ⟨n, a, b, fun R _ V _ _ ρ σ => ⟨fun v => ?_, fun v hv => ?_⟩⟩
  · rw [eigSp, Submodule.mem_iInf]
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply]
    obtain ⟨m, hma, hmb⟩ := hm x
    have L : ∀ i, ρ x (ρ (a i) v) = ∑ j, (m i j : R) • ρ (a j) v := fun i => by
      rw [← Module.End.mul_apply, ← map_mul, hma i, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply,
        Int.cast_smul_eq_zsmul]
    have Rr : ∀ j, σ x * σ (b j) = ∑ i, (m i j : R) * σ (b i) := fun j => by
      rw [← map_mul, hmb j, map_sum]
      simp [map_mul, map_intCast]
    rw [map_sum, Finset.smul_sum]
    simp only [map_smul, L, Finset.smul_sum, smul_smul, Rr, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  · have hv' : ∀ x, ρ x v = σ x • v := by
      intro x
      rw [eigSp, Submodule.mem_iInf] at hv
      have h := hv x
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    simp only [hv', smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← map_intCast σ, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Sandwich.Sep
