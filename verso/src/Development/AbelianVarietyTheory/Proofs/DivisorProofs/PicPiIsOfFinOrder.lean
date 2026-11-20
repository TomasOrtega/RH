import Mathlib

open TensorProduct

namespace GlobalTheory

namespace PicPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [DecidableEq ι]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul r y`. Use `⟨(Pi.single i r : (j : ι) → R j) • y, ?_⟩` and prove the remaining obligations. Rewrite using `[← TensorProduct.smul_tmul]`.

Use `congr 1`. Rewrite using `[Algebra.smul_def, hA]`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb`. Take `⟨ya, rfl⟩` from `ha`.

Take `⟨yb, rfl⟩` from `hb`. Conclude with `⟨ya + yb, by rw [TensorProduct.tmul_add]⟩`.
-/
theorem exists_one_tmul (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i)
    (z : R i ⊗[(j : ι) → R j] M) : ∃ y : M, (1 : R i) ⊗ₜ y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r y =>
    refine ⟨(Pi.single i r : (j : ι) → R j) • y, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, hA]
    simp
  | add a b ha hb =>
    obtain ⟨ya, rfl⟩ := ha
    obtain ⟨yb, rfl⟩ := hb
    exact ⟨ya + yb, by rw [TensorProduct.tmul_add]⟩

/- English proof (translation)
Set `φ : R i →ₗ[(j : ι) → R j] M →ₗ[(j : ι) → R j] M` to `LinearMap.mk₂ _ (fun r y => (Pi.single i r : (j : ι) → R j) • y) (fun r₁ r₂ y => by simp only [Pi.single_add, add_smul]) (fun s r y => by`. Establish `hs : (Pi.single i (s • r) : (j : ι) → R j) = s * Pi.single i r`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[Algebra.smul_def, hA]`. Simplify using `[hj]`. Simplify using `only [hs, mul_smul])`. Use the proof step `(fun r y₁ y₂ => smul_add _ _ _)`. Use the proof step `(fun s r y => smul_comm _ _ _)`.

Use `congrArg (TensorProduct.lift φ) h` as an intermediate fact. Simplify `this` using `[φ]`.
-/
theorem single_smul_eq_zero (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i) (y : M)
    (h : (1 : R i) ⊗ₜ[(j : ι) → R j] y = 0) : (Pi.single i 1 : (j : ι) → R j) • y = 0 := by
  let φ : R i →ₗ[(j : ι) → R j] M →ₗ[(j : ι) → R j] M :=
    LinearMap.mk₂ _ (fun r y => (Pi.single i r : (j : ι) → R j) • y)
      (fun r₁ r₂ y => by simp only [Pi.single_add, add_smul])
      (fun s r y => by
        have hs : (Pi.single i (s • r) : (j : ι) → R j) = s * Pi.single i r := by
          ext j
          by_cases hj : j = i
          · subst hj; simp [Algebra.smul_def, hA]
          · simp [hj]
        simp only [hs, mul_smul])
      (fun r y₁ y₂ => smul_add _ _ _)
      (fun s r y => smul_comm _ _ _)
  have := congrArg (TensorProduct.lift φ) h
  simpa [φ] using this

variable [Fintype ι]

/- English proof (translation)
Use `letI inst : ∀ i, Algebra ((j : ι) → R j) (R i) := fun i => (Pi.evalRingHom R i).toAlgebra`. Establish `hA : ∀ i, algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i` using `fun i => rfl`. Establish `e : ∀ i, (R i ⊗[(j : ι) → R j] M) ≃ₗ[R i] R i`. Introduce `i`. Establish `hi` using `h i`.

Rewrite `hi` using `[← hA i, CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff]`. Conclude with `hi.some`. Use `choose m hm using fun i => exists_one_tmul i M (hA i) ((e i).symm 1)`. Set `m₀ : M` to `∑ i, (Pi.single i 1 : (j : ι) → R j) • m i`. Establish `hsurj : Function.Surjective (LinearMap.toSpanSingleton ((j : ι) → R j) M m₀)`.

Introduce `x`. Use `⟨fun i => e i ((1 : R i) ⊗ₜ x), ?_⟩` and prove the remaining obligations. Establish `key : ∀ i, (Pi.single i 1 : (j : ι) → R j) • x = (Pi.single i (e i ((1 : R i) ⊗ₜ x)) : (j : ι) → R j) • m i`. Introduce `i`. Use `set r := e i ((1 : R i) ⊗ₜ x) with hr`.

Establish `h1 : (1 : R i) ⊗ₜ[(j : ι) → R j] x = (1 : R i) ⊗ₜ ((Pi.single i r : (j : ι) → R j) • m i)`. Apply `(e i).injective` to reduce the goal to its premises. Rewrite using `[← TensorProduct.smul_tmul]`. Establish `h0 : (Pi.single i r : (j : ι) → R j) • (1 : R i) = r`. Rewrite using `[Algebra.smul_def, hA i]`.

Simplify using the standard rewrite rules. Rewrite using `[h0]`. Establish `h5 : (r ⊗ₜ[(j : ι) → R j] m i : R i ⊗[(j : ι) → R j] M) = r • ((1 : R i) ⊗ₜ m i)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h5, map_smul, hm i, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]`.

Establish `h2 : (1 : R i) ⊗ₜ[(j : ι) → R j] (x - (Pi.single i r : (j : ι) → R j) • m i) = 0`. Rewrite using `[TensorProduct.tmul_sub, h1, sub_self]`. Establish `h3` using `single_smul_eq_zero i M (hA i) _ h2`. Rewrite `h3` using `[smul_sub, sub_eq_zero, smul_smul]`. Rewrite using `[h3, ← Pi.single_mul, one_mul]`.

Rewrite using `[LinearMap.toSpanSingleton_apply, Finset.smul_sum]`. Establish `hs : ∀ i, (fun i => e i ((1 : R i) ⊗ₜ x) : (j : ι) → R j) • (Pi.single i 1 : (j : ι) → R j) • m i = (Pi.single i 1 : (j : ι) → R j) • x`. Introduce `i`. Rewrite using `[key i, smul_smul]`. Use `congr 1`.

Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.

Rewrite using `[Finset.sum_congr rfl (fun i _ => hs i), ← Finset.sum_smul]`. Establish `h1 : ∑ i, (Pi.single i 1 : (j : ι) → R j) = 1`. Simplify using `using Finset.univ_sum_single (1 : (j : ι) → R j)`. Rewrite using `[h1, one_smul]`. Establish `hbij` using `Module.Invertible.bijective_of_surjective hsurj`.

Conclude with `CommRing.Pic.mk_eq_self.symm.trans (CommRing.Pic.mk_eq_one_iff.mpr ⟨(LinearEquiv.ofBijective _ hbij).symm⟩)`.
-/
theorem eq_one_of_forall (M : CommRing.Pic ((j : ι) → R j))
    (h : ∀ i, CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M = 1) : M = 1 := by
  letI inst : ∀ i, Algebra ((j : ι) → R j) (R i) := fun i => (Pi.evalRingHom R i).toAlgebra
  have hA : ∀ i, algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i := fun i => rfl
  have e : ∀ i, (R i ⊗[(j : ι) → R j] M) ≃ₗ[R i] R i := by
    intro i
    have hi := h i
    rw [← hA i, CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapAlgebra_apply,
      CommRing.Pic.mk_eq_one_iff] at hi
    exact hi.some
  choose m hm using fun i => exists_one_tmul i M (hA i) ((e i).symm 1)
  let m₀ : M := ∑ i, (Pi.single i 1 : (j : ι) → R j) • m i
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ((j : ι) → R j) M m₀) := by
    intro x
    refine ⟨fun i => e i ((1 : R i) ⊗ₜ x), ?_⟩
    have key : ∀ i, (Pi.single i 1 : (j : ι) → R j) • x =
        (Pi.single i (e i ((1 : R i) ⊗ₜ x)) : (j : ι) → R j) • m i := by
      intro i
      set r := e i ((1 : R i) ⊗ₜ x) with hr
      have h1 : (1 : R i) ⊗ₜ[(j : ι) → R j] x =
          (1 : R i) ⊗ₜ ((Pi.single i r : (j : ι) → R j) • m i) := by
        apply (e i).injective
        rw [← TensorProduct.smul_tmul]
        have h0 : (Pi.single i r : (j : ι) → R j) • (1 : R i) = r := by
          rw [Algebra.smul_def, hA i]; simp
        rw [h0]
        have h5 : (r ⊗ₜ[(j : ι) → R j] m i : R i ⊗[(j : ι) → R j] M) = r • ((1 : R i) ⊗ₜ m i) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h5, map_smul, hm i, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      have h2 : (1 : R i) ⊗ₜ[(j : ι) → R j] (x - (Pi.single i r : (j : ι) → R j) • m i) = 0 := by
        rw [TensorProduct.tmul_sub, h1, sub_self]
      have h3 := single_smul_eq_zero i M (hA i) _ h2
      rw [smul_sub, sub_eq_zero, smul_smul] at h3
      rw [h3, ← Pi.single_mul, one_mul]
    rw [LinearMap.toSpanSingleton_apply, Finset.smul_sum]
    have hs : ∀ i, (fun i => e i ((1 : R i) ⊗ₜ x) : (j : ι) → R j) •
        (Pi.single i 1 : (j : ι) → R j) • m i = (Pi.single i 1 : (j : ι) → R j) • x := by
      intro i
      rw [key i, smul_smul]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [Finset.sum_congr rfl (fun i _ => hs i), ← Finset.sum_smul]
    have h1 : ∑ i, (Pi.single i 1 : (j : ι) → R j) = 1 := by
      simpa using Finset.univ_sum_single (1 : (j : ι) → R j)
    rw [h1, one_smul]
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact CommRing.Pic.mk_eq_self.symm.trans
    (CommRing.Pic.mk_eq_one_iff.mpr ⟨(LinearEquiv.ofBijective _ hbij).symm⟩)

end PicPi

/- English proof (translation)
Introduce `ι _ R _ hR M`. Use `haveI := Fintype.ofFinite ι`. Establish `hk : 0 < ∏ i, orderOf (CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M)` using `Finset.prod_pos fun i _ => (hR i _).orderOf_pos`. Use `isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hk, ?_⟩` and prove the remaining obligations. Apply `PicPi.eq_one_of_forall` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[map_pow]`. Conclude with `orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))`.
-/
theorem pic_pi_isOfFinOrder : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)],
    (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) →
      ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  intro ι _ R _ hR M
  classical
  haveI := Fintype.ofFinite ι
  have hk : 0 < ∏ i, orderOf (CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M) :=
    Finset.prod_pos fun i _ => (hR i _).orderOf_pos
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hk, ?_⟩
  apply PicPi.eq_one_of_forall
  intro i
  rw [map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

end GlobalTheory
