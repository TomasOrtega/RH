import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagMatLower

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def cellMat (b g : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) : Matrix (Fin m) (Fin m) k :=
  fun c a => (b i).repr (g i (Fin.castLE hm a)) (Fin.castLE hm c)

/- English proof (translation)
Establish `hinj : Function.Injective (Fin.castLE hm)` using `Fin.castLE_injective hm`. Establish `hrepr (x : Fin m → k) (c : Fin (finrank k (V i))) : (b i).repr (∑ a, x a • g i (Fin.castLE hm a)) c = ∑ a, (b i).repr (g i (Fin.castLE hm a)) c * x a`. Simplify using `[map_sum, Finsupp.finset_sum_apply, mul_comm]`. Prove the components needed by the constructor for the conclusion. Introduce `hd h0`.

Take `⟨x, hx, hMx⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `h1 : (∑ a, x a • g i (Fin.castLE hm a)) ∈ g.flags.step i m` using `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (step_flags_le.1 le_rfl _ (by simp))`. Establish `h2 : (∑ a, x a • g i (Fin.castLE hm a)) ∈ Submodule.span k (b i '' {a | m ≤ (a : ℕ)})`. Rewrite using `[Basis.mem_span_image]`. Introduce `c hc`.

Assume the negation of the conclusion as `hlt`. Establish `hlt' : (c : ℕ) < m` using `not_le.1 hlt`. Use `(Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hc)) ?_` and prove the remaining obligations. Rewrite using `[hrepr]`. Conclude with `congrFun hMx ⟨c, hlt'⟩`.

Establish `h3` using `Submodule.disjoint_def.1 hd _ h1 h2`. Conclude with `hx (funext (Fintype.linearIndependent_iff.1 ((g i).linearIndependent.comp _ hinj) x h3))`. Introduce `hd`. Rewrite using `[Submodule.disjoint_def]`. Introduce `v h1 h2`.

Establish `h1'` using `mem_step_flags.1 h1`. Establish `hv : v = ∑ a, (g i).repr v (Fin.castLE hm a) • g i (Fin.castLE hm a)` using `by conv_lhs => rw [← (g i).sum_repr v]`. Use `symm`. Use `Fintype.sum_of_injective _ hinj _ _ (fun a ha => ?_) fun a => rfl` and prove the remaining obligations. Establish `: m ≤ (a : ℕ)`.

Assume the negation of the conclusion as `hlt`. Conclude with `ha ⟨⟨a, not_le.1 hlt⟩, Fin.ext rfl⟩`. Rewrite using `[h1' a this, zero_smul]`. Establish `hMx : (cellMat b g i m hm).mulVec (fun a => (g i).repr v (Fin.castLE hm a)) = 0`. Use function extensionality and compare the values at `c`.

Establish `h0 : (b i).repr v (Fin.castLE hm c) = 0`. Assume the negation of the conclusion as `hne`. Use `((b i).mem_span_image.1 h2) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))` as an intermediate fact. Establish `hc` using `c.2`. Simplify using `only [Set.mem_setOf_eq, Fin.val_castLE] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite `h0` using `[hv, hrepr]`. Simplify `h0` using `[Matrix.mulVec, dotProduct, cellMat]`. Establish `hx` using `Matrix.eq_zero_of_mulVec_eq_zero hd hMx`. Rewrite using `[hv]`.

Conclude with `Finset.sum_eq_zero fun a _ => by rw [congrFun hx a, Pi.zero_apply, zero_smul]`.
-/
theorem disjoint_step_iff_det_ne_zero (b g : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) :
    Disjoint (g.flags.step i m) (Submodule.span k (b i '' {a | m ≤ (a : ℕ)})) ↔
      (cellMat b g i m hm).det ≠ 0 := by
  have hinj : Function.Injective (Fin.castLE hm) := Fin.castLE_injective hm
  have hrepr (x : Fin m → k) (c : Fin (finrank k (V i))) :
      (b i).repr (∑ a, x a • g i (Fin.castLE hm a)) c =
        ∑ a, (b i).repr (g i (Fin.castLE hm a)) c * x a := by
    simp [map_sum, Finsupp.finset_sum_apply, mul_comm]
  constructor
  · intro hd h0
    obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : (∑ a, x a • g i (Fin.castLE hm a)) ∈ g.flags.step i m :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
        (step_flags_le.1 le_rfl _ (by simp))
    have h2 : (∑ a, x a • g i (Fin.castLE hm a)) ∈
        Submodule.span k (b i '' {a | m ≤ (a : ℕ)}) := by
      rw [Basis.mem_span_image]
      intro c hc
      by_contra hlt
      have hlt' : (c : ℕ) < m := not_le.1 hlt
      refine (Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hc)) ?_
      rw [hrepr]
      exact congrFun hMx ⟨c, hlt'⟩
    have h3 := Submodule.disjoint_def.1 hd _ h1 h2
    exact hx (funext (Fintype.linearIndependent_iff.1
      ((g i).linearIndependent.comp _ hinj) x h3))
  · intro hd
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h1' := mem_step_flags.1 h1
    have hv : v = ∑ a, (g i).repr v (Fin.castLE hm a) • g i (Fin.castLE hm a) := by
      conv_lhs => rw [← (g i).sum_repr v]
      symm
      refine Fintype.sum_of_injective _ hinj _ _ (fun a ha => ?_) fun a => rfl
      have : m ≤ (a : ℕ) := by
        by_contra hlt
        exact ha ⟨⟨a, not_le.1 hlt⟩, Fin.ext rfl⟩
      rw [h1' a this, zero_smul]
    have hMx : (cellMat b g i m hm).mulVec (fun a => (g i).repr v (Fin.castLE hm a)) = 0 := by
      funext c
      have h0 : (b i).repr v (Fin.castLE hm c) = 0 := by
        by_contra hne
        have := ((b i).mem_span_image.1 h2) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
        have hc := c.2
        simp only [Set.mem_setOf_eq, Fin.val_castLE] at this
        omega
      rw [hv, hrepr] at h0
      simpa [Matrix.mulVec, dotProduct, cellMat] using h0
    have hx := Matrix.eq_zero_of_mulVec_eq_zero hd hMx
    rw [hv]
    exact Finset.sum_eq_zero fun a _ => by rw [congrFun hx a, Pi.zero_apply, zero_smul]

/- English proof (translation)
Establish `h : (fun g : Frames k V => (cellMat b g i m hm).det) = ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : k) • ∏ c, fun g : Frames k V => (b i).coord (Fin.castLE hm (σ c)) (g i (Fin.castLE hm c))`. Use function extensionality and compare the values at `g`. Simplify using `[Matrix.det_apply', Finset.sum_apply, Finset.prod_apply, cellMat]`. Rewrite using `[h]`. Conclude with `Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun c _ => Algebra.subset_adjoin (.inl ⟨i, _, _, rfl⟩)) _`.
-/
theorem det_cellMat_mem_regFns (b : Frames k V) (i : ι) (m : ℕ) (hm : m ≤ finrank k (V i)) :
    (fun g : Frames k V => (cellMat b g i m hm).det) ∈ regFns k V := by
  have h : (fun g : Frames k V => (cellMat b g i m hm).det) =
      ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : k) •
        ∏ c, fun g : Frames k V => (b i).coord (Fin.castLE hm (σ c)) (g i (Fin.castLE hm c)) := by
    funext g
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply, cellMat]
  rw [h]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun c _ =>
    Algebra.subset_adjoin (.inl ⟨i, _, _, rfl⟩)) _

/- English proof (translation)
Use `isOpen_coinduced.2 ?_` and prove the remaining obligations. Establish `h : Frames.flags ⁻¹' bigCell b = ⋂ i, ⋂ m : Fin (finrank k (V i) + 1), {g : Frames k V | (cellMat b g i m (Nat.lt_succ_iff.1 m.2)).det ≠ 0}`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, bigCell, Set.mem_setOf_eq, Set.mem_iInter]`. Use `⟨fun hg i m => (disjoint_step_iff_det_ne_zero b g i m _).1 (hg i m), fun hg i m => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hm : m ≤ finrank k (V i)`. Conclude with `(disjoint_step_iff_det_ne_zero b g i m hm).2 (hg i ⟨m, Nat.lt_succ_iff.2 hm⟩)`. Establish `he : {a : Fin (finrank k (V i)) | m ≤ (a : ℕ)} = ∅` using `Set.eq_empty_of_forall_notMem fun a ha => hm (le_trans ha a.2.le)`. Rewrite using `[he, Set.image_empty, Submodule.span_empty]`. Conclude with `disjoint_bot_right`.

Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun m => isOpen_generateFrom_of_mem ⟨_, det_cellMat_mem_regFns b i m _, rfl⟩`.
-/
theorem isOpen_bigCell (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (b : Frames k V) : IsOpen (bigCell b) := by
  refine isOpen_coinduced.2 ?_
  have h : Frames.flags ⁻¹' bigCell b = ⋂ i, ⋂ m : Fin (finrank k (V i) + 1),
      {g : Frames k V | (cellMat b g i m (Nat.lt_succ_iff.1 m.2)).det ≠ 0} := by
    ext g
    simp only [Set.mem_preimage, bigCell, Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun hg i m => (disjoint_step_iff_det_ne_zero b g i m _).1 (hg i m), fun hg i m => ?_⟩
    by_cases hm : m ≤ finrank k (V i)
    · exact (disjoint_step_iff_det_ne_zero b g i m hm).2 (hg i ⟨m, Nat.lt_succ_iff.2 hm⟩)
    · have he : {a : Fin (finrank k (V i)) | m ≤ (a : ℕ)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun a ha => hm (le_trans ha a.2.le)
      rw [he, Set.image_empty, Submodule.span_empty]
      exact disjoint_bot_right
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun m =>
    isOpen_generateFrom_of_mem ⟨_, det_cellMat_mem_regFns b i m _, rfl⟩

/- English proof (translation)
Introduce `k _ ι _ V _ _ _ b` and use `isOpen_bigCell k ι V b`.
-/
example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpen (bigCell b) :=
  fun k _ ι _ V _ _ _ b => isOpen_bigCell k ι V b

end GlobalTheory.FlagPts
