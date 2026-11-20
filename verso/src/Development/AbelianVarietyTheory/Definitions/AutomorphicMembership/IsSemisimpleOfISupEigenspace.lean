import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

noncomputable section

open Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

section Lin

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
The claim follows from `End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by rw [aeval_algHom_apply, minpoly.aeval, map_zero])`.
-/
theorem isSemisimple_map [FiniteDimensional ℂ V] (φ : End ℂ V →ₐ[ℂ] End ℂ V') {f : End ℂ V}
    (hf : f.IsSemisimple) : (φ f).IsSemisimple :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero])

/- English proof (translation)
Establish `hfin : Set.Finite {α : ℂ | f.HasEigenvalue α}` using `Module.End.finite_hasEigenvalue f`. Use `End.isSemisimple_of_squarefree_aeval_eq_zero (p := ∏ α ∈ hfin.toFinset, (X - C α)) (separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h).squarefree ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_top, eq_top_iff, ← hf]`. Use `iSup_le fun α v hv => ?_` and prove the remaining obligations. Distinguish the cases in `hα : f.HasEigenvalue α`.

Rewrite using `[LinearMap.mem_ker, ← Finset.prod_erase_mul _ _ (hfin.mem_toFinset.mpr hα), map_mul, End.mul_apply]`. Establish `: aeval f (X - C α) v = 0`. Simplify using `[End.mem_eigenspace_iff.mp hv]`. Rewrite using `[this, map_zero]`. Rewrite `hα` using `[End.hasEigenvalue_iff, not_not]`.

Rewrite `hv` using `[hα, Submodule.mem_bot]`. Rewrite using `[hv]`. Conclude with `zero_mem _`.
-/
theorem isSemisimple_of_iSup_eigenspace [FiniteDimensional ℂ V] {f : End ℂ V}
    (hf : ⨆ α, f.eigenspace α = ⊤) : f.IsSemisimple := by
  classical
  have hfin : Set.Finite {α : ℂ | f.HasEigenvalue α} := Module.End.finite_hasEigenvalue f
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := ∏ α ∈ hfin.toFinset, (X - C α))
    (separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h).squarefree ?_
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← hf]
  refine iSup_le fun α v hv => ?_
  by_cases hα : f.HasEigenvalue α
  · rw [LinearMap.mem_ker, ← Finset.prod_erase_mul _ _ (hfin.mem_toFinset.mpr hα), map_mul,
      End.mul_apply]
    have : aeval f (X - C α) v = 0 := by
      simp [End.mem_eigenspace_iff.mp hv]
    rw [this, map_zero]
  · rw [End.hasEigenvalue_iff, not_not] at hα
    rw [hα, Submodule.mem_bot] at hv
    rw [hv]; exact zero_mem _

/- English proof (translation)
Use `isSemisimple_of_iSup_eigenspace ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← Submodule.prod_top, ← hf.iSup_eigenspace_eq_top, ← hg.iSup_eigenspace_eq_top, LinearMap.prod_eq_sup_map, Submodule.map_iSup, Submodule.map_iSup]`. Use `sup_le (iSup_mono fun α => ?_) (iSup_mono fun α => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify `hv` using `[End.mem_eigenspace_iff]`.

Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify `hv` using `[End.mem_eigenspace_iff]`.
-/
theorem isSemisimple_prodMap [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {f : End ℂ V}
    {g : End ℂ V'} (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (f.prodMap g : End ℂ (V × V')) := by
  refine isSemisimple_of_iSup_eigenspace ?_
  rw [eq_top_iff, ← Submodule.prod_top, ← hf.iSup_eigenspace_eq_top, ← hg.iSup_eigenspace_eq_top,
    LinearMap.prod_eq_sup_map, Submodule.map_iSup, Submodule.map_iSup]
  refine sup_le (iSup_mono fun α => ?_) (iSup_mono fun α => ?_)
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv
  · rintro _ ⟨v, hv, rfl⟩
    simpa [End.mem_eigenspace_iff] using hv

/- English proof (translation)
Establish `h1 : End.IsSemisimple (f.rTensor V' : End ℂ (V ⊗[ℂ] V'))` using `isSemisimple_map (End.rTensorAlgHom ℂ V V') hf`. Establish `h2 : End.IsSemisimple (g.lTensor V : End ℂ (V ⊗[ℂ] V'))` using `isSemisimple_map (End.lTensorAlgHom ℂ V' V) hg`. Establish `e : (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) = f.rTensor V' * g.lTensor V` using `by ext; simp`. Rewrite using `[e]`. Use `End.IsSemisimple.mul_of_commute ?_ h1 h2` and prove the remaining obligations.

Use `show _ = _`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem isSemisimple_tensorMap [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {f : End ℂ V}
    {g : End ℂ V'} (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) := by
  have h1 : End.IsSemisimple (f.rTensor V' : End ℂ (V ⊗[ℂ] V')) :=
    isSemisimple_map (End.rTensorAlgHom ℂ V V') hf
  have h2 : End.IsSemisimple (g.lTensor V : End ℂ (V ⊗[ℂ] V')) :=
    isSemisimple_map (End.lTensorAlgHom ℂ V' V) hg
  have e : (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) = f.rTensor V' * g.lTensor V := by
    ext; simp
  rw [e]
  refine End.IsSemisimple.mul_of_commute ?_ h1 h2
  show _ = _
  ext; simp

/- English proof (translation)
Establish `hp : ∀ n : ℕ, (f.dualMap : End ℂ (Dual ℂ V)) ^ n = (f ^ n : End ℂ V).dualMap`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => ext`. Simplify using the standard rewrite rules.

Consider the case `succ n ih => rw [pow_succ, ih, pow_succ']`. Use `ext`. Simplify using the standard rewrite rules. Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`.

Use `ext`. Simplify using the standard rewrite rules. Consider the case `monomial n a => rw [aeval_monomial, aeval_monomial, hp]`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem aeval_dualMap (f : End ℂ V) (p : ℂ[X]) :
    aeval (f.dualMap : End ℂ (Dual ℂ V)) p = (aeval f p : End ℂ V).dualMap := by
  have hp : ∀ n : ℕ, (f.dualMap : End ℂ (Dual ℂ V)) ^ n = (f ^ n : End ℂ V).dualMap := by
    intro n
    induction n with
    | zero => ext; simp
    | succ n ih => rw [pow_succ, ih, pow_succ']; ext; simp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]; ext; simp
  | monomial n a => rw [aeval_monomial, aeval_monomial, hp]; ext; simp

/- English proof (translation)
The claim follows from `End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by rw [aeval_dualMap, minpoly.aeval]; ext; simp)`.
-/
theorem isSemisimple_dualMap [FiniteDimensional ℂ V] {f : End ℂ V} (hf : f.IsSemisimple) :
    End.IsSemisimple (f.dualMap : End ℂ (Dual ℂ V)) :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by
    rw [aeval_dualMap, minpoly.aeval]; ext; simp)

def diagEnd {ι : Type*} (c : ι → ℂ) : End ℂ (ι → ℂ) where
  toFun v i := c i * v i
  map_add' v v' := by ext; simp [mul_add]
  map_smul' a v := by ext; simp [mul_left_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem diagEnd_apply {ι : Type*} (c v : ι → ℂ) (i : ι) : diagEnd c v i = c i * v i := rfl

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `isSemisimple_of_iSup_eigenspace (eq_top_iff.mpr fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.univ_sum_single v]`. Use `Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (c i) ?_` and prove the remaining obligations. Rewrite using `[End.mem_eigenspace_iff]`.

Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.
-/
theorem isSemisimple_diagEnd {ι : Type*} [Finite ι] (c : ι → ℂ) : (diagEnd c).IsSemisimple := by
  classical
  have := Fintype.ofFinite ι
  refine isSemisimple_of_iSup_eigenspace (eq_top_iff.mpr fun v _ => ?_)
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (c i) ?_
  rw [End.mem_eigenspace_iff]
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/- English proof (translation)
Establish `e : diagEnd c = Matrix.toLin' (Matrix.diagonal c)`. Use `LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations. Simplify using `[Matrix.mulVec_diagonal]`. Rewrite using `[e, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]`.
-/
theorem charpoly_diagEnd {ι : Type*} [Fintype ι] (c : ι → ℂ) :
    (diagEnd c).charpoly = ∏ i, (X - C (c i)) := by
  classical
  have e : diagEnd c = Matrix.toLin' (Matrix.diagonal c) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [Matrix.mulVec_diagonal]
  rw [e, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

def absSpace (f : End ℂ V) (r : ℝ) : Submodule ℂ V := ⨆ (α : ℂ) (_ : ‖α‖ = r), f.eigenspace α

/- English proof (translation)
Simplify using `only [absSpace, Submodule.map_iSup]`. Use `iSup₂_mono fun α _ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite `hv` using `[SetLike.mem_coe, End.mem_eigenspace_iff]`. Rewrite using `[End.mem_eigenspace_iff, ← he, hv, map_smul]`.
-/
theorem map_absSpace_le {f : End ℂ V} {g : End ℂ V'} (e : V →ₗ[ℂ] V') (he : ∀ v, e (f v) = g (e v))
    (r : ℝ) : (absSpace f r).map e ≤ absSpace g r := by
  simp only [absSpace, Submodule.map_iSup]
  refine iSup₂_mono fun α _ => ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, End.mem_eigenspace_iff] at hv
  rw [End.mem_eigenspace_iff, ← he, hv, map_smul]

/- English proof (translation)
Use `⟨fun hv => ?_, fun hv => map_absSpace_le e.toLinearMap he r ⟨v, hv, rfl⟩⟩` and prove the remaining obligations. Use `map_absSpace_le (f := g) (g := f) e.symm.toLinearMap (fun x => by simp [e.symm_apply_eq, he]) r ⟨_, hv, rfl⟩` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_absSpace_iff {f : End ℂ V} {g : End ℂ V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ v, e (f v) = g (e v)) (r : ℝ) (v : V) : e v ∈ absSpace g r ↔ v ∈ absSpace f r := by
  refine ⟨fun hv => ?_, fun hv => map_absSpace_le e.toLinearMap he r ⟨v, hv, rfl⟩⟩
  have := map_absSpace_le (f := g) (g := f) e.symm.toLinearMap
    (fun x => by simp [e.symm_apply_eq, he]) r ⟨_, hv, rfl⟩
  simpa using this

def IsPurePair (q : ℝ) (f N : End ℂ V) : Prop :=
  ⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2)) = ⊤ ∧
    ∀ i : ℕ, Set.BijOn (N ^ i) (absSpace f (q ^ (-(i : ℝ) / 2))) (absSpace f (q ^ ((i : ℝ) / 2)))

/- English proof (translation)
Establish `hpow : ∀ (i : ℕ) v, e ((N ^ i) v) = (M ^ i) (e v)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => intro v`.

Rewrite using `[pow_succ, pow_succ, End.mul_apply, End.mul_apply, ih, hN]`. Use `⟨?_, fun i => ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← LinearEquiv.range e, LinearMap.range_eq_map, ← hp.1, Submodule.map_iSup]`. Conclude with `iSup_mono fun i => map_absSpace_le e.toLinearMap he _`. Take `⟨v, rfl⟩` from `e.surjective v`.

Rewrite `hv` using `[SetLike.mem_coe, mem_absSpace_iff e he]`. Rewrite using `[SetLike.mem_coe, ← hpow, mem_absSpace_iff e he]`. Conclude with `(hp.2 i).1 hv`. Take `⟨v, rfl⟩` from `e.surjective v`. Take `⟨v', rfl⟩` from `e.surjective v'`.

Rewrite `hv`, `hv'` using `[SetLike.mem_coe, mem_absSpace_iff e he]`. Rewrite `hvv` using `[← hpow, ← hpow]`. Rewrite using `[(hp.2 i).2.1 hv hv' (e.injective hvv)]`. Take `⟨v, rfl⟩` from `e.surjective v`. Rewrite `hv` using `[SetLike.mem_coe, mem_absSpace_iff e he]`.

Take `⟨u, hu, rfl⟩` from `(hp.2 i).2.2 hv`. Conclude with `⟨e u, (mem_absSpace_iff e he _ u).mpr hu, (hpow i u).symm⟩`.
-/
theorem IsPurePair.of_equiv {q : ℝ} {f N : End ℂ V} {g M : End ℂ V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ v, e (f v) = g (e v)) (hN : ∀ v, e (N v) = M (e v)) (hp : IsPurePair q f N) :
    IsPurePair q g M := by
  have hpow : ∀ (i : ℕ) v, e ((N ^ i) v) = (M ^ i) (e v) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro v; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, ih, hN]
  refine ⟨?_, fun i => ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩⟩
  · rw [eq_top_iff, ← LinearEquiv.range e, LinearMap.range_eq_map, ← hp.1, Submodule.map_iSup]
    exact iSup_mono fun i => map_absSpace_le e.toLinearMap he _
  · obtain ⟨v, rfl⟩ := e.surjective v
    rw [SetLike.mem_coe, mem_absSpace_iff e he] at hv
    rw [SetLike.mem_coe, ← hpow, mem_absSpace_iff e he]
    exact (hp.2 i).1 hv
  · obtain ⟨v, rfl⟩ := e.surjective v
    obtain ⟨v', rfl⟩ := e.surjective v'
    rw [SetLike.mem_coe, mem_absSpace_iff e he] at hv hv'
    rw [← hpow, ← hpow] at hvv
    rw [(hp.2 i).2.1 hv hv' (e.injective hvv)]
  · obtain ⟨v, rfl⟩ := e.surjective v
    rw [SetLike.mem_coe, mem_absSpace_iff e he] at hv
    obtain ⟨u, hu, rfl⟩ := (hp.2 i).2.2 hv
    exact ⟨e u, (mem_absSpace_iff e he _ u).mpr hu, (hpow i u).symm⟩

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `hv i hi`. Establish `hle : absSpace (diagEnd c) r ≤ LinearMap.ker (LinearMap.proj i : (ι → ℂ) →ₗ[ℂ] ℂ)`. Use `iSup₂_le fun α hα u hu => ?_` and prove the remaining obligations.

Establish `h1` using `congrFun (End.mem_eigenspace_iff.mp hu) i`. Simplify using `only [diagEnd_apply, Pi.smul_apply, smul_eq_mul] at h1`. Establish `h2 : c i ≠ α` using `fun h => hi (h ▸ hα)`. Simplify `h1` using `[h2]`. Conclude with `hle hv`.

Introduce `hv`. Rewrite using `[← Finset.univ_sum_single v]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : ‖c i‖ = r`. Use `Submodule.mem_iSup_of_mem (c i) (Submodule.mem_iSup_of_mem hi ?_)` and prove the remaining obligations.

Rewrite using `[End.mem_eigenspace_iff]`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hj]`. Simplify using `[hv i hi]`.
-/
theorem mem_absSpace_diagEnd {ι : Type*} [Finite ι] (c : ι → ℂ) (r : ℝ) (v : ι → ℂ) :
    v ∈ absSpace (diagEnd c) r ↔ ∀ i, ‖c i‖ ≠ r → v i = 0 := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · intro hv i hi
    have hle : absSpace (diagEnd c) r ≤ LinearMap.ker (LinearMap.proj i : (ι → ℂ) →ₗ[ℂ] ℂ) := by
      refine iSup₂_le fun α hα u hu => ?_
      have h1 := congrFun (End.mem_eigenspace_iff.mp hu) i
      simp only [diagEnd_apply, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : c i ≠ α := fun h => hi (h ▸ hα)
      simpa [h2] using h1
    exact hle hv
  · intro hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ‖c i‖ = r
    · refine Submodule.mem_iSup_of_mem (c i) (Submodule.mem_iSup_of_mem hi ?_)
      rw [End.mem_eigenspace_iff]
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    · simp [hv i hi]

def shiftEnd (n : ℕ) : End ℂ (Fin n → ℂ) where
  toFun v i := if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0
  map_add' v v' := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]
  map_smul' a v := by ext i; by_cases hi : 1 ≤ (i : ℕ) <;> simp [hi]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shiftEnd_apply {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    shiftEnd n v i = if 1 ≤ (i : ℕ) then v ⟨i - 1, by omega⟩ else 0 := rfl

/- English proof (translation)
Proceed by induction on `k generalizing i with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', End.mul_apply, shiftEnd_apply]`. Distinguish the cases in `h1 : 1 ≤ (i : ℕ)`.

Rewrite using `[if_pos h1, ih]`. Distinguish the cases in `h2 : k + 1 ≤ (i : ℕ)`. Rewrite using `[if_pos h2, if_pos (by simp only; omega)]`. Use `congr 2`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h2, if_neg (by simp only; omega)]`. Rewrite using `[if_neg h1, if_neg (by omega)]`.
-/
theorem shiftEnd_pow_apply {n : ℕ} (k : ℕ) (v : Fin n → ℂ) (i : Fin n) :
    (shiftEnd n ^ k) v i = if k ≤ (i : ℕ) then v ⟨i - k, by omega⟩ else 0 := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', End.mul_apply, shiftEnd_apply]
    by_cases h1 : 1 ≤ (i : ℕ)
    · rw [if_pos h1, ih]
      by_cases h2 : k + 1 ≤ (i : ℕ)
      · rw [if_pos h2, if_pos (by simp only; omega)]
        congr 2
        simp only; omega
      · rw [if_neg h2, if_neg (by simp only; omega)]
    · rw [if_neg h1, if_neg (by omega)]

/- English proof (translation)
Assemble the required witnesses or components as `⟨n, LinearMap.ext fun v => funext fun i => by rw [shiftEnd_pow_apply, if_neg (by omega)]; rfl⟩`.
-/
theorem isNilpotent_shiftEnd (n : ℕ) : IsNilpotent (shiftEnd n) :=
  ⟨n, LinearMap.ext fun v => funext fun i => by
    rw [shiftEnd_pow_apply, if_neg (by omega)]; rfl⟩

/- English proof (translation)
Introduce `h0`. Use `congrFun (LinearMap.congr_fun h0 (fun _ => 1)) ⟨1, by omega⟩` as an intermediate fact. Simplify using `[shiftEnd_apply] at this`.
-/
theorem shiftEnd_ne_zero {n : ℕ} (hn : 2 ≤ n) : shiftEnd n ≠ 0 := by
  intro h0
  have := congrFun (LinearMap.congr_fun h0 (fun _ => 1)) ⟨1, by omega⟩
  simp [shiftEnd_apply] at this

/- English proof (translation)
Establish `hmem : ∀ (j : ℤ) (v : Fin n → ℂ), v ∈ absSpace (diagEnd c) (q ^ ((j : ℝ) / 2)) ↔ ∀ i : Fin n, 2 * ((i : ℕ) : ℤ) + 1 - n ≠ j → v i = 0`. Introduce `j v`. Rewrite using `[mem_absSpace_diagEnd]`. Use `forall_congr' fun i => imp_congr_left (not_congr ?_)` and prove the remaining obligations. Rewrite using `[hc, Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne', ← @Int.cast_inj ℝ]`.

Use `push_cast`. Apply the tactic sequence `constructor <;> intro h <;> linarith`. Use `⟨eq_top_iff.mpr fun v _ => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.univ_sum_single v]`. Use `Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem (2 * ((i : ℕ) : ℤ) + 1 - n) ((hmem _ _).mpr fun j hj => ?_)` and prove the remaining obligations.

Rewrite using `[Pi.single_eq_of_ne]`. Introduce and unpack `rfl`. Conclude with `hj rfl`. Establish `e1 : (-(k : ℝ) / 2) = ((-(k : ℤ) : ℤ) : ℝ) / 2` using `by push_cast; ring`. Establish `e2 : ((k : ℝ) / 2) = (((k : ℤ) : ℤ) : ℝ) / 2` using `by push_cast; ring`.

Rewrite using `[e1, e2]`. Use `⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[SetLike.mem_coe, hmem]`. Introduce `i hi`. Rewrite using `[shiftEnd_pow_apply]`.

Use `split_ifs with hk`. Conclude with `hv _ (by simp only; omega)`. Both sides reduce to the same expression. Rewrite `hv`, `hv'` using `[SetLike.mem_coe, hmem]`. Use extensionality with `i`.

Distinguish the cases in `hi : 2 * ((i : ℕ) : ℤ) + 1 - n = -(k : ℤ)`. Use `congrFun hvv ⟨i + k, by omega⟩` as an intermediate fact. Rewrite `this` using `[shiftEnd_pow_apply, shiftEnd_pow_apply, if_pos (by simp), if_pos (by simp)]`. Simplify using `using this`. Rewrite using `[hv i hi, hv' i hi]`.

Rewrite `hv` using `[SetLike.mem_coe, hmem]`. Use `⟨fun i => if hi : (i : ℕ) + k < n then v ⟨i + k, hi⟩ else 0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hmem]`. Introduce `i hi`. Use `split_ifs with hk`.

Conclude with `hv _ (by simp only; omega)`. Both sides reduce to the same expression. Use extensionality with `i`. Rewrite using `[shiftEnd_pow_apply]`. Use `split_ifs with hk h2`.

Use `congr 2`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Conclude with `(hv i (by omega)).symm`.
-/
theorem isPurePair_diagEnd_shiftEnd {q : ℝ} (hq : 1 < q) {n : ℕ} (c : Fin n → ℂ)
    (hc : ∀ i : Fin n, ‖c i‖ = q ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)) :
    IsPurePair q (diagEnd c) (shiftEnd n) := by
  classical
  have hmem : ∀ (j : ℤ) (v : Fin n → ℂ), v ∈ absSpace (diagEnd c) (q ^ ((j : ℝ) / 2)) ↔
      ∀ i : Fin n, 2 * ((i : ℕ) : ℤ) + 1 - n ≠ j → v i = 0 := by
    intro j v
    rw [mem_absSpace_diagEnd]
    refine forall_congr' fun i => imp_congr_left (not_congr ?_)
    rw [hc, Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne', ← @Int.cast_inj ℝ]
    push_cast
    constructor <;> intro h <;> linarith
  refine ⟨eq_top_iff.mpr fun v _ => ?_, fun k => ?_⟩
  · rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem (2 * ((i : ℕ) : ℤ) + 1 - n) ((hmem _ _).mpr fun j hj => ?_)
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact hj rfl
  · have e1 : (-(k : ℝ) / 2) = ((-(k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    have e2 : ((k : ℝ) / 2) = (((k : ℤ) : ℤ) : ℝ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩
    · rw [SetLike.mem_coe, hmem] at hv ⊢
      intro i hi
      rw [shiftEnd_pow_apply]
      split_ifs with hk
      · exact hv _ (by simp only; omega)
      · rfl
    · rw [SetLike.mem_coe, hmem] at hv hv'
      ext i
      by_cases hi : 2 * ((i : ℕ) : ℤ) + 1 - n = -(k : ℤ)
      · have := congrFun hvv ⟨i + k, by omega⟩
        rw [shiftEnd_pow_apply, shiftEnd_pow_apply, if_pos (by simp), if_pos (by simp)] at this
        simpa using this
      · rw [hv i hi, hv' i hi]
    · rw [SetLike.mem_coe, hmem] at hv
      refine ⟨fun i => if hi : (i : ℕ) + k < n then v ⟨i + k, hi⟩ else 0, ?_, ?_⟩
      · rw [SetLike.mem_coe, hmem]
        intro i hi
        split_ifs with hk
        · exact hv _ (by simp only; omega)
        · rfl
      · ext i
        rw [shiftEnd_pow_apply]
        split_ifs with hk h2
        · congr 2
          simp only; omega
        · exfalso; apply h2; simp only; omega
        · exact (hv i (by omega)).symm

end Lin

end GlobalTheory.WeilDeligne
