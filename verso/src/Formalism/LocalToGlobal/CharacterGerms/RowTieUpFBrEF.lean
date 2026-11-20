import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrS
import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `M hM`. Distinguish the cases in `h0 : ∃ v ∈ M, v ≠ 0`.

Use `swap`. Use `push_neg at h0`. Use `⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun v hv => ?_⟩` and prove the remaining obligations. Simplify using `[h0 v hv]`. Take `⟨v, hvM, hv0⟩` from `h0`.

Take `⟨x₀, hx₀⟩` from `Function.ne_iff.1 hv0`. Take `⟨j, -, hjmax⟩` from `(Finset.univ : Finset (Fin n)).exists_max_image (fun x => vm (v x)) ⟨x₀, Finset.mem_univ _⟩`. Establish `hvj : v j ≠ 0`. Introduce `h`. Establish `h1 : vm (v x₀) ≤ vm (v j)` using `hjmax x₀ (Finset.mem_univ _)`.

Rewrite `h1` using `[h, map_zero]`. Conclude with `hx₀ ((Valuation.zero_iff vm).1 (le_antisymm h1 zero_le'))`. Use `set v₀ : Fin n → C := (v j)⁻¹ • v with hv₀`. Establish `hv₀j : v₀ j = 1` using `by simp [hv₀, hvj]`. Establish `hv₀M : v₀ ∈ M` using `M.smul_mem _ hvM`.

Establish `hv₀le : ∀ x, vm (v₀ x) ≤ 1`. Introduce `x`. Establish `hpos : 0 < vm (v j)` using `pos_iff_ne_zero.2 ((Valuation.ne_zero_iff vm).2 hvj)`. Simplify using `only [hv₀, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]`. Rewrite using `[inv_mul_le_iff₀ hpos, mul_one]`.

Conclude with `hjmax x (Finset.mem_univ _)`. Use `set M' : Submodule C (Fin n → C) := M ⊓ LinearMap.ker (LinearMap.proj j) with hM'`. Establish `hlt : M' < M`. Use `lt_of_le_of_ne inf_le_left fun h => ?_` and prove the remaining obligations. Establish `h1 : v₀ ∈ M'` using `h ▸ hv₀M`.

Establish `h2 : v₀ j = 0` using `(Submodule.mem_inf.1 h1).2`. Rewrite `h2` using `[hv₀j]`. Conclude with `one_ne_zero h2`. Establish `hfr : Module.finrank C M' < k` using `hM ▸ Submodule.finrank_lt_finrank_of_lt hlt`. Take `⟨s, J', B', hB'M, hB'le, hB'δ, hB'span⟩` from `ih _ hfr M' rfl`.

Establish `hB'j : ∀ i, B' i j = 0` using `fun i => (Submodule.mem_inf.1 (hB'M i)).2`. Establish `hB'M0 : ∀ i, B' i ∈ M` using `fun i => (Submodule.mem_inf.1 (hB'M i)).1`. Use `set b : Fin n → C := v₀ - ∑ i, v₀ (J' i) • B' i with hb`. Establish `hbM : b ∈ M` using `M.sub_mem hv₀M (M.sum_mem fun i _ => M.smul_mem _ (hB'M0 i))`. Establish `hbj : b j = 1` using `by simp [hb, Finset.sum_apply, hB'j, hv₀j]`.

Establish `hbJ : ∀ i', b (J' i') = 0`. Introduce `i'`. Simplify using `[hb, Finset.sum_apply, hB'δ]`. Establish `hble : ∀ x, vm (b x) ≤ 1`. Introduce `x`.

Simplify using `only [hb, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Valuation.map_sub_le _ (hv₀le x) (Valuation.map_sum_le _ fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hv₀le _) (hB'le i x)`. Use `⟨s + 1, (Fin.cons j J' : Fin (s + 1) → Fin n), (Fin.cons b B' : Fin (s + 1) → Fin n → C), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simpa using hbM`. Consider the case `succ i => simpa using hB'M0 i`. Introduce `i x`.

Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simpa using hble x`. Consider the case `succ i => simpa using hB'le i x`. Introduce `i i'`. Proceed by induction on `i using Fin.cases with`.

Consider the case `zero`. Proceed by induction on `i' using Fin.cases with`. Consider the case `zero => simp [hbj]`. Consider the case `succ i' => simp only [Fin.cons_zero, Fin.cons_succ, hbJ]`. Rewrite using `[if_neg (Fin.succ_ne_zero i').symm]`.

Consider the case `succ i`. Proceed by induction on `i' using Fin.cases with`. Consider the case `zero => simp only [Fin.cons_zero, Fin.cons_succ, hB'j]`. Rewrite using `[if_neg (Fin.succ_ne_zero i)]`. Consider the case `succ i' => simp [hB'δ, Fin.succ_inj]`.

Introduce `w hw`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Establish `hw' : w - w j • b ∈ M'`. Use `Submodule.mem_inf.2 ⟨M.sub_mem hw (M.smul_mem _ hbM), ?_⟩` and prove the remaining obligations.

Simplify using `[LinearMap.mem_ker, hbj]`. Establish `h1` using `hB'span _ hw'`. Establish `e : ∀ i, (w - w j • b) (J' i) = w (J' i)`. Introduce `i`. Simplify using `[hbJ]`.

Simplify using `only [e] at h1`. Rewrite using `[← h1]`. Normalize the expressions using the abelian group laws.
-/
theorem echelon {C : Type} [Field C] (vm : Valuation C NNReal) (n : ℕ) :
    ∀ (k : ℕ) (M : Submodule C (Fin n → C)), Module.finrank C M = k →
    ∃ (s : ℕ) (J : Fin s → Fin n) (B : Fin s → Fin n → C), (∀ i, B i ∈ M) ∧ (∀ i x, vm (B i x) ≤ 1) ∧
      (∀ i i', B i (J i') = if i = i' then 1 else 0) ∧ ∀ v ∈ M, v = ∑ i, v (J i) • B i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M hM
  by_cases h0 : ∃ v ∈ M, v ≠ 0
  swap
  · push_neg at h0
    refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun v hv => ?_⟩
    simp [h0 v hv]
  obtain ⟨v, hvM, hv0⟩ := h0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hv0
  obtain ⟨j, -, hjmax⟩ := (Finset.univ : Finset (Fin n)).exists_max_image (fun x => vm (v x))
    ⟨x₀, Finset.mem_univ _⟩
  have hvj : v j ≠ 0 := by
    intro h
    have h1 : vm (v x₀) ≤ vm (v j) := hjmax x₀ (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hx₀ ((Valuation.zero_iff vm).1 (le_antisymm h1 zero_le'))

  set v₀ : Fin n → C := (v j)⁻¹ • v with hv₀
  have hv₀j : v₀ j = 1 := by simp [hv₀, hvj]
  have hv₀M : v₀ ∈ M := M.smul_mem _ hvM
  have hv₀le : ∀ x, vm (v₀ x) ≤ 1 := by
    intro x
    have hpos : 0 < vm (v j) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff vm).2 hvj)
    simp only [hv₀, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hjmax x (Finset.mem_univ _)
  set M' : Submodule C (Fin n → C) := M ⊓ LinearMap.ker (LinearMap.proj j) with hM'
  have hlt : M' < M := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h1 : v₀ ∈ M' := h ▸ hv₀M
    have h2 : v₀ j = 0 := (Submodule.mem_inf.1 h1).2
    rw [hv₀j] at h2
    exact one_ne_zero h2
  have hfr : Module.finrank C M' < k := hM ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨s, J', B', hB'M, hB'le, hB'δ, hB'span⟩ := ih _ hfr M' rfl
  have hB'j : ∀ i, B' i j = 0 := fun i => (Submodule.mem_inf.1 (hB'M i)).2
  have hB'M0 : ∀ i, B' i ∈ M := fun i => (Submodule.mem_inf.1 (hB'M i)).1
  set b : Fin n → C := v₀ - ∑ i, v₀ (J' i) • B' i with hb
  have hbM : b ∈ M := M.sub_mem hv₀M (M.sum_mem fun i _ => M.smul_mem _ (hB'M0 i))
  have hbj : b j = 1 := by simp [hb, Finset.sum_apply, hB'j, hv₀j]
  have hbJ : ∀ i', b (J' i') = 0 := by
    intro i'
    simp [hb, Finset.sum_apply, hB'δ]
  have hble : ∀ x, vm (b x) ≤ 1 := by
    intro x
    simp only [hb, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Valuation.map_sub_le _ (hv₀le x) (Valuation.map_sum_le _ fun i _ => ?_)
    rw [map_mul]
    exact mul_le_one' (hv₀le _) (hB'le i x)
  refine ⟨s + 1, (Fin.cons j J' : Fin (s + 1) → Fin n), (Fin.cons b B' : Fin (s + 1) → Fin n → C),
    ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hbM
    | succ i => simpa using hB'M0 i
  · intro i x
    induction i using Fin.cases with
    | zero => simpa using hble x
    | succ i => simpa using hB'le i x
  · intro i i'
    induction i using Fin.cases with
    | zero =>
      induction i' using Fin.cases with
      | zero => simp [hbj]
      | succ i' => simp only [Fin.cons_zero, Fin.cons_succ, hbJ]; rw [if_neg (Fin.succ_ne_zero i').symm]
    | succ i =>
      induction i' using Fin.cases with
      | zero => simp only [Fin.cons_zero, Fin.cons_succ, hB'j]; rw [if_neg (Fin.succ_ne_zero i)]
      | succ i' => simp [hB'δ, Fin.succ_inj]
  · intro w hw
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hw' : w - w j • b ∈ M' := by
      refine Submodule.mem_inf.2 ⟨M.sub_mem hw (M.smul_mem _ hbM), ?_⟩
      simp [LinearMap.mem_ker, hbj]
    have h1 := hB'span _ hw'
    have e : ∀ i, (w - w j • b) (J' i) = w (J' i) := by
      intro i
      simp [hbJ]
    simp only [e] at h1
    rw [← h1]
    abel

/- English proof (translation)
Introduce `C _ vm R _ _ hI n ι L χ`. Use `set f := algebraMap R C`. Set `M : Submodule C (Fin n → C)` to `{ carrier := {w | ∀ a, ((L a).map f).mulVec w = f (χ a) • w} add_mem' := by`. Introduce `w w' hw hw' a`. Simplify using `only [Set.mem_setOf_eq] at hw hw' ⊢`.

Rewrite using `[Matrix.mulVec_add, hw a, hw' a, smul_add]`. Use the proof step `zero_mem' := by`. Introduce `a`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`.

Introduce `c w hw a`. Simplify using `only [Set.mem_setOf_eq] at hw ⊢`. Rewrite using `[Matrix.mulVec_smul, hw a, smul_comm] }`. Take `⟨s, J, B, hBM, hBle, hBδ, hspan⟩` from `echelon vm n _ M rfl`. Establish `hlift : ∀ i x, ∃ r : R, f r = B i x` using `fun i x => hI.exists_of_le_one (hBle i x)`.

Use `choose W hW using hlift`. Establish `hfW : ∀ i, f ∘ W i = B i` using `fun i => funext (hW i)`. Establish `hmap : ∀ (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R), f ∘ (A.mulVec v) = (A.map f).mulVec (f ∘ v)`. Introduce `A v`. Use function extensionality and compare the values at `x`.

Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Establish `hinj : Function.Injective f` using `hI.hom_inj`. Establish `hinjv : ∀ v w : Fin n → R, f ∘ v = f ∘ w → v = w` using `fun v w h => funext fun x => hinj (congrFun h x)`. Use `⟨s, W, fun i a => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Apply `hinjv` to reduce the goal to its premises.

Rewrite using `[hmap, hfW, hBM i a]`. Use function extensionality and compare the values at `x`. Simplify using `[hW]`. Establish `hvM : f ∘ v ∈ M`. Introduce `a`.

Rewrite using `[← hmap, hv a]`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use `⟨fun i => v (J i), ?_, ?_⟩` and prove the remaining obligations. Apply `hinjv` to reduce the goal to its premises.

Establish `h1` using `hspan _ hvM`. Use function extensionality and compare the values at `x`. Establish `hx` using `congrFun h1 x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hx ⊢`. Rewrite using `[map_sum]`.

Simplify using `only [map_mul, hW]`. Conclude with `hx.symm`. Introduce `c hc`. Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun hc (J i)`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← h1]`. Simplify using `[Finset.sum_apply, map_sum, hW, hBδ]`.
-/
theorem eigFreeSt_holds : EigFreeSt := by
  intro C _ vm R _ _ hI n ι L χ
  set f := algebraMap R C
  let M : Submodule C (Fin n → C) :=
    { carrier := {w | ∀ a, ((L a).map f).mulVec w = f (χ a) • w}
      add_mem' := by
        intro w w' hw hw' a
        simp only [Set.mem_setOf_eq] at hw hw' ⊢
        rw [Matrix.mulVec_add, hw a, hw' a, smul_add]
      zero_mem' := by
        intro a
        simp
      smul_mem' := by
        intro c w hw a
        simp only [Set.mem_setOf_eq] at hw ⊢
        rw [Matrix.mulVec_smul, hw a, smul_comm] }
  obtain ⟨s, J, B, hBM, hBle, hBδ, hspan⟩ := echelon vm n _ M rfl
  have hlift : ∀ i x, ∃ r : R, f r = B i x := fun i x => hI.exists_of_le_one (hBle i x)
  choose W hW using hlift
  have hfW : ∀ i, f ∘ W i = B i := fun i => funext (hW i)
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R), f ∘ (A.mulVec v) = (A.map f).mulVec (f ∘ v) := by
    intro A v
    funext x
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hinj : Function.Injective f := hI.hom_inj
  have hinjv : ∀ v w : Fin n → R, f ∘ v = f ∘ w → v = w :=
    fun v w h => funext fun x => hinj (congrFun h x)
  refine ⟨s, W, fun i a => ?_, fun v hv => ?_⟩
  · apply hinjv
    rw [hmap, hfW, hBM i a]
    funext x
    simp [hW]
  · have hvM : f ∘ v ∈ M := by
      intro a
      rw [← hmap, hv a]
      funext x
      simp
    refine ⟨fun i => v (J i), ?_, ?_⟩
    · apply hinjv
      have h1 := hspan _ hvM
      funext x
      have hx := congrFun h1 x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hx ⊢
      rw [map_sum]
      simp only [map_mul, hW]
      exact hx.symm
    · intro c hc
      funext i
      have h1 := congrFun hc (J i)
      apply hinj
      rw [← h1]
      simp [Finset.sum_apply, map_sum, hW, hBδ]

end UpFBr

end Formalism.L2.FormalSeriesBounds
