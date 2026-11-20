import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExists

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Unfold `FlagG.coefX`. Conclude with `dif_pos hx`.
-/
theorem coefX_of_mem (F : FlagG S r T) (x : S.V) (hx : x ∈ Submodule.span E (Set.range F.e))
    (k : Fin r) : F.coefX x k = F.e_indep.repr ⟨x, hx⟩ k := by
  unfold FlagG.coefX
  exact dif_pos hx

/- English proof (translation)
Rewrite using `[coefX_of_mem F _ (F.X.add_mem hx hy), coefX_of_mem F _ hx, coefX_of_mem F _ hy]`. Establish `: (⟨x + y, F.X.add_mem hx hy⟩ : Submodule.span E (Set.range F.e)) = ⟨x, hx⟩ + ⟨y, hy⟩` using `rfl`. Rewrite using `[this, map_add, Finsupp.add_apply]`.
-/
theorem coefX_add' (F : FlagG S r T) (x y : S.V) (k : Fin r) (hx : x ∈ F.X) (hy : y ∈ F.X) :
    F.coefX (x + y) k = F.coefX x k + F.coefX y k := by
  rw [coefX_of_mem F _ (F.X.add_mem hx hy), coefX_of_mem F _ hx, coefX_of_mem F _ hy]
  have : (⟨x + y, F.X.add_mem hx hy⟩ : Submodule.span E (Set.range F.e)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add, Finsupp.add_apply]

/- English proof (translation)
Rewrite using `[coefX_of_mem F _ (F.X.smul_mem a hx), coefX_of_mem F _ hx]`. Establish `: (⟨a • x, F.X.smul_mem a hx⟩ : Submodule.span E (Set.range F.e)) = a • ⟨x, hx⟩` using `rfl`. Rewrite using `[this, map_smul, Finsupp.smul_apply, smul_eq_mul]`.
-/
theorem coefX_smul' (F : FlagG S r T) (a : E) (x : S.V) (k : Fin r) (hx : x ∈ F.X) :
    F.coefX (a • x) k = a * F.coefX x k := by
  rw [coefX_of_mem F _ (F.X.smul_mem a hx), coefX_of_mem F _ hx]
  have : (⟨a • x, F.X.smul_mem a hx⟩ : Submodule.span E (Set.range F.e)) = a • ⟨x, hx⟩ := rfl
  rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem e_mem_X (F : FlagG S r T) (j : Fin r) : F.e j ∈ F.X :=
  Submodule.subset_span ⟨j, rfl⟩

/- English proof (translation)
Rewrite using `[coefX_of_mem F _ (e_mem_X F j), F.e_indep.repr_eq_single j _ rfl, Finsupp.single_apply]`.
-/
theorem coefX_e' (F : FlagG S r T) (j k : Fin r) :
    F.coefX (F.e j) k = if j = k then 1 else 0 := by
  rw [coefX_of_mem F _ (e_mem_X F j), F.e_indep.repr_eq_single j _ rfl, Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[coefX_of_mem F _ F.X.zero_mem]`. Establish `: (⟨0, F.X.zero_mem⟩ : Submodule.span E (Set.range F.e)) = 0` using `rfl`. Rewrite using `[this, map_zero, Finsupp.zero_apply]`.
-/
theorem coefX_zero' (F : FlagG S r T) (k : Fin r) : F.coefX 0 k = 0 := by
  rw [coefX_of_mem F _ F.X.zero_mem]
  have : (⟨0, F.X.zero_mem⟩ : Submodule.span E (Set.range F.e)) = 0 := rfl
  rw [this, map_zero, Finsupp.zero_apply]

/- English proof (translation)
Unfold `FlagG.Xa FlagG.X`. Conclude with `Submodule.span_mono (by rintro _ ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)`.
-/
theorem Xa_le_X (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (by rintro _ ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)

/- English proof (translation)
Establish `key : x ∈ F.X ∧ F.coefX x k = 0`. Unfold `FlagG.Xa at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, hi, rfl⟩` from `hy`.

Use `⟨e_mem_X F i, ?_⟩` and prove the remaining obligations. Rewrite using `[coefX_e']`. Establish `hne : i ≠ k`. Introduce `h`. Establish `: i.val < a` using `hi`.

Rewrite `this` using `[h]`. Use linear arithmetic over natural numbers and integers. Simplify using `[hne]`. Consider the case `zero => exact ⟨F.X.zero_mem, coefX_zero' F k⟩`. Consider the case `add y z _ _ hy hz`.

Conclude with `⟨F.X.add_mem hy.1 hz.1, by rw [coefX_add' F y z k hy.1 hz.1, hy.2, hz.2, add_zero]⟩`. Consider the case `smul b y _ hy`. Conclude with `⟨F.X.smul_mem b hy.1, by rw [coefX_smul' F b y k hy.1, hy.2, mul_zero]⟩`. Conclude with `key.2`.
-/
theorem coefX_low' (F : FlagG S r T) (a : ℕ) (x : S.V) (k : Fin r) (hx : x ∈ F.Xa a)
    (hk : a ≤ k.val) : F.coefX x k = 0 := by
  have key : x ∈ F.X ∧ F.coefX x k = 0 := by
    unfold FlagG.Xa at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      refine ⟨e_mem_X F i, ?_⟩
      rw [coefX_e']
      have hne : i ≠ k := by
        intro h
        have : i.val < a := hi
        rw [h] at this
        omega
      simp [hne]
    | zero => exact ⟨F.X.zero_mem, coefX_zero' F k⟩
    | add y z _ _ hy hz =>
      exact ⟨F.X.add_mem hy.1 hz.1, by rw [coefX_add' F y z k hy.1 hz.1, hy.2, hz.2, add_zero]⟩
    | smul b y _ hy =>
      exact ⟨F.X.smul_mem b hy.1, by rw [coefX_smul' F b y k hy.1, hy.2, mul_zero]⟩
  exact key.2

end Local

/- English proof (translation)
Introduce `E _ _ _ S r T F x y k hx hy`. Conclude with `coefX_add' F x y k hx hy`.
-/
theorem coefAdd : CoefAdd := by
  intro E _ _ _ S r T F x y k hx hy
  exact coefX_add' F x y k hx hy

/- English proof (translation)
Introduce `E _ _ _ S r T F a x k hx`. Conclude with `coefX_smul' F a x k hx`.
-/
theorem coefSmul : CoefSmul := by
  intro E _ _ _ S r T F a x k hx
  exact coefX_smul' F a x k hx

/- English proof (translation)
Introduce `E _ _ _ S r T F j k`. Conclude with `coefX_e' F j k`.
-/
theorem coefE : CoefE := by
  intro E _ _ _ S r T F j k
  exact coefX_e' F j k

/- English proof (translation)
Introduce `E _ _ _ S r T F a x k hx hk`. Conclude with `coefX_low' F a x k hx hk`.
-/
theorem coefLow : CoefLow := by
  intro E _ _ _ S r T F a x k hx hk
  exact coefX_low' F a x k hx hk

end PI.FRS
