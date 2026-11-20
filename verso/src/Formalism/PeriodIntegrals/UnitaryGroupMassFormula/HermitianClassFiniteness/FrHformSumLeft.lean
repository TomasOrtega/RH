import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.HformSumRight

noncomputable section

open NumberField Matrix Formalism.UG PI.InHHClassFin Module

namespace PI.UnitaryGroupMassFormula.InHHClassFin

section FrameEx

variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}

variable (I S) in

def frW : Submodule I.E (Fin I.n → I.E) where
  carrier := {y | ∀ s ∈ S, hform (starRingEnd I.E) I.J s y = 0}
  add_mem' := fun {x y} hx hy s hs => by rw [hform_add_right, hx s hs, hy s hs, add_zero]
  zero_mem' := fun s _ => by simp [hform]
  smul_mem' := fun c x hx s hs => by rw [hform_smul_right, hx s hs, mul_zero]

/- English proof (translation)
Establish `hT` using `I.cm.totReal`. Take `⟨v⟩ : Nonempty (NumberField.InfinitePlace I.F)` from `inferInstance`. Conclude with `⟨NumberField.InfinitePlace.embedding_of_isReal (hT.isReal v)⟩`.
-/
theorem fr_real_emb (I : Formalism.MainNotions.S.AutInst) : Nonempty (I.F →+* ℝ) := by
  have hT := I.cm.totReal
  obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace I.F) := inferInstance
  exact ⟨NumberField.InfinitePlace.embedding_of_isReal (hT.isReal v)⟩

/- English proof (translation)
Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxS hxW`. Assume the negation of the conclusion as `hx0`. Establish `key : ∀ z ∈ Submodule.span I.E S, hform (starRingEnd I.E) I.J z x = 0`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => exact hxW z hz`. Consider the case `zero => simp [hform]`. Consider the case `add u v _ _ hu hv => rw [hform_add_left, hu, hv, add_zero]`. Consider the case `smul c u _ hu => rw [hform_smul_left, hu, mul_zero]`.

Take `⟨ι⟩` from `fr_real_emb I`. Break down `hS ι with h | h` into its components or cases. Take `⟨a, ha, hpos⟩` from `h x hx0 (fun s hs => hxW s hs)`. Rewrite `ha` using `[key x hxS]`. Establish `ha0 : a = 0` using `(algebraMap I.F I.E).injective (by rw [ha, map_zero])`.

Rewrite `hpos` using `[ha0, map_zero]`. Conclude with `lt_irrefl _ hpos`. Take `⟨a, ha, hneg⟩` from `h x hx0 (fun s hs => hxW s hs)`. Rewrite `ha` using `[key x hxS]`. Establish `ha0 : a = 0` using `(algebraMap I.F I.E).injective (by rw [ha, map_zero])`.

Rewrite `hneg` using `[ha0, map_zero]`. Conclude with `lt_irrefl _ hneg`.
-/
theorem fr_disj (hS : DefiniteCompl I S) : Disjoint (Submodule.span I.E S) (frW I S) := by
  rw [Submodule.disjoint_def]
  intro x hxS hxW
  by_contra hx0
  have key : ∀ z ∈ Submodule.span I.E S, hform (starRingEnd I.E) I.J z x = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hxW z hz
    | zero => simp [hform]
    | add u v _ _ hu hv => rw [hform_add_left, hu, hv, add_zero]
    | smul c u _ hu => rw [hform_smul_left, hu, mul_zero]
  obtain ⟨ι⟩ := fr_real_emb I
  rcases hS ι with h | h
  · obtain ⟨a, ha, hpos⟩ := h x hx0 (fun s hs => hxW s hs)
    rw [key x hxS] at ha
    have ha0 : a = 0 := (algebraMap I.F I.E).injective (by rw [ha, map_zero])
    rw [ha0, map_zero] at hpos
    exact lt_irrefl _ hpos
  · obtain ⟨a, ha, hneg⟩ := h x hx0 (fun s hs => hxW s hs)
    rw [key x hxS] at ha
    have ha0 : a = 0 := (algebraMap I.F I.E).injective (by rw [ha, map_zero])
    rw [ha0, map_zero] at hneg
    exact lt_irrefl _ hneg

/- English proof (translation)
Use `Finset.induction_on s (by simp [hform]) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, hform_add_left, ih]`.
-/
theorem fr_hform_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin I.n → I.E) (y : Fin I.n → I.E) :
    hform (starRingEnd I.E) I.J (∑ i ∈ s, x i) y = ∑ i ∈ s, hform (starRingEnd I.E) I.J (x i) y := by
  classical
  refine Finset.induction_on s (by simp [hform]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_left, ih]

/- English proof (translation)
Use `set V := Submodule.span I.E S with hV`. Set `b` to `Module.finBasis I.E V`. Set `T : (Fin I.n → I.E) →ₗ[I.E] (Fin (Module.finrank I.E V) → I.E)` to `{ toFun := fun y k => hform (starRingEnd I.E) I.J (b k : Fin I.n → I.E) y map_add' := by intro x y; funext k; simp [hform_add_right] map_smul' := by intro c x; funext k; simp [hform_smul_right] }`. Establish `hker : LinearMap.ker T ≤ frW I S`. Introduce `y hy s hs`.

Establish `hy' : ∀ k, hform (starRingEnd I.E) I.J (b k : Fin I.n → I.E) y = 0` using `fun k => congrFun (LinearMap.mem_ker.mp hy) k`. Establish `hexp : ∑ k, b.repr ⟨s, Submodule.subset_span hs⟩ k • (b k : Fin I.n → I.E) = s`. Use `congrArg Subtype.val (b.sum_repr ⟨s, Submodule.subset_span hs⟩)` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`.

Conclude with `this`. Rewrite using `[← hexp, fr_hform_sum_left]`. Simplify using `[hform_smul_left, hy']`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker T`. Establish `hr : Module.finrank I.E (LinearMap.range T) ≤ Module.finrank I.E V`.

Use `Submodule.finrank_le (LinearMap.range T)` as an intermediate fact. Simplify using `using this`. Establish `hW : Module.finrank I.E (LinearMap.ker T) ≤ Module.finrank I.E (frW I S)` using `Submodule.finrank_mono hker`. Establish `hsup` using `Submodule.finrank_sup_add_finrank_inf_eq V (frW I S)`. Establish `hinf : V ⊓ frW I S = ⊥` using `disjoint_iff.mp (fr_disj hS)`.

Rewrite `hsup` using `[hinf, finrank_bot, add_zero]`. Establish `hn : Module.finrank I.E (Fin I.n → I.E) = I.n` using `Module.finrank_fin_fun I.E`. Establish `hle` using `Submodule.finrank_le (V ⊔ frW I S)`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
theorem fr_sup (hS : DefiniteCompl I S) : Submodule.span I.E S ⊔ frW I S = ⊤ := by
  classical
  set V := Submodule.span I.E S with hV
  let b := Module.finBasis I.E V
  let T : (Fin I.n → I.E) →ₗ[I.E] (Fin (Module.finrank I.E V) → I.E) :=
    { toFun := fun y k => hform (starRingEnd I.E) I.J (b k : Fin I.n → I.E) y
      map_add' := by intro x y; funext k; simp [hform_add_right]
      map_smul' := by intro c x; funext k; simp [hform_smul_right] }

  have hker : LinearMap.ker T ≤ frW I S := by
    intro y hy s hs
    have hy' : ∀ k, hform (starRingEnd I.E) I.J (b k : Fin I.n → I.E) y = 0 :=
      fun k => congrFun (LinearMap.mem_ker.mp hy) k
    have hexp : ∑ k, b.repr ⟨s, Submodule.subset_span hs⟩ k • (b k : Fin I.n → I.E) = s := by
      have := congrArg Subtype.val (b.sum_repr ⟨s, Submodule.subset_span hs⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this
    rw [← hexp, fr_hform_sum_left]
    simp [hform_smul_left, hy']
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hr : Module.finrank I.E (LinearMap.range T) ≤ Module.finrank I.E V := by
    have := Submodule.finrank_le (LinearMap.range T)
    simpa using this
  have hW : Module.finrank I.E (LinearMap.ker T) ≤ Module.finrank I.E (frW I S) :=
    Submodule.finrank_mono hker
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq V (frW I S)
  have hinf : V ⊓ frW I S = ⊥ := disjoint_iff.mp (fr_disj hS)
  rw [hinf, finrank_bot, add_zero] at hsup
  have hn : Module.finrank I.E (Fin I.n → I.E) = I.n := Module.finrank_fin_fun I.E
  have hle := Submodule.finrank_le (V ⊔ frW I S)
  apply Submodule.eq_top_of_finrank_eq
  omega

/- English proof (translation)
Introduce `I S hS`. Establish `hc : IsCompl (Submodule.span I.E S) (frW I S)` using `⟨fr_disj hS, codisjoint_iff.mpr (fr_sup hS)⟩`. Set `bS` to `Module.finBasis I.E (Submodule.span I.E S)`. Set `bW` to `Module.finBasis I.E (frW I S)`. Set `bb` to `(bS.prod bW).map (Submodule.prodEquivOfIsCompl _ _ hc)`.

Set `e` to `Pi.basisFun I.E (Fin I.n)`. Use `⟨Frame.mk _ _ (e.toMatrix bb) (bb.toMatrix e) (e.toMatrix_mul_toMatrix_flip bb) (bb.toMatrix_mul_toMatrix_flip e) ?_ ?_ ?_⟩` and prove the remaining obligations. Introduce `j`. Establish `hcol : (fun i => e.toMatrix bb i (Sum.inl j)) = (bS j : Fin I.n → I.E)`. Use function extensionality and compare the values at `i`.

Simplify using `[bb, e, Basis.toMatrix_apply]`. Rewrite using `[hcol]`. Conclude with `(bS j).2`. Introduce `s hs j`. Establish `h1 : bb.toMatrix e *ᵥ s = bb.repr s`.

Use `e.toMatrix_mulVec_repr bb s` as an intermediate fact. Establish `he : ⇑(e.repr s) = s` using `by funext i; simp [e]`. Rewrite `this` using `[he]`. Conclude with `this`. Rewrite using `[h1]`.

Establish `hs' : s = Submodule.prodEquivOfIsCompl _ _ hc (⟨s, Submodule.subset_span hs⟩, 0)` using `by simp`. Rewrite using `[hs', Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Basis.prod_repr_inr]`. Simplify using the standard rewrite rules. Introduce `s hs j`. Establish `hcol : (fun i => e.toMatrix bb i (Sum.inr j)) = (bW j : Fin I.n → I.E)`.

Use function extensionality and compare the values at `i`. Simplify using `[bb, e, Basis.toMatrix_apply]`. Rewrite using `[hcol]`. Conclude with `(bW j).2 s hs`.
-/
theorem frameExists : FrameExists := by
  intro I S hS
  classical
  have hc : IsCompl (Submodule.span I.E S) (frW I S) :=
    ⟨fr_disj hS, codisjoint_iff.mpr (fr_sup hS)⟩
  let bS := Module.finBasis I.E (Submodule.span I.E S)
  let bW := Module.finBasis I.E (frW I S)
  let bb := (bS.prod bW).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let e := Pi.basisFun I.E (Fin I.n)
  refine ⟨Frame.mk _ _ (e.toMatrix bb) (bb.toMatrix e) (e.toMatrix_mul_toMatrix_flip bb)
    (bb.toMatrix_mul_toMatrix_flip e) ?_ ?_ ?_⟩
  · intro j
    have hcol : (fun i => e.toMatrix bb i (Sum.inl j)) = (bS j : Fin I.n → I.E) := by
      funext i; simp [bb, e, Basis.toMatrix_apply]
    rw [hcol]; exact (bS j).2
  · intro s hs j
    have h1 : bb.toMatrix e *ᵥ s = bb.repr s := by
      have := e.toMatrix_mulVec_repr bb s
      have he : ⇑(e.repr s) = s := by funext i; simp [e]
      rw [he] at this
      exact this
    rw [h1]
    have hs' : s = Submodule.prodEquivOfIsCompl _ _ hc (⟨s, Submodule.subset_span hs⟩, 0) := by simp
    rw [hs', Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      Basis.prod_repr_inr]
    simp
  · intro s hs j
    have hcol : (fun i => e.toMatrix bb i (Sum.inr j)) = (bW j : Fin I.n → I.E) := by
      funext i; simp [bb, e, Basis.toMatrix_apply]
    rw [hcol]; exact (bW j).2 s hs

end FrameEx

end PI.UnitaryGroupMassFormula.InHHClassFin
