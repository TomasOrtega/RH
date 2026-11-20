import Mathlib
import GroundTheory.GlobalFields.Adele.WeakApprox

namespace GroundTheory.Global

open IsDedekindDomain NumberField Topology

variable {K : Type*} [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

/- English proof (translation)
Use `set f := fun a : Kˣ ↦ ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a), (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a)) with hf`. Use `set E : ((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ) → ((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion) := Prod.map (Pi.map fun _ ↦ Units.val) (Pi.map fun _ ↦ Units.val) with hE`. Establish `hEi : IsInducing E` using `(IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing).prodMap (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing)`. Set `W : Set (((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion))` to `{z | (∀ v, z.1 v ≠ 0) ∧ ∀ w, z.2 w ≠ 0}`. Establish `hW : IsOpen W`.

Establish `: W = (⋂ v, {z | z.1 v ≠ 0}) ∩ ⋂ w, {z | z.2 w ≠ 0}`. Use extensionality with `z`. Simplify using `[W]`. Rewrite using `[this]`. Conclude with `(isOpen_iInter_of_finite fun v ↦ isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const).inter (isOpen_iInter_of_finite fun w ↦ isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)`.

Use `dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ ↦ ?_` and prove the remaining obligations. Take `⟨V, hV, rfl⟩` from `hEi.isOpen_iff.1 hU`. Establish `hEu : E u ∈ W` using `⟨fun v ↦ (u.1 v).ne_zero, fun w ↦ (u.2 w).ne_zero⟩`. Take `⟨x, hxV, hxW⟩` from `(denseRange_algebraMap_prod_pi S T).exists_mem_open (hV.inter hW) ⟨E u, hu, hEu⟩`. Distinguish the cases in `hx : x = 0`.

Establish `hS : IsEmpty S` using `⟨fun v ↦ hxW.1 v (by rw [hx]; exact map_zero _)⟩`. Establish `hT : IsEmpty T` using `⟨fun w ↦ hxW.2 w (by rw [hx]; exact map_zero _)⟩`. Use `⟨f 1, ?_, 1, rfl⟩` and prove the remaining obligations. Use `show E (f 1) ∈ V`. Use `hxV using 1` and compare the differences between its conclusion and the goal.

Conclude with `Prod.ext (funext fun v ↦ isEmptyElim v) (funext fun w ↦ isEmptyElim w)`. Use `⟨f (Units.mk0 x hx), ?_, _, rfl⟩` and prove the remaining obligations. Conclude with `hxV`.
-/
theorem denseRange_units_prod_pi :
    DenseRange (fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a))) := by
  classical
  set f := fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a)) with hf
  set E : ((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ) →
      ((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion) :=
    Prod.map (Pi.map fun _ ↦ Units.val) (Pi.map fun _ ↦ Units.val) with hE
  have hEi : IsInducing E :=
    (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing).prodMap
      (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing)
  let W : Set (((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion)) :=
    {z | (∀ v, z.1 v ≠ 0) ∧ ∀ w, z.2 w ≠ 0}
  have hW : IsOpen W := by
    have : W = (⋂ v, {z | z.1 v ≠ 0}) ∩ ⋂ w, {z | z.2 w ≠ 0} := by
      ext z; simp [W]
    rw [this]
    exact (isOpen_iInter_of_finite fun v ↦
      isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const).inter
      (isOpen_iInter_of_finite fun w ↦
        isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ ↦ ?_
  obtain ⟨V, hV, rfl⟩ := hEi.isOpen_iff.1 hU
  have hEu : E u ∈ W := ⟨fun v ↦ (u.1 v).ne_zero, fun w ↦ (u.2 w).ne_zero⟩
  obtain ⟨x, hxV, hxW⟩ := (denseRange_algebraMap_prod_pi S T).exists_mem_open (hV.inter hW)
    ⟨E u, hu, hEu⟩
  by_cases hx : x = 0
  · have hS : IsEmpty S := ⟨fun v ↦ hxW.1 v (by rw [hx]; exact map_zero _)⟩
    have hT : IsEmpty T := ⟨fun w ↦ hxW.2 w (by rw [hx]; exact map_zero _)⟩
    refine ⟨f 1, ?_, 1, rfl⟩
    show E (f 1) ∈ V
    convert hxV using 1
    exact Prod.ext (funext fun v ↦ isEmptyElim v) (funext fun w ↦ isEmptyElim w)
  · refine ⟨f (Units.mk0 x hx), ?_, _, rfl⟩
    exact hxV

end GroundTheory.Global
