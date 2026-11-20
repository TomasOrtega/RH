import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.HilbTensorExists

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `H _ _`. Use `⟨ℂ, inferInstance, inferInstance, fun _ => 1, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.univ_eq_empty, Finset.prod_empty]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `H _ _`. Take `⟨K, iK, iK', t, ht⟩` from `ih (fun i => H i.castSucc)`. Use `⟨K ⊗[ℂ] H (Fin.last n), inferInstance, inferInstance, fun x => t (fun i => x i.castSucc) ⊗ₜ[ℂ] x (Fin.last n), fun x y => ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.inner_tmul, ht, Fin.prod_univ_castSucc]`.
-/
theorem exists_pre_fin (n : ℕ) : ∀ (H : Fin n → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)],
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  induction n with
  | zero =>
    intro H _ _
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 1, fun x y => ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  | succ n ih =>
    intro H _ _
    obtain ⟨K, iK, iK', t, ht⟩ := ih (fun i => H i.castSucc)
    refine ⟨K ⊗[ℂ] H (Fin.last n), inferInstance, inferInstance,
      fun x => t (fun i => x i.castSucc) ⊗ₜ[ℂ] x (Fin.last n), fun x y => ?_⟩
    rw [TensorProduct.inner_tmul, ht, Fin.prod_univ_castSucc]

/- English proof (translation)
Set `e` to `Fintype.equivFin ι`. Take `⟨K, iK, iK', t, ht⟩` from `exists_pre_fin (Fintype.card ι) (fun i => H (e.symm i))`. Use `⟨K, iK, iK', fun x => t (fun i => x (e.symm i)), fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[ht]`. Conclude with `e.symm.prod_comp (fun v => ⟪x v, y v⟫_ℂ)`.
-/
theorem exists_pre {ι : Type} [Fintype ι] (H : ι → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  let e := Fintype.equivFin ι
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre_fin (Fintype.card ι) (fun i => H (e.symm i))
  refine ⟨K, iK, iK', fun x => t (fun i => x (e.symm i)), fun x y => ?_⟩
  rw [ht]
  exact e.symm.prod_comp (fun v => ⟪x v, y v⟫_ℂ)

/- English proof (translation)
Set `V` to `Submodule.span ℂ (Set.range t)`. Set `u : X → V` to `fun x => ⟨t x, Submodule.subset_span ⟨x, rfl⟩⟩`. Establish `hu : Submodule.span ℂ (Set.range u) = ⊤`. Apply `Submodule.map_injective_of_injective V.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]`.

Both sides reduce to the same expression. Use `⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance, fun x => ((u x : V) : UniformSpace.Completion V), fun x y => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[UniformSpace.Completion.inner_coe]`. Both sides reduce to the same expression. Use `UniformSpace.Completion.denseRange_coe.mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨v, rfl⟩`. Establish `hv : v ∈ Submodule.span ℂ (Set.range u)` using `hu ▸ Submodule.mem_top`. Establish `hm` using `Submodule.mem_map_of_mem (f := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap) hv`. Rewrite `hm` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `hm`.
-/
theorem exists_complete_dense {X K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : X → K) :
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : CompleteSpace L) (s : X → L),
      (∀ x y, ⟪s x, s y⟫_ℂ = ⟪t x, t y⟫_ℂ) ∧ Dense (Submodule.span ℂ (Set.range s) : Set L) := by
  let V := Submodule.span ℂ (Set.range t)
  let u : X → V := fun x => ⟨t x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    rfl
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    fun x => ((u x : V) : UniformSpace.Completion V), fun x y => ?_, ?_⟩
  · rw [UniformSpace.Completion.inner_coe]
    rfl
  · refine UniformSpace.Completion.denseRange_coe.mono ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ (Set.range u) := hu ▸ Submodule.mem_top
    have hm := Submodule.mem_map_of_mem
      (f := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap) hv
    rw [Submodule.map_span, ← Set.range_comp] at hm
    exact hm

/- English proof (translation)
Set `S` to `Finsupp.linearCombination ℂ s`. Set `A` to `Finsupp.linearCombination ℂ (s ∘ f)`. Establish `key : ∀ c : X →₀ ℂ, ⟪A c, A c⟫_ℂ = ⟪S c, S c⟫_ℂ`. Introduce `c`. Simplify using `only [A, S, Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left, inner_smul_right, Function.comp_apply, hf]`.

Establish `hn : ∀ c, ‖A c‖ ≤ 1 * ‖S c‖`. Introduce `c`. Rewrite using `[one_mul, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, key]`. Establish `hd : DenseRange S`. Rewrite using `[DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]`.

Conclude with `hs`. Use `⟨A.extendOfNorm S, fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `LinearMap.extendOfNorm_eq hd ⟨1, hn⟩ (Finsupp.single x (1 : ℂ))`. Simplify using `only [S, A, Finsupp.linearCombination_single, one_smul, Function.comp_apply] at h`. Conclude with `h`.
-/
theorem exists_extension {X L : Type} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (s : X → L) (hs : Dense (Submodule.span ℂ (Set.range s) : Set L)) (f : X → X)
    (hf : ∀ x y, ⟪s (f x), s (f y)⟫_ℂ = ⟪s x, s y⟫_ℂ) :
    ∃ T : L →L[ℂ] L, ∀ x, T (s x) = s (f x) := by
  let S := Finsupp.linearCombination ℂ s
  let A := Finsupp.linearCombination ℂ (s ∘ f)
  have key : ∀ c : X →₀ ℂ, ⟪A c, A c⟫_ℂ = ⟪S c, S c⟫_ℂ := by
    intro c
    simp only [A, S, Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
      inner_smul_left, inner_smul_right, Function.comp_apply, hf]
  have hn : ∀ c, ‖A c‖ ≤ 1 * ‖S c‖ := by
    intro c
    rw [one_mul, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, key]
  have hd : DenseRange S := by
    rw [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact hs
  refine ⟨A.extendOfNorm S, fun x => ?_⟩
  have h := LinearMap.extendOfNorm_eq hd ⟨1, hn⟩ (Finsupp.single x (1 : ℂ))
  simp only [S, A, Finsupp.linearCombination_single, one_smul, Function.comp_apply] at h
  exact h

/- English proof (translation)
Take `⟨K, iK, iK', t, ht⟩` from `exists_pre H`. Take `⟨L, iL, iL', iL'', s, hs, hd⟩` from `exists_complete_dense t`. Establish `hext : ∀ g : I.Ginf, ∃ T : L →L[ℂ] L, ∀ x, T (s x) = s (fun v => σ v (uMat (g v)) (x v))`. Introduce `g`. Use `exists_extension s hd (fun x v => σ v (uMat (g v)) (x v)) (fun x y => ?_)` and prove the remaining obligations.

Simplify using `only [hs, ht]`. Conclude with `Finset.prod_congr rfl fun v _ => hσ v (g v) (x v) (y v)`. Use `choose σs hσs using hext`. Use `⟨L, iL, iL', iL'', σs, s, ?_⟩` and prove the remaining obligations. Unfold `Formalism.MainNotions.S.AutInst.IsHilbTensor`.

Conclude with `⟨fun x y => by rw [hs, ht], hσs, hd⟩`.
-/
theorem exists_isHilbTensor (I : AutInst) (H : NumberField.InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (hσ : ∀ v (g : Formalism.REAL.UJ (I.ε v)) x y, ⟪σ v (uMat g) x, σ v (uMat g) y⟫_ℂ = ⟪x, y⟫_ℂ) :
    ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (_ : CompleteSpace Hs)
      (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs), I.IsHilbTensor σ σs tens := by
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre H
  obtain ⟨L, iL, iL', iL'', s, hs, hd⟩ := exists_complete_dense t
  have hext : ∀ g : I.Ginf, ∃ T : L →L[ℂ] L,
      ∀ x, T (s x) = s (fun v => σ v (uMat (g v)) (x v)) := by
    intro g
    refine exists_extension s hd (fun x v => σ v (uMat (g v)) (x v)) (fun x y => ?_)
    simp only [hs, ht]
    exact Finset.prod_congr rfl fun v _ => hσ v (g v) (x v) (y v)
  choose σs hσs using hext
  refine ⟨L, iL, iL', iL'', σs, s, ?_⟩
  unfold Formalism.MainNotions.S.AutInst.IsHilbTensor
  exact ⟨fun x y => by rw [hs, ht], hσs, hd⟩

end GlobalTheory.HilbTensorExists
