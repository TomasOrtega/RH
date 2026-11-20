import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

noncomputable section

open Matrix Finset

namespace PI.IsoInvMetricW

/- English proof (translation)
Introduce `h N A B`. Rewrite using `[GenFrameSpan.det_mul_rect]`. Establish `hR : ∀ J : Fin h ↪o Fin N, (A.submatrix id J).det * (B.submatrix J id).det = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (J (σ i)) i) * (A.submatrix id (J ∘ σ)).det`. Introduce `J`. Rewrite using `[det_apply (B.submatrix J id), Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hA : A.submatrix id (J ∘ σ) = (A.submatrix id J).submatrix id σ`. Use extensionality with `i k`. Simplify using the standard rewrite rules. Rewrite using `[hA, det_permute']`.

Simplify using `only [Units.smul_def, zsmul_eq_mul, submatrix_apply, id]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun J _ => hR J), ← Fintype.sum_prod_type']`. Use `symm`. Use `Finset.sum_bij_ne_zero (fun p _ _ => (p.1 : Fin h → Fin N) ∘ p.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)` and prove the remaining obligations.

Introduce and unpack `⟨J, σ⟩ _ _ ⟨J', σ'⟩ _ _ heq`. Establish `hr : Set.range J = Set.range J'`. Establish `h1 : Set.range ((J : Fin h → Fin N) ∘ σ) = Set.range J` using `σ.surjective.range_comp _`. Establish `h2 : Set.range ((J' : Fin h → Fin N) ∘ σ') = Set.range J'` using `σ'.surjective.range_comp _`. Rewrite using `[← h1, ← h2]`.

Conclude with `congrArg Set.range heq`. Establish `hJ : J = J'` using `OrderEmbedding.range_inj.mp hr`. Substitute `hJ` using the available equality. Establish `hσ : σ = σ'`. Use extensionality with `i`.

Use `congrFun heq i` as an intermediate fact. Simplify using `only [Function.comp_apply] at this`. Rewrite using `[J.injective this]`. Rewrite using `[hσ]`. Introduce `f _ hf`.

Establish `hinj : Function.Injective f`. Assume the negation of the conclusion as `hni`. Apply `hf` to reduce the goal to its premises. Establish `: ∃ i j, f i = f j ∧ i ≠ j`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `hni fun i j e => hc i j e`. Take `⟨i, j, hij, hne⟩` from `this`. Rewrite using `[Matrix.det_zero_of_column_eq hne (by intro r; simp [hij]), mul_zero]`. Use `set s : Finset (Fin N) := Finset.univ.image f with hs`.

Establish `hcard : s.card = h`. Rewrite using `[hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]`. Establish `hmem : ∀ i, f i ∈ s` using `fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)`. Set `g : Fin h → Fin h` to `fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩`. Establish `hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i`.

Introduce `i`. Rewrite using `[← Finset.coe_orderIsoOfFin_apply]`. Simplify using `[g]`. Establish `ginj : Function.Injective g`. Introduce `i j e`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hg i, ← hg j, e]`. Set `σ : Equiv.Perm (Fin h)` to `Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)`. Use `⟨(s.orderEmbOfFin hcard, σ), Finset.mem_univ _, ?_, ?_⟩` and prove the remaining obligations. Establish `hfi : ∀ i, (s.orderEmbOfFin hcard) (σ i) = f i` using `fun i => by simp [σ, hg]`.

Establish `: ((s.orderEmbOfFin hcard : Fin h ↪o Fin N) : Fin h → Fin N) ∘ σ = f`. Use function extensionality and compare the values at `i`. Conclude with `hfi i`. Rewrite using `[this]`. Simplify using `only`.

Simplify using `only [hfi]`. Conclude with `hf`. Use function extensionality and compare the values at `i`. Simplify using `[σ, hg]`.
-/
theorem metric_constant_bound : CB := by
  intro h N A B
  classical
  rw [GenFrameSpan.det_mul_rect]
  have hR : ∀ J : Fin h ↪o Fin N, (A.submatrix id J).det * (B.submatrix J id).det
      = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (J (σ i)) i) * (A.submatrix id (J ∘ σ)).det := by
    intro J
    rw [det_apply (B.submatrix J id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hA : A.submatrix id (J ∘ σ) = (A.submatrix id J).submatrix id σ := by
      ext i k; simp
    rw [hA, det_permute']
    simp only [Units.smul_def, zsmul_eq_mul, submatrix_apply, id]
    ring
  rw [Finset.sum_congr rfl (fun J _ => hR J), ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1 : Fin h → Fin N) ∘ p.2)
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨J, σ⟩ _ _ ⟨J', σ'⟩ _ _ heq
    have hr : Set.range J = Set.range J' := by
      have h1 : Set.range ((J : Fin h → Fin N) ∘ σ) = Set.range J :=
        σ.surjective.range_comp _
      have h2 : Set.range ((J' : Fin h → Fin N) ∘ σ') = Set.range J' :=
        σ'.surjective.range_comp _
      rw [← h1, ← h2]
      exact congrArg Set.range heq
    have hJ : J = J' := OrderEmbedding.range_inj.mp hr
    subst hJ
    have hσ : σ = σ' := by
      ext i
      have := congrFun heq i
      simp only [Function.comp_apply] at this
      rw [J.injective this]
    rw [hσ]
  · intro f _ hf
    have hinj : Function.Injective f := by
      by_contra hni
      apply hf
      have : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        push Not at hc
        exact hni fun i j e => hc i j e
      obtain ⟨i, j, hij, hne⟩ := this
      rw [Matrix.det_zero_of_column_eq hne (by intro r; simp [hij]), mul_zero]
    set s : Finset (Fin N) := Finset.univ.image f with hs
    have hcard : s.card = h := by
      rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, f i ∈ s := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
    let g : Fin h → Fin h := fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩
    have hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i := by
      intro i
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [g]
    have ginj : Function.Injective g := by
      intro i j e
      apply hinj
      rw [← hg i, ← hg j, e]
    let σ : Equiv.Perm (Fin h) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)
    refine ⟨(s.orderEmbOfFin hcard, σ), Finset.mem_univ _, ?_, ?_⟩
    · have hfi : ∀ i, (s.orderEmbOfFin hcard) (σ i) = f i := fun i => by simp [σ, hg]
      have : ((s.orderEmbOfFin hcard : Fin h ↪o Fin N) : Fin h → Fin N) ∘ σ = f := by
        funext i; exact hfi i
      rw [this]; dsimp only; simp only [hfi]; exact hf
    · funext i; simp [σ, hg]

end PI.IsoInvMetricW
