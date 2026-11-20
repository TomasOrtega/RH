import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

open Matrix Finset

noncomputable section

namespace PI.IsoDerivBFintype

instance finiteOE (h n : ℕ) : Finite (Fin h ↪o Fin n) :=
  Finite.of_injective (fun f : Fin h ↪o Fin n => (f : Fin h → Fin n)) DFunLike.coe_injective

instance fintypeOE (h n : ℕ) : Fintype (Fin h ↪o Fin n) := Fintype.ofFinite _

/- English proof (translation)
Use `set s : Finset (Fin n) := Finset.univ.image f with hs`. Establish `hcard : s.card = h`. Rewrite using `[hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]`. Establish `hmem : ∀ i, f i ∈ s` using `fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)`. Set `g : Fin h → Fin h` to `fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩`.

Establish `hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i`. Introduce `i`. Rewrite using `[← Finset.coe_orderIsoOfFin_apply]`. Simplify using `[g]`. Establish `ginj : Function.Injective g`.

Introduce `i j e`. Apply `hf` to reduce the goal to its premises. Rewrite using `[← hg i, ← hg j, e]`. Conclude with `⟨s.orderEmbOfFin hcard, Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj), hg⟩`.
-/
theorem exists_oe_perm {h n : ℕ} (f : Fin h → Fin n) (hf : Function.Injective f) :
    ∃ (I : Fin h ↪o Fin n) (σ : Equiv.Perm (Fin h)), ∀ i, I (σ i) = f i := by
  classical
  set s : Finset (Fin n) := Finset.univ.image f with hs
  have hcard : s.card = h := by
    rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ i, f i ∈ s := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
  let g : Fin h → Fin h := fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩
  have hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i := by
    intro i
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [g]
  have ginj : Function.Injective g := by
    intro i j e
    apply hf
    rw [← hg i, ← hg j, e]
  exact ⟨s.orderEmbOfFin hcard, Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj), hg⟩

/- English proof (translation)
Rewrite using `[GenFrameSpan.det_mul_rect]`. Establish `hR : ∀ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (I (σ i)) i) * (A.submatrix id (fun i => I (σ i))).det`. Introduce `I`. Rewrite using `[det_apply (B.submatrix I id), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Establish `e : A.submatrix id (fun i => I (σ i)) = (A.submatrix id I).submatrix id σ` using `rfl`. Rewrite using `[e, det_permute']`. Simplify using `only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun I _ => hR I, ← Finset.sum_product']`.

Use `symm`. Use `Finset.sum_bij_ne_zero (fun p _ _ => fun i => p.1 (p.2 i)) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)` and prove the remaining obligations. Introduce and unpack `⟨I, σ⟩ _ _ ⟨I', σ'⟩ _ _ e`. Establish `e' : (fun i => I (σ i)) = fun i => I' (σ' i)` using `e`. Establish `hr : Set.range I = Set.range I'`.

Establish `h1 : Set.range (fun i => I (σ i)) = Set.range I` using `σ.surjective.range_comp I`. Establish `h2 : Set.range (fun i => I' (σ' i)) = Set.range I'` using `σ'.surjective.range_comp I'`. Rewrite using `[← h1, ← h2, e']`. Establish `hI : I = I'` using `OrderEmbedding.range_inj.mp hr`. Substitute `hI` using the available equality.

Establish `: σ = σ'`. Use extensionality with `i`. Use `congrFun e' i` as an intermediate fact. Conclude with `congrArg Fin.val (I.injective this)`. Rewrite using `[this]`.

Introduce `f _ hne`. Establish `hf : Function.Injective f`. Introduce `i j e`. Assume the negation of the conclusion as `hij`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[Matrix.det_zero_of_column_eq hij (by intro r; simp [e]), mul_zero]`. Take `⟨I, σ, hIσ⟩` from `exists_oe_perm f hf`. Conclude with `⟨(I, σ), Finset.mem_univ _, by simpa [hIσ] using hne, funext hIσ⟩`.
-/
theorem cauchyBinet {R : Type*} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det := by
  classical
  rw [GenFrameSpan.det_mul_rect]
  have hR : ∀ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det
      = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (I (σ i)) i) * (A.submatrix id (fun i => I (σ i))).det := by
    intro I
    rw [det_apply (B.submatrix I id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have e : A.submatrix id (fun i => I (σ i)) = (A.submatrix id I).submatrix id σ := rfl
    rw [e, det_permute']
    simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun I _ => hR I, ← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => fun i => p.1 (p.2 i)) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨I, σ⟩ _ _ ⟨I', σ'⟩ _ _ e
    have e' : (fun i => I (σ i)) = fun i => I' (σ' i) := e
    have hr : Set.range I = Set.range I' := by
      have h1 : Set.range (fun i => I (σ i)) = Set.range I := σ.surjective.range_comp I
      have h2 : Set.range (fun i => I' (σ' i)) = Set.range I' := σ'.surjective.range_comp I'
      rw [← h1, ← h2, e']
    have hI : I = I' := OrderEmbedding.range_inj.mp hr
    subst hI
    have : σ = σ' := by
      ext i
      have := congrFun e' i
      exact congrArg Fin.val (I.injective this)
    rw [this]
  · intro f _ hne
    have hf : Function.Injective f := by
      intro i j e
      by_contra hij
      apply hne
      rw [Matrix.det_zero_of_column_eq hij (by intro r; simp [e]), mul_zero]
    obtain ⟨I, σ, hIσ⟩ := exists_oe_perm f hf
    exact ⟨(I, σ), Finset.mem_univ _, by simpa [hIσ] using hne, funext hIσ⟩

end PI.IsoDerivBFintype
