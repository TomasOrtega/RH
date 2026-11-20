import Mathlib

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators Matrix

namespace GlobalTheory

/- English proof (translation)
Use `set LA := Matrix.toLin' A with hLA`. Use `set K := LinearMap.ker LA`. Take `⟨U, hU⟩` from `Submodule.exists_isCompl (LinearMap.range LA)`. Take `⟨K', hK'⟩` from `Submodule.exists_isCompl K`. Establish `h1 : Module.finrank k (LinearMap.range LA) + Module.finrank k K = Module.finrank k (Fin n → k)` using `LinearMap.finrank_range_add_finrank_ker LA`.

Establish `h2` using `Submodule.finrank_add_eq_of_isCompl hU`. Establish `hdim : Module.finrank k K = Module.finrank k U` using `by omega`. Set `e : K ≃ₗ[k] U` to `LinearEquiv.ofFinrankEq K U hdim`. Set `f : (Fin n → k) →ₗ[k] (Fin n → k)` to `U.subtype ∘ₗ (e : K →ₗ[k] U) ∘ₗ Submodule.linearProjOfIsCompl K K' hK'`. Use `⟨LinearMap.toMatrix' f, ?_⟩` and prove the remaining obligations.

Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Apply `hv0` to reduce the goal to its premises. Establish `hfw : ∀ w, LinearMap.toMatrix' f *ᵥ w = f w`. Introduce `w`.

Rewrite using `[← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']`. Establish `hfU : ∀ w, f w ∈ U` using `fun w => (e _).2`. Rewrite `hv` using `[Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hfw]`. Establish `hAv : A *ᵥ v = 0`. Establish `hr : A *ᵥ v ∈ LinearMap.range LA` using `⟨v, by rw [hLA, Matrix.toLin'_apply]⟩`.

Establish `hu : A *ᵥ v ∈ U`. Rewrite using `[eq_neg_of_add_eq_zero_left hv]`. Conclude with `U.neg_mem (hfU _)`. Conclude with `(Submodule.disjoint_def.mp hU.disjoint) _ hr hu`. Rewrite `hv` using `[hAv, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero, sub_zero]`.

Establish `hvK : v ∈ K` using `by show LA v = 0`. Rewrite using `[hLA, Matrix.toLin'_apply, hAv]`. Establish `hp : Submodule.linearProjOfIsCompl K K' hK' v = ⟨v, hvK⟩` using `Submodule.linearProjOfIsCompl_apply_left hK' ⟨v, hvK⟩`. Establish `he : e ⟨v, hvK⟩ = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `: f v = 0` using `hv`. Simplify `this` using `[f, hp]`. Establish `: (⟨v, hvK⟩ : K) = 0` using `by simpa using he`. Simplify using `using congrArg Subtype.val this`.
-/
theorem exists_det_add_mul_one_sub_mul_ne_zero {k : Type*} [Field k] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) k) :
    ∃ T : Matrix (Fin n) (Fin n) k, (A + T * (1 - B * A)).det ≠ 0 := by
  classical
  set LA := Matrix.toLin' A with hLA
  set K := LinearMap.ker LA
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (LinearMap.range LA)
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl K
  have h1 : Module.finrank k (LinearMap.range LA) + Module.finrank k K = Module.finrank k (Fin n → k) :=
    LinearMap.finrank_range_add_finrank_ker LA
  have h2 := Submodule.finrank_add_eq_of_isCompl hU
  have hdim : Module.finrank k K = Module.finrank k U := by omega
  let e : K ≃ₗ[k] U := LinearEquiv.ofFinrankEq K U hdim
  let f : (Fin n → k) →ₗ[k] (Fin n → k) :=
    U.subtype ∘ₗ (e : K →ₗ[k] U) ∘ₗ Submodule.linearProjOfIsCompl K K' hK'
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hfw : ∀ w, LinearMap.toMatrix' f *ᵥ w = f w := by
    intro w
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hfU : ∀ w, f w ∈ U := fun w => (e _).2
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hfw] at hv
  have hAv : A *ᵥ v = 0 := by
    have hr : A *ᵥ v ∈ LinearMap.range LA := ⟨v, by rw [hLA, Matrix.toLin'_apply]⟩
    have hu : A *ᵥ v ∈ U := by
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (hfU _)
    exact (Submodule.disjoint_def.mp hU.disjoint) _ hr hu
  rw [hAv, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hAv,
    Matrix.mulVec_zero, sub_zero] at hv
  have hvK : v ∈ K := by
    show LA v = 0
    rw [hLA, Matrix.toLin'_apply, hAv]
  have hp : Submodule.linearProjOfIsCompl K K' hK' v = ⟨v, hvK⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hK' ⟨v, hvK⟩
  have he : e ⟨v, hvK⟩ = 0 := by
    apply Subtype.ext
    have : f v = 0 := hv
    simpa [f, hp] using this
  have : (⟨v, hvK⟩ : K) = 0 := by simpa using he
  simpa using congrArg Subtype.val this

/- English proof (translation)
Introduce `O M _ _ _ _ n x y hspan`. Establish `hA : ∀ i, ∃ c : Fin n → O, ∑ j, c j • x j = y i` using `fun i => (Submodule.mem_span_range_iff_exists_fun O).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)`. Establish `hB : ∀ i, ∃ c : Fin n → O, ∑ j, c j • y j = x i` using `fun i => (Submodule.mem_span_range_iff_exists_fun O).mp (hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, A i j • x j = y i` from `⟨fun i => (hA i).choose, fun i => (hA i).choose_spec⟩`. Take `⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, B i j • y j = x i` from `⟨fun i => (hB i).choose, fun i => (hB i).choose_spec⟩`.

Establish `hmul : ∀ (P Q : Matrix (Fin n) (Fin n) O) (z : Fin n → M) i, ∑ j, (P * Q) i j • z j = ∑ l, P i l • ∑ j, Q l j • z j`. Introduce `P Q z i`. Simplify using `only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]`. Conclude with `Finset.sum_comm`. Establish `hC : ∀ l, ∑ j, ((1 : Matrix (Fin n) (Fin n) O) - B * A) l j • x j = 0`.

Introduce `l`. Simplify using `only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hmul, hA, hB]`. Simplify using `[Matrix.one_apply]`. Set `r` to `IsLocalRing.residue O`. Take `⟨Tb, hTb⟩` from `exists_det_add_mul_one_sub_mul_ne_zero (r.mapMatrix A) (r.mapMatrix B)`.

Take `⟨s, hs⟩ : ∃ s : IsLocalRing.ResidueField O → O, ∀ a, r (s a) = a` from `⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩`. Set `T : Matrix (Fin n) (Fin n) O` to `Tb.map s`. Establish `hT : r.mapMatrix T = Tb` using `by ext i j; simp [T, hs]`. Set `H : Matrix (Fin n) (Fin n) O` to `A + T * (1 - B * A)`. Establish `hdet : IsUnit H.det`.

Establish `hne : r H.det ≠ 0`. Rewrite using `[RingHom.map_det]`. Simplify using `only [H, map_add, map_mul, map_sub, map_one, hT]`. Conclude with `hTb`. Assume the negation of the conclusion as `hnu`.

Conclude with `hne ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))`. Establish `hHu : IsUnit H` using `(Matrix.isUnit_iff_isUnit_det H).mpr hdet`. Use `⟨hHu.unit, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec]`. Simplify using `only [H, Matrix.add_apply, add_smul, Finset.sum_add_distrib, hA, hmul, hC, smul_zero, Finset.sum_const_zero, add_zero]`.
-/
theorem exists_GL_of_span_range_eq : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M]
    [Module O M] (n : ℕ) (x y : Fin n → M),
    Submodule.span O (Set.range x) = Submodule.span O (Set.range y) →
    ∃ h : GL (Fin n) O, ∀ i, y i = ∑ j, (h : Matrix (Fin n) (Fin n) O) i j • x j := by
  intro O M _ _ _ _ n x y hspan
  classical
  have hA : ∀ i, ∃ c : Fin n → O, ∑ j, c j • x j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hB : ∀ i, ∃ c : Fin n → O, ∑ j, c j • y j = x i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, A i j • x j = y i :=
    ⟨fun i => (hA i).choose, fun i => (hA i).choose_spec⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, B i j • y j = x i :=
    ⟨fun i => (hB i).choose, fun i => (hB i).choose_spec⟩
  have hmul : ∀ (P Q : Matrix (Fin n) (Fin n) O) (z : Fin n → M) i,
      ∑ j, (P * Q) i j • z j = ∑ l, P i l • ∑ j, Q l j • z j := by
    intro P Q z i
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hC : ∀ l, ∑ j, ((1 : Matrix (Fin n) (Fin n) O) - B * A) l j • x j = 0 := by
    intro l
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hmul, hA, hB]
    simp [Matrix.one_apply]
  let r := IsLocalRing.residue O
  obtain ⟨Tb, hTb⟩ := exists_det_add_mul_one_sub_mul_ne_zero (r.mapMatrix A) (r.mapMatrix B)
  obtain ⟨s, hs⟩ : ∃ s : IsLocalRing.ResidueField O → O, ∀ a, r (s a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  let T : Matrix (Fin n) (Fin n) O := Tb.map s
  have hT : r.mapMatrix T = Tb := by ext i j; simp [T, hs]
  let H : Matrix (Fin n) (Fin n) O := A + T * (1 - B * A)
  have hdet : IsUnit H.det := by
    have hne : r H.det ≠ 0 := by
      rw [RingHom.map_det]
      simp only [H, map_add, map_mul, map_sub, map_one, hT]
      exact hTb
    by_contra hnu
    exact hne ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hdet
  refine ⟨hHu.unit, fun i => ?_⟩
  rw [IsUnit.unit_spec]
  simp only [H, Matrix.add_apply, add_smul, Finset.sum_add_distrib, hA, hmul, hC, smul_zero,
    Finset.sum_const_zero, add_zero]

end GlobalTheory
