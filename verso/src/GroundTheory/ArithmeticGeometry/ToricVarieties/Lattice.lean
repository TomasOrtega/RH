import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.ExistsDualNegOfNotMemHullFinset

namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct

section Comb

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on generalizing x with`. Consider the case `empty`. Simplify using `only [Finset.coe_empty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, Finset.sum_empty]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`.

Conclude with `⟨0, fun _ => le_rfl, rfl⟩`. Introduce and unpack `⟨_, _, rfl⟩`. Both sides reduce to the same expression. Consider the case `insert a T ha ih`. Rewrite using `[Finset.coe_insert, Set.image_insert_eq, mem_hull_insert]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, y, hy, rfl⟩`. Take `⟨d, hd, rfl⟩` from `ih.1 hy`. Use `⟨Function.update d a c, fun i => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = a`.

Substitute `h` using the available equality. Simplify using `using hc`. Simplify `hd i` using `[h]`. Rewrite using `[Finset.sum_insert ha, Function.update_self]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun i hi => by`. Rewrite using `[Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]`. Introduce and unpack `⟨c, hc, rfl⟩`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `⟨c a, hc a, _, ih.2 ⟨c, hc, rfl⟩, rfl⟩`.
-/
theorem mem_hull_image_finset_iff {ι : Type*} [DecidableEq ι] (T : Finset ι) (v : ι → E)
    {x : E} : x ∈ hull 𝕜 (v '' T) ↔ ∃ c : ι → 𝕜, (∀ i, 0 ≤ c i) ∧ ∑ i ∈ T, c i • v i = x := by
  induction T using Finset.induction_on generalizing x with
  | empty =>
    simp only [Finset.coe_empty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot,
      Finset.sum_empty]
    constructor
    · rintro rfl; exact ⟨0, fun _ => le_rfl, rfl⟩
    · rintro ⟨_, _, rfl⟩; rfl
  | insert a T ha ih =>
    rw [Finset.coe_insert, Set.image_insert_eq, mem_hull_insert]
    constructor
    · rintro ⟨c, hc, y, hy, rfl⟩
      obtain ⟨d, hd, rfl⟩ := ih.1 hy
      refine ⟨Function.update d a c, fun i => ?_, ?_⟩
      · by_cases h : i = a
        · subst h; simpa using hc
        · simpa [h] using hd i
      · rw [Finset.sum_insert ha, Function.update_self]
        congr 1
        exact Finset.sum_congr rfl fun i hi => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)]
    · rintro ⟨c, hc, rfl⟩
      rw [Finset.sum_insert ha]
      exact ⟨c a, hc a, _, ih.2 ⟨c, hc, rfl⟩, rfl⟩

/- English proof (translation)
Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations. Establish `key : ∀ y ∈ Submodule.span 𝕜 (Set.range b), y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) ∧ -y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i))`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `⟨subset_hull (Or.inl ⟨i, rfl⟩), subset_hull (Or.inr ⟨i, rfl⟩)⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Conclude with `⟨add_mem hy.1 hz.1, by rw [neg_add]; exact add_mem hy.2 hz.2⟩`.

Consider the case `smul c y _ hy`. Break down `le_total 0 c with hc | hc` into its components or cases. Conclude with `⟨smul_mem _ hc hy.1, by rw [← smul_neg]; exact smul_mem _ hc hy.2⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← neg_neg c, neg_smul, ← smul_neg]`.

Conclude with `smul_mem _ (neg_nonneg.2 hc) hy.2`. Rewrite using `[← neg_smul]`. Conclude with `smul_mem _ (neg_nonneg.2 hc) hy.1`. Conclude with `(key x (by rw [b.span_eq]; exact Submodule.mem_top)).1`.
-/
theorem hull_basis_neg_eq_top {ι : Type*} (b : Basis ι 𝕜 E) :
    hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have key : ∀ y ∈ Submodule.span 𝕜 (Set.range b),
      y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) ∧
        -y ∈ hull 𝕜 (Set.range b ∪ Set.range (fun i => -b i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨subset_hull (Or.inl ⟨i, rfl⟩), subset_hull (Or.inr ⟨i, rfl⟩)⟩
    | zero => simp
    | add y z _ _ hy hz =>
      exact ⟨add_mem hy.1 hz.1, by rw [neg_add]; exact add_mem hy.2 hz.2⟩
    | smul c y _ hy =>
      rcases le_total 0 c with hc | hc
      · exact ⟨smul_mem _ hc hy.1, by rw [← smul_neg]; exact smul_mem _ hc hy.2⟩
      · refine ⟨?_, ?_⟩
        · rw [← neg_neg c, neg_smul, ← smul_neg]; exact smul_mem _ (neg_nonneg.2 hc) hy.2
        · rw [← neg_smul]; exact smul_mem _ (neg_nonneg.2 hc) hy.1
  exact (key x (by rw [b.span_eq]; exact Submodule.mem_top)).1

end Comb

section Integral

variable {L E : Type*} [AddCommGroup L] [AddCommGroup E] [Module ℝ E]

def IsRationalPolyhedral (ι : L →ₗ[ℤ] E) (σ : PointedCone ℝ E) : Prop :=
  ∃ S : Finset L, hull ℝ (ι '' S) = σ

/- English proof (translation)
Take `⟨S, rfl⟩` from `hσ`. Conclude with `⟨S.image ι, by rw [Finset.coe_image]⟩`.
-/
theorem IsRationalPolyhedral.fg {ι : L →ₗ[ℤ] E} {σ : PointedCone ℝ E}
    (hσ : IsRationalPolyhedral ι σ) : σ.FG := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  exact ⟨S.image ι, by rw [Finset.coe_image]⟩

/- English proof (translation)
Establish `h` using `hull_inf_halfspace (𝕜 := ℝ) (T.image ι) g`. Rewrite `h` using `[Finset.coe_image]`. Rewrite using `[h]`. Establish `hcomb : ∀ a b, g (ι a) • ι b - g (ι b) • ι a = ι (gL a • b - gL b • a)`. Introduce `a b`.

Simplify using `[hg, map_sub, Int.cast_smul_eq_zsmul]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Finset.coe_union, Finset.coe_filter, Finset.coe_image, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_image, Finset.mem_product, Prod.exists]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(⟨⟨a, ha, rfl⟩, hga⟩ | ⟨s, t, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, h1, h2⟩, rfl⟩)`. Rewrite `hga` using `[hg]`. Conclude with `⟨a, Or.inl ⟨ha, by exact_mod_cast hga⟩, rfl⟩`. Rewrite `h1`, `h2` using `[hg]`. Use `⟨gL a • b - gL b • a, Or.inr ⟨a, b, ⟨⟨ha, hb⟩, by exact_mod_cast h1, by exact_mod_cast h2⟩, rfl⟩, (hcomb a b).symm⟩` and prove the remaining obligations.

Introduce and unpack `⟨l, (⟨hl, hgl⟩ | ⟨a, b, ⟨⟨ha, hb⟩, h1, h2⟩, rfl⟩), rfl⟩`. Conclude with `Or.inl ⟨⟨l, hl, rfl⟩, by rw [hg]; exact_mod_cast hgl⟩`. Use `Or.inr ⟨ι a, ι b, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, by rw [hg]; exact_mod_cast h1, by rw [hg]; exact_mod_cast h2⟩, hcomb a b⟩` and prove the remaining obligations.
-/
theorem hull_image_inf_halfspace_int [DecidableEq L] (ι : L →ₗ[ℤ] E) (T : Finset L)
    (g : Dual ℝ E) (gL : L →ₗ[ℤ] ℤ) (hg : ∀ l, g (ι l) = gL l) :
    hull ℝ (ι '' T) ⊓ (positive ℝ ℝ).comap g =
      hull ℝ (ι '' ↑(T.filter (fun t => 0 ≤ gL t) ∪
        ((T ×ˢ T).filter (fun st => 0 < gL st.1 ∧ gL st.2 < 0)).image
          (fun st => gL st.1 • st.2 - gL st.2 • st.1))) := by
  classical
  have h := hull_inf_halfspace (𝕜 := ℝ) (T.image ι) g
  rw [Finset.coe_image] at h
  rw [h]
  have hcomb : ∀ a b, g (ι a) • ι b - g (ι b) • ι a = ι (gL a • b - gL b • a) := by
    intro a b
    simp [hg, map_sub, Int.cast_smul_eq_zsmul]
  congr 1
  ext y
  simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_image, Set.mem_union,
    Set.mem_ofPred_eq, Set.mem_image, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro (⟨⟨a, ha, rfl⟩, hga⟩ | ⟨s, t, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, h1, h2⟩, rfl⟩)
    · rw [hg] at hga
      exact ⟨a, Or.inl ⟨ha, by exact_mod_cast hga⟩, rfl⟩
    · rw [hg] at h1 h2
      refine ⟨gL a • b - gL b • a, Or.inr ⟨a, b, ⟨⟨ha, hb⟩, by exact_mod_cast h1,
        by exact_mod_cast h2⟩, rfl⟩, (hcomb a b).symm⟩
  · rintro ⟨l, (⟨hl, hgl⟩ | ⟨a, b, ⟨⟨ha, hb⟩, h1, h2⟩, rfl⟩), rfl⟩
    · exact Or.inl ⟨⟨l, hl, rfl⟩, by rw [hg]; exact_mod_cast hgl⟩
    · refine Or.inr ⟨ι a, ι b, ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, by rw [hg]; exact_mod_cast h1,
        by rw [hg]; exact_mod_cast h2⟩, hcomb a b⟩

def latticePoints (ι : L →ₗ[ℤ] E) (τ : PointedCone ℝ E) : AddSubmonoid L :=
  τ.toAddSubmonoid.comap ι.toAddMonoidHom

@[simp]
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latticePoints {ι : L →ₗ[ℤ] E} {τ : PointedCone ℝ E} {m : L} :
    m ∈ latticePoints ι τ ↔ ι m ∈ τ := Iff.rfl

end Integral

section Lattice

variable (N : Type*) [AddCommGroup N]

def toRealSpan : N →ₗ[ℤ] ℝ ⊗[ℤ] N := TensorProduct.mk ℤ ℝ N 1

def toRealDual : Dual ℤ N →ₗ[ℤ] Dual ℝ (ℝ ⊗[ℤ] N) := Module.Dual.baseChange ℝ

variable {N}

/- English proof (translation)
The claim follows from `rfl @[simp]`.
-/
theorem toRealSpan_apply (n : N) : toRealSpan N n = (1 : ℝ) ⊗ₜ n := rfl

@[simp]
/- English proof (translation)
Simplify using `[toRealDual, toRealSpan_apply, Module.Dual.baseChange_apply_tmul]`.
-/
theorem toRealDual_apply_toRealSpan (m : Dual ℤ N) (n : N) :
    toRealDual N m (toRealSpan N n) = (m n : ℝ) := by
  simp [toRealDual, toRealSpan_apply, Module.Dual.baseChange_apply_tmul]

/- English proof (translation)
Use `(e.baseChange ℝ).ext fun i => ?_` and prove the remaining obligations. Rewrite using `[Basis.dualBasis_apply_self, Basis.baseChange_apply, ← toRealSpan_apply, toRealDual_apply_toRealSpan, Basis.dualBasis_apply_self]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem toRealDual_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι ℤ N) (j : ι) :
    toRealDual N (e.dualBasis j) = (e.baseChange ℝ).dualBasis j := by
  refine (e.baseChange ℝ).ext fun i => ?_
  rw [Basis.dualBasis_apply_self, Basis.baseChange_apply, ← toRealSpan_apply,
    toRealDual_apply_toRealSpan, Basis.dualBasis_apply_self]
  split_ifs <;> simp

variable [Module.Free ℤ N] [Module.Finite ℤ N]

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis ℤ N`. Use `⟨Finset.univ.image e.dualBasis ∪ Finset.univ.image (fun j => -e.dualBasis j), ?_⟩` and prove the remaining obligations. Establish `h1 : (toRealDual N ∘ e.dualBasis) = (e.baseChange ℝ).dualBasis`. Use function extensionality and compare the values at `fun j => toRealDual_dualBasis e j`. Establish `h2 : (toRealDual N ∘ fun j => -e.dualBasis j) = fun j => -(e.baseChange ℝ).dualBasis j`.

Use function extensionality and compare the values at `fun j => by simp only [Function.comp_apply, map_neg, toRealDual_dualBasis]`. Rewrite using `[← hull_basis_neg_eq_top (e.baseChange ℝ).dualBasis, Finset.coe_union, Finset.coe_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union, ← Set.range_comp, ← Set.range_comp, h1, h2]`.
-/
theorem isRationalPolyhedral_top_dual :
    IsRationalPolyhedral (toRealDual N) (⊤ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))) := by
  classical
  let e := Module.Free.chooseBasis ℤ N
  refine ⟨Finset.univ.image e.dualBasis ∪ Finset.univ.image (fun j => -e.dualBasis j), ?_⟩
  have h1 : (toRealDual N ∘ e.dualBasis) = (e.baseChange ℝ).dualBasis :=
    funext fun j => toRealDual_dualBasis e j
  have h2 : (toRealDual N ∘ fun j => -e.dualBasis j) = fun j => -(e.baseChange ℝ).dualBasis j :=
    funext fun j => by simp only [Function.comp_apply, map_neg, toRealDual_dualBasis]
  rw [← hull_basis_neg_eq_top (e.baseChange ℝ).dualBasis, Finset.coe_union, Finset.coe_image,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, h1, h2]

/- English proof (translation)
Set `e` to `Module.Free.chooseBasis ℤ N`. Use `⟨Finset.univ.image e ∪ Finset.univ.image (fun j => -e j), ?_⟩` and prove the remaining obligations. Establish `h1 : (toRealSpan N ∘ e) = e.baseChange ℝ`. Use function extensionality and compare the values at `fun j => by simp [Basis.baseChange_apply, toRealSpan_apply]`. Establish `h2 : (toRealSpan N ∘ fun j => -e j) = fun j => -(e.baseChange ℝ) j`.

Use function extensionality and compare the values at `fun j => by simp [Basis.baseChange_apply, toRealSpan_apply, TensorProduct.tmul_neg]`. Rewrite using `[← hull_basis_neg_eq_top (e.baseChange ℝ), Finset.coe_union, Finset.coe_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union, ← Set.range_comp, ← Set.range_comp, h1, h2]`.
-/
theorem isRationalPolyhedral_top :
    IsRationalPolyhedral (toRealSpan N) (⊤ : PointedCone ℝ (ℝ ⊗[ℤ] N)) := by
  classical
  let e := Module.Free.chooseBasis ℤ N
  refine ⟨Finset.univ.image e ∪ Finset.univ.image (fun j => -e j), ?_⟩
  have h1 : (toRealSpan N ∘ e) = e.baseChange ℝ :=
    funext fun j => by simp [Basis.baseChange_apply, toRealSpan_apply]
  have h2 : (toRealSpan N ∘ fun j => -e j) = fun j => -(e.baseChange ℝ) j :=
    funext fun j => by simp [Basis.baseChange_apply, toRealSpan_apply, TensorProduct.tmul_neg]
  rw [← hull_basis_neg_eq_top (e.baseChange ℝ), Finset.coe_union, Finset.coe_image,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, h1, h2]

/- English proof (translation)
Take `⟨S, rfl⟩` from `hσ`. Rewrite using `[dual_hull]`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using isRationalPolyhedral_top_dual`. Consider the case `insert n S _ ih`.

Take `⟨T, hT⟩` from `ih`. Rewrite using `[Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hT, hull_image_inf_halfspace_int (toRealDual N) T _ (Dual.eval ℤ N n) (fun m => by simp)]`. Conclude with `⟨_, rfl⟩`.
-/
theorem IsRationalPolyhedral.dual {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) :
    IsRationalPolyhedral (toRealDual N) (dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set (ℝ ⊗[ℤ] N))) := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  rw [dual_hull]
  induction S using Finset.induction_on with
  | empty => simpa using isRationalPolyhedral_top_dual
  | insert n S _ ih =>
    obtain ⟨T, hT⟩ := ih
    rw [Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hT,
      hull_image_inf_halfspace_int (toRealDual N) T _ (Dual.eval ℤ N n) (fun m => by simp)]
    exact ⟨_, rfl⟩

/- English proof (translation)
Take `⟨T, rfl⟩` from `hτ`. Rewrite using `[dual_hull]`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using isRationalPolyhedral_top`. Consider the case `insert m T _ ih`.

Take `⟨S, hS⟩` from `ih`. Rewrite using `[Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hS, hull_image_inf_halfspace_int (toRealSpan N) S _ m (fun n => by simp)]`. Conclude with `⟨_, rfl⟩`.
-/
theorem IsRationalPolyhedral.predual {τ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))}
    (hτ : IsRationalPolyhedral (toRealDual N) τ) :
    IsRationalPolyhedral (toRealSpan N)
      (PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] Dual ℝ (ℝ ⊗[ℤ] N)) (τ : Set _)) := by
  classical
  obtain ⟨T, rfl⟩ := hτ
  rw [dual_hull]
  induction T using Finset.induction_on with
  | empty => simpa using isRationalPolyhedral_top
  | insert m T _ ih =>
    obtain ⟨S, hS⟩ := ih
    rw [Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hS,
      hull_image_inf_halfspace_int (toRealSpan N) S _ m (fun n => by simp)]
    exact ⟨_, rfl⟩

end Lattice

section Duality

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/- English proof (translation)
The claim follows from `dual_dual_flip_of_fg _ Function.surjective_id hσ`.
-/
theorem dual_dual_eq_self {σ : PointedCone ℝ V} (hσ : σ.FG) :
    dual (LinearMap.id : Dual ℝ V →ₗ[ℝ] Dual ℝ V) (dual (Dual.eval ℝ V) (σ : Set V)) = σ :=
  dual_dual_flip_of_fg _ Function.surjective_id hσ

/- English proof (translation)
Take `⟨S, rfl⟩` from `h`. Take `⟨S', rfl⟩` from `h'`. Conclude with `⟨S ∪ S', by rw [Finset.coe_union, Set.image_union]; exact Submodule.span_union _ _⟩`.
-/
theorem IsRationalPolyhedral.sup {L : Type*} [AddCommGroup L] [DecidableEq L] {ι : L →ₗ[ℤ] V}
    {σ σ' : PointedCone ℝ V} (h : IsRationalPolyhedral ι σ) (h' : IsRationalPolyhedral ι σ') :
    IsRationalPolyhedral ι (σ ⊔ σ') := by
  obtain ⟨S, rfl⟩ := h
  obtain ⟨S', rfl⟩ := h'
  exact ⟨S ∪ S', by rw [Finset.coe_union, Set.image_union]; exact Submodule.span_union _ _⟩

end Duality

section Operations

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

/- English proof (translation)
Establish `key : σ ⊓ σ' = PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] _) ((PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set _) ⊔ PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ' : Set _) : PointedCone ℝ _) : Set _)`. Rewrite using `[dual_sup, dual_union, dual_dual_eq_self h.fg, dual_dual_eq_self h'.fg]`. Rewrite using `[key]`. Conclude with `(h.dual.sup h'.dual).predual`.
-/
theorem IsRationalPolyhedral.inf {σ σ' : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (h : IsRationalPolyhedral (toRealSpan N) σ) (h' : IsRationalPolyhedral (toRealSpan N) σ') :
    IsRationalPolyhedral (toRealSpan N) (σ ⊓ σ') := by
  classical
  have key : σ ⊓ σ' = PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] _)
      ((PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set _) ⊔
        PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ' : Set _) : PointedCone ℝ _) : Set _) := by
    rw [dual_sup, dual_union, dual_dual_eq_self h.fg, dual_dual_eq_self h'.fg]
  rw [key]
  exact (h.dual.sup h'.dual).predual

end Operations

section Gordan

variable {N : Type*} [AddCommGroup N]

def dualMonoid (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : AddSubmonoid (Dual ℤ N) :=
  latticePoints (toRealDual N) (dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set (ℝ ⊗[ℤ] N)))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dualMonoid {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)} {m : Dual ℤ N} :
    m ∈ dualMonoid σ ↔ ∀ x ∈ σ, 0 ≤ toRealDual N m x := Iff.rfl

variable [Module.Free ℤ N] [Module.Finite ℤ N]

/- English proof (translation)
Take `⟨T, rfl⟩` from `hτ`. Set `e` to `Module.Free.chooseBasis ℤ N`. Set `B : Module.Free.ChooseBasisIndex ℤ N → ℤ` to `fun j => ∑ t ∈ T, |t (e j)|`. Set `K : Set (Dual ℤ N)` to `{m | m ∈ latticePoints (toRealDual N) (hull ℝ (toRealDual N '' T)) ∧ ∀ j, m (e j) ∈ Set.Icc (-B j) (B j)}`. Establish `hKfin : K.Finite`.

Establish `hbig : ((fun m : Dual ℤ N => fun j => m (e j)) ⁻¹' Set.univ.pi (fun j => Set.Icc (-B j) (B j))).Finite` using `(Set.Finite.pi (fun j => Set.finite_Icc _ _)).preimage (fun m _ m' _ h => e.ext fun j => congrFun h j)`. Conclude with `hbig.subset fun m hm => Set.mem_preimage.2 (Set.mem_univ_pi.2 fun j => hm.2 j)`. Use `⟨(hKfin.union T.finite_toSet).toFinset, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.coe_toFinset]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[AddSubmonoid.closure_le]`. Introduce and unpack `m (hm | hm)`. Conclude with `hm.1`. Conclude with `subset_hull ⟨m, hm, rfl⟩`. Introduce `m hm`.

Take `⟨c, hc, hcm⟩` from `(mem_hull_image_finset_iff T (toRealDual N)).1 hm`. Use `replace hcm : ∑ t ∈ T, c t • toRealDual N t = toRealDual N m := hcm`. Use `set m' := m - ∑ t ∈ T, (⌊c t⌋₊) • t with hm'`. Establish `him' : toRealDual N m' = ∑ t ∈ T, (c t - ⌊c t⌋₊) • toRealDual N t`. Rewrite using `[hm', map_sub, map_sum, ← hcm, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]`. Conclude with `(sub_smul _ _ _).symm`. Establish `hm'K : m' ∈ K`. Use `⟨?_, fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_latticePoints, him']`. Conclude with `(mem_hull_image_finset_iff T (toRealDual N)).2 ⟨fun t => c t - ⌊c t⌋₊, fun t => sub_nonneg.2 (Nat.floor_le (hc t)), rfl⟩`. Establish `hval : (m' (e j) : ℝ) = ∑ t ∈ T, (c t - ⌊c t⌋₊) * (t (e j) : ℝ)`. Rewrite using `[← toRealDual_apply_toRealSpan, him']`. Express the relevant statement in the definitionally equal form `Dual.eval ℝ (ℝ ⊗[ℤ] N) (toRealSpan N (e j)) (∑ t ∈ T, (c t - ⌊c t⌋₊) • toRealDual N t) = _`.

Rewrite using `[map_sum]`. Simplify using the standard rewrite rules. Establish `hbound : |(m' (e j) : ℝ)| ≤ (B j : ℝ)`. Rewrite using `[hval]`. Simplify using `only [B]`.

Use `push_cast`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)` and prove the remaining obligations. Rewrite using `[abs_mul]`. Establish `h0 : 0 ≤ c t - ⌊c t⌋₊` using `sub_nonneg.2 (Nat.floor_le (hc t))`. Establish `h1 : c t - ⌊c t⌋₊ ≤ 1` using `by linarith [Nat.lt_floor_add_one (c t)]`.

Rewrite using `[abs_of_nonneg h0]`. Conclude with `mul_le_of_le_one_left (abs_nonneg _) h1`. Establish `h2 : |m' (e j)| ≤ B j` using `by exact_mod_cast hbound`. Conclude with `Set.mem_Icc.2 (abs_le.1 h2)`. Establish `hmeq : m = m' + ∑ t ∈ T, (⌊c t⌋₊) • t` using `by rw [hm', sub_add_cancel]`.

Rewrite using `[hmeq]`. Conclude with `add_mem (AddSubmonoid.subset_closure (Or.inl hm'K)) (AddSubmonoid.sum_mem _ fun t ht => AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (show t ∈ K ∪ (T : Set (Dual ℤ N)) from Or.inr ht)) _)`.
-/
theorem latticePoints_fg {τ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))}
    (hτ : IsRationalPolyhedral (toRealDual N) τ) : (latticePoints (toRealDual N) τ).FG := by
  classical
  obtain ⟨T, rfl⟩ := hτ
  let e := Module.Free.chooseBasis ℤ N
  let B : Module.Free.ChooseBasisIndex ℤ N → ℤ := fun j => ∑ t ∈ T, |t (e j)|
  let K : Set (Dual ℤ N) := {m | m ∈ latticePoints (toRealDual N) (hull ℝ (toRealDual N '' T)) ∧
    ∀ j, m (e j) ∈ Set.Icc (-B j) (B j)}
  have hKfin : K.Finite := by
    have hbig : ((fun m : Dual ℤ N => fun j => m (e j)) ⁻¹'
        Set.univ.pi (fun j => Set.Icc (-B j) (B j))).Finite :=
      (Set.Finite.pi (fun j => Set.finite_Icc _ _)).preimage
        (fun m _ m' _ h => e.ext fun j => congrFun h j)
    exact hbig.subset fun m hm => Set.mem_preimage.2 (Set.mem_univ_pi.2 fun j => hm.2 j)
  refine ⟨(hKfin.union T.finite_toSet).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  apply le_antisymm
  · rw [AddSubmonoid.closure_le]
    rintro m (hm | hm)
    · exact hm.1
    · exact subset_hull ⟨m, hm, rfl⟩
  · intro m hm
    obtain ⟨c, hc, hcm⟩ := (mem_hull_image_finset_iff T (toRealDual N)).1 hm
    replace hcm : ∑ t ∈ T, c t • toRealDual N t = toRealDual N m := hcm
    set m' := m - ∑ t ∈ T, (⌊c t⌋₊) • t with hm'
    have him' : toRealDual N m' = ∑ t ∈ T, (c t - ⌊c t⌋₊) • toRealDual N t := by
      rw [hm', map_sub, map_sum, ← hcm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]
      exact (sub_smul _ _ _).symm
    have hm'K : m' ∈ K := by
      refine ⟨?_, fun j => ?_⟩
      · rw [mem_latticePoints, him']
        exact (mem_hull_image_finset_iff T (toRealDual N)).2
          ⟨fun t => c t - ⌊c t⌋₊, fun t => sub_nonneg.2 (Nat.floor_le (hc t)), rfl⟩
      · have hval : (m' (e j) : ℝ) = ∑ t ∈ T, (c t - ⌊c t⌋₊) * (t (e j) : ℝ) := by
          rw [← toRealDual_apply_toRealSpan, him']
          change Dual.eval ℝ (ℝ ⊗[ℤ] N) (toRealSpan N (e j))
            (∑ t ∈ T, (c t - ⌊c t⌋₊) • toRealDual N t) = _
          rw [map_sum]
          simp
        have hbound : |(m' (e j) : ℝ)| ≤ (B j : ℝ) := by
          rw [hval]
          simp only [B]
          push_cast
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
          rw [abs_mul]
          have h0 : 0 ≤ c t - ⌊c t⌋₊ := sub_nonneg.2 (Nat.floor_le (hc t))
          have h1 : c t - ⌊c t⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one (c t)]
          rw [abs_of_nonneg h0]
          exact mul_le_of_le_one_left (abs_nonneg _) h1
        have h2 : |m' (e j)| ≤ B j := by exact_mod_cast hbound
        exact Set.mem_Icc.2 (abs_le.1 h2)
    have hmeq : m = m' + ∑ t ∈ T, (⌊c t⌋₊) • t := by rw [hm', sub_add_cancel]
    rw [hmeq]
    exact add_mem (AddSubmonoid.subset_closure (Or.inl hm'K))
      (AddSubmonoid.sum_mem _ fun t ht => AddSubmonoid.nsmul_mem _
        (AddSubmonoid.subset_closure (show t ∈ K ∪ (T : Set (Dual ℤ N)) from Or.inr ht)) _)

/- English proof (translation)
The claim follows from `latticePoints_fg hσ.dual`.
-/
theorem dualMonoid_fg {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) : (dualMonoid σ).FG :=
  latticePoints_fg hσ.dual

end Gordan

end GroundTheory.Arith.Toric
