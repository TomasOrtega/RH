import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinIndOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
  Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Establish `e : G.det = (SP K 𝔭).subtype (Matrix.det (Matrix.of fun i j => (⟨G i j, hG i j⟩ : SP K 𝔭)))`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `SetLike.coe_mem _`.
-/
theorem det_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {G : Matrix κ κ K} (hG : Ent (SP K 𝔭) G) :
    G.det ∈ SP K 𝔭 := by
  have e : G.det = (SP K 𝔭).subtype
      (Matrix.det (Matrix.of fun i j => (⟨G i j, hG i j⟩ : SP K 𝔭))) := by
    rw [RingHom.map_det]; rfl
  rw [e]
  exact SetLike.coe_mem _

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv, hGv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Apply `hv` to reduce the goal to its premises. Establish `hy : ∀ x, h x (β.equivFun.symm v) = 0`. Introduce `x`.

Rewrite using `[form_repr h β, LinearEquiv.apply_symm_apply, hGv]`. Simplify using the standard rewrite rules. Establish `h0 : β.equivFun.symm v = 0`. Apply `hnd` to reduce the goal to its premises. Introduce `y`.

Use `hs.eq y (β.equivFun.symm v)` as an intermediate fact. Rewrite using `[← this, hy y, map_zero]`. Conclude with `β.equivFun.symm.injective (by rw [h0, map_zero])`.
-/
theorem gram_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) (β : Basis κ K V) :
    (gramK h β).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hy : ∀ x, h x (β.equivFun.symm v) = 0 := by
    intro x
    rw [form_repr h β, LinearEquiv.apply_symm_apply, hGv]
    simp
  have h0 : β.equivFun.symm v = 0 := by
    apply hnd
    intro y
    have := hs.eq y (β.equivFun.symm v)
    rw [← this, hy y, map_zero]
  exact β.equivFun.symm.injective (by rw [h0, map_zero])

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) K) (x : K) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨t, -, rfl⟩` from `hx`. Conclude with `(hF _).mpr ⟨(t : F), rfl⟩`. Consider the case `one => simp`.

Consider the case `mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]`.
-/
private lemma star_fix_lemma_2 (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    exact (hF _).mpr ⟨(t : F), rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]

/- English proof (translation)
Rewrite `ha`, the goal using `[mem_SP_iff_locF]`. Take `⟨s, hs', hsa⟩` from `(mem_locF_lemma 𝔭 _ a).mp ha`. Take `⟨z, hz⟩` from `Submodule.mem_one.mp hsa`. Take `⟨r, hr⟩` from `Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range z`. Use `(mem_locF_lemma 𝔭 _ _).mpr ⟨s, hs', Submodule.mem_one.mpr ⟨r, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hr, hz, Algebra.smul_def, Algebra.smul_def, star_mul', star_fix_lemma_2 hF hs']`.
-/
private lemma star_mem_SP' (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {a : K}
    (ha : a ∈ SP K 𝔭) : star a ∈ SP K 𝔭 := by
  rw [mem_SP_iff_locF] at ha ⊢
  obtain ⟨s, hs', hsa⟩ := (mem_locF_lemma 𝔭 _ a).mp ha
  obtain ⟨z, hz⟩ := Submodule.mem_one.mp hsa
  obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range z
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨s, hs', Submodule.mem_one.mpr ⟨r, ?_⟩⟩
  rw [hr, hz, Algebra.smul_def, Algebra.smul_def, star_mul', star_fix_lemma_2 hF hs']

/- English proof (translation)
Establish `hdet` using `gram_det_ne_zero hs hnd β`. Establish `hunit : IsUnit (gramK h β).det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hmemL : ∀ x, x ∈ locF 𝔭 (spanO β) ↔ ∀ i, β.equivFun x i ∈ SP K 𝔭` using `fun x => mem_locF_iff_repr β x`. Establish `hβ : ∀ i, β i ∈ locF 𝔭 (spanO β)` using `fun i => by`. Simplify using `using smul_basis_mem β (SP K 𝔭).one_mem i`.

Establish `hdual : ∀ x ∈ locF 𝔭 (spanO β), ∀ y ∈ locF 𝔭 (spanO β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`. Introduce `x hx`. Rewrite `hx` using `[← hsd]`. Conclude with `hx`. Establish `hG : Ent (SP K 𝔭) (gramK h β)` using `fun i j => mem_SP_iff_locF.mpr (hdual _ (hβ j) _ (hβ i))`.

Establish `hinv : gramK h β * (gramK h β)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hunit`. Establish `hcol : ∀ k l, (gramK h β)⁻¹ l k ∈ SP K 𝔭`. Introduce `k l`. Take `⟨x, hxdef⟩ : ∃ x : V, β.equivFun x = (gramK h β)⁻¹ *ᵥ Pi.single k (1 : K)` from `⟨_, LinearEquiv.apply_symm_apply _ _⟩`. Establish `hx : x ∈ locF 𝔭 (spanO β)`.

Rewrite using `[← hsd]`. Express the relevant statement in the definitionally equal form `∀ y ∈ locF 𝔭 (spanO β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)`. Introduce `y hy`. Rewrite using `[← mem_SP_iff_locF, form_repr h β, hxdef, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Use `star_mem_SP' hF ((hmemL y).mp hy k) using 1` and compare the differences between its conclusion and the goal.

Simplify using `[dotProduct, Pi.single_apply]`. Establish `hc` using `(hmemL x).mp hx l`. Rewrite `hc` using `[hxdef]`. Simplify `hc` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hdi : ((gramK h β)⁻¹).det = (gramK h β).det⁻¹`.

Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Use `⟨det_mem_SP hG, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdi]`. Conclude with `det_mem_SP fun l k => hcol k l`.
-/
theorem det_unit_of_selfdual (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) (β : Basis κ K V) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]
    (hsd : dualF h 𝔭 (locF 𝔭 (spanO β)) = locF 𝔭 (spanO β)) :
    (gramK h β).det ∈ SP K 𝔭 ∧ (gramK h β).det⁻¹ ∈ SP K 𝔭 := by
  have hdet := gram_det_ne_zero hs hnd β
  have hunit : IsUnit (gramK h β).det := isUnit_iff_ne_zero.mpr hdet
  have hmemL : ∀ x, x ∈ locF 𝔭 (spanO β) ↔ ∀ i, β.equivFun x i ∈ SP K 𝔭 :=
    fun x => mem_locF_iff_repr β x
  have hβ : ∀ i, β i ∈ locF 𝔭 (spanO β) := fun i => by
    simpa using smul_basis_mem β (SP K 𝔭).one_mem i
  have hdual : ∀ x ∈ locF 𝔭 (spanO β), ∀ y ∈ locF 𝔭 (spanO β),
      h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro x hx
    rw [← hsd] at hx
    exact hx
  have hG : Ent (SP K 𝔭) (gramK h β) := fun i j =>
    mem_SP_iff_locF.mpr (hdual _ (hβ j) _ (hβ i))
  have hinv : gramK h β * (gramK h β)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hcol : ∀ k l, (gramK h β)⁻¹ l k ∈ SP K 𝔭 := by
    intro k l
    obtain ⟨x, hxdef⟩ : ∃ x : V, β.equivFun x = (gramK h β)⁻¹ *ᵥ Pi.single k (1 : K) :=
      ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    have hx : x ∈ locF 𝔭 (spanO β) := by
      rw [← hsd]
      change ∀ y ∈ locF 𝔭 (spanO β), h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
      intro y hy
      rw [← mem_SP_iff_locF, form_repr h β, hxdef, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      convert star_mem_SP' hF ((hmemL y).mp hy k) using 1
      simp [dotProduct, Pi.single_apply]
    have hc := (hmemL x).mp hx l
    rw [hxdef] at hc
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hc
  have hdi : ((gramK h β)⁻¹).det = (gramK h β).det⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨det_mem_SP hG, ?_⟩
  rw [← hdi]
  exact det_mem_SP fun l k => hcol k l

/- English proof (translation)
Use extensionality with `i j`. Establish `e : gramK h γ i j = h (γ i) (γ j)` using `rfl`. Rewrite using `[e, form_repr h β, Matrix.mul_assoc]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Basis.toMatrix_apply, Basis.equivFun_apply, Pi.star_apply]`.
-/
theorem gram_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    gramK h γ = (β.toMatrix γ)ᴴ * gramK h β * β.toMatrix γ := by
  ext i j
  have e : gramK h γ i j = h (γ i) (γ j) := rfl
  rw [e, form_repr h β, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    Basis.toMatrix_apply, Basis.equivFun_apply, Pi.star_apply]

/- English proof (translation)
Rewrite using `[gram_change h β γ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`.
-/
theorem gram_det_change (h : V →ₗ⋆[K] V →ₗ[K] K) (β γ : Basis κ K V) :
    (gramK h γ).det = star (β.toMatrix γ).det * (gramK h β).det * (β.toMatrix γ).det := by
  rw [gram_change h β γ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

/- English proof (translation)
Establish `e : gramK h γ = Matrix.diagonal fun s => h (γ s) (γ s)`. Use extensionality with `s t`. Distinguish the cases in `hst : s = t`. Substitute `hst` using the available equality. Simplify using `[gramK]`.

Simplify using `[gramK, Matrix.diagonal_apply_ne _ hst, ho s t hst]`. Rewrite using `[e, Matrix.det_diagonal]`.
-/
theorem gram_det_orth (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : Basis κ K V)
    (ho : ∀ s t, s ≠ t → h (γ s) (γ t) = 0) : (gramK h γ).det = ∏ s, h (γ s) (γ s) := by
  have e : gramK h γ = Matrix.diagonal fun s => h (γ s) (γ s) := by
    ext s t
    by_cases hst : s = t
    · subst hst; simp [gramK]
    · simp [gramK, Matrix.diagonal_apply_ne _ hst, ho s t hst]
  rw [e, Matrix.det_diagonal]

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
