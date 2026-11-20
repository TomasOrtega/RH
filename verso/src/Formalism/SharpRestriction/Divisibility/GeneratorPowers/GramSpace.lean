import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramFormPhiStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinima
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasis

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix

namespace GramSpaceAlt

def GramSp (ι : Type) : Type := ι → ℝ

instance (ι : Type) : AddCommGroup (GramSp ι) := inferInstanceAs (AddCommGroup (ι → ℝ))
instance (ι : Type) : Module ℝ (GramSp ι) := inferInstanceAs (Module ℝ (ι → ℝ))
instance (ι : Type) [Fintype ι] : FiniteDimensional ℝ (GramSp ι) :=
  inferInstanceAs (FiniteDimensional ℝ (ι → ℝ))

def toG (ι : Type) : (ι → ℝ) ≃ₗ[ℝ] GramSp ι := LinearEquiv.refl ℝ (ι → ℝ)

def gBasis (ι : Type) [Fintype ι] [DecidableEq ι] : Basis ι ℝ (GramSp ι) := (Pi.basisFun ℝ ι).map (toG ι)

@[instance_reducible]
def gramCore {ι : Type} [Fintype ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) : InnerProductSpace.Core ℝ (GramSp ι) where
  inner x y := dotProduct ((toG ι).symm x) (G *ᵥ (toG ι).symm y)
  conj_inner_symm x y := by
    have hT : Gᵀ = G := by
      have h := hG.1
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simp only [conj_trivial]
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  re_inner_nonneg x := by
    simp only [RCLike.re_to_real]
    by_cases hx : (toG ι).symm x = 0
    · rw [hx, zero_dotProduct]
    · have h := hG.dotProduct_mulVec_pos hx
      rw [star_trivial] at h
      exact h.le
  add_left x y z := by simp only [map_add, add_dotProduct]
  smul_left x y r := by simp only [map_smul, smul_dotProduct, conj_trivial, smul_eq_mul]
  definite x h := by
    by_contra hx
    have hx' : (toG ι).symm x ≠ 0 := fun h0 => hx (by simpa using congrArg (toG ι) h0)
    have h2 := hG.dotProduct_mulVec_pos hx'
    rw [star_trivial] at h2
    exact h2.ne' h

end GramSpaceAlt

open GramSpaceAlt

/- English proof (translation)
Introduce `E _ _ cj hcj hcm w₀ hw₀ Y _ _ _ _ β hpos`. Take `⟨v, hv, hvb⟩` from `phiCMinima_holds E cj hcj hcm w₀ hw₀ Y β hpos`. Take `⟨ι, hι, b0, hG⟩` from `hpos`. Set `_` to `hι`. Use `set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hBdef`.

Use `set G : Matrix ι ι ℝ := Matrix.of fun i j => B (b0 i) (b0 j) with hGdef`. Set `cd : InnerProductSpace.Core ℝ (GramSp ι)` to `gramCore G hG`. Set `_ : NormedAddCommGroup (GramSp ι)` to `@InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ cd`. Set `_ : InnerProductSpace ℝ (GramSp ι)` to `InnerProductSpace.ofCore cd.toCore`. Set `ψ0 : Y →ₗ[ℤ] (ι → ℝ)` to `{ toFun := fun y i => (b0.repr y i : ℝ) map_add' := fun y z => by funext i; simp map_smul' := fun c y => by funext i; simp }`.

Set `ψ : Y →ₗ[ℤ] GramSp ι` to `((toG ι).toLinearMap.restrictScalars ℤ).comp ψ0`. Establish `hψ_apply : ∀ y, (toG ι).symm (ψ y) = ψ0 y` using `fun y => rfl`. Establish `key : ∀ y z, B y z = ∑ i, ∑ j, (b0.repr y i : ℝ) * ((b0.repr z j : ℝ) * B (b0 i) (b0 j))`. Introduce `y z`. Rewrite using `[← LinearMap.sum_repr_mul_repr_mul b0 b0 (B := B) y z, Finsupp.sum_fintype _ _ (by simp)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_fintype _ _ (by simp)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [zsmul_eq_mul]`. Establish `hin : ∀ y z, inner ℝ (ψ y) (ψ z) = B y z`.

Introduce `y z`. Rewrite using `[key]`. Express the relevant statement in the definitionally equal form `dotProduct (ψ0 y) (G *ᵥ ψ0 z) = _`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [ψ0, LinearMap.coe_mk, AddHom.coe_mk, hGdef, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnorm : ∀ y, ‖ψ y‖ ^ 2 = B y y` using `fun y => by`. Rewrite using `[← real_inner_self_eq_norm_sq, hin]`.

Establish `hψX : ∀ y, ψ y ∈ Submodule.span ℤ (Set.range (gBasis ι))`. Introduce `y`. Rewrite using `[(gBasis ι).mem_span_iff_repr_mem ℤ]`. Introduce `i`. Use `⟨b0.repr y i, ?_⟩` and prove the remaining obligations.

Simplify using `only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq, eq_intCast]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective ψ`. Introduce `y z h`. Apply `b0.ext_elem` to reduce the goal to its premises.

Introduce `i`. Establish `h2` using `congrArg (fun x => ((toG ι).symm x) i) h`. Simplify using `only [hψ_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h2`. Conclude with `h2` after adjusting the coercions. Establish `hsurj : ∀ x ∈ Submodule.span ℤ (Set.range (gBasis ι)), ∃ y, ψ y = x`.

Introduce `x hx`. Establish `h` using `((gBasis ι).mem_span_iff_repr_mem ℤ x).1 hx`. Use `choose c hc using h`. Use `⟨b0.equivFun.symm c, ?_⟩` and prove the remaining obligations. Apply `(toG ι).symm.injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Rewrite using `[hψ_apply]`. Simplify using `only [ψ0, LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[show b0.repr (b0.equivFun.symm c) i = c i from by`. Rewrite using `[← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]]`.

Use `hc i` as an intermediate fact. Simplify using `only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this`. Conclude with `this`. Set `eX : Y ≃ₗ[ℤ] Submodule.span ℤ (Set.range (gBasis ι))` to `LinearEquiv.ofBijective (ψ.codRestrict _ hψX) ⟨fun y z h => hinj (congrArg Subtype.val h), fun x => by`. Take `⟨y, hy⟩` from `hsurj x x.2`.

Conclude with `⟨y, Subtype.ext hy⟩⟩`. Establish `heX : ∀ x, ψ (eX.symm x) = (x : GramSp ι)` using `fun x => congrArg Subtype.val (eX.apply_symm_apply x)`. Establish `hdY : finrank ℤ Y = Fintype.card ι` using `finrank_eq_card_basis b0`. Establish `hdV : finrank ℝ (GramSp ι) = Fintype.card ι` using `finrank_eq_card_basis (gBasis ι)`. Establish `hd : finrank ℤ Y = finrank ℝ (GramSp ι)` using `hdY.trans hdV.symm`.

Establish `hdR : ((finrank ℝ (GramSp ι) : ℕ) : ℝ) = ((finrank ℤ Y : ℕ) : ℝ)` using `by rw [hd]`. Establish `hvR : LinearIndependent ℝ fun i => ψ (v i)`. Set `e : ι ≃ Fin (finrank ℤ Y)` to `Fintype.equivFinOfCardEq hdY.symm`. Set `Mz : Matrix (Fin (finrank ℤ Y)) (Fin (finrank ℤ Y)) ℤ` to `Matrix.of fun a i => b0.repr (v i) (e.symm a)`. Establish `hMz : Mz.det ≠ 0`.

Introduce `h0`. Take `⟨c, hc0, hc⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hc0` to reduce the goal to its premises. Establish `hsum : ∑ i, c i • v i = 0`. Apply `b0.ext_elem` to reduce the goal to its premises.

Introduce `k`. Establish `h1` using `congrFun hc (e k)`. Simplify using `only [Mz, mulVec, dotProduct, Matrix.of_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h1`. Simplify using `only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]`. Rewrite using `[← h1]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.1 hv c hsum i`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hdet : ((Int.castRingHom ℝ).mapMatrix Mz).det = 0`. Use `Matrix.exists_mulVec_eq_zero_iff.1 ⟨g, fun h => ?_, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hne`.

Conclude with `hi (congrFun h i)`. Use function extensionality and compare the values at `a`. Establish `h1` using `congrArg (fun x => ((toG ι).symm x) (e.symm a)) hg`. Simplify using `only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ_apply, map_zero, Pi.zero_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h1`. Simplify using `only [mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Mz, eq_intCast, Pi.zero_apply]`.

Rewrite using `[← h1]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Rewrite `hdet` using `[← RingHom.map_det, eq_intCast, Int.cast_eq_zero]`. Conclude with `hMz hdet`. Set `vX : Fin (finrank ℝ (GramSp ι)) → GramSp ι` to `fun i => ψ (v (Fin.cast hd.symm i))`.

Establish `hvX : LinearIndependent ℝ vX` using `hvR.comp _ (Fin.cast_injective _)`. Take `⟨b, hb1, hb2⟩` from `ReciprocityTheory.ChartRestriction.G.H1.reducedBasis_holds (GramSp ι) (Submodule.span ℤ (Set.range (gBasis ι))) ((|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * phiC cj β) vX hvX (fun i => hψX _) (fun i => …`. Use `⟨(b.map eX.symm).reindex (finCongr hd.symm), fun j => ?_, fun j z => ?_⟩` and prove the remaining obligations. Establish `hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι)`. Rewrite using `[Basis.reindex_apply, Basis.map_apply, heX]`.

Both sides reduce to the same expression. Rewrite using `[← hnorm, hbj]`. Establish `h1` using `hb1 (Fin.cast hd j)`. Rewrite `h1` using `[hdR]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι)`. Rewrite using `[Basis.reindex_apply, Basis.map_apply, heX]`. Both sides reduce to the same expression. Rewrite using `[← hin, hbj, ← hnorm]`. Establish `h2` using `hb2 (Fin.cast hd j) (ψ z) (hψX z)`.

Rewrite `h2` using `[hdR]`. Conclude with `h2`.
-/
theorem gram_form_phi_holds : GramFormPhiStatement := by
  classical
  intro E _ _ cj hcj hcm w₀ hw₀ Y _ _ _ _ β hpos
  obtain ⟨v, hv, hvb⟩ := phiCMinima_holds E cj hcj hcm w₀ hw₀ Y β hpos
  obtain ⟨ι, hι, b0, hG⟩ := hpos
  let _ := hι
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hBdef
  set G : Matrix ι ι ℝ := Matrix.of fun i j => B (b0 i) (b0 j) with hGdef
  let cd : InnerProductSpace.Core ℝ (GramSp ι) := gramCore G hG
  let _ : NormedAddCommGroup (GramSp ι) := @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ cd
  let _ : InnerProductSpace ℝ (GramSp ι) := InnerProductSpace.ofCore cd.toCore

  let ψ0 : Y →ₗ[ℤ] (ι → ℝ) :=
    { toFun := fun y i => (b0.repr y i : ℝ)
      map_add' := fun y z => by funext i; simp
      map_smul' := fun c y => by funext i; simp }
  let ψ : Y →ₗ[ℤ] GramSp ι := ((toG ι).toLinearMap.restrictScalars ℤ).comp ψ0
  have hψ_apply : ∀ y, (toG ι).symm (ψ y) = ψ0 y := fun y => rfl

  have key : ∀ y z, B y z = ∑ i, ∑ j, (b0.repr y i : ℝ) * ((b0.repr z j : ℝ) * B (b0 i) (b0 j)) := by
    intro y z
    rw [← LinearMap.sum_repr_mul_repr_mul b0 b0 (B := B) y z, Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zsmul_eq_mul]
  have hin : ∀ y z, inner ℝ (ψ y) (ψ z) = B y z := by
    intro y z
    rw [key]
    change dotProduct (ψ0 y) (G *ᵥ ψ0 z) = _
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ψ0, LinearMap.coe_mk, AddHom.coe_mk, hGdef, Matrix.of_apply]
    ring
  have hnorm : ∀ y, ‖ψ y‖ ^ 2 = B y y := fun y => by
    rw [← real_inner_self_eq_norm_sq, hin]

  have hψX : ∀ y, ψ y ∈ Submodule.span ℤ (Set.range (gBasis ι)) := by
    intro y
    rw [(gBasis ι).mem_span_iff_repr_mem ℤ]
    intro i
    refine ⟨b0.repr y i, ?_⟩
    simp only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq, eq_intCast]
    rfl
  have hinj : Function.Injective ψ := by
    intro y z h
    apply b0.ext_elem
    intro i
    have h2 := congrArg (fun x => ((toG ι).symm x) i) h
    simp only [hψ_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h2
    exact_mod_cast h2
  have hsurj : ∀ x ∈ Submodule.span ℤ (Set.range (gBasis ι)), ∃ y, ψ y = x := by
    intro x hx
    have h := ((gBasis ι).mem_span_iff_repr_mem ℤ x).1 hx
    choose c hc using h
    refine ⟨b0.equivFun.symm c, ?_⟩
    apply (toG ι).symm.injective
    funext i
    rw [hψ_apply]
    simp only [ψ0, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show b0.repr (b0.equivFun.symm c) i = c i from by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]]
    have := hc i
    simp only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq,
      eq_intCast] at this
    exact this
  let eX : Y ≃ₗ[ℤ] Submodule.span ℤ (Set.range (gBasis ι)) :=
    LinearEquiv.ofBijective (ψ.codRestrict _ hψX)
      ⟨fun y z h => hinj (congrArg Subtype.val h), fun x => by
        obtain ⟨y, hy⟩ := hsurj x x.2
        exact ⟨y, Subtype.ext hy⟩⟩
  have heX : ∀ x, ψ (eX.symm x) = (x : GramSp ι) := fun x =>
    congrArg Subtype.val (eX.apply_symm_apply x)

  have hdY : finrank ℤ Y = Fintype.card ι := finrank_eq_card_basis b0
  have hdV : finrank ℝ (GramSp ι) = Fintype.card ι := finrank_eq_card_basis (gBasis ι)
  have hd : finrank ℤ Y = finrank ℝ (GramSp ι) := hdY.trans hdV.symm
  have hdR : ((finrank ℝ (GramSp ι) : ℕ) : ℝ) = ((finrank ℤ Y : ℕ) : ℝ) := by rw [hd]

  have hvR : LinearIndependent ℝ fun i => ψ (v i) := by
    let e : ι ≃ Fin (finrank ℤ Y) := Fintype.equivFinOfCardEq hdY.symm
    let Mz : Matrix (Fin (finrank ℤ Y)) (Fin (finrank ℤ Y)) ℤ := Matrix.of fun a i => b0.repr (v i) (e.symm a)
    have hMz : Mz.det ≠ 0 := by
      intro h0
      obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      apply hc0
      have hsum : ∑ i, c i • v i = 0 := by
        apply b0.ext_elem
        intro k
        have h1 := congrFun hc (e k)
        simp only [Mz, mulVec, dotProduct, Matrix.of_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h1
        simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
          smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      funext i
      exact Fintype.linearIndependent_iff.1 hv c hsum i
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    have hdet : ((Int.castRingHom ℝ).mapMatrix Mz).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨g, fun h => ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne
        exact hi (congrFun h i)
      · funext a
        have h1 := congrArg (fun x => ((toG ι).symm x) (e.symm a)) hg
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ_apply, map_zero,
          Pi.zero_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h1
        simp only [mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Mz,
          eq_intCast, Pi.zero_apply]
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← RingHom.map_det, eq_intCast, Int.cast_eq_zero] at hdet
    exact hMz hdet

  let vX : Fin (finrank ℝ (GramSp ι)) → GramSp ι := fun i => ψ (v (Fin.cast hd.symm i))
  have hvX : LinearIndependent ℝ vX := hvR.comp _ (Fin.cast_injective _)
  obtain ⟨b, hb1, hb2⟩ := ReciprocityTheory.ChartRestriction.G.H1.reducedBasis_holds (GramSp ι)
    (Submodule.span ℤ (Set.range (gBasis ι)))
    ((|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
      (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * phiC cj β) vX hvX
    (fun i => hψX _) (fun i => by rw [hnorm]; exact hvb _)
  refine ⟨(b.map eX.symm).reindex (finCongr hd.symm), fun j => ?_, fun j z => ?_⟩
  · have hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι) := by
      rw [Basis.reindex_apply, Basis.map_apply, heX]
      rfl
    rw [← hnorm, hbj]
    have h1 := hb1 (Fin.cast hd j)
    rw [hdR] at h1
    calc ‖(b (Fin.cast hd j) : GramSp ι)‖ ^ 2 / 2 ≤ _ := h1
      _ = _ := by ring
  · have hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι) := by
      rw [Basis.reindex_apply, Basis.map_apply, heX]
      rfl
    rw [← hin, hbj, ← hnorm]
    have h2 := hb2 (Fin.cast hd j) (ψ z) (hψX z)
    rw [hdR] at h2
    exact h2

end Formalism.MainNotions.ModuliIntegralCharts.H1
