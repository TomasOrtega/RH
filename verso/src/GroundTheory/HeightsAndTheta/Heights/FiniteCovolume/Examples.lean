import Mathlib
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

section General

variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]

/- English proof (translation)
Set `f : W →+ W` to `((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom`. Establish `hf : Function.Injective f` using `(γ : W ≃ₗ[E] W).injective`. Establish `hfx : ∀ y : W, f y = γ • y` using `fun y => rfl`. Establish `h1 : (ringMultiples E x).map f = ringMultiples E (γ • x)`. Rewrite using `[ringMultiples, ringMultiples, ← AddMonoidHom.range_comp]`.

Use `congr 1`. Use extensionality with `a`. Simplify using `only [AddMonoidHom.comp_apply, hfx]`. Simplify using `[Subgroup.smul_def, LinearEquiv.smul_def]`. Establish `h2 : La.map f = La` using `by conv_rhs => rw [← hγ]`.

Express the relevant statement in the definitionally equal form `La.map f = (γ : W ≃ₗ[E] W) • La`. Rewrite using `[AddSubgroup.pointwise_smul_def]`. Both sides reduce to the same expression. Establish `h3 : ((Submodule.span E {x}).toAddSubgroup).map f = (Submodule.span E {γ • x}).toAddSubgroup`. Use extensionality with `y`.

Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, ⟨c, rfl⟩, rfl⟩`. Conclude with `⟨c, by rw [hfx, smul_comm]⟩`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `⟨c • x, ⟨c, rfl⟩, by rw [hfx, smul_comm]⟩`. Unfold `lineIndex`. Use `conv_rhs => rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf]`. Rewrite using `[AddSubgroup.map_inf_eq _ _ f hf, h1, h2, h3]`.
-/
theorem lineIndex_smul {h : HermitianForm F E W} {La : AddSubgroup W} {γ : h.unitaryGroup}
    (hγ : γ • La = La) (x : W) : lineIndex E La (γ • x) = lineIndex E La x := by
  let f : W →+ W := ((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom
  have hf : Function.Injective f := (γ : W ≃ₗ[E] W).injective
  have hfx : ∀ y : W, f y = γ • y := fun y => rfl
  have h1 : (ringMultiples E x).map f = ringMultiples E (γ • x) := by
    rw [ringMultiples, ringMultiples, ← AddMonoidHom.range_comp]
    congr 1
    ext a
    simp only [AddMonoidHom.comp_apply, hfx]
    simp [Subgroup.smul_def, LinearEquiv.smul_def]
  have h2 : La.map f = La := by
    conv_rhs => rw [← hγ]
    change La.map f = (γ : W ≃ₗ[E] W) • La
    rw [AddSubgroup.pointwise_smul_def]
    rfl
  have h3 : ((Submodule.span E {x}).toAddSubgroup).map f =
      (Submodule.span E {γ • x}).toAddSubgroup := by
    ext y
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, by rw [hfx, smul_comm]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c • x, ⟨c, rfl⟩, by rw [hfx, smul_comm]⟩
  unfold lineIndex
  conv_rhs => rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf]
  rw [AddSubgroup.map_inf_eq _ _ f hf, h1, h2, h3]

end General

abbrev Eg : Type := CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ Eg := CyclotomicField.isCyclotomicExtension 4 ℚ

/- English proof (translation)
Rewrite using `[IsCyclotomicExtension.finrank (n := 4) Eg (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]`. Evaluate the decidable proposition.
-/
theorem finrank_Eg : finrank ℚ Eg = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Eg
    (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

instance : Algebra.IsQuadraticExtension ℚ Eg := { finrank_eq_two' := finrank_Eg }

instance : IsTotallyComplex Eg := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) Eg (by norm_num)

/- English proof (translation)
Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank Eg`. Rewrite `h1` using `[IsTotallyComplex.nrRealPlaces_eq_zero, finrank_Eg]`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_infinitePlace : Fintype.card (InfinitePlace Eg) = 1 := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank Eg
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, finrank_Eg] at h1
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
  omega

instance : Subsingleton (InfinitePlace Eg) :=
  Fintype.card_le_one_iff_subsingleton.mp card_infinitePlace.le

/- English proof (translation)
Rewrite using `[InfinitePlace.norm_embedding_eq]`. Conclude with `InfinitePlace.one_le_of_lt_one ha fun z hz => absurd (Subsingleton.elim z w) hz`.
-/
theorem one_le_norm_embedding (w : InfinitePlace Eg) {a : 𝓞 Eg} (ha : a ≠ 0) :
    1 ≤ ‖w.embedding (a : Eg)‖ := by
  rw [InfinitePlace.norm_embedding_eq]
  exact InfinitePlace.one_le_of_lt_one ha fun z hz => absurd (Subsingleton.elim z w) hz

def signs : Fin 2 → ℚˣ := ![1, -1]

def hG : HermitianForm ℚ Eg (Fin 2 → Eg) := diagForm signs

def vG : Basis (Fin 2) Eg (Fin 2 → Eg) := Pi.basisFun Eg (Fin 2)

/- English proof (translation)
Simplify using `only [hG, diagForm, signs, LinearMap.mk₂'ₛₗ_apply, Fin.sum_univ_two]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hG_apply (x y : Fin 2 → Eg) : hG.toSesq x y = conj ℚ Eg (x 0) * y 0 - conj ℚ Eg (x 1) * y 1 := by
  simp only [hG, diagForm, signs, LinearMap.mk₂'ₛₗ_apply, Fin.sum_univ_two]
  simp
  ring

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp only [Automorphic.gram_apply, vG, Pi.basisFun_apply] <;> rw [hG_apply] <;> simp`.
-/
theorem gram_hG : gram hG.toSesq vG = Matrix.diagonal ![1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Automorphic.gram_apply, vG, Pi.basisFun_apply] <;> rw [hG_apply] <;> simp

/- English proof (translation)
Rewrite using `[gramAt, gram_hG]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]`.
-/
theorem gramAt_hG (w : InfinitePlace Eg) : gramAt hG vG w = Matrix.diagonal ![1, -1] := by
  rw [gramAt, gram_hG]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

def MG : Majorant hG vG where
  P _ := 1
  posDef _ := Matrix.PosDef.one
  siegel w := by
    rw [gramAt_hG, Matrix.one_mul, Matrix.mul_one]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

def LaG : AddSubgroup (Fin 2 → Eg) :=
  (AddMonoidHom.compLeft (algebraMap (𝓞 Eg) Eg).toAddMonoidHom (Fin 2)).range

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ i`. Conclude with `(mem_integralClosure_iff ℤ Eg).2 (RingOfIntegers.isIntegral_coe (y i))`. Introduce `hx`. Conclude with `⟨fun i => ⟨x i, hx i⟩, rfl⟩`.
-/
theorem mem_LaG {x : Fin 2 → Eg} : x ∈ LaG ↔ ∀ i, x i ∈ integralClosure ℤ Eg := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (mem_integralClosure_iff ℤ Eg).2 (RingOfIntegers.isIntegral_coe (y i))
  · intro hx
    exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩

/- English proof (translation)
Rewrite `*` using `[mem_integralClosure_iff ℤ Eg]`. Conclude with `hz.map ((conj ℚ Eg).toAlgHom.restrictScalars ℤ)`.
-/
theorem conj_mem {z : Eg} (hz : z ∈ integralClosure ℤ Eg) : conj ℚ Eg z ∈ integralClosure ℤ Eg := by
  rw [mem_integralClosure_iff ℤ Eg] at *
  exact hz.map ((conj ℚ Eg).toAlgHom.restrictScalars ℤ)

/- English proof (translation)
Rewrite using `[mem_LaG]`. Introduce `j`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `only [Pi.single_eq_same]`.

Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hij]`. Conclude with `zero_mem _`.
-/
theorem single_mem_LaG (i : Fin 2) : (Pi.single i 1 : Fin 2 → Eg) ∈ LaG := by
  rw [mem_LaG]
  intro j
  by_cases hij : j = i
  · subst hij
    simp only [Pi.single_eq_same]
    exact one_mem _
  · rw [Pi.single_eq_of_ne hij]
    exact zero_mem _

/- English proof (translation)
Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[mem_LaG]`. Rewrite using `[hG_apply]`. Conclude with `sub_mem (mul_mem (conj_mem (hx 0)) (hy 0)) (mul_mem (conj_mem (hx 1)) (hy 1))`.
-/
theorem integral_LaG : IsIntegralOn hG LaG := by
  intro x hx y hy
  rw [mem_LaG] at hx hy
  rw [hG_apply]
  exact sub_mem (mul_mem (conj_mem (hx 0)) (hy 0)) (mul_mem (conj_mem (hx 1)) (hy 1))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Establish `hy' : ∀ x ∈ LaG, hG.toSesq y x ∈ integralClosure ℤ Eg` using `hy`. Rewrite using `[mem_LaG]`. Introduce `i`.

Establish `h0` using `hy' _ (single_mem_LaG 0)`. Establish `h1` using `hy' _ (single_mem_LaG 1)`. Rewrite `h0`, `h1` using `[hG_apply]`. Simplify using `at h0 h1`. Rewrite using `[← conj_conj (F := ℚ) (y i)]`.

Use `fin_cases i`. Conclude with `conj_mem h0`. Conclude with `conj_mem (by simpa using neg_mem h1)`. Introduce `x hx y hy`. Conclude with `integral_LaG x hx y hy`.
-/
theorem dual_LaG : dualLattice hG LaG = LaG := by
  apply le_antisymm
  · intro y hy
    have hy' : ∀ x ∈ LaG, hG.toSesq y x ∈ integralClosure ℤ Eg := hy
    rw [mem_LaG]
    intro i
    have h0 := hy' _ (single_mem_LaG 0)
    have h1 := hy' _ (single_mem_LaG 1)
    rw [hG_apply] at h0 h1
    simp at h0 h1
    rw [← conj_conj (F := ℚ) (y i)]
    fin_cases i
    · exact conj_mem h0
    · exact conj_mem (by simpa using neg_mem h1)
  · intro x hx y hy
    exact integral_LaG x hx y hy

/- English proof (translation)
The claim follows from `{ smul_mem := fun a x hx => by rw [mem_LaG] at hx ⊢ intro i simp only [Pi.smul_apply, smul_eq_mul] exact mul_mem ((mem_integralClosure_iff ℤ Eg).2 (RingOfIntegers.isIntegral_coe a)) (hx i) fg := by have : AddGroup.FG (Fin 2 → 𝓞 Eg) := Module.Finite.iff_addGroup_fg.mp inferInstanc …`.
-/
theorem isDIntegral_LaG : IsDIntegral hG 1 LaG where
  isLattice :=
    { smul_mem := fun a x hx => by
        rw [mem_LaG] at hx ⊢
        intro i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_mem ((mem_integralClosure_iff ℤ Eg).2 (RingOfIntegers.isIntegral_coe a)) (hx i)
      fg := by
        have : AddGroup.FG (Fin 2 → 𝓞 Eg) := Module.Finite.iff_addGroup_fg.mp inferInstance
        exact (AddGroup.fg_iff_addSubgroup_fg _).1
          (AddGroup.fg_of_surjective (AddMonoidHom.rangeRestrict_surjective _))
      span_eq_top := by
        rw [eq_top_iff, ← (Pi.basisFun Eg (Fin 2)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        simpa using single_mem_LaG i }
  integral := integral_LaG
  index_ne_zero := by rw [dual_LaG, AddSubgroup.relIndex_self]; norm_num
  index_le := by rw [dual_LaG, AddSubgroup.relIndex_self]

def v0 : Fin 2 → Eg := fun _ => 1

/- English proof (translation)
Rewrite using `[mem_LaG]`. Introduce `i`. Conclude with `one_mem _`.
-/
theorem isotropicVector_mem_lattice : v0 ∈ LaG := by
  rw [mem_LaG]
  intro i
  exact one_mem _

/- English proof (translation)
Introduce `h` and use `one_ne_zero (congrFun h 0)`.
-/
theorem isotropicVector_ne_zero : v0 ≠ 0 := fun h => one_ne_zero (congrFun h 0)

/- English proof (translation)
Rewrite using `[hG_apply]`. Simplify using `[v0]`.
-/
theorem hermitian_isotropicVector : hG.toSesq v0 v0 = 0 := by
  rw [hG_apply]
  simp [v0]

def lG : Submodule Eg (Fin 2 → Eg) := Submodule.span Eg {v0}

/- English proof (translation)
Use `⟨finrank_span_singleton isotropicVector_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hx`. Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Rewrite using `[LinearMap.map_smulₛₗ₂, map_smul, hermitian_isotropicVector]`.

Simplify using the standard rewrite rules.
-/
theorem isIsotropicLine_lG : IsIsotropicLine hG lG := by
  refine ⟨finrank_span_singleton isotropicVector_ne_zero, ?_⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [LinearMap.map_smulₛₗ₂, map_smul, hermitian_isotropicVector]
  simp

/- English proof (translation)
Apply `AddSubgroup.relIndex_eq_one.2` to reduce the goal to its premises. Introduce and unpack `y ⟨hyL, hyl⟩`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hyl`. Establish `hc : c ∈ integralClosure ℤ Eg`. Use `mem_LaG.1 hyL 0` as an intermediate fact.

Simplify `this` using `[v0]`. Conclude with `⟨⟨c, hc⟩, rfl⟩`.
-/
theorem lineIndex_isotropicVector : lineIndex Eg LaG v0 = 1 := by
  apply AddSubgroup.relIndex_eq_one.2
  rintro y ⟨hyL, hyl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyl
  have hc : c ∈ integralClosure ℤ Eg := by
    have := mem_LaG.1 hyL 0
    simpa [v0] using this
  exact ⟨⟨c, hc⟩, rfl⟩

def muG : Measure (archUnitary hG vG) := Measure.haar

instance : muG.IsHaarMeasure := by
  unfold muG
  infer_instance

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`.
-/
theorem re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/- English proof (translation)
Rewrite using `[Majorant.len, Fintype.sum_subsingleton _ w]`. Simplify using `[MG, dotProduct, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]`.
-/
theorem len_MG (y : InfinitePlace Eg → Fin 2 → ℂ) (w : InfinitePlace Eg) :
    MG.len y = Real.sqrt (‖y w 0‖ ^ 2 + ‖y w 1‖ ^ 2) := by
  rw [Majorant.len, Fintype.sum_subsingleton _ w]
  simp [MG, dotProduct, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `[invApply]`.
-/
theorem invApply_one (y : InfinitePlace Eg → Fin 2 → ℂ) :
    invApply (1 : archUnitary hG vG) y = y := by
  funext w
  simp [invApply]

/- English proof (translation)
Simplify using `[vecAt, vG]`.
-/
theorem vecAt_apply (x : Fin 2 → Eg) (w : InfinitePlace Eg) (i : Fin 2) :
    vecAt vG x w i = w.embedding (x i) := by
  simp [vecAt, vG]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace Eg)` from `inferInstance`. Rewrite using `[invApply_one, len_MG _ w, vecAt_apply, vecAt_apply]`. Rewrite using `[Real.one_le_sqrt]`. Establish `key : ∀ i, x i ≠ 0 → 1 ≤ ‖w.embedding (x i)‖ ^ 2`. Introduce `i hi`.

Establish `h1` using `one_le_norm_embedding w (a := ⟨x i, mem_LaG.1 hx i⟩) (fun h => hi (congrArg (fun a : 𝓞 Eg => (a : Eg)) h))`. Express the relevant statement in the definitionally equal form `1 ≤ ‖w.embedding (x i)‖ at h1`. Use the polynomial consequences of the given equalities and inequalities. Distinguish the cases in `h0 : x 0 = 0`. Establish `h1 : x 1 ≠ 0`.

Introduce `h1`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `h0`.

Conclude with `h1`. Use `key 1 h1` as an intermediate fact. Combine the linear relations using `[sq_nonneg ‖w.embedding (x 0)‖]`. Use `key 0 h0` as an intermediate fact. Combine the linear relations using `[sq_nonneg ‖w.embedding (x 1)‖]`.
-/
theorem one_le_len {x : Fin 2 → Eg} (hx : x ∈ LaG) (hx0 : x ≠ 0) :
    1 ≤ MG.len (invApply (1 : archUnitary hG vG) (vecAt vG x)) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace Eg) := inferInstance
  rw [invApply_one, len_MG _ w, vecAt_apply, vecAt_apply]
  rw [Real.one_le_sqrt]
  have key : ∀ i, x i ≠ 0 → 1 ≤ ‖w.embedding (x i)‖ ^ 2 := by
    intro i hi
    have h1 := one_le_norm_embedding w (a := ⟨x i, mem_LaG.1 hx i⟩)
      (fun h => hi (congrArg (fun a : 𝓞 Eg => (a : Eg)) h))
    change 1 ≤ ‖w.embedding (x i)‖ at h1
    nlinarith
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx0
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have := key 1 h1
    linarith [sq_nonneg ‖w.embedding (x 0)‖]
  · have := key 0 h0
    linarith [sq_nonneg ‖w.embedding (x 1)‖]

def Bm : Matrix (Fin 2) (Fin 2) ℂ := !![5 / 4, 3 / 4; 3 / 4, 5 / 4]

/- English proof (translation)
Simplify using `[Bm, Matrix.det_fin_two]`. Evaluate the numerical expressions.
-/
theorem det_Bm : Bm.det = 1 := by
  simp [Bm, Matrix.det_fin_two]
  norm_num

def gBu : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero Bm (by rw [det_Bm]; norm_num)

def gB : archUnitary hG vG :=
  ⟨fun _ => gBu, mem_archUnitary.2 fun w => by
    rw [gramAt_hG]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gBu, Bm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, map_ofNat] <;> norm_num⟩

/- English proof (translation)
Use function extensionality and compare the values at `w`. Establish `hv : vecAt vG v0 w = (gBu : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (fun _ => (1 / 2 : ℂ))`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;>`. Apply the tactic sequence `simp [vecAt_apply, v0, gBu, Bm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num`.

Establish `hm : ((((gB⁻¹ : archUnitary hG vG) : InfinitePlace Eg → GL (Fin 2) ℂ) w : Matrix (Fin 2) (Fin 2) ℂ) * (gBu : Matrix (Fin 2) (Fin 2) ℂ)) = 1` using `by show ((gBu⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * gBu = 1`. Conclude with `Units.inv_mul gBu`. Simplify using `only [invApply]`. Rewrite using `[hv, Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]`.
-/
theorem boost_isotropicVector_eq_half : invApply gB (vecAt vG v0) = fun _ _ => 1 / 2 := by
  funext w
  have hv : vecAt vG v0 w = (gBu : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (fun _ => (1 / 2 : ℂ)) := by
    funext i
    fin_cases i <;>
      simp [vecAt_apply, v0, gBu, Bm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have hm : ((((gB⁻¹ : archUnitary hG vG) : InfinitePlace Eg → GL (Fin 2) ℂ) w :
      Matrix (Fin 2) (Fin 2) ℂ) * (gBu : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    show ((gBu⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * gBu = 1
    exact Units.inv_mul gBu
  simp only [invApply]
  rw [hv, Matrix.mulVec_mulVec, hm, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace Eg)` from `inferInstance`. Rewrite using `[boost_isotropicVector_eq_half, len_MG _ w, Real.sqrt_lt' one_pos]`. Evaluate the numerical expressions.
-/
theorem majorantLength_boost_isotropic_lt_one : MG.len (invApply gB (vecAt vG v0)) < 1 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace Eg) := inferInstance
  rw [boost_isotropicVector_eq_half, len_MG _ w, Real.sqrt_lt' one_pos]
  norm_num

def e0 : Fin 2 → Eg := Pi.single 0 1

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace Eg)` from `inferInstance`. Rewrite using `[invApply_one, len_MG _ w, vecAt_apply, vecAt_apply]`. Simplify using `[e0]`.
-/
theorem majorantLength_firstBasisVector : MG.len (invApply (1 : archUnitary hG vG) (vecAt vG e0)) = 1 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace Eg) := inferInstance
  rw [invApply_one, len_MG _ w, vecAt_apply, vecAt_apply]
  simp [e0]

/- English proof (translation)
Rewrite using `[majorantLength_firstBasisVector]`. Conclude with `one_le_len hy hy0`.
-/
theorem firstBasisVector_shortest (y : Fin 2 → Eg) (hy : y ∈ LaG) (hy0 : y ≠ 0) :
    MG.len (invApply (1 : archUnitary hG vG) (vecAt vG e0)) ≤
      MG.len (invApply (1 : archUnitary hG vG) (vecAt vG y)) := by
  rw [majorantLength_firstBasisVector]
  exact one_le_len hy hy0

/- English proof (translation)
The claim follows from `single_mem_LaG 0`.
-/
theorem unitaryTransvection_zero_first_mem_closure : e0 ∈ LaG := single_mem_LaG 0

/- English proof (translation)
Introduce `h` and use `by have := congrFun h 0 simp [e0] at this`.
-/
theorem first_basis_ne_zero : e0 ≠ 0 := fun h => by
  have := congrFun h 0
  simp [e0] at this

/- English proof (translation)
Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 Eg)) = 2 * finrank ℚ ℚ`. Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_Eg, Module.finrank_self]`. Set `e : Fin (2 * finrank ℚ ℚ) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 Eg)` to `(Fintype.equivFinOfCardEq hcard).symm`. Set `a : Fin (2 * finrank ℚ ℚ) → 𝓞 Eg` to `fun i => RingOfIntegers.basis Eg (e i)`. Use `⟨∑ i, ∑ σ : Eg →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩` and prove the remaining obligations.

Use `(integralBasis Eg).linearIndependent.comp e e.injective` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[a, integralBasis_apply]`. Introduce `i σ`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_integral_family : ∃ r : ℝ, ∃ a : Fin (2 * finrank ℚ ℚ) → 𝓞 Eg,
    LinearIndependent ℚ (fun i => (a i : Eg)) ∧ ∀ i (σ : Eg →+* ℂ), ‖σ (a i)‖ ≤ r := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 Eg)) = 2 * finrank ℚ ℚ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_Eg,
      Module.finrank_self]
  let e : Fin (2 * finrank ℚ ℚ) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 Eg) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (2 * finrank ℚ ℚ) → 𝓞 Eg := fun i => RingOfIntegers.basis Eg (e i)
  refine ⟨∑ i, ∑ σ : Eg →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩
  · have := (integralBasis Eg).linearIndependent.comp e e.injective
    convert this using 1
    funext i
    simp [a, integralBasis_apply]
  · intro i σ
    calc ‖σ (a i)‖ ≤ ∑ σ' : Eg →+* ℂ, ‖σ' (a i)‖ :=
          Finset.single_le_sum (f := fun σ' : Eg →+* ℂ => ‖σ' (a i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ ∑ j, ∑ σ' : Eg →+* ℂ, ‖σ' (a j)‖ :=
          Finset.single_le_sum (f := fun j => ∑ σ' : Eg →+* ℂ, ‖σ' (a j)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

def VVG : Set (Fin 2 → Eg) := {y | ∃ γ ∈ latticeStab hG LaG, γ • v0 = y}

/- English proof (translation)
Introduce and unpack `γ hγ _ ⟨δ, hδ, rfl⟩`. Conclude with `⟨γ * δ, mul_mem hγ hδ, mul_smul γ δ v0⟩`.
-/
theorem VVG_stable : ∀ γ ∈ latticeStab hG LaG, ∀ x ∈ VVG, γ • x ∈ VVG := by
  rintro γ hγ _ ⟨δ, hδ, rfl⟩
  exact ⟨γ * δ, mul_mem hγ hδ, mul_smul γ δ v0⟩

/- English proof (translation)
Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Establish `h1 : γ • v0 ∈ γ • LaG` using `AddSubgroup.smul_mem_pointwise_smul _ _ _ isotropicVector_mem_lattice`. Rewrite `h1` using `[MulAction.mem_stabilizer_iff.1 hγ]`. Then use the resulting hypothesis.
-/
theorem VVG_subset : VVG ⊆ LaG := by
  rintro _ ⟨γ, hγ, rfl⟩
  have h1 : γ • v0 ∈ γ • LaG := AddSubgroup.smul_mem_pointwise_smul _ _ _ isotropicVector_mem_lattice
  rwa [MulAction.mem_stabilizer_iff.1 hγ] at h1

/- English proof (translation)
Introduce and unpack `_ ⟨γ, -, rfl⟩`. Use `⟨fun h => isotropicVector_ne_zero ((smul_eq_zero_iff_eq γ).1 h), ?_⟩` and prove the remaining obligations. Rewrite using `[← hermitian_isotropicVector]`. Conclude with `HermitianForm.mem_unitaryGroup.1 γ.2 v0 v0`.
-/
theorem VVG_isotropic : ∀ x ∈ VVG, x ≠ 0 ∧ hG.toSesq x x = 0 := by
  rintro _ ⟨γ, -, rfl⟩
  refine ⟨fun h => isotropicVector_ne_zero ((smul_eq_zero_iff_eq γ).1 h), ?_⟩
  rw [← hermitian_isotropicVector]
  exact HermitianForm.mem_unitaryGroup.1 γ.2 v0 v0

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_mem _, one_smul _ _⟩`.
-/
theorem isotropicVector_mem_gaussianSpan : v0 ∈ VVG := ⟨1, one_mem _, one_smul _ _⟩

/- English proof (translation)
Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Rewrite using `[lineIndex_smul (MulAction.mem_stabilizer_iff.1 hγ), lineIndex_isotropicVector]`.
-/
theorem VVG_index : ∀ x ∈ VVG, lineIndex Eg LaG x ≤ 1 := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [lineIndex_smul (MulAction.mem_stabilizer_iff.1 hγ), lineIndex_isotropicVector]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
