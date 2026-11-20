import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothDescent

open TensorProduct

/- English proof (translation)
Take `⟨A₁, B₁, _, _, hA₁, _, ⟨eB⟩⟩` from `Algebra.Smooth.exists_subalgebra_fg ℤ R B`. Take `⟨A₂, C₁, _, _, hA₂, _, ⟨eC⟩⟩` from `Algebra.Smooth.exists_subalgebra_fg ℤ R C`. Set `A : Subalgebra ℤ R` to `A₁ ⊔ A₂`. Set `: Algebra A₁ A` to `(Subalgebra.inclusion (le_sup_left : A₁ ≤ A)).toRingHom.toAlgebra`. Set `: Algebra A₂ A` to `(Subalgebra.inclusion (le_sup_right : A₂ ≤ A)).toRingHom.toAlgebra`.

Establish `: IsScalarTower A₁ A R` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower A₂ A R` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Algebra.FiniteType ℤ A` using `(Subalgebra.fg_iff_finiteType A).mp (hA₁.sup hA₂)`. Conclude with `⟨A, A ⊗[A₁] B₁, A ⊗[A₂] C₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ A, inferInstance, inferInstance, ⟨(Algebra.TensorProduct.cancelBaseChange A₁ A R R B₁).trans eB.symm⟩, ⟨(Algebra.TensorProdu …`.
-/
theorem exists_common_model (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] :
    ∃ (A B₁ C₁ : Type) (_ : CommRing A) (_ : Algebra A R) (_ : CommRing B₁) (_ : CommRing C₁)
      (_ : Algebra A B₁) (_ : Algebra A C₁), IsNoetherianRing A ∧ Algebra.Smooth A B₁ ∧
      Algebra.Smooth A C₁ ∧ Nonempty (R ⊗[A] B₁ ≃ₐ[R] B) ∧ Nonempty (R ⊗[A] C₁ ≃ₐ[R] C) := by
  obtain ⟨A₁, B₁, _, _, hA₁, _, ⟨eB⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R B
  obtain ⟨A₂, C₁, _, _, hA₂, _, ⟨eC⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R C
  let A : Subalgebra ℤ R := A₁ ⊔ A₂
  let : Algebra A₁ A := (Subalgebra.inclusion (le_sup_left : A₁ ≤ A)).toRingHom.toAlgebra
  let : Algebra A₂ A := (Subalgebra.inclusion (le_sup_right : A₂ ≤ A)).toRingHom.toAlgebra
  have : IsScalarTower A₁ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₂ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp (hA₁.sup hA₂)
  exact ⟨A, A ⊗[A₁] B₁, A ⊗[A₂] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ A, inferInstance,
    inferInstance, ⟨(Algebra.TensorProduct.cancelBaseChange A₁ A R R B₁).trans eB.symm⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange A₂ A R R C₁).trans eC.symm⟩⟩

variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]

noncomputable abbrev incl (C₁ : Type) [CommRing C₁] [Algebra A C₁] (S : Subalgebra A R) :
    S ⊗[A] C₁ →ₐ[A] R ⊗[A] C₁ :=
  Algebra.TensorProduct.map S.val (AlgHom.id A C₁)

/- English proof (translation)
Establish `e : incl C₁ S = (incl C₁ T).comp (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A C₁))` using `Algebra.TensorProduct.ext' fun _ _ => rfl`. Rewrite using `[e]`. Conclude with `AlgHom.range_comp_le_range _ _`.
-/
theorem range_incl_mono {S T : Subalgebra A R} (h : S ≤ T) :
    (incl C₁ S).range ≤ (incl C₁ T).range := by
  have e : incl C₁ S = (incl C₁ T).comp
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A C₁)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  rw [e]
  exact AlgHom.range_comp_le_range _ _

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩`. Consider the case `tmul r c`. Conclude with `⟨Algebra.adjoin A {r}, ⟨{r}, by simp⟩, (AlgHom.mem_range _).mpr ⟨⟨r, Algebra.subset_adjoin rfl⟩ ⊗ₜ c, rfl⟩⟩`. Consider the case `add x y hx hy`.

Take `⟨S, hS, hxS⟩` from `hx`. Take `⟨T, hT, hyT⟩` from `hy`. Conclude with `⟨S ⊔ T, hS.sup hT, add_mem (range_incl_mono le_sup_left hxS) (range_incl_mono le_sup_right hyT)⟩`.
-/
theorem exists_fg_mem_range_incl (x : R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ x ∈ (incl C₁ S).range := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩
  | tmul r c =>
    exact ⟨Algebra.adjoin A {r}, ⟨{r}, by simp⟩,
      (AlgHom.mem_range _).mpr ⟨⟨r, Algebra.subset_adjoin rfl⟩ ⊗ₜ c, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨S, hS, hxS⟩ := hx
    obtain ⟨T, hT, hyT⟩ := hy
    exact ⟨S ⊔ T, hS.sup hT,
      add_mem (range_incl_mono le_sup_left hxS) (range_incl_mono le_sup_right hyT)⟩

/- English proof (translation)
Use `Finset.induction_on t ⟨⊥, Subalgebra.fg_bot, by simp⟩ ?_` and prove the remaining obligations. Introduce `a t _ ih`. Take `⟨S, hS, hSt⟩` from `ih`. Take `⟨T, hT, haT⟩` from `exists_fg_mem_range_incl (C₁ := C₁) a`. Use `⟨S ⊔ T, hS.sup hT, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.coe_insert, Set.insert_subset_iff]`. Conclude with `⟨range_incl_mono le_sup_right haT, hSt.trans (SetLike.coe_subset_coe.mpr (range_incl_mono le_sup_left))⟩`.
-/
theorem exists_fg_subset_range_incl (t : Finset (R ⊗[A] C₁)) :
    ∃ S : Subalgebra A R, S.FG ∧ (t : Set (R ⊗[A] C₁)) ⊆ (incl C₁ S).range := by
  classical
  refine Finset.induction_on t ⟨⊥, Subalgebra.fg_bot, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨S, hS, hSt⟩ := ih
  obtain ⟨T, hT, haT⟩ := exists_fg_mem_range_incl (C₁ := C₁) a
  refine ⟨S ⊔ T, hS.sup hT, ?_⟩
  rw [Finset.coe_insert, Set.insert_subset_iff]
  exact ⟨range_incl_mono le_sup_right haT,
    hSt.trans (SetLike.coe_subset_coe.mpr (range_incl_mono le_sup_left))⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra A B₁).FG)`. Take `⟨S, hS, hsub⟩` from `exists_fg_subset_range_incl (C₁ := C₁) (s.image φ)`. Use `⟨S, hS, ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]`. Rewrite `hsub` using `[Finset.coe_image]`. Then use the resulting hypothesis.
-/
theorem exists_fg_range_le [Algebra.FiniteType A B₁] (φ : B₁ →ₐ[A] R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ φ.range ≤ (incl C₁ S).range := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B₁).FG)
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := C₁) (s.image φ)
  refine ⟨S, hS, ?_⟩
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rwa [Finset.coe_image] at hsub

/- English proof (translation)
The claim follows from `Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) S.val.toLinearMap Subtype.val_injective`.
-/
theorem incl_injective [Module.Flat A C₁] (S : Subalgebra A R) :
    Function.Injective (incl C₁ S) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) S.val.toLinearMap
    Subtype.val_injective

/- English proof (translation)
Set `e` to `AlgEquiv.ofInjective i hi`. Set `φ'` to `φ.codRestrict i.range fun b => h (AlgHom.mem_range_self φ b)`. Use `⟨e.symm.toAlgHom.comp φ', fun b => ?_⟩` and prove the remaining obligations. Establish `h1 : ((e (e.symm (φ' b)) : i.range) : E) = (φ' b : E)` using `by rw [e.apply_symm_apply]`. Conclude with `h1`.
-/
theorem exists_lift {D E : Type} [CommRing D] [CommRing E] [Algebra A D] [Algebra A E]
    (φ : B₁ →ₐ[A] E) (i : D →ₐ[A] E) (hi : Function.Injective i) (h : φ.range ≤ i.range) :
    ∃ ψ : B₁ →ₐ[A] D, ∀ b, i (ψ b) = φ b := by
  let e := AlgEquiv.ofInjective i hi
  let φ' := φ.codRestrict i.range fun b => h (AlgHom.mem_range_self φ b)
  refine ⟨e.symm.toAlgHom.comp φ', fun b => ?_⟩
  have h1 : ((e (e.symm (φ' b)) : i.range) : E) = (φ' b : E) := by rw [e.apply_symm_apply]
  exact h1

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s c => simp [Algebra.TensorProduct.cancelBaseChange_tmul, incl, Algebra.smul_def]`. Consider the case `add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]`.
-/
theorem cancel_one_tmul (S : Subalgebra A R) (x : S ⊗[A] C₁) :
    Algebra.TensorProduct.cancelBaseChange A S R R C₁ (1 ⊗ₜ x) = incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s c => simp [Algebra.TensorProduct.cancelBaseChange_tmul, incl, Algebra.smul_def]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]

/- English proof (translation)
Simplify using `[incl, TensorProduct.smul_tmul']`.
-/
theorem incl_tmul (S : Subalgebra A R) (s : S) (c : C₁) :
    incl C₁ S (s ⊗ₜ c) = (s : R) • ((1 : R) ⊗ₜ[A] c) := by
  simp [incl, TensorProduct.smul_tmul']

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s' c => simp [incl, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]`.
-/
theorem incl_smul (S : Subalgebra A R) (s : S) (x : S ⊗[A] C₁) :
    incl C₁ S (s • x) = (s : R) • incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s' c => simp [incl, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

noncomputable def extend (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) : S ⊗[A] B₁ →ₐ[S] D :=
  Algebra.TensorProduct.lift (Algebra.ofId S D) ψ fun _ _ => Commute.all _ _

/- English proof (translation)
Simplify using `[extend, Algebra.smul_def]`.
-/
theorem extend_tmul (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) (s : S) (b : B₁) :
    extend S ψ (s ⊗ₜ b) = s • ψ b := by
  simp [extend, Algebra.smul_def]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s b => rw [extend_tmul, incl_smul, h, incl_tmul, map_smul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem incl_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁)
    (ψ : B₁ →ₐ[A] S ⊗[A] C₁) (h : ∀ b, incl C₁ S (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    incl C₁ S (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rw [extend_tmul, incl_smul, h, incl_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s b`. Rewrite using `[extend_tmul, smul_eq_mul, map_mul, h, incl_tmul, map_smul, smul_eq_mul]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem val_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R)
    (ψ : B₁ →ₐ[A] S) (h : ∀ b, S.val (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    S.val (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    rw [extend_tmul, smul_eq_mul, map_mul, h, incl_tmul, map_smul, smul_eq_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end GlobalTheory.SmoothDescent

namespace GlobalTheory

open TensorProduct SmoothDescent

/- English proof (translation)
Introduce `R B C _ _ _ _ _ _ _ f g r`. Take `⟨A, B₁, C₁, _, _, _, _, _, _, hA, hB, hC, ⟨eB⟩, ⟨eC⟩⟩` from `exists_common_model R B C`. Set `F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁` to `(eC.symm.toAlgHom.comp f).comp eB.toAlgHom`. Set `G : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁` to `(eC.symm.toAlgHom.comp g).comp eB.toAlgHom`. Set `ρ : R ⊗[A] B₁ →ₐ[R] R` to `r.comp eB.toAlgHom`.

Set `j : B₁ →ₐ[A] R ⊗[A] B₁` to `Algebra.TensorProduct.includeRight`. Set `φF : B₁ →ₐ[A] R ⊗[A] C₁` to `(F.restrictScalars A).comp j`. Set `φG : B₁ →ₐ[A] R ⊗[A] C₁` to `(G.restrictScalars A).comp j`. Set `φr : B₁ →ₐ[A] R` to `(ρ.restrictScalars A).comp j`. Take `⟨S₁, hS₁, h₁⟩` from `exists_fg_range_le (C₁ := C₁) φF`.

Take `⟨S₂, hS₂, h₂⟩` from `exists_fg_range_le (C₁ := C₁) φG`. Establish `h₃ : φr.range.FG`. Rewrite using `[← Algebra.map_top]`. Conclude with `Subalgebra.FG.map φr Algebra.FiniteType.out`. Set `S : Subalgebra A R` to `S₁ ⊔ S₂ ⊔ φr.range`.

Establish `: Algebra.FiniteType A S` using `(Subalgebra.fg_iff_finiteType S).mp ((hS₁.sup hS₂).sup h₃)`. Establish `: IsNoetherianRing S` using `Algebra.FiniteType.isNoetherianRing A S`. Establish `hF : φF.range ≤ (incl C₁ S).range` using `h₁.trans (range_incl_mono (le_sup_left.trans le_sup_left))`. Establish `hG : φG.range ≤ (incl C₁ S).range` using `h₂.trans (range_incl_mono (le_sup_right.trans le_sup_left))`. Establish `hr : φr.range ≤ S.val.range`.

Rewrite using `[Subalgebra.range_val]`. Conclude with `le_sup_right`. Take `⟨ψF, hψF⟩` from `exists_lift φF (incl C₁ S) (incl_injective S) hF`. Take `⟨ψG, hψG⟩` from `exists_lift φG (incl C₁ S) (incl_injective S) hG`. Take `⟨ψr, hψr⟩` from `exists_lift φr S.val Subtype.val_injective hr`.

Use `⟨S, S ⊗[A] B₁, S ⊗[A] C₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, extend S ψF, extend S ψG, extend S ψr, (Algebra.TensorProduct.cancelBaseChange A S R R B₁).trans eB, (Algebra.TensorProduct.cancelBaseChange A S R R …` and prove the remaining obligations. Rewrite using `[AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul, incl_extend S F ψF hψF]`. Simplify using `[F]`. Rewrite using `[AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul, incl_extend S G ψG hψG]`. Simplify using `[G]`.

Rewrite using `[AlgEquiv.trans_apply, cancel_one_tmul]`. Express the relevant statement in the definitionally equal form `_ = S.val (extend S ψr b)`. Rewrite using `[val_extend S ρ ψr hψr]`. Simplify using `[ρ]`.
-/
theorem exists_noetherian_model_of_smooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b) := by
  intro R B C _ _ _ _ _ _ _ f g r
  obtain ⟨A, B₁, C₁, _, _, _, _, _, _, hA, hB, hC, ⟨eB⟩, ⟨eC⟩⟩ := exists_common_model R B C
  let F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp f).comp eB.toAlgHom
  let G : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp g).comp eB.toAlgHom
  let ρ : R ⊗[A] B₁ →ₐ[R] R := r.comp eB.toAlgHom
  let j : B₁ →ₐ[A] R ⊗[A] B₁ := Algebra.TensorProduct.includeRight
  let φF : B₁ →ₐ[A] R ⊗[A] C₁ := (F.restrictScalars A).comp j
  let φG : B₁ →ₐ[A] R ⊗[A] C₁ := (G.restrictScalars A).comp j
  let φr : B₁ →ₐ[A] R := (ρ.restrictScalars A).comp j
  obtain ⟨S₁, hS₁, h₁⟩ := exists_fg_range_le (C₁ := C₁) φF
  obtain ⟨S₂, hS₂, h₂⟩ := exists_fg_range_le (C₁ := C₁) φG
  have h₃ : φr.range.FG := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map φr Algebra.FiniteType.out
  let S : Subalgebra A R := S₁ ⊔ S₂ ⊔ φr.range
  have : Algebra.FiniteType A S := (Subalgebra.fg_iff_finiteType S).mp ((hS₁.sup hS₂).sup h₃)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have hF : φF.range ≤ (incl C₁ S).range :=
    h₁.trans (range_incl_mono (le_sup_left.trans le_sup_left))
  have hG : φG.range ≤ (incl C₁ S).range :=
    h₂.trans (range_incl_mono (le_sup_right.trans le_sup_left))
  have hr : φr.range ≤ S.val.range := by
    rw [Subalgebra.range_val]
    exact le_sup_right
  obtain ⟨ψF, hψF⟩ := exists_lift φF (incl C₁ S) (incl_injective S) hF
  obtain ⟨ψG, hψG⟩ := exists_lift φG (incl C₁ S) (incl_injective S) hG
  obtain ⟨ψr, hψr⟩ := exists_lift φr S.val Subtype.val_injective hr
  refine ⟨S, S ⊗[A] B₁, S ⊗[A] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, extend S ψF, extend S ψG, extend S ψr,
    (Algebra.TensorProduct.cancelBaseChange A S R R B₁).trans eB,
    (Algebra.TensorProduct.cancelBaseChange A S R R C₁).trans eC, inferInstance, inferInstance,
    fun b => ⟨?_, ?_, ?_⟩⟩
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S F ψF hψF]
    simp [F]
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S G ψG hψG]
    simp [G]
  · rw [AlgEquiv.trans_apply, cancel_one_tmul]
    change _ = S.val (extend S ψr b)
    rw [val_extend S ρ ψr hψr]
    simp [ρ]

end GlobalTheory
