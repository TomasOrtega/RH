import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitsOfIsAffineOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct

namespace GlobalTheory.KuennethOne

/- English proof (translation)
Use `letI := hR.toField`. Establish `hex` using `rTensor_exact B (LinearMap.exact_map_mkQ_range δ) (Submodule.mkQ_surjective _)`. Use `(hex z).mp ?_` and prove the remaining obligations. Set `b` to `Module.Basis.ofVectorSpace R (C₁ ⧸ LinearMap.range δ)`. Apply `(TensorProduct.equivFinsuppOfBasisLeft b).injective` to reduce the goal to its premises.

Use extensionality with `i`. Establish `h1` using `h (b.coord i ∘ₗ (LinearMap.range δ).mkQ) (by`. Use extensionality with `x`. Simplify using `[(Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self δ x)])`. Rewrite using `[map_zero, Finsupp.zero_apply, ← h1]`.

Use `clear h h1`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem mem_range_rTensor_of_forall_dual {R C₀ C₁ B : Type} [CommRing R] (hR : IsField R)
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup B] [Module R B]
    (δ : C₀ →ₗ[R] C₁) (z : C₁ ⊗[R] B)
    (h : ∀ l : C₁ →ₗ[R] R, l ∘ₗ δ = 0 → TensorProduct.lid R B (l.rTensor B z) = 0) :
    ∃ y, δ.rTensor B y = z := by
  classical
  letI := hR.toField
  have hex := rTensor_exact B (LinearMap.exact_map_mkQ_range δ) (Submodule.mkQ_surjective _)
  refine (hex z).mp ?_
  let b := Module.Basis.ofVectorSpace R (C₁ ⧸ LinearMap.range δ)
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  have h1 := h (b.coord i ∘ₗ (LinearMap.range δ).mkQ) (by
    ext x
    simp [(Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self δ x)])
  rw [map_zero, Finsupp.zero_apply, ← h1]
  clear h h1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable {S X Y Z T : Scheme.{0}}

def Fn (_ : X ⟶ S) (U : X.Opens) : Type := Γ(X, U)

noncomputable instance (i : X ⟶ S) (U : X.Opens) : CommRing (Fn i U) :=
  inferInstanceAs (CommRing Γ(X, U))

noncomputable instance (i : X ⟶ S) (U : X.Opens) : Algebra Γ(S, ⊤) (Fn i U) :=
  (show Γ(S, ⊤) →+* Fn i U from (i.appLE ⊤ U le_top).hom).toAlgebra

/- English proof (translation)
Substitute `e` using the available equality. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]`.
-/
theorem appLE_appLE (f : T ⟶ X) (g : X ⟶ Y) (h : T ⟶ Y) (e : f ≫ g = h) {W : Y.Opens}
    {U : X.Opens} {N : T.Opens} (h1 : U ≤ g ⁻¹ᵁ W) (h2 : N ≤ f ⁻¹ᵁ U) (h3 : N ≤ h ⁻¹ᵁ W)
    (x : Γ(Y, W)) :
    (f.appLE U N h2).hom ((g.appLE W U h1).hom x) = (h.appLE W N h3).hom x := by
  subst e
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/- English proof (translation)
Simplify using `only [Scheme.Hom.appLE, rs]`. Both sides reduce to the same expression.
-/
theorem id_appLE {U N : X.Opens} (h : N ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U N h).hom x = rs (show N ≤ U from h) x := by
  simp only [Scheme.Hom.appLE, rs]
  rfl

noncomputable def pb {iT : T ⟶ S} {iX : X ⟶ S} (g : T ⟶ X) (hg : g ≫ iX = iT) (U : X.Opens)
    (N : T.Opens) (e : N ≤ g ⁻¹ᵁ U) : Fn iX U →ₐ[Γ(S, ⊤)] Fn iT N where
  toRingHom := (g.appLE U N e).hom
  commutes' r := appLE_appLE g iX iT hg _ _ _ r

noncomputable def rsA (iX : X ⟶ S) {U V : X.Opens} (h : U ≤ V) :
    Fn iX V →ₐ[Γ(S, ⊤)] Fn iX U where
  toRingHom := rs h
  commutes' r := rs_appLE iX h _ r

noncomputable def evA {iY : Y ⟶ S} (y : S ⟶ Y) (hy : y ≫ iY = 𝟙 S) (W : Y.Opens)
    (e : ⊤ ≤ y ⁻¹ᵁ W) : Fn iY W →ₐ[Γ(S, ⊤)] Γ(S, ⊤) where
  toRingHom := (y.appLE W ⊤ e).hom
  commutes' r := ((appLE_appLE y iY _ hy _ _ le_top r).trans (id_appLE _ _)).trans (rs_self _ _)

variable {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY)

noncomputable def mm (U : X.Opens) (W : Y.Opens) (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U)
    (hW : O ≤ q ⁻¹ᵁ W) : Fn iX U ⊗[Γ(S, ⊤)] Fn iY W →ₐ[Γ(S, ⊤)] Fn (p ≫ iX) O :=
  Algebra.TensorProduct.productMap (pb p rfl U O hU) (pb q H.w.symm W O hW)

/- English proof (translation)
Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)`. Establish `h1` using `CommRingCat.isPushout_tensorProduct Γ(S, ⊤) (Fn iX U) (Fn iY W)`. Set `e` to `h1.isoIsPushout _ _ po`. Establish `: e.hom = CommRingCat.ofHom (mm H U W (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) inf_le_left inf_le_right).toRingHom`. Use `h1.hom_ext ?_ ?_` and prove the remaining obligations.

Use `(h1.inl_isoIsPushout_hom _ _ po).trans ?_` and prove the remaining obligations. Use extensionality with `x`. Conclude with `(Algebra.TensorProduct.productMap_left_apply (pb p rfl U _ inf_le_left) (pb q H.w.symm W _ inf_le_right) x).symm`. Use `(h1.inr_isoIsPushout_hom _ _ po).trans ?_` and prove the remaining obligations. Use extensionality with `x`.

Conclude with `(Algebra.TensorProduct.productMap_right_apply (pb p rfl U _ inf_le_left) (pb q H.w.symm W _ inf_le_right) x).symm`. Establish `hb` using `ConcreteCategory.bijective_of_isIso e.hom`. Rewrite `hb` using `[this]`. Conclude with `hb`.
-/
theorem mm_bijective [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) :
    Function.Bijective (mm H U W (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) inf_le_left inf_le_right) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)
  have h1 := CommRingCat.isPushout_tensorProduct Γ(S, ⊤) (Fn iX U) (Fn iY W)
  let e := h1.isoIsPushout _ _ po
  have : e.hom = CommRingCat.ofHom
      (mm H U W (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) inf_le_left inf_le_right).toRingHom := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po).trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_left_apply (pb p rfl U _ inf_le_left)
        (pb q H.w.symm W _ inf_le_right) x).symm
    · refine (h1.inr_isoIsPushout_hom _ _ po).trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_right_apply (pb p rfl U _ inf_le_left)
        (pb q H.w.symm W _ inf_le_right) x).symm
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [this] at hb
  exact hb

variable {ι : Type}

noncomputable def MM (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i)
    (hW : O ≤ q ⁻¹ᵁ W) : (∀ i, Fn iX (U i)) ⊗[Γ(S, ⊤)] Fn iY W →+ Γ(Z, O) :=
  ((mm H (U i) W O hU hW).toLinearMap ∘ₗ (LinearMap.proj i).rTensor _).toAddMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem MM_tmul (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i)
    (hW : O ≤ q ⁻¹ᵁ W) (a : ∀ i, Fn iX (U i)) (b : Fn iY W) :
    MM H U W i O hU hW (a ⊗ₜ b) = (p.appLE (U i) O hU).hom (a i) * (q.appLE W O hW).hom b := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, Pi.zero_apply]`. Both sides reduce to the same expression. Consider the case `tmul x y => rw [MM_tmul]`. Simplify using `[mm]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]`. Both sides reduce to the same expression.
-/
theorem MM_eq [Fintype ι] [DecidableEq ι] (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W) (z) :
    MM H U W i O hU hW z = mm H (U i) W O hU hW (TensorProduct.piLeft _ _ _ z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]; rfl
  | tmul x y => rw [MM_tmul]; simp [mm]; rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; rfl

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `choose w hw using fun i => (mm_bijective H (hU i) hW).2 (c i)`. Use `⟨(TensorProduct.piLeft _ _ _).symm w, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[MM_eq, LinearEquiv.apply_symm_apply, hw]`.
-/
theorem MM_surj [IsAffine S] [Finite ι] {U : ι → X.Opens} {W : Y.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hW : IsAffineOpen W)
    (c : ∀ i, Γ(Z, p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W)) :
    ∃ z, ∀ i, MM H U W i _ inf_le_left inf_le_right z = c i := by
  classical
  have := Fintype.ofFinite ι
  choose w hw using fun i => (mm_bijective H (hU i) hW).2 (c i)
  refine ⟨(TensorProduct.piLeft _ _ _).symm w, fun i => ?_⟩
  rw [MM_eq, LinearEquiv.apply_symm_apply, hw]

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Apply `(TensorProduct.piLeft _ _ _).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply `(mm_bijective H (hU i) hW).1` to reduce the goal to its premises. Rewrite using `[← MM_eq, h, map_zero, Pi.zero_apply, map_zero]`.

Both sides reduce to the same expression.
-/
theorem MM_inj [IsAffine S] [Finite ι] {U : ι → X.Opens} {W : Y.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hW : IsAffineOpen W) (z)
    (h : ∀ i, MM H U W i _ inf_le_left inf_le_right z = 0) : z = 0 := by
  classical
  have := Fintype.ofFinite ι
  apply (TensorProduct.piLeft _ _ _).injective
  funext i
  apply (mm_bijective H (hU i) hW).1
  rw [← MM_eq, h, map_zero, Pi.zero_apply, map_zero]
  rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul x y`. Rewrite using `[MM_tmul, MM_tmul, map_mul]`. Conclude with `congrArg₂ _ (rs_appLE p h hU _) (rs_appLE q h hW _)`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem rs_MM (U : ι → X.Opens) (W : Y.Opens) (i : ι) {O O' : Z.Opens} (h : O' ≤ O)
    (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W) (z) :
    rs h (MM H U W i O hU hW z) = MM H U W i O' (h.trans hU) (h.trans hW) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [MM_tmul, MM_tmul, map_mul]
    exact congrArg₂ _ (rs_appLE p h hU _) (rs_appLE q h hW _)
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul x y`. Rewrite using `[LinearMap.lTensor_tmul, MM_tmul, MM_tmul]`. Conclude with `congrArg _ (appLE_rs q h hW y)`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem MM_lTensor (U : ι → X.Opens) {W W' : Y.Opens} (h : W' ≤ W) (i : ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W') (z) :
    MM H U W' i O hU hW ((rsA iY h).toLinearMap.lTensor _ z) =
      MM H U W i O hU (hW.trans (q.preimage_mono h)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, MM_tmul, MM_tmul]
    exact congrArg _ (appLE_rs q h hW y)
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def dlt (iX : X ⟶ S) (U : ι → X.Opens) :
    (∀ i, Fn iX (U i)) →ₗ[Γ(S, ⊤)] ∀ k : ι × ι, Fn iX (U k.1 ⊓ U k.2) :=
  LinearMap.pi fun k => (rsA iX inf_le_left).toLinearMap ∘ₗ LinearMap.proj k.1 -
    (rsA iX inf_le_right).toLinearMap ∘ₗ LinearMap.proj k.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dlt_apply (iX : X ⟶ S) (U : ι → X.Opens) (x : ∀ i, Fn iX (U i)) (k : ι × ι) :
    dlt iX U x k = (rs inf_le_left (x k.1) - rs inf_le_right (x k.2) : Γ(X, U k.1 ⊓ U k.2)) := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, sub_zero]`. Consider the case `tmul x y`. Rewrite using `[LinearMap.rTensor_tmul, MM_tmul, MM_tmul, MM_tmul, dlt_apply, map_sub, sub_mul]`. Conclude with `congrArg₂ _ (congrArg (· * _) (appLE_rs p _ hU _)) (congrArg (· * _) (appLE_rs p _ hU _))`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem MM_dlt (U : ι → X.Opens) (W : Y.Opens) (k : ι × ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ (U k.1 ⊓ U k.2)) (hW : O ≤ q ⁻¹ᵁ W) (z) :
    MM H (fun k : ι × ι => U k.1 ⊓ U k.2) W k O hU hW ((dlt iX U).rTensor _ z) =
      MM H U W k.1 O (hU.trans (p.preimage_mono inf_le_left)) hW z -
        MM H U W k.2 O (hU.trans (p.preimage_mono inf_le_right)) hW z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, MM_tmul, MM_tmul, MM_tmul, dlt_apply, map_sub, sub_mul]
    exact congrArg₂ _ (congrArg (· * _) (appLE_rs p _ hU _)) (congrArg (· * _) (appLE_rs p _ hU _))
  | add x y hx hy => simp only [map_add, hx, hy]; ring

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Both sides reduce to the same expression. Consider the case `tmul a b`. Establish `h3 : U i ≤ (iX ≫ y) ⁻¹ᵁ W` using `le_top.trans (iX.preimage_mono e)`.

Rewrite using `[LinearMap.lTensor_tmul, MM_tmul, map_mul, TensorProduct.rid_tmul, Pi.smul_apply, Algebra.smul_def, mul_comm]`. Conclude with `congrArg₂ _ ((appLE_appLE s q _ hs' hW hO h3 b).trans (appLE_appLE iX y _ rfl e le_top h3 b).symm) (((appLE_appLE s p _ hs hU hO le_rfl (a i)).trans (id_appLE _ _)).trans (rs_self _ _))`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Both sides reduce to the same expression.
-/
theorem section_MM {y : S ⟶ Y} (hy : y ≫ iY = 𝟙 S) {s : X ⟶ Z} (hs : s ≫ p = 𝟙 X)
    (hs' : s ≫ q = iX ≫ y) (U : ι → X.Opens) (W : Y.Opens) (e : ⊤ ≤ y ⁻¹ᵁ W) (i : ι)
    (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W) (hO : U i ≤ s ⁻¹ᵁ O) (z) :
    (s.appLE O (U i) hO).hom (MM H U W i O hU hW z) =
      TensorProduct.rid _ _ ((evA y hy W e).toLinearMap.lTensor _ z) i := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    have h3 : U i ≤ (iX ≫ y) ⁻¹ᵁ W := le_top.trans (iX.preimage_mono e)
    rw [LinearMap.lTensor_tmul, MM_tmul, map_mul, TensorProduct.rid_tmul, Pi.smul_apply,
      Algebra.smul_def, mul_comm]
    exact congrArg₂ _ ((appLE_appLE s q _ hs' hW hO h3 b).trans
      (appLE_appLE iX y _ rfl e le_top h3 b).symm)
      (((appLE_appLE s p _ hs hU hO le_rfl (a i)).trans (id_appLE _ _)).trans (rs_self _ _))
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

end GlobalTheory.KuennethOne
