import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatConst

open scoped TensorProduct

/- English proof (translation)
Take `⟨l, hl⟩` from `Module.Projective.exists_dual_eq_one K ht`. Establish `e` using `congrArg (fun v => TensorProduct.rid K F (LinearMap.lTensor F l v)) h`. Simplify using `only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl, one_smul, Algebra.smul_def] at e`. Use `⟨(l u)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀]`.

Conclude with `inv_eq_of_mul_eq_one_right (by simpa using e.symm)`.
-/
theorem mem_range_of_tmul_eq {K F O : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup O] [Module K O]
    {t u : O} {c : F} (ht : t ≠ 0) (h : (1 : F) ⊗ₜ[K] t = c ⊗ₜ[K] u) : ∃ x : K, algebraMap K F x = c := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K ht
  have e := congrArg (fun v => TensorProduct.rid K F (LinearMap.lTensor F l v)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl, one_smul, Algebra.smul_def] at e
  refine ⟨(l u)⁻¹, ?_⟩
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right (by simpa using e.symm)

/- English proof (translation)
Establish `e` using `congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality h)`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e`. Rewrite using `[e]`. Conclude with `((gs_pull (𝟙 _) (Spec.map h) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm`.
-/
theorem gs_spec {A B : CommRingCat.{0}} (h : A ⟶ B) (y : Spec B) (x : A) :
    gs (Spec.map h) y ⊤ ((Scheme.ΓSpecIso A).inv.hom x) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom x)) := by
  have e := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e]
  exact ((gs_pull (𝟙 _) (Spec.map h) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

/- English proof (translation)
Establish `: Z.fromSpecStalk z y ⤳ z`. Use `Set.mem_range_self (f := Z.fromSpecStalk z) y` as an intermediate fact. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Conclude with `(this.map f.continuous).mem_open U.isOpen hz`.
-/
theorem mem_of_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (y : Spec (Z.presheaf.stalk z)) :
    f (Z.fromSpecStalk z y) ∈ U := by
  have : Z.fromSpecStalk z y ⤳ z := by
    have := Set.mem_range_self (f := Z.fromSpecStalk z) y
    rwa [Scheme.range_fromSpecStalk] at this
  exact (this.map f.continuous).mem_open U.isOpen hz

/- English proof (translation)
Establish `m` using `mem_of_stalk f z U hz (Spec.map h y)`. Rewrite using `[← gs_spec, ← Category.assoc, ← gs_pull _ f y U m, ← gs_pull _ (Z.fromSpecStalk z) y _ m, Scheme.fromSpecStalk_app (U := f ⁻¹ᵁ U) hz, gs_eq f z U hz]`. Conclude with `gs_res (Spec.map h) y le_top m _`.
-/
theorem gs_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (a : Γ(X, U)) {B : CommRingCat.{0}}
    (h : Z.presheaf.stalk z ⟶ B) (y : Spec B) :
    gs (Spec.map h ≫ Z.fromSpecStalk z ≫ f) y U a = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom (gs f z U a))) := by
  have m := mem_of_stalk f z U hz (Spec.map h y)
  rw [← gs_spec, ← Category.assoc, ← gs_pull _ f y U m, ← gs_pull _ (Z.fromSpecStalk z) y _ m,
    Scheme.fromSpecStalk_app (U := f ⁻¹ᵁ U) hz, gs_eq f z U hz]
  exact gs_res (Spec.map h) y le_top m _

/- English proof (translation)
Introduce `R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s c H ⟨Z, p, p', h₁, h₂, z, J, hJ, hne⟩`. Set `O` to `Z.presheaf.stalk z`. Take `⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of F ⟶ O, Spec.map ρ = Z.fromSpecStalk z ≫ p' ≫ (fst (TFK (R` from `R) F) C.A.A).left := ⟨Spec.preimage _, Spec.map_preimage _⟩`. Use `letI : Algebra (FractionRing W) O := (ρ.hom.comp (algebraMap (FractionRing W) F)).toAlgebra`. Set `B` to `CommRingCat.of (F ⊗[FractionRing W] O)`.

Set `iL : CommRingCat.of F ⟶ B` to `CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom`. Set `iR : O ⟶ B` to `CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).toRingHom`. Establish `hK : ∀ x : FractionRing W, iR.hom (ρ.hom (algebraMap _ F x)) = iL.hom (algebraMap _ F x)` using `fun x => ((Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).commutes x).trans rfl`. Set `g : Spec B ⟶ Z` to `Spec.map iR ≫ Z.fromSpecStalk z`. Establish `hg : g ≫ p' ≫ (fst (TFK (R` using `R) F) C.A.A).left = Spec.map (ρ ≫ iR) := by`.

Rewrite using `[Spec.map_comp, hρ, Category.assoc]`. Establish `w : (g ≫ p' ≫ (snd (TFK (R` using `R) F) C.A.A).left) ≫ C.A.A.hom = Spec.map iL ≫ jFK (R := R) F := by`. Establish `e : (snd (TFK (R` using `R) F) C.A.A).left ≫ C.A.A.hom = (fst (TFK (R := R) F) C.A.A).left ≫ jFK (R := R) F := (Over.w _).trans (Over.w (fst (TFK (R := R) F) C.A.A)).symm`. Establish `e' : (g ≫ p' ≫ (snd (TFK (R` using `R) F) C.A.A).left) ≫ C.A.A.hom = (g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫ jFK (R := R) F := by simp only [Category.assoc, e]`. Rewrite using `[e', hg]`.

Use `(Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))` and prove the remaining obligations. Use `CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))` and prove the remaining obligations. Conclude with `(congrArg (fun q => iR.hom (ρ.hom q)) (hF r)).trans ((hK _).trans (congrArg iL.hom (hF r).symm))`. Take `⟨q, q₁, q₂⟩ : ∃ q : Spec B ⟶ (TFK (R` from `R) F ⊗ C.A.A).left, q ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map iL ∧ q ≫ (snd (TFK (R := R) F) C.A.A).left = g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left := by`. Set `T' : Over (Sp (FractionRing R))` to `Over.mk (Spec.map iL ≫ jFK (R := R) F)`.

Set `a : T' ⟶ TFK (R` to `R) F := Over.homMk (Spec.map iL) rfl`. Set `b : T' ⟶ C.A.A` to `Over.homMk (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) w`. Conclude with `⟨(lift a b).left, congrArg (·.left) (lift_fst a b), congrArg (·.left) (lift_snd a b)⟩`. Establish `k₁ : (g ≫ p) ≫ T.β = q ≫ (snd (TFK (R` using `R) F) C.A.A).left ≫ C.α := by`. Rewrite using `[← Category.assoc q, q₂, Category.assoc, h₁]`.

Simplify using `only [Category.assoc]`. Establish `k₂ : (g ≫ p) ≫ T.G.hom = q ≫ (fst (TFK (R` using `R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by`. Rewrite using `[← Category.assoc q, q₁, Category.assoc, h₂, ← Category.assoc p', ← Category.assoc g, hg]`. Use `(Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))` and prove the remaining obligations. Conclude with `CommRingCat.hom_ext (RingHom.ext fun r => hK _)`.

Set `u : O` to `sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J`. Set `t : O` to `sval σ p z J`. Establish `key : iR.hom t = iL.hom c * iR.hom u`. Apply `(Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective` to reduce the goal to its premises. Use `fn_ext (V := ⊤) fun y _ => ?_` and prove the remaining obligations.

Take `⟨J', hJ', e⟩` from `exists_good C.P.L.L C.P.L.isLB y (K := Unit) (fun _ => (g ≫ p) ≫ T.β) (fun _ => J (p ≫ T.β)) (fun _ _ _ => rfl) (fun _ => mem_of_stalk (p ≫ T.β) z _ (hJ _) (Spec.map iR y))`. Establish `e` using `e ()`. Use `H _ (g ≫ p) q k₁ k₂ y J' hJ'` as an intermediate fact. Rewrite using `[sval_of σ _ y J' (fun _ => J (p ≫ T.β)) (fun _ => e), sval_of s _ y J' (fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) (fun _ => by`. Rewrite using `[Category.assoc, ← k₁, Category.assoc p', ← h₁]`.

Conclude with `e), q₁, q₂] at this`. Establish `a₁` using `gs_stalk p z _ (hJ.mem (fun _ : Fin 1 => T.β) p) (σ.f fun _ => J (p ≫ T.β)) iR y`. Establish `a₂` using `gs_stalk (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z _ (hJ.mem (fun _ : Fin 1 => C.α) (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) (s.f fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) iR y`. Establish `a₃` using `gs_spec iL y c`. Simplify using `only [g, Category.assoc] at this a₁ a₂`.

Use `a₁.symm.trans (this.trans (Eq.trans (congrArg₂ (· * ·) a₃ a₂) ?_))` and prove the remaining obligations. Use `(gs_mul _ y ⊤ trivial _ _).symm.trans (congrArg _ ?_)` and prove the remaining obligations. Simplify using `only [u, sval, Category.assoc]`. Conclude with `(map_mul _ _ _).symm`. Use `mem_range_of_tmul_eq (O := O) (t := t) (u := u) hne (key.trans ?_)` and prove the remaining obligations.

Conclude with `(Algebra.TensorProduct.tmul_mul_tmul c 1 1 u).trans (by rw [_root_.mul_one, _root_.one_mul])`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s c H ⟨Z, p, p', h₁, h₂, z, J, hJ, hne⟩
  let O := Z.presheaf.stalk z
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of F ⟶ O,
      Spec.map ρ = Z.fromSpecStalk z ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left := ⟨Spec.preimage _, Spec.map_preimage _⟩
  letI : Algebra (FractionRing W) O := (ρ.hom.comp (algebraMap (FractionRing W) F)).toAlgebra
  let B := CommRingCat.of (F ⊗[FractionRing W] O)
  let iL : CommRingCat.of F ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : O ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).toRingHom
  have hK : ∀ x : FractionRing W, iR.hom (ρ.hom (algebraMap _ F x)) = iL.hom (algebraMap _ F x) := fun x =>
    ((Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).commutes x).trans rfl
  let g : Spec B ⟶ Z := Spec.map iR ≫ Z.fromSpecStalk z
  have hg : g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map (ρ ≫ iR) := by
    rw [Spec.map_comp, hρ, Category.assoc]
  have w : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom = Spec.map iL ≫ jFK (R := R) F := by
    have e : (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom = (fst (TFK (R := R) F) C.A.A).left ≫ jFK (R := R) F :=
      (Over.w _).trans (Over.w (fst (TFK (R := R) F) C.A.A)).symm
    have e' : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom =
        (g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫ jFK (R := R) F := by simp only [Category.assoc, e]
    rw [e', hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    refine CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    exact (congrArg (fun q => iR.hom (ρ.hom q)) (hF r)).trans ((hK _).trans (congrArg iL.hom (hF r).symm))
  obtain ⟨q, q₁, q₂⟩ : ∃ q : Spec B ⟶ (TFK (R := R) F ⊗ C.A.A).left,
      q ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map iL ∧
      q ≫ (snd (TFK (R := R) F) C.A.A).left = g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left := by
    let T' : Over (Sp (FractionRing R)) := Over.mk (Spec.map iL ≫ jFK (R := R) F)
    let a : T' ⟶ TFK (R := R) F := Over.homMk (Spec.map iL) rfl
    let b : T' ⟶ C.A.A := Over.homMk (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) w
    exact ⟨(lift a b).left, congrArg (·.left) (lift_fst a b), congrArg (·.left) (lift_snd a b)⟩
  have k₁ : (g ≫ p) ≫ T.β = q ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
    rw [← Category.assoc q, q₂, Category.assoc, h₁]; simp only [Category.assoc]
  have k₂ : (g ≫ p) ≫ T.G.hom = q ≫ (fst (TFK (R := R) F) C.A.A).left ≫
      spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [← Category.assoc q, q₁, Category.assoc, h₂, ← Category.assoc p', ← Category.assoc g, hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun r => hK _)
  let u : O := sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J
  let t : O := sval σ p z J
  have key : iR.hom t = iL.hom c * iR.hom u := by
    apply (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J', hJ', e⟩ := exists_good C.P.L.L C.P.L.isLB y (K := Unit) (fun _ => (g ≫ p) ≫ T.β) (fun _ => J (p ≫ T.β))
      (fun _ _ _ => rfl) (fun _ => mem_of_stalk (p ≫ T.β) z _ (hJ _) (Spec.map iR y))
    have e := e ()
    have := H _ (g ≫ p) q k₁ k₂ y J' hJ'
    rw [sval_of σ _ y J' (fun _ => J (p ≫ T.β)) (fun _ => e),
      sval_of s _ y J' (fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) (fun _ => by
        rw [Category.assoc, ← k₁, Category.assoc p', ← h₁]; exact e), q₁, q₂] at this
    have a₁ := gs_stalk p z _ (hJ.mem (fun _ : Fin 1 => T.β) p) (σ.f fun _ => J (p ≫ T.β)) iR y
    have a₂ := gs_stalk (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z _
      (hJ.mem (fun _ : Fin 1 => C.α) (p' ≫ (snd (TFK (R := R) F) C.A.A).left))
      (s.f fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) iR y
    have a₃ := gs_spec iL y c
    simp only [g, Category.assoc] at this a₁ a₂
    refine a₁.symm.trans (this.trans (Eq.trans (congrArg₂ (· * ·) a₃ a₂) ?_))
    refine (gs_mul _ y ⊤ trivial _ _).symm.trans (congrArg _ ?_)
    simp only [u, sval, Category.assoc]
    exact (map_mul _ _ _).symm
  refine mem_range_of_tmul_eq (O := O) (t := t) (u := u) hne (key.trans ?_)
  exact (Algebra.TensorProduct.tmul_mul_tmul c 1 1 u).trans (by rw [_root_.mul_one, _root_.one_mul])

end GlobalTheory.Mum.RatConst
