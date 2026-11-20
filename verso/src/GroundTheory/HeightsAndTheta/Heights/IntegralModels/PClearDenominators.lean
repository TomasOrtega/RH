import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.RatLocalAffine
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Sheaf

variable {X : Scheme.{0}} (M : X.Modules)

/- English proof (translation)
Rewrite using `[Subsingleton.elim k (i ≫ j), op_comp, CategoryTheory.Functor.map_comp]`. Both sides reduce to the same expression.
-/
lemma res_res {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C) (x : Γ(M, C)) :
    (M.presheaf.map i.op).hom ((M.presheaf.map j.op).hom x) = (M.presheaf.map k.op).hom x := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, CategoryTheory.Functor.map_comp]
  rfl

/- English proof (translation)
Set `F : TopCat.Sheaf Ab X` to `⟨M.presheaf, M.isSheaf⟩`. Use `choose W i hx h using h`. Use `F.eq_of_locally_eq' (U := fun x : V => W x.1 x.2) V (fun x => homOfLE (i _ _)) ?_ a b (fun x => h _ _)` and prove the remaining obligations. Introduce `x hxV`. Conclude with `Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _ _⟩`.
-/
lemma modules_eq_of_locally {V : X.Opens} (a b : Γ(M, V))
    (h : ∀ x ∈ V, ∃ (W : X.Opens) (i : W ≤ V), x ∈ W ∧
      (M.presheaf.map (homOfLE i).op).hom a = (M.presheaf.map (homOfLE i).op).hom b) : a = b := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  choose W i hx h using h
  refine F.eq_of_locally_eq' (U := fun x : V => W x.1 x.2) V (fun x => homOfLE (i _ _)) ?_ a b
    (fun x => h _ _)
  intro x hxV
  exact Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _ _⟩

/- English proof (translation)
Set `F : TopCat.Sheaf Ab X` to `⟨M.presheaf, M.isSheaf⟩`. Take `⟨s, hs, -⟩` from `F.existsUnique_gluing' W V (fun a => homOfLE (i a)) (fun x hxV => Opens.mem_iSup.2 (hcov x hxV)) sf hsf`. Conclude with `⟨s, hs⟩`.
-/
lemma modules_exists_glue {V : X.Opens} {ι : Type} (W : ι → X.Opens) (i : ∀ a, W a ≤ V)
    (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, Γ(M, W a))
    (hsf : ∀ a b, (M.presheaf.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op).hom (sf a) =
      (M.presheaf.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op).hom (sf b)) :
    ∃ s : Γ(M, V), ∀ a, (M.presheaf.map (homOfLE (i a)).op).hom s = sf a := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W V (fun a => homOfLE (i a))
    (fun x hxV => Opens.mem_iSup.2 (hcov x hxV)) sf hsf
  exact ⟨s, hs⟩

variable {M}

/- English proof (translation)
Establish `e : ∀ x : Γ(M, U), (M.presheaf.map (homOfLE (le_refl U)).op).hom x = x`. Introduce `x`. Rewrite using `[Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression. Simplify `hs U le_rfl` using `only [e]`.
-/
lemma IsBasisOn.bijective_self {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    Function.Bijective (fun r : Fin n → Γ(X, U) => ∑ i, r i • s i) := by
  have e : ∀ x : Γ(M, U), (M.presheaf.map (homOfLE (le_refl U)).op).hom x = x := by
    intro x
    rw [Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
    rfl
  simpa only [e] using hs U le_rfl

end Sheaf

section Pull

variable {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules)

/- English proof (translation)
The claim follows from `Scheme.Modules.Hom.app_smul _ r m`.
-/
lemma pullSectionOn_smul (U : Z.Opens) (r : Γ(Z, U)) (m : Γ(M, U)) :
    pullSectionOn g M U (r • m) = g.app U r • pullSectionOn g M U m :=
  Scheme.Modules.Hom.app_smul _ r m

/- English proof (translation)
Use `((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality (homOfLE h).op` as an intermediate fact. Establish `h2` using `congrArg (fun φ => φ.hom m) this`. Simplify using `only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2`. Rewrite using `[Subsingleton.elim i ((Opens.map g.base).map (homOfLE h))]`. Conclude with `h2`.
-/
lemma pullSectionOn_res {U V : Z.Opens} (h : V ≤ U) (i : g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ U) (m : Γ(M, U)) :
    pullSectionOn g M V ((M.presheaf.map (homOfLE h).op).hom m) =
      (((Scheme.Modules.pullback g).obj M).presheaf.map i.op).hom (pullSectionOn g M U m) := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality
    (homOfLE h).op
  have h2 := congrArg (fun φ => φ.hom m) this
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2
  rw [Subsingleton.elim i ((Opens.map g.base).map (homOfLE h))]
  exact h2

/- English proof (translation)
Rewrite using `[map_sum]`. Simplify using `only [pullSectionOn_smul]`.
-/
lemma pullSectionOn_sum (U : Z.Opens) {n : ℕ} (t : Fin n → Γ(M, U)) (r : Fin n → Γ(Z, U)) :
    pullSectionOn g M U (∑ i, r i • t i) = ∑ i, g.app U (r i) • pullSectionOn g M U (t i) := by
  rw [map_sum]
  simp only [pullSectionOn_smul]

end Pull

section Local

variable (hPB : PullbackBasis.Statement.{0}) (hRL : RatLocalAffine.Statement)
  {X : Scheme.{0}} (f : X ⟶ SpecZ) [Flat f] (L : X.Modules)
  {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} {t : Fin n → Γ(L, W)} (ht : IsBasisOn L W t)
include hPB hRL hW ht

/- English proof (translation)
Establish `hb` using `(hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self`. Establish `hinj` using `(hRL X f W hW).1`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `τ hτ`. Take `⟨r, rfl⟩` from `ht.bijective_self.2 τ`.

Establish `h0 : (fun i => (baseChangeMap f ℚ).app W (r i)) = 0`. Apply `hb.1` to reduce the goal to its premises. Simplify using `only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]`. Conclude with `(pullSectionOn_sum _ L W t r).symm.trans hτ`. Establish `hr : r = 0` using `funext fun i => hinj (by rw [Pi.zero_apply, map_zero]; exact congrFun h0 i)`.

Simplify using `[hr]`.
-/
lemma pullSectionOn_injective_of_basis :
    Function.Injective (pullSectionOn (baseChangeMap f ℚ) L W) := by
  have hb := (hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self
  have hinj := (hRL X f W hW).1
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  obtain ⟨r, rfl⟩ := ht.bijective_self.2 τ
  have h0 : (fun i => (baseChangeMap f ℚ).app W (r i)) = 0 := by
    apply hb.1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (pullSectionOn_sum _ L W t r).symm.trans hτ
  have hr : r = 0 := funext fun i => hinj (by rw [Pi.zero_apply, map_zero]; exact congrFun h0 i)
  simp [hr]

/- English proof (translation)
Establish `hb` using `(hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self`. Take `⟨b, rfl⟩` from `hb.2 σ`. Use `choose N hN a ha using fun i => (hRL X f W hW).2 (b i)`. Use `⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • a i) • t i, ?_⟩` and prove the remaining obligations. Rewrite using `[pullSectionOn_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, ha i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]`.
-/
lemma exists_pullSectionOn_eq_nsmul_of_basis
    (σ : Γ((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L, baseChangeMap f ℚ ⁻¹ᵁ W)) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : Γ(L, W), pullSectionOn (baseChangeMap f ℚ) L W τ = N • σ := by
  have hb := (hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self
  obtain ⟨b, rfl⟩ := hb.2 σ
  choose N hN a ha using fun i => (hRL X f W hW).2 (b i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i,
    ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • a i) • t i, ?_⟩
  rw [pullSectionOn_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ha i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]

end Local

/- English proof (translation)
Introduce `X f _ _ _ L hL s`. Establish `good : ∀ x : X, ∀ V : X.Opens, x ∈ V → ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V ∧ ∃ (n : ℕ) (t : Fin n → Γ(L, W)), IsBasisOn L W t`. Introduce `x V hxV`. Take `⟨U, -, hxU, n, t, ht⟩` from `hL x`. Take `⟨W, hW, hxW, hWle⟩` from `Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)`.

Conclude with `⟨W, hW, hxW, hWle.trans inf_le_right, n, _, ht.restrict (hWle.trans inf_le_left)⟩`. Establish `inj : ∀ V : X.Opens, Function.Injective (pullSectionOn (baseChangeMap f ℚ) L V)`. Introduce `V`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `τ hτ`.

Apply `modules_eq_of_locally L τ 0` to reduce the goal to its premises. Introduce `x hx`. Take `⟨W, hW, hxW, hWV, n, t, ht⟩` from `good x V hx`. Use `⟨W, hWV, hxW, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`.

Apply `pullSectionOn_injective_of_basis hPB hRL f L hW ht` to reduce the goal to its premises. Rewrite using `[pullSectionOn_res (baseChangeMap f ℚ) L hWV (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone hWV)) τ, hτ, map_zero, map_zero]`. Use `choose W hW hxW _hle n t ht using fun x : X => good x ⊤ trivial`. Establish `hcl` using `fun x : X => exists_pullSectionOn_eq_nsmul_of_basis hPB hRL f L (hW x) (ht x) ((((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W x ≤ ⊤))).op).hom s)`. Use `choose N hN τ hτ using hcl`.

Take `⟨F, hF⟩` from `isCompact_univ.elim_finite_subcover (fun x => (W x : Set X)) (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)`. Establish `hcov : ∀ x : X, ∃ a : F, x ∈ W a`. Introduce `x`. Take `⟨a, ha, hx⟩` from `Set.mem_iUnion₂.1 (hF (Set.mem_univ x))`. Conclude with `⟨⟨a, ha⟩, hx⟩`.

Set `c : F → ℕ` to `fun a => ∏ y ∈ F.erase a, N y`. Establish `hc : ∀ a : F, c a * N a = ∏ y ∈ F, N y` using `fun a => Finset.prod_erase_mul _ _ a.2`. Set `τ' : ∀ a : F, Γ(L, W a)` to `fun a => c a • τ a`. Establish `hτ' : ∀ a : F, pullSectionOn (baseChangeMap f ℚ) L (W a) (τ' a) = (∏ y ∈ F, N y) • (((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W a ≤ ⊤))).op).hom s`. Introduce `a`.

Simplify using `only [τ', map_nsmul, hτ, smul_smul, hc]`. Take `⟨T', hT'⟩` from `modules_exists_glue L (V := ⊤) (fun a : F => W a) (fun _ => le_top) (fun x _ => hcov x) τ' (fun a b => by`. Apply `inj` to reduce the goal to its premises. Rewrite using `[pullSectionOn_res (baseChangeMap f ℚ) L inf_le_left (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_left)), pullSectionOn_res (baseChangeMap f ℚ) L inf_le_right (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_right)), hτ', hτ', map_nsmul, map_nsmul, …`. Use `⟨∏ y ∈ F, N y, Finset.prod_pos fun y _ => hN y, T', ?_⟩` and prove the remaining obligations.

Apply `modules_eq_of_locally` to reduce the goal to its premises. Introduce `y _`. Take `⟨a, ha⟩` from `hcov ((baseChangeMap f ℚ).base y)`. Use `⟨(baseChangeMap f ℚ) ⁻¹ᵁ W a, (Opens.map (baseChangeMap f ℚ).base).monotone le_top, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← pullSectionOn_top, ← pullSectionOn_res (baseChangeMap f ℚ) L le_top, hT', hτ', map_nsmul]`.
-/
theorem ClearDenominators.proof (hPB : PullbackBasis.Statement.{0})
    (hRL : RatLocalAffine.Statement) : ClearDenominators.Statement := by
  classical
  intro X f _ _ _ L hL s
  have good : ∀ x : X, ∀ V : X.Opens, x ∈ V → ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V ∧
      ∃ (n : ℕ) (t : Fin n → Γ(L, W)), IsBasisOn L W t := by
    intro x V hxV
    obtain ⟨U, -, hxU, n, t, ht⟩ := hL x
    obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
    exact ⟨W, hW, hxW, hWle.trans inf_le_right, n, _, ht.restrict (hWle.trans inf_le_left)⟩

  have inj : ∀ V : X.Opens, Function.Injective (pullSectionOn (baseChangeMap f ℚ) L V) := by
    intro V
    rw [injective_iff_map_eq_zero]
    intro τ hτ
    apply modules_eq_of_locally L τ 0
    intro x hx
    obtain ⟨W, hW, hxW, hWV, n, t, ht⟩ := good x V hx
    refine ⟨W, hWV, hxW, ?_⟩
    rw [map_zero]
    apply pullSectionOn_injective_of_basis hPB hRL f L hW ht
    rw [pullSectionOn_res (baseChangeMap f ℚ) L hWV (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone hWV)) τ, hτ, map_zero,
      map_zero]

  choose W hW hxW _hle n t ht using fun x : X => good x ⊤ trivial
  have hcl := fun x : X => exists_pullSectionOn_eq_nsmul_of_basis hPB hRL f L (hW x) (ht x)
    ((((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map
      (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W x ≤ ⊤))).op).hom s)
  choose N hN τ hτ using hcl
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  have hcov : ∀ x : X, ∃ a : F, x ∈ W a := by
    intro x
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩

  let c : F → ℕ := fun a => ∏ y ∈ F.erase a, N y
  have hc : ∀ a : F, c a * N a = ∏ y ∈ F, N y := fun a => Finset.prod_erase_mul _ _ a.2
  let τ' : ∀ a : F, Γ(L, W a) := fun a => c a • τ a
  have hτ' : ∀ a : F, pullSectionOn (baseChangeMap f ℚ) L (W a) (τ' a) = (∏ y ∈ F, N y) •
      (((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map
        (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W a ≤ ⊤))).op).hom s := by
    intro a
    simp only [τ', map_nsmul, hτ, smul_smul, hc]
  obtain ⟨T', hT'⟩ := modules_exists_glue L (V := ⊤) (fun a : F => W a) (fun _ => le_top)
    (fun x _ => hcov x) τ' (fun a b => by
      apply inj
      rw [pullSectionOn_res (baseChangeMap f ℚ) L inf_le_left (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_left)),
        pullSectionOn_res (baseChangeMap f ℚ) L inf_le_right (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_right)),
        hτ', hτ', map_nsmul, map_nsmul, res_res, res_res _ _ _
          (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W a ⊓ W b ≤ ⊤)))])
  refine ⟨∏ y ∈ F, N y, Finset.prod_pos fun y _ => hN y, T', ?_⟩
  apply modules_eq_of_locally
  intro y _
  obtain ⟨a, ha⟩ := hcov ((baseChangeMap f ℚ).base y)
  refine ⟨(baseChangeMap f ℚ) ⁻¹ᵁ W a, (Opens.map (baseChangeMap f ℚ).base).monotone le_top, ha, ?_⟩
  rw [← pullSectionOn_top, ← pullSectionOn_res (baseChangeMap f ℚ) L le_top, hT', hτ', map_nsmul]

end

end GroundTheory.Heights₂.Heights.Model
