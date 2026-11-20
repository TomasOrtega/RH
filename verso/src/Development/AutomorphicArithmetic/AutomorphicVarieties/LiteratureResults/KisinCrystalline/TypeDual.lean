import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinCrystalline.TypeSt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformPer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AutomorphicArithmetic.AutomorphicVarieties.KisinPhiModules.TypeDualTwistIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module UpperTheory.V.Loc UpperTheory.V.Lit GlobalTheory.Pst GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

noncomputable section

namespace UpperTheory.V.Lit.TypeDual

section Alg

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨Fintype.linearIndependent_iff.2 fun k hk i => congrFun ((h 0 U.zero_mem).unique hk.symm (y₂ := 0) (by simp)) i, le_antisymm ?_ fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hz i`. Take `⟨k, hk, -⟩` from `h y hy`. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨k, hk.symm⟩`. Introduce and unpack `⟨h1, rfl⟩ y hy`. Take `⟨k, hk⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hy`.

Conclude with `⟨k, hk.symm, fun k' h' => funext ((Fintype.linearIndependent_iffₛ.1 h1) k' k (h'.symm.trans hk.symm))⟩`.
-/
private theorem exu_iff {F W κ : Type} [Field F] [AddCommGroup W] [Module F W] [Fintype κ] (U : Submodule F W)
    (z : κ → W) (hz : ∀ i, z i ∈ U) :
    (∀ y ∈ U, ∃! k : κ → F, y = ∑ i, k i • z i) ↔
      LinearIndependent F z ∧ Submodule.span F (Set.range z) = U := by
  constructor
  · intro h
    refine ⟨Fintype.linearIndependent_iff.2 fun k hk i =>
      congrFun ((h 0 U.zero_mem).unique hk.symm (y₂ := 0) (by simp)) i, le_antisymm ?_ fun y hy => ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hz i
    · obtain ⟨k, hk, -⟩ := h y hy
      exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨k, hk.symm⟩
  · rintro ⟨h1, rfl⟩ y hy
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    exact ⟨k, hk.symm, fun k' h' => funext ((Fintype.linearIndependent_iffₛ.1 h1) k' k (h'.symm.trans hk.symm))⟩

/- English proof (translation)
Establish `hw₀` using `hw.restrict_scalars' F₀`. Rewrite using `[exu_iff _ z hz, exu_iff _ z fun i => Submodule.span_subset_span F₀ F _ (hz i)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `h3 : Submodule.span F (Set.range z) = Submodule.span F (Set.range w)`.

Rewrite using `[← Submodule.span_span_of_tower F₀ F (Set.range z), h2, Submodule.span_span_of_tower]`. Use `⟨linearIndependent_iff_card_eq_finrank_span.2 ?_, h3⟩` and prove the remaining obligations. Rewrite using `[Set.finrank, h3, finrank_span_eq_card hw, ← finrank_span_eq_card hw₀, ← h2, finrank_span_eq_card h1]`. Introduce and unpack `⟨h1, h2⟩`. Establish `h3` using `h1.restrict_scalars' F₀`.

Use `⟨h3, ?_⟩` and prove the remaining obligations. Use `haveI := FiniteDimensional.span_of_finite F₀ (Set.finite_range w)`. Use `Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hz i`.

Rewrite using `[finrank_span_eq_card h3, finrank_span_eq_card hw₀, ← finrank_span_eq_card h1, h2, finrank_span_eq_card hw]`.
-/
private theorem field_iff {F₀ F W ι κ : Type} [Field F₀] [Field F] [Algebra F₀ F] [AddCommGroup W] [Module F W]
    [Module F₀ W] [IsScalarTower F₀ F W] [Fintype κ] [Fintype ι] (w : ι → W) (hw : LinearIndependent F w)
    (z : κ → W) (hz : ∀ i, z i ∈ Submodule.span F₀ (Set.range w)) :
    (∀ y ∈ Submodule.span F₀ (Set.range w), ∃! k : κ → F₀, y = ∑ i, k i • z i) ↔
      (∀ y ∈ Submodule.span F (Set.range w), ∃! k : κ → F, y = ∑ i, k i • z i) := by
  have hw₀ := hw.restrict_scalars' F₀
  rw [exu_iff _ z hz, exu_iff _ z fun i => Submodule.span_subset_span F₀ F _ (hz i)]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : Submodule.span F (Set.range z) = Submodule.span F (Set.range w) := by
      rw [← Submodule.span_span_of_tower F₀ F (Set.range z), h2, Submodule.span_span_of_tower]
    refine ⟨linearIndependent_iff_card_eq_finrank_span.2 ?_, h3⟩
    rw [Set.finrank, h3, finrank_span_eq_card hw, ← finrank_span_eq_card hw₀, ← h2, finrank_span_eq_card h1]
  · rintro ⟨h1, h2⟩
    have h3 := h1.restrict_scalars' F₀
    refine ⟨h3, ?_⟩
    haveI := FiniteDimensional.span_of_finite F₀ (Set.finite_range w)
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact hz i
    · rw [finrank_span_eq_card h3, finrank_span_eq_card hw₀, ← finrank_span_eq_card h1, h2, finrank_span_eq_card hw]

variable {Q A V F P J ι : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V]
  [IsScalarTower Q A V] [Field F] [Algebra Q F] [CommRing P] [Algebra Q P] [Algebra F P] [IsScalarTower Q F P]
  [Fintype J] [Fintype ι] (α : Basis J Q A)

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul v b => simp [Thick.sm_tmul, smul_tmul']`.
-/
private theorem sm_comm (a : A) (k : F) (y : V ⊗[Q] P) :
    Thick.sm V P (a ⊗ₜ[Q] k) y = TensorProduct.comm Q P V (k • (TensorProduct.comm Q P V).symm (a • y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul v b => simp [Thick.sm_tmul, smul_tmul']

/- English proof (translation)
Set `e : (ι × J → F) ≃ (ι → A ⊗[Q] F)` to `(Equiv.curry ι J F).trans (Equiv.piCongrRight fun _ => Finsupp.equivFunOnFinite.symm.trans (TensorProduct.equivFinsuppOfBasisLeft α).symm.toEquiv)`. Establish `he : ∀ k a, e k a = ∑ j, α j ⊗ₜ[Q] k (a, j)`. Introduce `k a`. Express the relevant statement in the definitionally equal form `(TensorProduct.equivFinsuppOfBasisLeft α).symm _ = _`. Rewrite using `[TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]`.

Both sides reduce to the same expression. Use `(e.existsUnique_congr fun k => ?_).symm` and prove the remaining obligations. Rewrite using `[LinearEquiv.symm_apply_eq]`. Simplify using `only [he, map_sum, LinearMap.sum_apply, sm_comm, Fintype.sum_prod_type]`.
-/
private theorem coord_iff (x : ι → V ⊗[Q] P) (y : V ⊗[Q] P) :
    (∃! c : ι → A ⊗[Q] F, y = ∑ a, Thick.sm V P (c a) (x a)) ↔
      ∃! k : ι × J → F, (TensorProduct.comm Q P V).symm y =
        ∑ i, k i • (TensorProduct.comm Q P V).symm (α i.2 • x i.1) := by
  classical
  let e : (ι × J → F) ≃ (ι → A ⊗[Q] F) := (Equiv.curry ι J F).trans (Equiv.piCongrRight fun _ =>
    Finsupp.equivFunOnFinite.symm.trans (TensorProduct.equivFinsuppOfBasisLeft α).symm.toEquiv)
  have he : ∀ k a, e k a = ∑ j, α j ⊗ₜ[Q] k (a, j) := by
    intro k a
    change (TensorProduct.equivFinsuppOfBasisLeft α).symm _ = _
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  refine (e.existsUnique_congr fun k => ?_).symm
  rw [LinearEquiv.symm_apply_eq]
  simp only [he, map_sum, LinearMap.sum_apply, sm_comm, Fintype.sum_prod_type]

end Alg

section Dual

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨T⟩` from `tiedP l`. Use `haveI := isDomain_of_tied T K`. Establish `h1` using `GlobalTheory.TateDualCrys.fracInv_of_tied T K`. Establish `h2` using `GlobalTheory.TateDualCrys.lineUnit_of_tied T K`. Set `e` to `dualTensorHomEquiv ℚ_[l] V V'`.

Use `subCrys _ ℚ_[l] h1 _ _ _ π (e.symm.toLinearMap ∘ₗ b) (fun g w => ?_) (e.symm.injective.comp hi) (tensorCrys _ ℚ_[l] h1 h2 _ _ _ _ (dualCrys _ ℚ_[l] h1 h2 _ ρ h) h')` and prove the remaining obligations. Establish `key : ∀ (t : Module.Dual ℚ_[l] V ⊗[ℚ_[l]] V') (x : V), e ((ρ.dual.tprod ρ') g t) (ρ g x) = ρ' g (e t x)`. Introduce `t x`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]`. Consider the case `tmul f y => simp [e, Module.Dual.transpose_apply]`. Apply `e.injective` to reduce the goal to its premises. Use extensionality with `x`. Take `⟨x, rfl⟩ : ∃ y, ρ g y = x` from `⟨ρ g⁻¹ x, by simp⟩`.

Rewrite using `[key]`. Simplify using `[hb]`.
-/
private theorem crys_pair (K : FinExt l) {V V' W : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [AddCommGroup V'] [Module ℚ_[l] V'] [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V'] [FiniteDimensional ℚ_[l] W]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V')
    (π : Representation ℚ_[l] ↥(GK K) W) (b : W →ₗ[ℚ_[l]] V →ₗ[ℚ_[l]] V')
    (hb : ∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x)) (hi : Function.Injective b)
    (h : IsCrys ((PP l).PD K) ρ) (h' : IsCrys ((PP l).PD K) ρ') : IsCrys ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  haveI := isDomain_of_tied T K
  have h1 := GlobalTheory.TateDualCrys.fracInv_of_tied T K
  have h2 := GlobalTheory.TateDualCrys.lineUnit_of_tied T K
  let e := dualTensorHomEquiv ℚ_[l] V V'
  refine subCrys _ ℚ_[l] h1 _ _ _ π (e.symm.toLinearMap ∘ₗ b) (fun g w => ?_) (e.symm.injective.comp hi)
    (tensorCrys _ ℚ_[l] h1 h2 _ _ _ _ (dualCrys _ ℚ_[l] h1 h2 _ ρ h) h')
  have key : ∀ (t : Module.Dual ℚ_[l] V ⊗[ℚ_[l]] V') (x : V),
      e ((ρ.dual.tprod ρ') g t) (ρ g x) = ρ' g (e t x) := by
    intro t x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
    | tmul f y => simp [e, Module.Dual.transpose_apply]
  apply e.injective
  ext x
  obtain ⟨x, rfl⟩ : ∃ y, ρ g y = x := ⟨ρ g⁻¹ x, by simp⟩
  rw [key]
  simp [hb]

/- English proof (translation)
Take `⟨T⟩` from `tiedP l`. Use `haveI := isDomain_of_tied T K`. Rewrite using `[isCrys_iff_span _ (GlobalTheory.TateDualCrys.fracInv_of_tied T K) (GlobalTheory.TateDualCrys.lineUnit_of_tied T K)]`. Take `⟨u, hu⟩` from `((PP l).PD K).t_unit`. Establish `hact : ∀ g, ((PP l).PD K).actB g ((u ^ (-w) : (Bcr l)ˣ) : Bcr l) = ((((PP l).PD K).χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • ((u ^ (-w) : (Bcr l)ˣ) : Bcr l)` using `fun g => by`.

Establish `h1 : Units.map (((PP l).PD K).actB g : Bcr l →* Bcr l) u = Units.map (algebraMap ℚ_[l] (Bcr l) : ℚ_[l] →* Bcr l) (((PP l).PD K).χ g) * u`. Use `ext`. Express the relevant statement in the definitionally equal form `((PP l).PD K).actB g u = algebraMap ℚ_[l] (Bcr l) (((PP l).PD K).χ g : ℚ_[l]ˣ) * u`. Rewrite using `[hu, ((PP l).PD K).t_act, Algebra.smul_def]`. Establish `h2` using `congrArg (fun x : (Bcr l)ˣ => ((x ^ (-w) : (Bcr l)ˣ) : Bcr l)) h1`.

Use `beta_reduce at h2`. Rewrite `h2` using `[mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul]`. Rewrite using `[Algebra.smul_def]`. Conclude with `h2`. Use `eq_top_of_tmul _ fun b v => ?_` and prove the remaining obligations.

Establish `e : b ⊗ₜ[ℚ_[l]] v = (b * ((u ^ w : (Bcr l)ˣ) : Bcr l)) • (((u ^ (-w) : (Bcr l)ˣ) : Bcr l) ⊗ₜ[ℚ_[l]] v)`. Rewrite using `[smul_tmul', smul_eq_mul, mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]`. Rewrite using `[e]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ((mem_DcrisK₀ _ _ _).2 fun g => ?_))` and prove the remaining obligations. Rewrite using `[sig_tmul, hact, h, smul_tmul, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_smul]`.
-/
private theorem crys_chi (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) (w : ℤ)
    (h : ∀ g x, ρ g x = ((((PP l).PD K).χ g ^ w : ℚ_[l]ˣ) : ℚ_[l]) • x) : IsCrys ((PP l).PD K) ρ := by
  obtain ⟨T⟩ := tiedP l
  haveI := isDomain_of_tied T K
  rw [isCrys_iff_span _ (GlobalTheory.TateDualCrys.fracInv_of_tied T K) (GlobalTheory.TateDualCrys.lineUnit_of_tied T K)]
  obtain ⟨u, hu⟩ := ((PP l).PD K).t_unit
  have hact : ∀ g, ((PP l).PD K).actB g ((u ^ (-w) : (Bcr l)ˣ) : Bcr l) =
      ((((PP l).PD K).χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • ((u ^ (-w) : (Bcr l)ˣ) : Bcr l) := fun g => by
    have h1 : Units.map (((PP l).PD K).actB g : Bcr l →* Bcr l) u =
        Units.map (algebraMap ℚ_[l] (Bcr l) : ℚ_[l] →* Bcr l) (((PP l).PD K).χ g) * u := by
      ext
      change ((PP l).PD K).actB g u = algebraMap ℚ_[l] (Bcr l) (((PP l).PD K).χ g : ℚ_[l]ˣ) * u
      rw [hu, ((PP l).PD K).t_act, Algebra.smul_def]
    have h2 := congrArg (fun x : (Bcr l)ˣ => ((x ^ (-w) : (Bcr l)ˣ) : Bcr l)) h1
    beta_reduce at h2
    rw [mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul] at h2
    rw [Algebra.smul_def]
    exact h2
  refine eq_top_of_tmul _ fun b v => ?_
  have e : b ⊗ₜ[ℚ_[l]] v = (b * ((u ^ w : (Bcr l)ˣ) : Bcr l)) • (((u ^ (-w) : (Bcr l)ˣ) : Bcr l) ⊗ₜ[ℚ_[l]] v) := by
    rw [smul_tmul', smul_eq_mul, mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      mul_one]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ((mem_DcrisK₀ _ _ _).2 fun g => ?_))
  rw [sig_tmul, hact, h, smul_tmul, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
    one_smul]

/- English proof (translation)
Use `set χ : ↥(GK K) →* Bˣ := ((cycA l l B).comp (GK K).subtype) ^ w with hχ`. Establish `h0 : Crys K (chRep χ)`. Use `crys_chi K _ w fun g x => ?_` and prove the remaining obligations. Establish `h2 : cycA l l B g = Units.map (algebraMap ℚ_[l] B : ℚ_[l] →* B) (((PP l).PD K).χ g)`. Use `ext`.

Express the relevant statement in the definitionally equal form `algebraMap ℤ_[l] B _ = algebraMap ℚ_[l] B _`. Rewrite using `[(PP l).PD_χ, (cycFacts l l).2.2, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `((cycA l l B g ^ w : Bˣ) : B) • x = _`. Rewrite using `[h2, ← map_zpow]`.

Conclude with `algebraMap_smul B _ x`. Set `b : (Fin n → B) →ₗ[ℚ_[l]] (Fin n → B) →ₗ[ℚ_[l]] B` to `dotProductBilin ℚ_[l] ℚ_[l]`. Establish `hb : ∀ x y, b x y = x ⬝ᵥ y` using `fun _ _ => rfl`. Establish `hi : Function.Injective b` using `fun x y h => dotProduct_eq _ _ fun u => by rw [← hb, ← hb, h]`. Establish `key : ∀ g x y, colRep (dualTw χ ρ) g x ⬝ᵥ colRep ρ g y = (χ g : B) * (x ⬝ᵥ y)`.

Introduce `g x y`. Express the relevant statement in the definitionally equal form `Matrix.mulVec ((χ g : B) • (ρ g⁻¹ : Matrix (Fin n) (Fin n) B).transpose) x ⬝ᵥ Matrix.mulVec (ρ g : Matrix (Fin n) (Fin n) B) y = _`. Rewrite using `[Matrix.smul_mulVec, smul_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec, smul_eq_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `crys_pair K _ _ _ b (fun g x y => key g x y) hi h h0`. Introduce `h`. Use `crys_pair K _ _ _ b (fun g x y => ?_) hi h h0` and prove the remaining obligations. Rewrite using `[hb, hb, dotProduct_comm, dotProduct_comm x]`. Conclude with `key g y x`.
-/
private theorem crys_dual (K : FinExt l) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
    [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] (n : ℕ) (ρ : ↥(GK K) →* GL (Fin n) B) (w : ℤ) :
    Crys K (colRep ρ) ↔ Crys K (colRep (dualTw (((cycA l l B).comp (GK K).subtype) ^ w) ρ)) := by
  set χ : ↥(GK K) →* Bˣ := ((cycA l l B).comp (GK K).subtype) ^ w with hχ
  have h0 : Crys K (chRep χ) := by
    refine crys_chi K _ w fun g x => ?_
    have h2 : cycA l l B g = Units.map (algebraMap ℚ_[l] B : ℚ_[l] →* B) (((PP l).PD K).χ g) := by
      ext
      change algebraMap ℤ_[l] B _ = algebraMap ℚ_[l] B _
      rw [(PP l).PD_χ, (cycFacts l l).2.2, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B]
      rfl
    change ((cycA l l B g ^ w : Bˣ) : B) • x = _
    rw [h2, ← map_zpow]
    exact algebraMap_smul B _ x
  let b : (Fin n → B) →ₗ[ℚ_[l]] (Fin n → B) →ₗ[ℚ_[l]] B := dotProductBilin ℚ_[l] ℚ_[l]
  have hb : ∀ x y, b x y = x ⬝ᵥ y := fun _ _ => rfl
  have hi : Function.Injective b := fun x y h => dotProduct_eq _ _ fun u => by rw [← hb, ← hb, h]
  have key : ∀ g x y, colRep (dualTw χ ρ) g x ⬝ᵥ colRep ρ g y = (χ g : B) * (x ⬝ᵥ y) := by
    intro g x y
    change Matrix.mulVec ((χ g : B) • (ρ g⁻¹ : Matrix (Fin n) (Fin n) B).transpose) x ⬝ᵥ
      Matrix.mulVec (ρ g : Matrix (Fin n) (Fin n) B) y = _
    rw [Matrix.smul_mulVec, smul_dotProduct, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec,
      smul_eq_mul]
  constructor
  · intro h
    exact crys_pair K _ _ _ b (fun g x y => key g x y) hi h h0
  · intro h
    refine crys_pair K _ _ _ b (fun g x y => ?_) hi h h0
    rw [hb, hb, dotProduct_comm, dotProduct_comm x]
    exact key g y x

/- English proof (translation)
The claim follows from `exists_congr fun L => exists_congr fun h => crys_dual L B n (ρ.comp (incl h)) w`.
-/
private theorem potCr_dual (K : FinExt l) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B]
    [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] (n : ℕ) (ρ : ↥(GK K) →* GL (Fin n) B) (w : ℤ) :
    PotCr K (colRep ρ) ↔ PotCr K (colRep (dualTw (((cycA l l B).comp (GK K).subtype) ^ w) ρ)) :=
  exists_congr fun L => exists_congr fun h => crys_dual L B n (ρ.comp (incl h)) w

end Dual

section Cov

variable {l : ℕ} [Fact l.Prime] {A V : Type} [CommRing A] [Algebra ℚ_[l] A]
  [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

local notation "ci" => crisIncl (PP l) ℚ_[l] V
local notation "cm" => TensorProduct.comm ℚ_[l] (Bst (PP l)) V

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v b => simp [actC, resCoef]`.
-/
private theorem st_ci {K : FinExt l} (ρ : Representation A ↥(GK K) V) (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bcr l) :
    stRep (PP l) (resCoef ℚ_[l] ρ) g (ci y) = ci (actC (GK K).subtype ρ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actC, resCoef]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul v b => simp [smul_tmul']`.
-/
private theorem ci_smul (a : A) (y : V ⊗[ℚ_[l]] Bcr l) : ci (a • y) = a • ci y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul v b => simp [smul_tmul']

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul a k`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v b`. Use `(congrArg _ (Thick.sm_tmul a k v b)).trans ?_` and prove the remaining obligations. Rewrite using `[crisIncl_tmul, crisIncl_tmul, Thick.sm_tmul, Polynomial.smul_C]`.
-/
private theorem ci_sm (L : FinExt l) (c : A ⊗[ℚ_[l]] ↥(K0 L)) (y : V ⊗[ℚ_[l]] Bcr l) :
    ci (smulC V L c y) = Thick.sm V (Bst (PP l)) c (ci y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    refine (congrArg _ (Thick.sm_tmul a k v b)).trans ?_
    rw [crisIncl_tmul, crisIncl_tmul, Thick.sm_tmul, Polynomial.smul_C]

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul v b => simp [smul_tmul']`.
-/
private theorem st_smul {K : FinExt l} (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (s : Bst (PP l))
    (u : Bst (PP l) ⊗[ℚ_[l]] V) :
    (cm).symm (stRep (PP l) ρ g (cm (s • u))) = actSt (PP l) (g : GQ l) s • (cm).symm (stRep (PP l) ρ g (cm u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul v b => simp [smul_tmul']

private def jU (A : Type) [CommRing A] [Algebra ℚ_[l] A] (L : FinExt l) :
    A ⊗[ℚ_[l]] ↥(K0 L) →ₐ[ℚ_[l]] A ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (IntermediateField.inclusion (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l))

/- English proof (translation)
The claim follows from `Module.Flat.lTensor_preserves_injective_linearMap (M := A) (IntermediateField.inclusion (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l)).toLinearMap (IntermediateField.inclusion_injective (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l))`.
-/
private theorem jU_inj (L : FinExt l) : Function.Injective (jU A L) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := A)
    (IntermediateField.inclusion (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l)).toLinearMap (IntermediateField.inclusion_injective (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l))

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul a k`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v b`. Use `(Thick.sm_tmul _ _ _ _).trans (Eq.trans ?_ (Thick.sm_tmul a k v b).symm)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def]`.

Both sides reduce to the same expression.
-/
private theorem sm_jU (L : FinExt l) (c : A ⊗[ℚ_[l]] ↥(K0 L)) (y : V ⊗[ℚ_[l]] Bst (PP l)) :
    Thick.sm V (Bst (PP l)) (jU A L c) y = Thick.sm V (Bst (PP l)) c y := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    refine (Thick.sm_tmul _ _ _ _).trans (Eq.trans ?_ (Thick.sm_tmul a k v b).symm)
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl

variable [FiniteDimensional ℚ_[l] V]

/- English proof (translation)
Take `⟨T⟩` from `tiedP l`. Use `haveI := isDomain_of_tied T L`. Establish `hf` using `GlobalTheory.TateDualCrys.fracInv_of_tied T L`. Establish `hu` using `GlobalTheory.TateDualCrys.lineUnit_of_tied T L`. Take `⟨h1, -⟩` from `finite_le₀ _ hf (resCoef ℚ_[l] ρ)`.

Set `d₀` to `Module.finBasis ↥(K0 L) ↥(DcrisK₀ ((PP l).PD L) (resCoef ℚ_[l] ρ))`. Set `b` to `(Algebra.TensorProduct.basis (Bcr l) d₀).map (LinearEquiv.ofBijective _ (comparison_bijective _ hf hu (resCoef ℚ_[l] ρ) hc))`. Set `e` to `AlgebraTensorModule.cancelBaseChange ℚ_[l] (Bcr l) (Bst (PP l)) (Bst (PP l)) V`. Establish `he : ∀ y, cm (e (1 ⊗ₜ y)) = ci (TensorProduct.comm ℚ_[l] (Bcr l) V y)`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [tmul_add, map_add, hx, hy]`. Consider the case `tmul v b => simp [e, Polynomial.smul_eq_C_mul]`. Use `⟨_, (Algebra.TensorProduct.basis (Bst (PP l)) b).map e, fun i => ⟨TensorProduct.comm ℚ_[l] (Bcr l) V (b i), ?_, ?_⟩⟩` and prove the remaining obligations.

Establish `: b i = (d₀ i : Bcr l ⊗[ℚ_[l]] V)` using `by simp [b, comparison_tmul]`. Rewrite using `[this, Thick.mem_Dcr_iff]`. Conclude with `(d₀ i).2`. Rewrite using `[← he]`. Use `congr 1`.

Conclude with `((Basis.map_apply _ _ _).trans (congrArg e (Algebra.TensorProduct.basis_apply _ _))).symm`.
-/
private theorem exists_basis (L : FinExt l) (ρ : Representation A ↥(GK L) V) (hc : Crys L ρ) :
    ∃ (d : ℕ) (w : Basis (Fin d) (Bst (PP l)) (Bst (PP l) ⊗[ℚ_[l]] V)),
      ∀ i, ∃ y ∈ Dcr (GK L).subtype ρ, ci y = cm (w i) := by
  obtain ⟨T⟩ := tiedP l
  haveI := isDomain_of_tied T L
  have hf := GlobalTheory.TateDualCrys.fracInv_of_tied T L
  have hu := GlobalTheory.TateDualCrys.lineUnit_of_tied T L
  obtain ⟨h1, -⟩ := finite_le₀ _ hf (resCoef ℚ_[l] ρ)
  let d₀ := Module.finBasis ↥(K0 L) ↥(DcrisK₀ ((PP l).PD L) (resCoef ℚ_[l] ρ))
  let b := (Algebra.TensorProduct.basis (Bcr l) d₀).map
    (LinearEquiv.ofBijective _ (comparison_bijective _ hf hu (resCoef ℚ_[l] ρ) hc))
  let e := AlgebraTensorModule.cancelBaseChange ℚ_[l] (Bcr l) (Bst (PP l)) (Bst (PP l)) V
  have he : ∀ y, cm (e (1 ⊗ₜ y)) = ci (TensorProduct.comm ℚ_[l] (Bcr l) V y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | tmul v b => simp [e, Polynomial.smul_eq_C_mul]
  refine ⟨_, (Algebra.TensorProduct.basis (Bst (PP l)) b).map e, fun i => ⟨TensorProduct.comm ℚ_[l] (Bcr l) V (b i), ?_, ?_⟩⟩
  · have : b i = (d₀ i : Bcr l ⊗[ℚ_[l]] V) := by simp [b, comparison_tmul]
    rw [this, Thick.mem_Dcr_iff]
    exact (d₀ i).2
  · rw [← he]
    congr 1
    exact ((Basis.map_apply _ _ _).trans (congrArg e (Algebra.TensorProduct.basis_apply _ _))).symm

/- English proof (translation)
Take `⟨d, w, hw⟩` from `exists_basis L _ hc`. Take `⟨hdom, hreg, -⟩` from `stRegular l (PP l) (AIP l) (tiedP l)`. Establish `fix : ∀ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V), ∀ g : ↥(GK K), (g : GQ l) ∈ GK L → stRep (PP l) (resCoef ℚ_[l] ρ) g (ci y) = ci y` using `fun y hy g hg => (st_ci ρ g y).trans (congrArg _ ((Thick.mem_Dcr _ _ _).1 hy ⟨g, hg⟩))`. Establish `coef : ∀ (L' : FinExt l), L.1 ≤ L'.1 → ∀ u, (∀ g : ↥(GK K), (g : GQ l) ∈ GK L' → stRep (PP l) (resCoef ℚ_[l] ρ) g (cm u) = cm u) → ∀ i, ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ L'.1 ∧ w.repr u i = algebraMap ↥(MaximalUnramifiedExtension l) (Bst (PP l)) c`. Introduce `L' hL u hu i`.

Take `⟨c, h1, h2⟩` from `hreg L' 1 (w.repr u i) one_ne_zero fun g => by`. Set `g' : ↥(GK K)` to `⟨g, GK_le (h.trans hL) g.2⟩`. Establish `e1 : u = ∑ j, actSt (PP l) (g : GQ l) (w.repr u j) • w j` using `by conv_lhs => rw [← (cm).symm_apply_apply u, ← hu g' g.2, ← w.sum_repr u]`. Simplify using `only [map_sum, st_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Take `⟨y, hy, e⟩` from `hw j`. Rewrite using `[← e, fix y hy g' (GK_le hL g.2), e, LinearEquiv.symm_apply_apply]`. Rewrite using `[map_one, one_mul, one_mul]`. Use `conv_rhs => rw [e1]`. Conclude with `(congrFun (w.repr_sum_self fun j => actSt (PP l) (g : GQ l) (w.repr u j)) i).symm`.

Conclude with `⟨c, h1, by rw [h2, mul_one]⟩`. Establish `last : ∀ u, (∀ g : ↥(GK K), (g : GQ l) ∈ GK L → stRep (PP l) (resCoef ℚ_[l] ρ) g (cm u) = cm u) → u ∈ Submodule.span ↥(K0 L) (Set.range w)`. Introduce `u hu`. Use `choose c h1 h2 using coef L le_rfl u hu`. Use `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨c i, h1 i, (c i).2⟩, ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← w.sum_repr u]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h2, ← algebraMap_smul (Bst (PP l))]`. Both sides reduce to the same expression. Use `haveI : FaithfulSMul ↥(MaximalUnramifiedExtension l) (Bst (PP l)) := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ↥(MaximalUnramifiedExtension l) (Bst (PP l))).injective`.

Use `⟨d, w, w.linearIndependent.restrict_scalars' _, fun u => ⟨fun hu => ?_, fun hu => ?_⟩, fun u => ⟨fun hu => ?_, ?_⟩, last⟩` and prove the remaining obligations. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨i, rfl⟩` from `hu`. Take `⟨y, hy, e⟩` from `hw i`.

Conclude with `e ▸ (mem_Dpst _ _).2 ⟨L, fix y hy⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`.

Establish `: ∀ a, cm (c • a) = mulV (PP l) ℚ_[l] V c (cm a)`. Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`.

Consider the case `tmul v b => rw [smul_tmul', comm_tmul, comm_tmul, mulV_tmul, Algebra.smul_def]`. Rewrite using `[this]`. Conclude with `mulV_mem_Dpst _ _ c _ ha`. Take `⟨K', hK⟩` from `(mem_Dpst _ _).1 hu choose c h1 h2 using coef (supExt L K') le_sup_left u fun g hg => hK g (GK_le (K' := supExt L K') le_sup_right hg)`. Use `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← w.sum_repr u]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h2, algebraMap_smul]`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`.

Take `⟨i, rfl⟩` from `hu`. Conclude with `hw i`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨x, hx, ex⟩` from `ha`.

Take `⟨y, hy, ey⟩` from `hb`. Conclude with `⟨x + y, Submodule.add_mem _ hx hy, by rw [map_add, map_add, ex, ey]⟩`. Consider the case `smul c a _ ha`. Take `⟨x, hx, ex⟩` from `ha`. Use `⟨_, Thick.smulC_mem L _ ((1 : A) ⊗ₜ c) hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[ci_sm, sm_comm, one_smul, ex, LinearEquiv.symm_apply_apply]`. Introduce and unpack `⟨y, hy, e⟩`. Conclude with `last u (e ▸ fix y hy)`.
-/
private theorem exists_frame {K L : FinExt l} (h : K.1 ≤ L.1) (ρ : Representation A ↥(GK K) V)
    (hc : Crys L (ρ.comp (incl h) : Representation A ↥(GK L) V)) :
    ∃ (d : ℕ) (w : Fin d → Bst (PP l) ⊗[ℚ_[l]] V), LinearIndependent ↥(MaximalUnramifiedExtension l) w ∧
      (∀ u, u ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (Set.range w) ↔ cm u ∈ Dpst (PP l) (resCoef ℚ_[l] ρ)) ∧
      (∀ u, u ∈ Submodule.span ↥(K0 L) (Set.range w) ↔
        ∃ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V), ci y = cm u) ∧
      ∀ u, (∀ g : ↥(GK K), (g : GQ l) ∈ GK L → stRep (PP l) (resCoef ℚ_[l] ρ) g (cm u) = cm u) →
        u ∈ Submodule.span ↥(K0 L) (Set.range w) := by
  obtain ⟨d, w, hw⟩ := exists_basis L _ hc
  obtain ⟨hdom, hreg, -⟩ := stRegular l (PP l) (AIP l) (tiedP l)
  have fix : ∀ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V), ∀ g : ↥(GK K),
      (g : GQ l) ∈ GK L → stRep (PP l) (resCoef ℚ_[l] ρ) g (ci y) = ci y := fun y hy g hg =>
    (st_ci ρ g y).trans (congrArg _ ((Thick.mem_Dcr _ _ _).1 hy ⟨g, hg⟩))
  have coef : ∀ (L' : FinExt l), L.1 ≤ L'.1 → ∀ u,
      (∀ g : ↥(GK K), (g : GQ l) ∈ GK L' → stRep (PP l) (resCoef ℚ_[l] ρ) g (cm u) = cm u) →
      ∀ i, ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ L'.1 ∧ w.repr u i = algebraMap ↥(MaximalUnramifiedExtension l) (Bst (PP l)) c := by
    intro L' hL u hu i
    obtain ⟨c, h1, h2⟩ := hreg L' 1 (w.repr u i) one_ne_zero fun g => by
      let g' : ↥(GK K) := ⟨g, GK_le (h.trans hL) g.2⟩
      have e1 : u = ∑ j, actSt (PP l) (g : GQ l) (w.repr u j) • w j := by
        conv_lhs => rw [← (cm).symm_apply_apply u, ← hu g' g.2, ← w.sum_repr u]
        simp only [map_sum, st_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        obtain ⟨y, hy, e⟩ := hw j
        rw [← e, fix y hy g' (GK_le hL g.2), e, LinearEquiv.symm_apply_apply]
      rw [map_one, one_mul, one_mul]
      conv_rhs => rw [e1]
      exact (congrFun (w.repr_sum_self fun j => actSt (PP l) (g : GQ l) (w.repr u j)) i).symm
    exact ⟨c, h1, by rw [h2, mul_one]⟩
  have last : ∀ u, (∀ g : ↥(GK K), (g : GQ l) ∈ GK L → stRep (PP l) (resCoef ℚ_[l] ρ) g (cm u) = cm u) →
      u ∈ Submodule.span ↥(K0 L) (Set.range w) := by
    intro u hu
    choose c h1 h2 using coef L le_rfl u hu
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨c i, h1 i, (c i).2⟩, ?_⟩
    conv_rhs => rw [← w.sum_repr u]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2, ← algebraMap_smul (Bst (PP l))]
    rfl
  haveI : FaithfulSMul ↥(MaximalUnramifiedExtension l) (Bst (PP l)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ↥(MaximalUnramifiedExtension l) (Bst (PP l))).injective
  refine ⟨d, w, w.linearIndependent.restrict_scalars' _, fun u => ⟨fun hu => ?_, fun hu => ?_⟩,
    fun u => ⟨fun hu => ?_, ?_⟩, last⟩
  · induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      obtain ⟨y, hy, e⟩ := hw i
      exact e ▸ (mem_Dpst _ _).2 ⟨L, fix y hy⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : ∀ a, cm (c • a) = mulV (PP l) ℚ_[l] V c (cm a) := by
        intro a
        induction a using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, smul_add, hx, hy]
        | tmul v b => rw [smul_tmul', comm_tmul, comm_tmul, mulV_tmul, Algebra.smul_def]
      rw [this]
      exact mulV_mem_Dpst _ _ c _ ha
  · obtain ⟨K', hK⟩ := (mem_Dpst _ _).1 hu
    choose c h1 h2 using coef (supExt L K') le_sup_left u fun g hg => hK g (GK_le (K' := supExt L K') le_sup_right hg)
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, ?_⟩
    conv_rhs => rw [← w.sum_repr u]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2, algebraMap_smul]
  · induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      exact hw i
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx, ex⟩ := ha
      obtain ⟨y, hy, ey⟩ := hb
      exact ⟨x + y, Submodule.add_mem _ hx hy, by rw [map_add, map_add, ex, ey]⟩
    | smul c a _ ha =>
      obtain ⟨x, hx, ex⟩ := ha
      refine ⟨_, Thick.smulC_mem L _ ((1 : A) ⊗ₜ c) hx, ?_⟩
      rw [ci_sm, sm_comm, one_smul, ex, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, e⟩
    exact last u (e ▸ fix y hy)

variable [Module.Finite ℚ_[l] A]

/- English proof (translation)
Take `⟨d, w, hw, h1, h2, -⟩` from `exists_frame h ρ hc`. Use `letI : Algebra ↥(K0 L) ↥(MaximalUnramifiedExtension l) := (IntermediateField.inclusion (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l)).toRingHom.toAlgebra`. Use `haveI : IsScalarTower ↥(K0 L) ↥(MaximalUnramifiedExtension l) (Bst (PP l) ⊗[ℚ_[l]] V) := IsScalarTower.of_algebraMap_smul fun k u => by`. Rewrite using `[← algebraMap_smul (Bst (PP l)) k, ← algebraMap_smul (Bst (PP l)) (algebraMap ↥(K0 L) ↥(MaximalUnramifiedExtension l) k)]`. Both sides reduce to the same expression.

Set `α` to `Module.finBasis ℚ_[l] A`. Establish `key` using `field_iff (F₀ := ↥(K0 L)) w hw (fun i : Fin n × Fin (finrank ℚ_[l] A) => (cm).symm (α i.2 • ci (x i.1))) fun i => (h2 _).2 ⟨α i.2 • x i.1, Submodule.smul_mem _ _ (hx _), by rw [ci_smul, LinearEquiv.apply_symm_apply]⟩`. Establish `e : ∀ y, (∃! c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L), y = ∑ a, smulC V L (c a) (x a)) ↔ ∃! c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L), ci y = ∑ a, Thick.sm V (Bst (PP l)) (c a) (ci (x a))`. Use `fun y => existsUnique_congr fun c => ?_` and prove the remaining obligations. Simplify using `only [← ci_sm, ← map_sum]`.

Conclude with `(crisIncl_injective (PP l)).eq_iff.symm`. Use `Iff.trans ⟨fun H u hu => ?_, fun H y hy => ?_⟩ (key.trans ⟨fun H y hy => ?_, fun H u hu => ?_⟩)` and prove the remaining obligations. Take `⟨y, hy, ey⟩` from `(h2 u).1 hu`. Use `(coord_iff α _ _).1 ((e y).1 (H y hy))` as an intermediate fact. Rewrite `this` using `[ey, LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Conclude with `(e y).2 ((coord_iff α _ _).2 (H _ ((h2 _).2 ⟨y, hy, ((cm).apply_symm_apply _).symm⟩)))`. Conclude with `(coord_iff α _ _).2 (H _ ((h1 _).2 (by rwa [LinearEquiv.apply_symm_apply])))`. Use `(coord_iff α _ _).1 (H _ ((h1 u).1 hu))` as an intermediate fact. Rewrite `this` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
private theorem basis_iff {K L : FinExt l} (h : K.1 ≤ L.1) (ρ : Representation A ↥(GK K) V)
    (hc : Crys L (ρ.comp (incl h) : Representation A ↥(GK L) V)) {n : ℕ} (x : Fin n → V ⊗[ℚ_[l]] Bcr l)
    (hx : ∀ a, x a ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V)) :
    (∀ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V),
      ∃! c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L), y = ∑ a, smulC V L (c a) (x a)) ↔
    ∀ y ∈ Dpst (PP l) (resCoef ℚ_[l] ρ), ∃! c : Fin n → A ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      y = ∑ a, Thick.sm V (Bst (PP l)) (c a) (ci (x a)) := by
  obtain ⟨d, w, hw, h1, h2, -⟩ := exists_frame h ρ hc
  letI : Algebra ↥(K0 L) ↥(MaximalUnramifiedExtension l) := (IntermediateField.inclusion (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l)).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(K0 L) ↥(MaximalUnramifiedExtension l) (Bst (PP l) ⊗[ℚ_[l]] V) := IsScalarTower.of_algebraMap_smul fun k u => by
    rw [← algebraMap_smul (Bst (PP l)) k, ← algebraMap_smul (Bst (PP l)) (algebraMap ↥(K0 L) ↥(MaximalUnramifiedExtension l) k)]
    rfl
  let α := Module.finBasis ℚ_[l] A
  have key := field_iff (F₀ := ↥(K0 L)) w hw
    (fun i : Fin n × Fin (finrank ℚ_[l] A) => (cm).symm (α i.2 • ci (x i.1)))
    fun i => (h2 _).2 ⟨α i.2 • x i.1, Submodule.smul_mem _ _ (hx _), by rw [ci_smul, LinearEquiv.apply_symm_apply]⟩
  have e : ∀ y, (∃! c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L), y = ∑ a, smulC V L (c a) (x a)) ↔
      ∃! c : Fin n → A ⊗[ℚ_[l]] ↥(K0 L), ci y = ∑ a, Thick.sm V (Bst (PP l)) (c a) (ci (x a)) := by
    refine fun y => existsUnique_congr fun c => ?_
    simp only [← ci_sm, ← map_sum]
    exact (crisIncl_injective (PP l)).eq_iff.symm
  refine Iff.trans ⟨fun H u hu => ?_, fun H y hy => ?_⟩ (key.trans ⟨fun H y hy => ?_, fun H u hu => ?_⟩)
  · obtain ⟨y, hy, ey⟩ := (h2 u).1 hu
    have := (coord_iff α _ _).1 ((e y).1 (H y hy))
    rwa [ey, LinearEquiv.symm_apply_apply] at this
  · exact (e y).2 ((coord_iff α _ _).2 (H _ ((h2 _).2 ⟨y, hy, ((cm).apply_symm_apply _).symm⟩)))
  · exact (coord_iff α _ _).2 (H _ ((h1 _).2 (by rwa [LinearEquiv.apply_symm_apply])))
  · have := (coord_iff α _ _).1 (H _ ((h1 u).1 hu))
    rwa [LinearEquiv.symm_apply_apply] at this

omit [Module.Finite ℚ_[l] A] [FiniteDimensional ℚ_[l] V] in
/- English proof (translation)
Use `haveI := (supExt K K').2`. Set `L : FinExt l` to `⟨IntermediateField.normalClosure ℚ_[l] ↥(supExt K K').1 (Om l), inferInstance⟩`. Establish `h : (supExt K K').1 ≤ L.1` using `IntermediateField.le_normalClosure _`. Use `haveI : (GK L).Normal := by haveI : IsGalois ℚ_[l] (Om l) := {} haveI : IsGalois ℚ_[l] ↥L.1 := { to_normal := normalClosure.normal _ _ _ }`. Conclude with `(InfiniteGalois.normal_iff_isGalois L.1).2 inferInstance`.

Conclude with `⟨L, le_sup_left.trans h, le_sup_right.trans h, inferInstance⟩`.
-/
private theorem exists_gal (K K' : FinExt l) :
    ∃ L : FinExt l, K.1 ≤ L.1 ∧ K'.1 ≤ L.1 ∧ ((GK L).subgroupOf (GK K)).Normal := by
  haveI := (supExt K K').2
  let L : FinExt l := ⟨IntermediateField.normalClosure ℚ_[l] ↥(supExt K K').1 (Om l), inferInstance⟩
  have h : (supExt K K').1 ≤ L.1 := IntermediateField.le_normalClosure _
  haveI : (GK L).Normal := by
    haveI : IsGalois ℚ_[l] (Om l) := {}
    haveI : IsGalois ℚ_[l] ↥L.1 := { to_normal := normalClosure.normal _ _ _ }
    exact (InfiniteGalois.normal_iff_isGalois L.1).2 inferInstance
  exact ⟨L, le_sup_left.trans h, le_sup_right.trans h, inferInstance⟩

/- English proof (translation)
Establish `hM : ∀ (L : FinExt l) (x : Fin n → V ⊗[ℚ_[l]] Bcr l) (γ : ↥(GK K)) (M : Matrix (Fin n) (Fin n) (A ⊗[ℚ_[l]] ↥(K0 L))), (∀ b, actC (GK K).subtype ρ γ (x b) = ∑ a, smulC V L (M a b) (x a)) → (∀ b, stRep (PP l) (resCoef ℚ_[l] ρ) γ (ci (x b)) = ∑ a, Thick.sm V (Bst (PP l)) ((jU A L).t …`. Introduce `L x γ M H b`. Rewrite using `[st_ci, H, map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => (ci_sm L _ _).trans (sm_jU L _ _).symm`. Establish `hT : ∀ (L : FinExt l) (M : Matrix (Fin n) (Fin n) (A ⊗[ℚ_[l]] ↥(K0 L))) (s : A), ((jU A L).toRingHom.mapMatrix M).trace = s ⊗ₜ[ℚ_[l]] 1 ↔ M.trace = s ⊗ₜ[ℚ_[l]] 1`.

Introduce `L M s`. Rewrite using `[← (jU_inj L).eq_iff]`. Establish `e1 : ((jU A L).toRingHom.mapMatrix M).trace = jU A L M.trace` using `(AddMonoidHom.map_trace (jU A L).toRingHom _).symm`. Establish `e2 : jU A L (s ⊗ₜ[ℚ_[l]] 1) = s ⊗ₜ[ℚ_[l]] 1` using `by simp [jU]`. Rewrite using `[e1, e2]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨L, h, hn, hc, x, hx, hb, htr⟩`. Establish `hb'` using `(basis_iff h ρ hc x hx).1 hb`. Establish `hp : ∀ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V), ci y ∈ Dpst (PP l) (resCoef ℚ_[l] ρ)` using `fun y hy => (mem_Dpst _ _).2 ⟨L, fun g hg => (st_ci ρ g y).trans (congrArg _ ((Thick.mem_Dcr _ _ _).1 hy ⟨g, hg⟩))⟩`. Use `⟨⟨L, h, hc⟩, fun a => ci (x a), fun a => hp _ (hx a), hb', fun γ hγ M' hM' => ?_⟩` and prove the remaining obligations.

Use `choose M hM₀ using fun b => (hb _ (Thick.act_mem_Dcr h hn ρ γ (hx b))).exists`. Establish `e : M' = (jU A L).toRingHom.mapMatrix (Matrix.of fun a b => M b a)` using `by ext1 a b`. Conclude with `congrFun ((hb' _ (stRep_mem_Dpst _ _ γ _ (hp _ (hx b)))).unique (hM' b) (hM L x γ (Matrix.of fun a b => M b a) hM₀ b)) a`. Rewrite using `[e, hT]`. Conclude with `htr γ hγ _ hM₀`.

Introduce and unpack `⟨⟨L₁, h₁, hc₁⟩, x, hx, hb, htr⟩ choose F hF using fun a => (mem_Dpst _ _).1 (hx a) haveI := fun a => (F a).2`. Take `⟨L, h, hL, hn⟩` from `exists_gal K (supExt L₁ ⟨⨆ a, (F a).1, inferInstance⟩)`. Establish `hc : Crys L (ρ.comp (incl h) : Representation A ↥(GK L) V)` using `(Thick.res_facts L₁ L (le_sup_left.trans hL) (resCoef ℚ_[l] (ρ.comp (incl h₁) : Representation A ↥(GK L₁) V))).2.1 hc₁`. Take `⟨d, w, -, -, h2, h3⟩` from `exists_frame h ρ hc`. Establish `: ∀ a, ∃ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V), ci y = x a`.

Introduce `a`. Use `(h2 _).1 (h3 ((cm).symm (x a)) fun g hg => by` as an intermediate fact. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `hF a g (GK_le (K' := L) ((le_iSup (fun a => (F a).1) a).trans (le_sup_right.trans hL)) hg))`. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.

Use `choose y hy e using this`. Take `rfl : x = fun a => ci (y a)` from `funext fun a => (e a).symm`. Conclude with `⟨L, h, hn, hc, y, hy, (basis_iff h ρ hc y hy).2 hb, fun γ hγ M H => (hT L M _).1 (htr γ hγ _ (hM L y γ M H))⟩`.
-/
private theorem cov (K : FinExt l) (ρ : Representation A ↥(GK K) V) (n : ℕ) (t : ↥(GK K) → A) :
    (∃ (L : FinExt l) (h : K.1 ≤ L.1), CrysTypeOver K L h ρ n t) ↔ PotCr K ρ ∧ TypeSt K ρ n t := by
  have hM : ∀ (L : FinExt l) (x : Fin n → V ⊗[ℚ_[l]] Bcr l) (γ : ↥(GK K))
      (M : Matrix (Fin n) (Fin n) (A ⊗[ℚ_[l]] ↥(K0 L))),
      (∀ b, actC (GK K).subtype ρ γ (x b) = ∑ a, smulC V L (M a b) (x a)) →
      (∀ b, stRep (PP l) (resCoef ℚ_[l] ρ) γ (ci (x b)) =
        ∑ a, Thick.sm V (Bst (PP l)) ((jU A L).toRingHom.mapMatrix M a b) (ci (x a))) := by
    intro L x γ M H b
    rw [st_ci, H, map_sum]
    exact Finset.sum_congr rfl fun a _ => (ci_sm L _ _).trans (sm_jU L _ _).symm
  have hT : ∀ (L : FinExt l) (M : Matrix (Fin n) (Fin n) (A ⊗[ℚ_[l]] ↥(K0 L))) (s : A),
      ((jU A L).toRingHom.mapMatrix M).trace = s ⊗ₜ[ℚ_[l]] 1 ↔ M.trace = s ⊗ₜ[ℚ_[l]] 1 := by
    intro L M s
    rw [← (jU_inj L).eq_iff]
    have e1 : ((jU A L).toRingHom.mapMatrix M).trace = jU A L M.trace :=
      (AddMonoidHom.map_trace (jU A L).toRingHom _).symm
    have e2 : jU A L (s ⊗ₜ[ℚ_[l]] 1) = s ⊗ₜ[ℚ_[l]] 1 := by simp [jU]
    rw [e1, e2]
  constructor
  · rintro ⟨L, h, hn, hc, x, hx, hb, htr⟩
    have hb' := (basis_iff h ρ hc x hx).1 hb
    have hp : ∀ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V),
        ci y ∈ Dpst (PP l) (resCoef ℚ_[l] ρ) := fun y hy => (mem_Dpst _ _).2 ⟨L, fun g hg =>
      (st_ci ρ g y).trans (congrArg _ ((Thick.mem_Dcr _ _ _).1 hy ⟨g, hg⟩))⟩
    refine ⟨⟨L, h, hc⟩, fun a => ci (x a), fun a => hp _ (hx a), hb', fun γ hγ M' hM' => ?_⟩
    choose M hM₀ using fun b => (hb _ (Thick.act_mem_Dcr h hn ρ γ (hx b))).exists
    have e : M' = (jU A L).toRingHom.mapMatrix (Matrix.of fun a b => M b a) := by
      ext1 a b
      exact congrFun ((hb' _ (stRep_mem_Dpst _ _ γ _ (hp _ (hx b)))).unique (hM' b)
        (hM L x γ (Matrix.of fun a b => M b a) hM₀ b)) a
    rw [e, hT]
    exact htr γ hγ _ hM₀
  · rintro ⟨⟨L₁, h₁, hc₁⟩, x, hx, hb, htr⟩
    choose F hF using fun a => (mem_Dpst _ _).1 (hx a)
    haveI := fun a => (F a).2
    obtain ⟨L, h, hL, hn⟩ := exists_gal K (supExt L₁ ⟨⨆ a, (F a).1, inferInstance⟩)
    have hc : Crys L (ρ.comp (incl h) : Representation A ↥(GK L) V) :=
      (Thick.res_facts L₁ L (le_sup_left.trans hL)
        (resCoef ℚ_[l] (ρ.comp (incl h₁) : Representation A ↥(GK L₁) V))).2.1 hc₁
    obtain ⟨d, w, -, -, h2, h3⟩ := exists_frame h ρ hc
    have : ∀ a, ∃ y ∈ Dcr (GK L).subtype (ρ.comp (incl h) : Representation A ↥(GK L) V), ci y = x a := by
      intro a
      have := (h2 _).1 (h3 ((cm).symm (x a)) fun g hg => by
        rw [LinearEquiv.apply_symm_apply]
        exact hF a g (GK_le (K' := L) ((le_iSup (fun a => (F a).1) a).trans (le_sup_right.trans hL)) hg))
      rwa [LinearEquiv.apply_symm_apply] at this
    choose y hy e using this
    obtain rfl : x = fun a => ci (y a) := funext fun a => (e a).symm
    exact ⟨L, h, hn, hc, y, hy, (basis_iff h ρ hc y hy).2 hb, fun γ hγ M H =>
      (hT L M _).1 (htr γ hγ _ (hM L y γ M H))⟩

end Cov

end UpperTheory.V.Lit.TypeDual

end

open UpperTheory.V.Lit UpperTheory.V.Published

/- English proof (translation)
Introduce `l _ K B _ _ _ _ _ n ρ _ a t`. Conclude with `⟨TypeDual.potCr_dual K B n ρ (-a), (TypeDual.cov K _ n t).trans (and_congr_right fun _ => UpperTheory.type_dual_twist_iff l K B n ρ a t)⟩`.
-/
theorem UpperTheory.V.Lit.typeDual :
    ∀ (l : ℕ) [Fact l.Prime], TypeDual l := by
  intro l _ K B _ _ _ _ _ n ρ _ a t
  exact ⟨TypeDual.potCr_dual K B n ρ (-a),
    (TypeDual.cov K _ n t).trans (and_congr_right fun _ => UpperTheory.type_dual_twist_iff l K B n ρ a t)⟩
