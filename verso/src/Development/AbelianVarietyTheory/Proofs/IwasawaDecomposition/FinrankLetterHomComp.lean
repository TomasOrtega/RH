import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst.LetterDim

section General

variable {L U D : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* End L D)
  {F : Type} [Field F]

def letterHom (s : L →+* F) (τ : U →+* F) : Submodule F (D →+ F) where
  carrier := {f | (∀ a x, f (a • x) = s a * f x) ∧ ∀ c x, f (m c x) = τ c * f x}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro f g ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun a x => by simp [h1, h3, mul_add], fun a x => by simp [h2, h4, mul_add]⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨fun a x => by simp [h1, mul_left_comm], fun a x => by simp [h2, mul_left_comm]⟩

/- English proof (translation)
Set `e : Dual F (Letter m F τ) →ₗ[F] ↥(letterHom m (algebraMap L F) τ)` to `{ toFun := fun φ => ⟨AddMonoidHom.mk' (fun x => φ (letterMk m F τ x)) (fun x y => by rw [letterMk_add, map_add]), fun a x => by simp [letterMk_smul], fun c x => by simp [letterMk_mul]⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `(LinearEquiv.ofBijective e ⟨fun φ ψ h => ?_, fun f => ?_⟩).finrank_eq` and prove the remaining obligations. Conclude with `letter_hom_ext m F τ fun x => DFunLike.congr_fun (congrArg Subtype.val h) x`. Set `f1 : D →ₗ[L] F` to `{ toFun := f.1, map_add' := f.1.map_add, map_smul' := fun a x => by`. Rewrite using `[f.2.1, RingHom.id_apply, Algebra.smul_def] }`.

Set `f2 : F ⊗[L] D →ₗ[F] F` to `LinearMap.liftBaseChange F f1`. Establish `h2 : letterKer m F τ ≤ LinearMap.ker f2`. Use `iSup_le fun c => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.range_le_ker_iff]`. Use `AlgebraTensorModule.ext fun a x => ?_` and prove the remaining obligations.

Simplify using `[f2, f1, f.2.2, mul_left_comm]`. Use `⟨(letterKer m F τ).liftQ f2 h2, Subtype.ext (AddMonoidHom.ext fun x => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f2 (1 ⊗ₜ x) = _`. Simplify using `[f2, f1]`.
-/
theorem finrank_dual_letter [Algebra L F] (τ : U →+* F) :
    finrank F (Dual F (Letter m F τ)) = finrank F ↥(letterHom m (algebraMap L F) τ) := by
  let e : Dual F (Letter m F τ) →ₗ[F] ↥(letterHom m (algebraMap L F) τ) :=
    { toFun := fun φ => ⟨AddMonoidHom.mk' (fun x => φ (letterMk m F τ x))
          (fun x y => by rw [letterMk_add, map_add]),
        fun a x => by simp [letterMk_smul], fun c x => by simp [letterMk_mul]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine (LinearEquiv.ofBijective e ⟨fun φ ψ h => ?_, fun f => ?_⟩).finrank_eq
  · exact letter_hom_ext m F τ fun x => DFunLike.congr_fun (congrArg Subtype.val h) x
  · let f1 : D →ₗ[L] F :=
      { toFun := f.1, map_add' := f.1.map_add, map_smul' := fun a x => by
          rw [f.2.1, RingHom.id_apply, Algebra.smul_def] }
    let f2 : F ⊗[L] D →ₗ[F] F := LinearMap.liftBaseChange F f1
    have h2 : letterKer m F τ ≤ LinearMap.ker f2 := by
      refine iSup_le fun c => ?_
      rw [LinearMap.range_le_ker_iff]
      refine AlgebraTensorModule.ext fun a x => ?_
      simp [f2, f1, f.2.2, mul_left_comm]
    refine ⟨(letterKer m F τ).liftQ f2 h2, Subtype.ext (AddMonoidHom.ext fun x => ?_)⟩
    change f2 (1 ⊗ₜ x) = _
    simp [f2, f1]

/- English proof (translation)
Set `j : ↥(letterHom m s τ) ≃+ ↥(letterHom m s' τ')` to `{ toFun := fun f => ⟨g.toAddMonoidHom.comp f.1, fun a x => by simp [f.2.1, hs], fun a x => by simp [f.2.2, hτ]⟩ invFun := fun f => ⟨g.symm.toAddMonoidHom.comp f.1, fun a x => by simp [f.2.1, ← hs], fun a x => by simp [f.2.2, ← hτ]⟩ left_inv := fun f => Subtype.ext (AddMonoidHom.e …`. Rewrite using `[finrank, finrank, rank_eq_of_equiv_equiv g j g.bijective fun c f => Subtype.ext (AddMonoidHom.ext fun x => by simp [j])]`.
-/
theorem finrank_letterHom_comp {F' : Type} [Field F'] (g : F ≃+* F') (s : L →+* F) (τ : U →+* F)
    (s' : L →+* F') (τ' : U →+* F') (hs : ∀ a, g (s a) = s' a) (hτ : ∀ a, g (τ a) = τ' a) :
    finrank F ↥(letterHom m s τ) = finrank F' ↥(letterHom m s' τ') := by
  let j : ↥(letterHom m s τ) ≃+ ↥(letterHom m s' τ') :=
    { toFun := fun f => ⟨g.toAddMonoidHom.comp f.1, fun a x => by simp [f.2.1, hs],
        fun a x => by simp [f.2.2, hτ]⟩
      invFun := fun f => ⟨g.symm.toAddMonoidHom.comp f.1, fun a x => by simp [f.2.1, ← hs],
        fun a x => by simp [f.2.2, ← hτ]⟩
      left_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => by simp)
      right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => by simp)
      map_add' := fun f f' => Subtype.ext (AddMonoidHom.ext fun x => by simp) }
  rw [finrank, finrank, rank_eq_of_equiv_equiv g j g.bijective fun c f =>
    Subtype.ext (AddMonoidHom.ext fun x => by simp [j])]

/- English proof (translation)
Establish `h1 : ∀ c x, φ (m c x) = m (σ c) (φ x)` using `fun c x => LinearMap.congr_fun (hσ c) x`. Set `e` to `LinearEquiv.ofBijective φ hφ`. Establish `h2 : ∀ c x, e.symm (m (σ c) x) = m c (e.symm x)` using `fun c x => by`. Take `⟨x, rfl⟩` from `e.surjective x`. Rewrite using `[e.symm_apply_apply, e.symm_apply_eq]`.

Conclude with `(h1 c x).symm`. Set `j : ↥(letterHom m s τ) ≃ₗ[F] ↥(letterHom m s τ')` to `{ toFun := fun f => ⟨f.1.comp φ.toAddMonoidHom, fun a x => by simp [f.2.1], fun a x => by simp [h1, f.2.2, hτ]⟩ invFun := fun f => ⟨f.1.comp e.symm.toLinearMap.toAddMonoidHom, fun a x => by simp [f.2.1], fun a x => by`. Take `⟨a, rfl⟩` from `hσ' a`. Simplify using `[h2, f.2.2, hτ]⟩`. Use `left_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => congrArg f.1 (e.apply_symm_apply x))`.

Use `right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => congrArg f.1 (e.symm_apply_apply x))`. Use the proof step `map_add' := fun _ _ => rfl`. Use the proof step `map_smul' := fun _ _ => rfl }`. Conclude with `j.finrank_eq`.
-/
theorem finrank_letterHom_frob (φ : End L D) (hφ : Function.Bijective φ) (σ : U → U)
    (hσ : ∀ c, φ * m c = m (σ c) * φ) (hσ' : Function.Surjective σ) (s : L →+* F) (τ τ' : U →+* F)
    (hτ : ∀ c, τ' c = τ (σ c)) :
    finrank F ↥(letterHom m s τ) = finrank F ↥(letterHom m s τ') := by
  have h1 : ∀ c x, φ (m c x) = m (σ c) (φ x) := fun c x => LinearMap.congr_fun (hσ c) x
  let e := LinearEquiv.ofBijective φ hφ
  have h2 : ∀ c x, e.symm (m (σ c) x) = m c (e.symm x) := fun c x => by
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply, e.symm_apply_eq]
    exact (h1 c x).symm
  let j : ↥(letterHom m s τ) ≃ₗ[F] ↥(letterHom m s τ') :=
    { toFun := fun f => ⟨f.1.comp φ.toAddMonoidHom, fun a x => by simp [f.2.1],
        fun a x => by simp [h1, f.2.2, hτ]⟩
      invFun := fun f => ⟨f.1.comp e.symm.toLinearMap.toAddMonoidHom, fun a x => by simp [f.2.1],
        fun a x => by
          obtain ⟨a, rfl⟩ := hσ' a
          simp [h2, f.2.2, hτ]⟩
      left_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => congrArg f.1 (e.apply_symm_apply x))
      right_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => congrArg f.1 (e.symm_apply_apply x))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact j.finrank_eq

/- English proof (translation)
Take `⟨α, hα⟩` from `Field.exists_primitive_element k L`. Establish `hint : IsIntegral k α` using `Algebra.IsIntegral.isIntegral α`. Establish `hpoly : ∀ a : L, ∃ q : k[X], a = aeval α q` using `fun a => by`. Establish `: a ∈ (IntermediateField.adjoin k {α}).toSubalgebra` using `by rw [hα]; trivial`. Rewrite `this` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨q, hq⟩` from `this`. Conclude with `⟨q, hq.symm⟩`. Establish `hev : ∀ q : k[X], r (aeval α q) = aeval (r α) (q.map (algebraMap k F))` using `fun q => by`. Rewrite using `[aeval_def, aeval_def, hom_eval₂, eval₂_map]`. Use `congr 1`.

Conclude with `RingHom.ext hr`. Establish `hE : ∀ s : L →ₐ[k] F, (⨅ a, (r a).eigenspace (s a)) = (r α).eigenspace (s α)` using `fun s => by`. Use `le_antisymm (iInf_le _ α) (le_iInf fun a x hx => ?_)` and prove the remaining obligations. Take `⟨q, rfl⟩` from `hpoly a`. Rewrite `hx`, the goal using `[End.mem_eigenspace_iff]`.

Rewrite using `[hev, End.aeval_apply_of_mem_apply_eq_smul hx, eval_map_algebraMap, aeval_algHom_apply]`. Establish `hinj : Function.Injective fun s : L →ₐ[k] F => s α` using `fun s t h => AlgHom.ext fun a => by`. Take `⟨q, rfl⟩` from `hpoly a`. Rewrite using `[← aeval_algHom_apply, ← aeval_algHom_apply, show s α = t α from h]`. Establish `h0 : aeval (r α) ((minpoly k α).map (algebraMap k F)) = 0`.

Rewrite using `[← hev, minpoly.aeval, map_zero]`. Establish `hss : (r α).IsSemisimple` using `End.isSemisimple_of_squarefree_aeval_eq_zero (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k α)).squarefree h0`. Establish `hI : DirectSum.IsInternal fun s : L →ₐ[k] F => (r α).eigenspace (s α)`. Use `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ((r α).eigenspaces_iSupIndep.comp hinj) (eq_top_iff.mpr ?_)` and prove the remaining obligations. Rewrite using `[← hss.iSup_eigenspace_eq_top]`.

Use `iSup_le fun μ x hx => ?_` and prove the remaining obligations. Break down `eq_or_ne x 0 with rfl | hx0` into its components or cases. Conclude with `zero_mem _`. Establish `h1` using `End.aeval_apply_of_mem_apply_eq_smul (p := (minpoly k α).map (algebraMap k F)) (End.mem_eigenspace_iff.mp hx)`. Rewrite `h1` using `[h0, LinearMap.zero_apply, eq_comm, smul_eq_zero_iff_left hx0, eval_map_algebraMap]`.

Establish `h2 : μ ∈ Set.range fun s : L →ₐ[k] F => s α`. Rewrite using `[Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly F α, mem_rootSet]`. Conclude with `⟨minpoly.ne_zero hint, h1⟩`. Take `⟨s, rfl⟩` from `h2`. Conclude with `Submodule.mem_iSup_of_mem s hx`.

Rewrite using `[Finset.sum_congr rfl fun s _ => by rw [hE s], ← (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hI).finrank_eq, finrank_directSum]`.
-/
theorem sum_finrank_eigen {k : Type} [Field k] [Algebra k L] [Algebra k F] [IsAlgClosed F]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {W : Type} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (r : L →+* End F W)
    (hr : ∀ c : k, r (algebraMap k L c) = algebraMap F (End F W) (algebraMap k F c)) :
    ∑ s : L →ₐ[k] F, finrank F ↥(⨅ a, (r a).eigenspace (s a)) = finrank F W := by
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hpoly : ∀ a : L, ∃ q : k[X], a = aeval α q := fun a => by
    have : a ∈ (IntermediateField.adjoin k {α}).toSubalgebra := by rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at this
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq.symm⟩
  have hev : ∀ q : k[X], r (aeval α q) = aeval (r α) (q.map (algebraMap k F)) := fun q => by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    exact RingHom.ext hr
  have hE : ∀ s : L →ₐ[k] F, (⨅ a, (r a).eigenspace (s a)) = (r α).eigenspace (s α) := fun s => by
    refine le_antisymm (iInf_le _ α) (le_iInf fun a x hx => ?_)
    obtain ⟨q, rfl⟩ := hpoly a
    rw [End.mem_eigenspace_iff] at hx ⊢
    rw [hev, End.aeval_apply_of_mem_apply_eq_smul hx, eval_map_algebraMap, aeval_algHom_apply]
  have hinj : Function.Injective fun s : L →ₐ[k] F => s α := fun s t h => AlgHom.ext fun a => by
    obtain ⟨q, rfl⟩ := hpoly a
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, show s α = t α from h]
  have h0 : aeval (r α) ((minpoly k α).map (algebraMap k F)) = 0 := by
    rw [← hev, minpoly.aeval, map_zero]
  have hss : (r α).IsSemisimple := End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable k α)).squarefree h0
  have hI : DirectSum.IsInternal fun s : L →ₐ[k] F => (r α).eigenspace (s α) := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((r α).eigenspaces_iSupIndep.comp hinj) (eq_top_iff.mpr ?_)
    rw [← hss.iSup_eigenspace_eq_top]
    refine iSup_le fun μ x hx => ?_
    rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem _
    have h1 := End.aeval_apply_of_mem_apply_eq_smul (p := (minpoly k α).map (algebraMap k F))
      (End.mem_eigenspace_iff.mp hx)
    rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero_iff_left hx0, eval_map_algebraMap] at h1
    have h2 : μ ∈ Set.range fun s : L →ₐ[k] F => s α := by
      rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly F α, mem_rootSet]
      exact ⟨minpoly.ne_zero hint, h1⟩
    obtain ⟨s, rfl⟩ := h2
    exact Submodule.mem_iSup_of_mem s hx
  rw [Finset.sum_congr rfl fun s _ => by rw [hE s],
    ← (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hI).finrank_eq, finrank_directSum]

/- English proof (translation)
Set `sm : L → D →ₗ[U] D` to `fun a => { toFun := fun x => a • x, map_add' := smul_add a map_smul' := fun c x => by rw [hm, RingHom.id_apply, hm, map_smul] }`. Set `r : L →+* End F (D →ₗ[U] F)` to `{ toFun := fun a => { toFun := fun f => f ∘ₗ sm a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } map_one' := by ext f x; simp [sm] map_mul' := fun a b => by ext f x; simp [sm, smul_smul, mul_comm] map_zero' := by ext f x; simp [sm] map_add' := fun a b => by ext f x; s …`. Establish `hr : ∀ a f x, r a f x = f (a • x)` using `fun _ _ _ => rfl`. Establish `h1` using `sum_finrank_eigen (k := k) r fun c => by`. Use extensionality with `f x`.

Rewrite using `[hr, ← hk, ← hm, map_smul, Module.algebraMap_end_apply, LinearMap.smul_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, smul_eq_mul]`. Rewrite `h1` using `[finrank_linearMap, finrank_self, mul_one]`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `hmem : ∀ f : D →ₗ[U] F, f ∈ (⨅ a, (r a).eigenspace (s a)) ↔ ∀ a x, f (a • x) = s a * f x` using `fun f => by`.

Simplify using `only [Submodule.mem_iInf, End.mem_eigenspace_iff, LinearMap.ext_iff, hr, LinearMap.smul_apply, smul_eq_mul]`. Set `j : ↥(letterHom m (s : L →+* F) (algebraMap U F)) ≃ₗ[F] ↥(⨅ a, (r a).eigenspace (s a))` to `{ toFun := fun f => ⟨{ toFun := f.1, map_add' := f.1.map_add map_smul' := fun c x => by rw [hm, f.2.2, RingHom.id_apply, Algebra.smul_def] }, (hmem _).mpr f.2.1⟩ invFun := fun f => ⟨f.1.toAddMonoidHom, (hmem _).mp f.2, fun c x => by`. Rewrite using `[← hm, ← Algebra.smul_def]`. Conclude with `f.1.map_smul c x⟩`. Use `left_inv := fun _ => rfl`.

Use `right_inv := fun _ => rfl`. Use the proof step `map_add' := fun _ _ => rfl`. Use the proof step `map_smul' := fun _ _ => rfl }`. Conclude with `j.finrank_eq`.
-/
theorem sum_finrank_letterHom {k : Type} [Field k] [Algebra k L] [Algebra k U] [Algebra k F] [Algebra U F]
    [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [Module U D] [FiniteDimensional U D] (hm : ∀ (c : U) (x : D), c • x = m c x)
    (hk : ∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) :
    ∑ s : L →ₐ[k] F, finrank F ↥(letterHom m (s : L →+* F) (algebraMap U F)) = finrank U D := by
  let sm : L → D →ₗ[U] D := fun a =>
    { toFun := fun x => a • x, map_add' := smul_add a
      map_smul' := fun c x => by rw [hm, RingHom.id_apply, hm, map_smul] }
  let r : L →+* End F (D →ₗ[U] F) :=
    { toFun := fun a =>
        { toFun := fun f => f ∘ₗ sm a, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp [sm]
      map_mul' := fun a b => by ext f x; simp [sm, smul_smul, mul_comm]
      map_zero' := by ext f x; simp [sm]
      map_add' := fun a b => by ext f x; simp [sm, add_smul] }
  have hr : ∀ a f x, r a f x = f (a • x) := fun _ _ _ => rfl
  have h1 := sum_finrank_eigen (k := k) r fun c => by
    ext f x
    rw [hr, ← hk, ← hm, map_smul, Module.algebraMap_end_apply, LinearMap.smul_apply, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply, smul_eq_mul]
  rw [finrank_linearMap, finrank_self, mul_one] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hmem : ∀ f : D →ₗ[U] F, f ∈ (⨅ a, (r a).eigenspace (s a)) ↔ ∀ a x, f (a • x) = s a * f x := fun f => by
    simp only [Submodule.mem_iInf, End.mem_eigenspace_iff, LinearMap.ext_iff, hr, LinearMap.smul_apply,
      smul_eq_mul]
  let j : ↥(letterHom m (s : L →+* F) (algebraMap U F)) ≃ₗ[F] ↥(⨅ a, (r a).eigenspace (s a)) :=
    { toFun := fun f =>
        ⟨{ toFun := f.1, map_add' := f.1.map_add
           map_smul' := fun c x => by rw [hm, f.2.2, RingHom.id_apply, Algebra.smul_def] },
         (hmem _).mpr f.2.1⟩
      invFun := fun f => ⟨f.1.toAddMonoidHom, (hmem _).mp f.2, fun c x => by
        rw [← hm, ← Algebra.smul_def]; exact f.1.map_smul c x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact j.finrank_eq

end General

section Local

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `: IsGalois ℚ_[l] (Om l)` using `{}`. Set `S : Subgroup (GQ l)` to `{ carrier := {g | ∀ s, d ((g : Om l →ₐ[ℚ_[l]] Om l).comp s) = d s} one_mem' := fun s => rfl mul_mem' := fun {a b} ha hb s => (ha ((b : Om l →ₐ[ℚ_[l]] Om l).comp s)).trans (hb s) inv_mem' := fun {a} ha s => by`. Rewrite using `[← ha]`. Use `congr 1`. Use extensionality with `x`.

Simplify using `}`. Establish `hN : (IntermediateField.normalClosure ℚ_[l] L (Om l)).fixingSubgroup ≤ S` using `fun g hg s => by`. Use `congr 1`. Use extensionality with `x`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ (s.fieldRange_le_normalClosure ⟨x, rfl⟩)`.

Establish `hopen : IsOpen (S : Set (GQ l))` using `Subgroup.isOpen_mono hN (IntermediateField.fixingSubgroup_isOpen _)`. Establish `h3` using `InfiniteGalois.fixingSubgroup_fixedField ⟨S, S.isClosed_of_isOpen hopen⟩`. Establish `h4 : IntermediateField.fixedField S = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Establish `hK : x ∈ MaximalUnramifiedExtension l`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]`. Conclude with `fun f hf => hx f (h1 f fun c => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hf _ c.2)`. Take `⟨g, hg⟩` from `GlobalTheory.MemLoc.FrobLaws.exists_ext (frobUr l)`.

Take `⟨c, hc⟩` from `(GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 ⟨x, hK⟩ (Subtype.ext (by rw [← hg]; exact hx g (h2 g hg)))`. Rewrite using `[IntermediateField.mem_bot]`. Conclude with `⟨c, congrArg Subtype.val hc⟩`. Establish `h5 : S = ⊤`. Establish `: (IntermediateField.fixedField S).fixingSubgroup = S` using `h3`.

Rewrite using `[← this, h4, IntermediateField.fixingSubgroup_bot]`. Take `⟨f, hf⟩` from `IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ_[l]) (L := ↥s.fieldRange) (M := Om l) (E := Om l) (t.comp (s.equivFieldRange.symm : _ →ₐ[ℚ_[l]] _))`. Establish `hg : AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f) ∈ S` using `h5 ▸ Subgroup.mem_top _`. Rewrite using `[← hg s]`. Use `congr 1`.

Use extensionality with `x`. Use `AlgHom.congr_fun hf (s.equivFieldRange x)` as an intermediate fact. Conclude with `this.trans (congrArg t (s.equivFieldRange.symm_apply_apply x))`.
-/
theorem const_of_invariant {L : Type} [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (d : (L →ₐ[ℚ_[l]] Om l) → ℕ)
    (h1 : ∀ g : GQ l, (∀ c : ↥(MaximalUnramifiedExtension l), g c = c) → ∀ s, d ((g : Om l →ₐ[ℚ_[l]] Om l).comp s) = d s)
    (h2 : ∀ g : GQ l, (∀ c : ↥(MaximalUnramifiedExtension l), g c = frobUr l c) →
      ∀ s, d ((g : Om l →ₐ[ℚ_[l]] Om l).comp s) = d s) (s t : L →ₐ[ℚ_[l]] Om l) : d s = d t := by
  have : IsGalois ℚ_[l] (Om l) := {}
  let S : Subgroup (GQ l) :=
    { carrier := {g | ∀ s, d ((g : Om l →ₐ[ℚ_[l]] Om l).comp s) = d s}
      one_mem' := fun s => rfl
      mul_mem' := fun {a b} ha hb s => (ha ((b : Om l →ₐ[ℚ_[l]] Om l).comp s)).trans (hb s)
      inv_mem' := fun {a} ha s => by
        rw [← ha]
        congr 1
        ext x
        simp }
  have hN : (IntermediateField.normalClosure ℚ_[l] L (Om l)).fixingSubgroup ≤ S := fun g hg s => by
    congr 1
    ext x
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ (s.fieldRange_le_normalClosure ⟨x, rfl⟩)
  have hopen : IsOpen (S : Set (GQ l)) :=
    Subgroup.isOpen_mono hN (IntermediateField.fixingSubgroup_isOpen _)
  have h3 := InfiniteGalois.fixingSubgroup_fixedField ⟨S, S.isClosed_of_isOpen hopen⟩
  have h4 : IntermediateField.fixedField S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hK : x ∈ MaximalUnramifiedExtension l := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (h1 f fun c => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hf _ c.2)
    obtain ⟨g, hg⟩ := GlobalTheory.MemLoc.FrobLaws.exists_ext (frobUr l)
    obtain ⟨c, hc⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 ⟨x, hK⟩
      (Subtype.ext (by rw [← hg]; exact hx g (h2 g hg)))
    rw [IntermediateField.mem_bot]
    exact ⟨c, congrArg Subtype.val hc⟩
  have h5 : S = ⊤ := by
    have : (IntermediateField.fixedField S).fixingSubgroup = S := h3
    rw [← this, h4, IntermediateField.fixingSubgroup_bot]
  obtain ⟨f, hf⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := ℚ_[l]) (L := ↥s.fieldRange) (M := Om l) (E := Om l) (t.comp (s.equivFieldRange.symm : _ →ₐ[ℚ_[l]] _))
  have hg : AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f) ∈ S := h5 ▸ Subgroup.mem_top _
  rw [← hg s]
  congr 1
  ext x
  have := AlgHom.congr_fun hf (s.equivFieldRange x)
  exact this.trans (congrArg t (s.equivFieldRange.symm_apply_apply x))

end Local

/- English proof (translation)
Use `LL.2` as an intermediate fact. Establish `: FiniteDimensional ℚ_[l] V` using `Module.Finite.trans ↥LL.1 V`. Establish `hfin` using `hV.finite`. Set `d : (↥LL.1 →ₐ[ℚ_[l]] Om l) → ℕ` to `fun s => finrank (Om l) ↥(letterHom (mulD P ρ) (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)))`. Establish `hd : ∀ s t, d s = d t` using `const_of_invariant d (fun g hg s => (finrank_letterHom_comp (mulD P ρ) g.toRingEquiv _ _ _ _ (fun _ => rfl) hg).symm) (fun g hg s => (finrank_letterHom_frob (mulD P ρ) (phiD P ρ) phiD_bijective (frobUr l) (phiD_mulD P ρ) frobUr_bijective.2 _ _ ((algebraMap ↥(MaximalUnramifiedExte …`.

Establish `hsum : ∑ s, d s = finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)`. Use `letI : Module ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := inferInstanceAs (Module ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))`. Use `haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := hfin`. Use `sum_finrank_letterHom (k := ℚ_[l]) (mulD P ρ) (fun _ _ => rfl) fun c x => Subtype.ext (by`. Establish `: mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = algebraMap ℚ_[l] ↥LL.1 c • LinearMap.id` using `end_ext P fun v b => by`.

Rewrite using `[mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul, LinearMap.smul_apply, algebraMap_smul, LinearMap.id_apply]`. Rewrite using `[coe_mulD, this]`. Use the proof step `rfl)`. Establish `h1 : finrank ℂ (WDSpace P ι ρ) = d LL.1.val`. Use `letI := algC ι LL`.

Rewrite using `[← Subspace.dual_finrank_eq, finrank_dual_letter]`. Conclude with `(finrank_letterHom_comp (mulD P ρ) ι _ _ _ _ (fun _ => rfl) (fun _ => rfl)).symm`. Rewrite `hsum` using `[Finset.sum_congr rfl fun s _ => hd s LL.1.val, Finset.sum_const, Finset.card_univ, AlgHom.card, ((isPst_iff P ρ).mp hV).2, ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, smul_eq_mul]`. Rewrite using `[h1]`. Conclude with `Nat.eq_of_mul_eq_mul_left finrank_pos hsum`.
-/
theorem finrank_wdSpace (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l) (V : Type)
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (hV : IsPst P ρ) :
    finrank ℂ (WDSpace P ι ρ) = finrank ↥LL.1 V := by
  have := LL.2
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  have hfin := hV.finite
  let d : (↥LL.1 →ₐ[ℚ_[l]] Om l) → ℕ := fun s =>
    finrank (Om l) ↥(letterHom (mulD P ρ) (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)))
  have hd : ∀ s t, d s = d t := const_of_invariant d
    (fun g hg s => (finrank_letterHom_comp (mulD P ρ) g.toRingEquiv _ _ _ _ (fun _ => rfl) hg).symm)
    (fun g hg s => (finrank_letterHom_frob (mulD P ρ) (phiD P ρ) phiD_bijective (frobUr l) (phiD_mulD P ρ)
      frobUr_bijective.2 _ _ ((algebraMap ↥(MaximalUnramifiedExtension l) (Om l)).comp (frobUr l : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l)))
      (fun _ => rfl)).trans
      (finrank_letterHom_comp (mulD P ρ) g.toRingEquiv _ _ _ _ (fun _ => rfl) hg).symm)
  have hsum : ∑ s, d s = finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    letI : Module ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := inferInstanceAs (Module ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))
    haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := hfin
    sum_finrank_letterHom (k := ℚ_[l]) (mulD P ρ) (fun _ _ => rfl) fun c x => Subtype.ext (by
      have : mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = algebraMap ℚ_[l] ↥LL.1 c • LinearMap.id :=
        end_ext P fun v b => by
          rw [mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul,
            LinearMap.smul_apply, algebraMap_smul, LinearMap.id_apply]
      rw [coe_mulD, this]
      rfl)
  have h1 : finrank ℂ (WDSpace P ι ρ) = d LL.1.val := by
    letI := algC ι LL
    rw [← Subspace.dual_finrank_eq, finrank_dual_letter]
    exact (finrank_letterHom_comp (mulD P ρ) ι _ _ _ _ (fun _ => rfl) (fun _ => rfl)).symm
  rw [Finset.sum_congr rfl fun s _ => hd s LL.1.val, Finset.sum_const, Finset.card_univ, AlgHom.card,
    ((isPst_iff P ρ).mp hV).2, ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V, smul_eq_mul] at hsum
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_left finrank_pos hsum

end GlobalTheory.Pst.LetterDim
