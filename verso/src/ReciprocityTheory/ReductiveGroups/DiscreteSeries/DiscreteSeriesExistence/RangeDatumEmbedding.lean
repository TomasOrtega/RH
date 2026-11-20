import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/- English proof (translation)
Establish `hEz : E z ∈ S`. Rewrite using `[← hE.2.2]`. Conclude with `LinearMap.mem_range_self _ z`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : E z ∈ LinearMap.range (j : V →ₗ[ℂ] H) := by`. Rewrite using `[hS]`.

Conclude with `hEz`. Establish `hw' : j w = E z` using `hw`. Establish `hfix : ∀ y ∈ S, E y = y`. Introduce `y hy`. Rewrite `hy` using `[← hE.2.2]`.

Take `⟨u, rfl⟩` from `hy`. Use `show E (E u) = E u`. Rewrite using `[← ContinuousLinearMap.comp_apply, hE.1]`. Establish `hinner : ∀ v v' : V, @inner ℂ H _ (j v) (j v') = @inner ℂ V _ v v'`. Introduce `v v'`.

Set `J : V →ₗᵢ[ℂ] H` to `{ toLinearMap := (j : V →ₗ[ℂ] H), norm_map' := hj }`. Conclude with `J.inner_map_map v v'`. Establish `hadj : ContinuousLinearMap.adjoint j z = w`. Use `ext_inner_right ℂ fun v => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_left]`.

Establish `hjv : j v ∈ S`. Rewrite using `[← hS]`. Conclude with `LinearMap.mem_range_self _ v`. Rewrite using `[← hfix _ hjv, ← hE.2.1, ← hw', hinner]`. Conclude with `⟨w, hw', le_of_eq (by rw [hadj, ← hw', hj])⟩`.
-/
theorem anyf_projE_le (j : V →L[ℂ] H) (hj : ∀ v, ‖j v‖ = ‖v‖) (E : H →L[ℂ] H) (S : Submodule ℂ H)
    (hE : Formalism.MainNotions.S.IsOrthProjOnto E S) (hS : LinearMap.range (j : V →ₗ[ℂ] H) = S) (z : H) :
    ∃ w : V, j w = E z ∧ ‖E z‖ ≤ ‖ContinuousLinearMap.adjoint j z‖ := by
  have hEz : E z ∈ S := by
    rw [← hE.2.2]
    exact LinearMap.mem_range_self _ z
  obtain ⟨w, hw⟩ : E z ∈ LinearMap.range (j : V →ₗ[ℂ] H) := by
    rw [hS]
    exact hEz
  have hw' : j w = E z := hw
  have hfix : ∀ y ∈ S, E y = y := by
    intro y hy
    rw [← hE.2.2] at hy
    obtain ⟨u, rfl⟩ := hy
    show E (E u) = E u
    rw [← ContinuousLinearMap.comp_apply, hE.1]
  have hinner : ∀ v v' : V, @inner ℂ H _ (j v) (j v') = @inner ℂ V _ v v' := by
    intro v v'
    let J : V →ₗᵢ[ℂ] H := { toLinearMap := (j : V →ₗ[ℂ] H), norm_map' := hj }
    exact J.inner_map_map v v'
  have hadj : ContinuousLinearMap.adjoint j z = w := by
    refine ext_inner_right ℂ fun v => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hjv : j v ∈ S := by
      rw [← hS]
      exact LinearMap.mem_range_self _ v
    rw [← hfix _ hjv, ← hE.2.1, ← hw', hinner]
  exact ⟨w, hw', le_of_eq (by rw [hadj, ← hw', hj])⟩

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_` and prove the remaining obligations. Take `⟨w, hw, hle⟩` from `anyf_projE_le j hj E S hE hS z`. Establish `hjn : ‖j‖ ≤ 1` using `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [hj]`. Establish `hwz : ‖w‖ ≤ ‖z‖`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨w', -, hle'⟩` from `anyf_projE_le j hj E S hE hS (A (j w))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hw]`. Use `_ ≤ ‖ContinuousLinearMap.adjoint j (A (j w))‖ := hle'`. Use `_ = ‖((ContinuousLinearMap.adjoint j).comp (A.comp j)) w‖ := rfl`.

Use `_ ≤ ‖(ContinuousLinearMap.adjoint j).comp (A.comp j)‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _`. Use `_ ≤ ‖(ContinuousLinearMap.adjoint j).comp (A.comp j)‖ * ‖z‖ := by gcongr`.
-/
theorem anyf_comp_norm_le (j : V →L[ℂ] H) (hj : ∀ v, ‖j v‖ = ‖v‖) (E A : H →L[ℂ] H) (S : Submodule ℂ H)
    (hE : Formalism.MainNotions.S.IsOrthProjOnto E S) (hS : LinearMap.range (j : V →ₗ[ℂ] H) = S) :
    ‖E.comp (A.comp E)‖ ≤ ‖(ContinuousLinearMap.adjoint j).comp (A.comp j)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  obtain ⟨w, hw, hle⟩ := anyf_projE_le j hj E S hE hS z
  have hjn : ‖j‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [hj]
  have hwz : ‖w‖ ≤ ‖z‖ := by
    calc ‖w‖ = ‖E z‖ := by rw [← hw, hj]
      _ ≤ ‖ContinuousLinearMap.adjoint j z‖ := hle
      _ ≤ ‖ContinuousLinearMap.adjoint j‖ * ‖z‖ := (ContinuousLinearMap.adjoint j).le_opNorm z
      _ = ‖j‖ * ‖z‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ 1 * ‖z‖ := by gcongr
      _ = ‖z‖ := one_mul _
  obtain ⟨w', -, hle'⟩ := anyf_projE_le j hj E S hE hS (A (j w))
  calc ‖(E.comp (A.comp E)) z‖ = ‖E (A (j w))‖ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hw]
    _ ≤ ‖ContinuousLinearMap.adjoint j (A (j w))‖ := hle'
    _ = ‖((ContinuousLinearMap.adjoint j).comp (A.comp j)) w‖ := rfl
    _ ≤ ‖(ContinuousLinearMap.adjoint j).comp (A.comp j)‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(ContinuousLinearMap.adjoint j).comp (A.comp j)‖ * ‖z‖ := by gcongr

end Gen

section Main

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def datumEmbedding (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] Hlam ε Ψ v₀ :=
  (ffaJ hP v₀).codRestrict (Hlam ε Ψ v₀) (fun v => datumEmbedding_mem_Hlam hP v)

/- English proof (translation)
Establish `hspan : Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀)) = LinearMap.range (ffaJ hP v₀)`. Conclude with `Submodule.span_eq (LinearMap.range (ffaJ hP v₀))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩`.

Establish `hs : uniformisationL2 ε Ψ v₀ v ∈ smD ε (rreg ε)`. Conclude with `datumEmbedding_mem_smooth hP v₀ v`. Simplify using `only [lowKSubLam, Submodule.mem_comap, Submodule.mem_map]`. Use `⟨⟨uniformisationL2 ε Ψ v₀ v, hs⟩, ?_, rfl⟩` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨v, rfl⟩`.

Introduce `hx`. Simplify using `only [lowKSubLam, Submodule.mem_comap, Submodule.mem_map] at hx`. Take `⟨y, hy, hyx⟩` from `hx`. Establish `hy' : (y : L2 ε) ∈ LinearMap.range (ffaJ hP v₀)` using `hspan ▸ hy`. Take `⟨v, hv⟩` from `hy'`.

Conclude with `⟨v, Subtype.ext (hv.trans hyx)⟩`.
-/
theorem range_datumEmbedding (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    LinearMap.range (datumEmbedding hP v₀) = lowKSubLam ε Ψ v₀ := by
  have hspan : Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀)) = LinearMap.range (ffaJ hP v₀) := by
    exact Submodule.span_eq (LinearMap.range (ffaJ hP v₀))
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    have hs : uniformisationL2 ε Ψ v₀ v ∈ smD ε (rreg ε) := by
      exact datumEmbedding_mem_smooth hP v₀ v
    simp only [lowKSubLam, Submodule.mem_comap, Submodule.mem_map]
    refine ⟨⟨uniformisationL2 ε Ψ v₀ v, hs⟩, ?_, rfl⟩
    exact Submodule.subset_span ⟨v, rfl⟩
  · intro hx
    simp only [lowKSubLam, Submodule.mem_comap, Submodule.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hy' : (y : L2 ε) ∈ LinearMap.range (ffaJ hP v₀) := hspan ▸ hy
    obtain ⟨v, hv⟩ := hy'
    exact ⟨v, Subtype.ext (hv.trans hyx)⟩

/- English proof (translation)
Establish `hw : T.w ≠ 0` using `fun h0 => by`. Establish `h1` using `T.w_norm`. Rewrite `h1` using `[h0, norm_zero]`. Conclude with `zero_ne_one h1`. Take `⟨U, hU⟩` from `equiv_sigLam_of_isDS hDS hgap hP hw`.

Establish `hc0` using `datumEmbedding_highest_ne_zero hgap hP hw`. Use `set c : ℝ := ‖uniformisationL2 ε Ψ T.w T.w‖ with hc`. Establish `hcne : (c : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc0)`. Set `jl : T.V →ₗ[ℂ] H` to `((c : ℂ)⁻¹) • (U.toLinearEquiv.toLinearMap ∘ₗ datumEmbedding hP T.w)`. Set `j : T.V →L[ℂ] H` to `LinearMap.toContinuousLinearMap jl`.

Establish `hjv : ∀ v, j v = ((c : ℂ)⁻¹) • U (datumEmbedding hP T.w v)` using `fun v => rfl`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε` using `by show inUJ ε 1`. Simplify using `[inUJ]`. Establish `hkey : ∀ g ∈ UJset ε, ∀ v v', inner ℂ (j v') (σ g (j v)) = inner ℂ v' (Ψ g v)`. Introduce `g hg v v'`.

Rewrite using `[hjv, hjv, map_smul, ← hU g hg, inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map]`. Establish `e` using `formulaF_sigLam hgap hP hw hg v v'`. Rewrite using `[show datumEmbedding hP T.w v = (⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_Hlam hP v⟩ : Hlam ε Ψ T.w) from rfl, show datumEmbedding hP T.w v' = (⟨uniformisationL2 ε Ψ T.w v', datumEmbedding_mem_Hlam hP v'⟩ : Hlam ε Ψ T.w) from rfl, e]`. Rewrite using `[map_inv₀, Complex.conj_ofReal]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hc]`. Establish `hiso : ∀ v, ‖j v‖ = ‖v‖`. Introduce `v`. Establish `e` using `hkey 1 h1 v v`.

Rewrite `e` using `[hDS.2.2.1.1.1, hP.2.1]`. Simplify using `only [ContinuousLinearMap.one_apply] at e`. Establish `e2 : ‖j v‖ ^ 2 = ‖v‖ ^ 2`. Rewrite using `[← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, e]`. Conclude with `(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e2`.

Establish `hK : ∀ (k : S7.KG ε) v, σ (S7.toMK k) (j v) = j (T.op k v)`. Introduce `k v`. Rewrite using `[hjv, hjv, map_smul, ← hU _ (ffa_toMK_mem k)]`. Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[sigLam_coe hgap hP hw (ffa_toMK_mem k)]`. Conclude with `rightRegular_datumEmbedding hP T.w v k`. Establish `hrange : LinearMap.range (j : T.V →ₗ[ℂ] H) = (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap` using `by show LinearMap.range jl = _`. Rewrite using `[LinearMap.range_smul _ _ (inv_ne_zero hcne), LinearMap.range_comp, range_datumEmbedding]`. Establish `hintU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.toLinearMap (sigLam ε Ψ T.w g x) = σ g (U.toLinearEquiv.toLinearMap x)`.

Introduce `g hg x`. Rewrite `hg` using `[mir_Kset_eq]`. Conclude with `hU g (UnitaryGroupOfForm.K_mem_UJ hg) x`. Establish `hintS : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.symm.toLinearMap (σ g x) = sigLam ε Ψ T.w g (U.toLinearEquiv.symm.toLinearMap x)`. Introduce `g hg x`.

Apply `U.injective` to reduce the goal to its premises. Establish `e` using `hintU g hg (U.toLinearEquiv.symm x)`. Simplify using `only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at e ⊢`. Rewrite using `[e]`. Simplify using the standard rewrite rules.

Establish `hlow : Formalism.MainNotions.S.lowKSub ε lam σ = (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap`. Establish `hdef : Formalism.MainNotions.S.lowKSub ε lam σ = sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}` using `rfl`. Establish `hset : {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} = {(lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap}`. Use extensionality with `S`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hS`. Establish `h2` using `(sigLam_lowK hgap hP hw).2 _ ((isKTypeOf_map_iff _ U.toLinearEquiv.symm.injective hintS _ S).1 hS)`. Rewrite using `[← h2, ← Submodule.map_comp]`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Introduce and unpack `rfl`. Conclude with `(isKTypeOf_map_iff _ U.toLinearEquiv.injective hintU _ _).1 (sigLam_lowK hgap hP hw).1`. Rewrite using `[hdef, hset, sSup_singleton]`. Use `⟨j, hiso, hK, hrange.trans hlow.symm, fun g hg => ?_⟩` and prove the remaining obligations.

Use `ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun v' => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply, hkey g hg v v']`.
-/
theorem anyF (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) :
    ∃ j : T.V →L[ℂ] H, (∀ v, ‖j v‖ = ‖v‖) ∧
      (∀ (k : S7.KG ε) (v : T.V), σ (S7.toMK k) (j v) = j (T.op k v)) ∧
      LinearMap.range (j : T.V →ₗ[ℂ] H) = Formalism.MainNotions.S.lowKSub ε lam σ ∧
      ∀ g ∈ UJset ε, (ContinuousLinearMap.adjoint j).comp ((σ g).comp j) = Ψ g := by
  have hw : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hDS hgap hP hw
  have hc0 := datumEmbedding_highest_ne_zero hgap hP hw
  set c : ℝ := ‖uniformisationL2 ε Ψ T.w T.w‖ with hc
  have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc0)
  let jl : T.V →ₗ[ℂ] H := ((c : ℂ)⁻¹) • (U.toLinearEquiv.toLinearMap ∘ₗ datumEmbedding hP T.w)
  let j : T.V →L[ℂ] H := LinearMap.toContinuousLinearMap jl
  have hjv : ∀ v, j v = ((c : ℂ)⁻¹) • U (datumEmbedding hP T.w v) := fun v => rfl
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show inUJ ε 1
    simp [inUJ]
  have hkey : ∀ g ∈ UJset ε, ∀ v v', inner ℂ (j v') (σ g (j v)) = inner ℂ v' (Ψ g v) := by
    intro g hg v v'
    rw [hjv, hjv, map_smul, ← hU g hg, inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map]
    have e := formulaF_sigLam hgap hP hw hg v v'
    rw [show datumEmbedding hP T.w v = (⟨uniformisationL2 ε Ψ T.w v, datumEmbedding_mem_Hlam hP v⟩ : Hlam ε Ψ T.w) from rfl,
      show datumEmbedding hP T.w v' = (⟨uniformisationL2 ε Ψ T.w v', datumEmbedding_mem_Hlam hP v'⟩ : Hlam ε Ψ T.w) from rfl, e]
    rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp
    rw [hc]
  have hiso : ∀ v, ‖j v‖ = ‖v‖ := by
    intro v
    have e := hkey 1 h1 v v
    rw [hDS.2.2.1.1.1, hP.2.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    have e2 : ‖j v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, e]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 e2
  have hK : ∀ (k : S7.KG ε) v, σ (S7.toMK k) (j v) = j (T.op k v) := by
    intro k v
    rw [hjv, hjv, map_smul, ← hU _ (ffa_toMK_mem k)]
    congr 2
    apply Subtype.ext
    rw [sigLam_coe hgap hP hw (ffa_toMK_mem k)]
    exact rightRegular_datumEmbedding hP T.w v k
  have hrange : LinearMap.range (j : T.V →ₗ[ℂ] H) =
      (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap := by
    show LinearMap.range jl = _
    rw [LinearMap.range_smul _ _ (inv_ne_zero hcne), LinearMap.range_comp, range_datumEmbedding]
  have hintU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.toLinearMap (sigLam ε Ψ T.w g x) =
      σ g (U.toLinearEquiv.toLinearMap x) := by
    intro g hg x
    rw [mir_Kset_eq] at hg
    exact hU g (UnitaryGroupOfForm.K_mem_UJ hg) x
  have hintS : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U.toLinearEquiv.symm.toLinearMap (σ g x) =
      sigLam ε Ψ T.w g (U.toLinearEquiv.symm.toLinearMap x) := by
    intro g hg x
    apply U.injective
    have e := hintU g hg (U.toLinearEquiv.symm x)
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] at e ⊢
    rw [e]
    simp
  have hlow : Formalism.MainNotions.S.lowKSub ε lam σ = (lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap := by
    have hdef : Formalism.MainNotions.S.lowKSub ε lam σ =
        sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} := rfl
    have hset : {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} =
        {(lowKSubLam ε Ψ T.w).map U.toLinearEquiv.toLinearMap} := by
      ext S
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hS
        have h2 := (sigLam_lowK hgap hP hw).2 _
          ((isKTypeOf_map_iff _ U.toLinearEquiv.symm.injective hintS _ S).1 hS)
        rw [← h2, ← Submodule.map_comp]
        ext x
        simp
      · rintro rfl
        exact (isKTypeOf_map_iff _ U.toLinearEquiv.injective hintU _ _).1 (sigLam_lowK hgap hP hw).1
    rw [hdef, hset, sSup_singleton]
  refine ⟨j, hiso, hK, hrange.trans hlow.symm, fun g hg => ?_⟩
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun v' => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply, hkey g hg v v']

end Main

end ReciprocityTheory.ChartRestriction.DS
