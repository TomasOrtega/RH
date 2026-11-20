import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetKernelTwoBlockUnipotentLeStagesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetModuleMaximalParabolicPrincipalSeriesTypeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroupsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockDiagonalPrincipalSeriesCongruenceSubgroupSpStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrderedCharacterFamilySplitsOrConstantOnUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `k _ _ _ _ n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `ψ V _ _ π hπ hψ hord v hv heig`. Break down `GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units k n ψ hord with ⟨r, hr0, hrn, hcut⟩ | ⟨χ, hχ, hag⟩` into its components or cases.

Use `swap`. Take `⟨hg, hth, -, -⟩` from `GlobalTheory.T.principalSeriesType_data_depend_only_on_units k n ψ _ hag`. Rewrite `heig` using `[hg, hth]`. Conclude with `GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character k n χ V π hπ (hχ hψ) v hv heig`. Take `⟨t, rfl⟩ : ∃ t, n = r + t` from `⟨n - r, by omega⟩`.

Establish `ht : 0 < t` using `by omega`. Use `set e := stdSum (rfl : r + t = r + t) with he`. Use `set ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i) with hψ₁`. Use `set ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i) with hψ₂`. Take `⟨ho₁, ho₂, hmem⟩` from `GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split k r t ψ hord hcut`.

Establish `hs₁ : ∀ i, IsSmoothChar (ψ₁ i)` using `fun i => hψ _`. Establish `hs₂ : ∀ i, IsSmoothChar (ψ₂ i)` using `fun i => hψ _`. Establish `one_grp : ∀ (m : ℕ) (φ : Fin m → kˣ →* ℂˣ), (1 : GL (Fin m) k) ∈ grp φ`. Introduce `m φ`. Use `⟨(KO k (Fin m)).one_mem, fun i j hij => ?_⟩` and prove the remaining obligations.

Establish `h0 : ((1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j = 0`. Simplify using `[Matrix.one_apply_ne (ne_of_lt hij)]`. Rewrite using `[h0]`. Conclude with `(GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _`. Set `Q` to `twKer π (unipRad k (two e)) 1`.

Set `ρ` to `jacU₂ e π`. Establish `hρ : IsSmooth ρ` using `isSmooth_comp (isSmooth_jacU _ hπ) _ (continuous_leviTwo k)`. Establish `hact : ∀ g w, ρ g (Q.mkQ w) = Q.mkQ (π (emb₂ k e g) w)` using `fun g w => rfl`. Set `P : Submodule ℂ V` to `(twKer (ρ.comp (MonoidHom.inl _ _)) (unipB k (Fin r)) 1 ⊔ twKer (ρ.comp (MonoidHom.inr _ _)) (unipB k (Fin t)) 1).comap Q.mkQ`. Establish `hP : twKer π (unipB k (Fin (r + t))) 1 ≤ P`.

Use `GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages k r t V π P ?_ ?_ ?_` and prove the remaining obligations. Introduce `w hw`. Use `Submodule.mem_comap.2 ?_` and prove the remaining obligations. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Q).2 hw]`. Conclude with `zero_mem _`.

Introduce `u hu w`. Use `Submodule.mem_comap.2 ?_` and prove the remaining obligations. Use `Submodule.mem_sup_left (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)` and prove the remaining obligations. Simplify using `only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]`. Both sides reduce to the same expression.

Introduce `u hu w`. Use `Submodule.mem_comap.2 ?_` and prove the remaining obligations. Use `Submodule.mem_sup_right (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)` and prove the remaining obligations. Simplify using `only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]`. Both sides reduce to the same expression.

Establish `hx` using `hP hv`. Establish `hzero : Q.mkQ v = 0`. Use `GlobalTheory.T.twistedJacquet_survival_product_of_two_groups (GL (Fin r) k) (GL (Fin t) k) _ ρ hρ (unipB k (Fin r)) (unipB k (Fin t)) (grp ψ₁) (grp ψ₂) (theta ψ₁) (theta ψ₂) (fun W _ _ σ hσ w hw hwe => ih r (by omega) ψ₁ W σ hσ hs₁ ho₁ w hw hwe) (fun W _ _ σ hσ w hw hwe => ih t ( …` and prove the remaining obligations. Introduce `a ha`. Establish `hm : emb₂ k e (a, 1) ∈ grp ψ` using `(hmem a 1).2 ⟨ha, one_grp _ _⟩`.

Establish `hth` using `GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord a ha 1 (one_grp _ _)`. Rewrite `hth` using `[(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k t ψ₂ hs₂).1, mul_one]`. Use `show ρ (a, 1) (Q.mkQ v) = _`. Rewrite using `[hact, heig _ hm, map_smul]`. Conclude with `congrArg (· • Q.mkQ v) hth`.

Introduce `b hb`. Establish `hm : emb₂ k e (1, b) ∈ grp ψ` using `(hmem 1 b).2 ⟨one_grp _ _, hb⟩`. Establish `hth` using `GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord 1 (one_grp _ _) b hb`. Rewrite `hth` using `[(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k r ψ₁ hs₁).1, one_mul]`. Use `show ρ (1, b) (Q.mkQ v) = _`.

Rewrite using `[hact, heig _ hm, map_smul]`. Conclude with `congrArg (· • Q.mkQ v) hth`. Establish `hvQ : v ∈ Q` using `(Submodule.Quotient.mk_eq_zero Q).1 hzero`. Conclude with `GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen k r t ψ V π hπ hψ hord hcut v hvQ heig`.
-/
theorem eq_zero_of_mem_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp ψ) (theta ψ) v → v = 0 := by
  intro k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ψ V _ _ π hπ hψ hord v hv heig
  rcases GlobalTheory.T.orderedCharacterFamily_splits_or_constant_on_units k n ψ hord with ⟨r, hr0, hrn, hcut⟩ | ⟨χ, hχ, hag⟩
  swap
  · obtain ⟨hg, hth, -, -⟩ := GlobalTheory.T.principalSeriesType_data_depend_only_on_units k n ψ _ hag
    rw [hg, hth] at heig
    exact GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character k n χ V π hπ (hχ hψ) v hv heig
  obtain ⟨t, rfl⟩ : ∃ t, n = r + t := ⟨n - r, by omega⟩
  have ht : 0 < t := by omega
  set e := stdSum (rfl : r + t = r + t) with he
  set ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i) with hψ₁
  set ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i) with hψ₂
  obtain ⟨ho₁, ho₂, hmem⟩ := GlobalTheory.T.blockDiagonal_principalSeriesCongruenceSubgroup_split k r t ψ hord hcut
  have hs₁ : ∀ i, IsSmoothChar (ψ₁ i) := fun i => hψ _
  have hs₂ : ∀ i, IsSmoothChar (ψ₂ i) := fun i => hψ _
  have one_grp : ∀ (m : ℕ) (φ : Fin m → kˣ →* ℂˣ), (1 : GL (Fin m) k) ∈ grp φ := by
    intro m φ
    refine ⟨(KO k (Fin m)).one_mem, fun i j hij => ?_⟩
    have h0 : ((1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  let Q := twKer π (unipRad k (two e)) 1
  let ρ := jacU₂ e π
  have hρ : IsSmooth ρ := isSmooth_comp (isSmooth_jacU _ hπ) _ (continuous_leviTwo k)
  have hact : ∀ g w, ρ g (Q.mkQ w) = Q.mkQ (π (emb₂ k e g) w) := fun g w => rfl
  let P : Submodule ℂ V := (twKer (ρ.comp (MonoidHom.inl _ _)) (unipB k (Fin r)) 1 ⊔
      twKer (ρ.comp (MonoidHom.inr _ _)) (unipB k (Fin t)) 1).comap Q.mkQ
  have hP : twKer π (unipB k (Fin (r + t))) 1 ≤ P := by
    refine GlobalTheory.T.twistedJacquetKernel_twoBlock_unipotent_le_stages k r t V π P ?_ ?_ ?_
    · intro w hw
      refine Submodule.mem_comap.2 ?_
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Q).2 hw]
      exact zero_mem _
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_left (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
    · intro u hu w
      refine Submodule.mem_comap.2 ?_
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨⟨u, hu⟩, Q.mkQ w, ?_⟩)
      simp only [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rfl
  have hx := hP hv
  have hzero : Q.mkQ v = 0 := by
    refine GlobalTheory.T.twistedJacquet_survival_product_of_two_groups (GL (Fin r) k) (GL (Fin t) k) _ ρ hρ (unipB k (Fin r)) (unipB k (Fin t))
      (grp ψ₁) (grp ψ₂) (theta ψ₁) (theta ψ₂)
      (fun W _ _ σ hσ w hw hwe => ih r (by omega) ψ₁ W σ hσ hs₁ ho₁ w hw hwe)
      (fun W _ _ σ hσ w hw hwe => ih t (by omega) ψ₂ W σ hσ hs₂ ho₂ w hw hwe)
      (Q.mkQ v) hx ?_ ?_
    · intro a ha
      have hm : emb₂ k e (a, 1) ∈ grp ψ := (hmem a 1).2 ⟨ha, one_grp _ _⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord a ha 1 (one_grp _ _)
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k t ψ₂ hs₂).1, mul_one] at hth
      show ρ (a, 1) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
    · intro b hb
      have hm : emb₂ k e (1, b) ∈ grp ψ := (hmem 1 b).2 ⟨one_grp _ _, hb⟩
      have hth := GlobalTheory.T.principalSeriesTypeCharacter_blockDiagonal k r t ψ hord 1 (one_grp _ _) b hb
      rw [(GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k r ψ₁ hs₁).1, one_mul] at hth
      show ρ (1, b) (Q.mkQ v) = _
      rw [hact, heig _ hm, map_smul]
      exact congrArg (· • Q.mkQ v) hth
  have hvQ : v ∈ Q := (Submodule.Quotient.mk_eq_zero Q).1 hzero
  exact GlobalTheory.T.jacquetModule_maximalParabolic_principalSeriesTypeEigen k r t ψ V π hπ hψ hord hcut v hvQ heig

end GlobalTheory.PsType
