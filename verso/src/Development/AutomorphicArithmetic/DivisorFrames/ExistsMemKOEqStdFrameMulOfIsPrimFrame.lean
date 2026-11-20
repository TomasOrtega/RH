import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

/- English proof (translation)
Introduce `k _ _ _ _ A A' D _ _ _ _ _ _ σ X hX`. Take `⟨R, hR, hXR⟩` from `GlobalTheory.PrimFrameMove.exists_rightInverse hX`. Set `X' : Matrix A D 𝒪[k]` to `Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩`. Set `R' : Matrix D A 𝒪[k]` to `Matrix.of fun i j => ⟨R i j, hR i j⟩`. Establish `h1 : X' * R' = 1`.

Apply `Matrix.map_injective (f := algebraMap 𝒪[k] k) Subtype.val_injective` to reduce the goal to its premises. Use `show (X' * R').map (algebraMap 𝒪[k] k) = (1 : Matrix A A 𝒪[k]).map (algebraMap 𝒪[k] k)`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `hXR`. Set `ρ` to `IsLocalRing.residue 𝒪[k]`.

Establish `h2 : X'.map ρ * R'.map ρ = 1`. Rewrite using `[← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h3 : (X'.map ρ).rank = Fintype.card A`. Use `le_antisymm (Matrix.rank_le_card_height _) ?_` and prove the remaining obligations. Use `Matrix.rank_mul_le_left (X'.map ρ) (R'.map ρ)` as an intermediate fact.

Rewrite `this` using `[h2, Matrix.rank_one]`. Then use the resulting hypothesis. Take `⟨h, hh⟩` from `(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ _).1 h3`. Use `choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])`. Set `C : Matrix D D 𝒪[k]` to `Matrix.of fun r j => Sum.elim (fun i => X' i j) (fun i => l ((invT h).val (σ (Sum.inr i)) j)) (σ.symm r)`. Establish `h4 : ρ.mapMatrix C = (invT h).val`.

Use extensionality with `r j`. Take `⟨i | i, rfl⟩` from `σ.surjective r`. Use `congrFun (congrFun hh i) j` as an intermediate fact. Rewrite `this` using `[frameMatrixFirstColumnBlock_mul_apply]`. Simplify `this` using `[C]`.

Simplify using `[C, ρ, hl]`. Establish `hK : IsUnit C`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Rewrite using `[show (IsLocalRing.residue 𝒪[k]).mapMatrix C = _ from h4]`. Conclude with `(invT h).det_ne_zero`.

Take `⟨w, hw⟩` from `hK`. Use `⟨invT (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w), invT_mem_KO ⟨w, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[invT_invT]`. Use extensionality with `i j`. Rewrite using `[frameMatrixFirstColumnBlock_mul_apply]`.

Use `show _ = ((w.val (σ (Sum.inl i)) j : 𝒪[k]) : k)`. Rewrite using `[hw]`. Simplify using `[C, X']`.
-/
theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) (X : Matrix A D k), IsPrimFrame (stdLat k D) X → ∃ u ∈ KO k D, X = X0 k σ * (invT u).val := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ X hX
  obtain ⟨R, hR, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let R' : Matrix D A 𝒪[k] := Matrix.of fun i j => ⟨R i j, hR i j⟩
  have h1 : X' * R' = 1 := by
    apply Matrix.map_injective (f := algebraMap 𝒪[k] k) Subtype.val_injective
    show (X' * R').map (algebraMap 𝒪[k] k) = (1 : Matrix A A 𝒪[k]).map (algebraMap 𝒪[k] k)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hXR
  let ρ := IsLocalRing.residue 𝒪[k]
  have h2 : X'.map ρ * R'.map ρ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : (X'.map ρ).rank = Fintype.card A := by
    refine le_antisymm (Matrix.rank_le_card_height _) ?_
    have := Matrix.rank_mul_le_left (X'.map ρ) (R'.map ρ)
    rwa [h2, Matrix.rank_one] at this
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ _).1 h3
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let C : Matrix D D 𝒪[k] := Matrix.of fun r j =>
    Sum.elim (fun i => X' i j) (fun i => l ((invT h).val (σ (Sum.inr i)) j)) (σ.symm r)
  have h4 : ρ.mapMatrix C = (invT h).val := by
    ext r j
    obtain ⟨i | i, rfl⟩ := σ.surjective r
    · have := congrFun (congrFun hh i) j
      rw [frameMatrixFirstColumnBlock_mul_apply] at this
      simpa [C] using this
    · simp [C, ρ, hl]
  have hK : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    rw [show (IsLocalRing.residue 𝒪[k]).mapMatrix C = _ from h4]
    exact (invT h).det_ne_zero
  obtain ⟨w, hw⟩ := hK
  refine ⟨invT (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w), invT_mem_KO ⟨w, rfl⟩, ?_⟩
  rw [invT_invT]
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply]
  show _ = ((w.val (σ (Sum.inl i)) j : 𝒪[k]) : k)
  rw [hw]
  simp [C, X']
