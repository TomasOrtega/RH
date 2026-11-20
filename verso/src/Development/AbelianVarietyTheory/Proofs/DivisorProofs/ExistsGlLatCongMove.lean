import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace GlobalTheory.PrimFrameMove

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

/- English proof (translation)
Establish `hli : LinearIndependent k X.row`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, ← hX.1, rank_eq_finrank_span_row]`. Both sides reduce to the same expression. Set `X' : Matrix A D 𝒪[k]` to `Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩`. Set `f : (A → 𝒪[k]) →ₗ[𝒪[k]] (D → 𝒪[k])` to `X'.vecMulLinear`.

Establish `hf : ∀ v j, ((f v j : 𝒪[k]) : k) = (∑ i, (v i : k) • X.row i) j` using `fun v j => by`. Simplify using `[f, X', vecMul, dotProduct, Finset.sum_apply]`. Establish `hinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`.

Establish `h1 : ∑ i, (v i : k) • X.row i = 0`. Use function extensionality and compare the values at `j`. Rewrite using `[← hf, hv]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`.

Conclude with `Subtype.ext (Fintype.linearIndependent_iff.1 hli _ h1 i)`. Establish `hsat : ∀ (r : 𝒪[k]) (x : D → 𝒪[k]), r ≠ 0 → r • x ∈ LinearMap.range f → x ∈ LinearMap.range f`. Introduce and unpack `r x hr ⟨v, hv⟩`. Establish `hr' : (r : k) ≠ 0` using `fun h => hr (Subtype.ext h)`. Establish `h1 : (fun j => (x j : k)) = (r : k)⁻¹ • ∑ i, (v i : k) • X.row i`.

Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, ← hf, hv]`. Simplify using `[hr']`. Establish `h2 : (fun j => (x j : k)) ∈ Submodule.span 𝒪[k] (Set.range X.row)`. Rewrite using `[hX.2.2]`.

Use `⟨?_, mem_stdLat.2 fun j => (x j).2⟩` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem (Submodule.span k _) _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))`. Take `⟨d, hd⟩` from `(Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2`. Use `⟨d, funext fun j => Subtype.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[hf]`. Conclude with `congrFun hd j`. Establish `: Module.IsTorsionFree 𝒪[k] ((D → 𝒪[k]) ⧸ LinearMap.range f)`. Use `Module.IsTorsionFree.of_smul_eq_zero fun r q h => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Distinguish the cases in `hr : r = 0`. Conclude with `.inl hr`. Use `.inr ((Submodule.Quotient.mk_eq_zero _).2 (hsat r x hr ?_))` and prove the remaining obligations. Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis. Take `⟨s, hs⟩` from `Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id (Submodule.mkQ_surjective _)`.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : (D → 𝒪[k]) →ₗ[𝒪[k]] (A → 𝒪[k]), l ∘ₗ f = LinearMap.id := by`. Establish `hs' : ∃ s : _ →ₗ[𝒪[k]] _, (LinearMap.range f).mkQ ∘ₗ s = LinearMap.id` using `⟨s, hs⟩`. Establish `H` using `((LinearMap.exact_map_mkQ_range f).split_tfae hinj (Submodule.mkQ_surjective _)).out 0 1`. Conclude with `H.1 hs'`. Use `⟨Matrix.of fun j i => (l (Pi.single j 1) i : k), fun j i => (l (Pi.single j 1) i).2, ?_⟩` and prove the remaining obligations.

Use extensionality with `i i'`. Establish `h1 : l (f (Pi.single i 1)) = Pi.single i 1` using `LinearMap.congr_fun hl _`. Establish `h2 : f (Pi.single i 1) = ∑ j, X' i j • Pi.single j 1`. Use function extensionality and compare the values at `j`. Simplify using `[f, Finset.sum_apply, Pi.single_apply]`.

Rewrite `h1` using `[h2, map_sum]`. Establish `h3` using `congrArg Subtype.val (congrFun h1 i')`. Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3`. Move the coercions through the operations in `at h3`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`.

Use `h3.trans ?_` and prove the remaining obligations. Rewrite using `[Pi.single_apply]`. Distinguish the cases in `h : i = i'`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem exists_rightInverse {X : Matrix A D k} (hX : IsPrimFrame (SplitFlip.stdLat k D) X) :
    ∃ R : Matrix D A k, (∀ i j, R i j ∈ 𝒪[k]) ∧ X * R = 1 := by
  have hli : LinearIndependent k X.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, ← hX.1, rank_eq_finrank_span_row]; rfl
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let f : (A → 𝒪[k]) →ₗ[𝒪[k]] (D → 𝒪[k]) := X'.vecMulLinear
  have hf : ∀ v j, ((f v j : 𝒪[k]) : k) = (∑ i, (v i : k) • X.row i) j := fun v j => by
    simp [f, X', vecMul, dotProduct, Finset.sum_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : ∑ i, (v i : k) • X.row i = 0 := by
      funext j; rw [← hf, hv]; rfl
    funext i
    exact Subtype.ext (Fintype.linearIndependent_iff.1 hli _ h1 i)
  have hsat : ∀ (r : 𝒪[k]) (x : D → 𝒪[k]), r ≠ 0 → r • x ∈ LinearMap.range f → x ∈ LinearMap.range f := by
    rintro r x hr ⟨v, hv⟩
    have hr' : (r : k) ≠ 0 := fun h => hr (Subtype.ext h)
    have h1 : (fun j => (x j : k)) = (r : k)⁻¹ • ∑ i, (v i : k) • X.row i := by
      funext j
      rw [Pi.smul_apply, ← hf, hv]
      simp [hr']
    have h2 : (fun j => (x j : k)) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      refine ⟨?_, mem_stdLat.2 fun j => (x j).2⟩
      rw [h1]
      exact Submodule.smul_mem (Submodule.span k _) _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    refine ⟨d, funext fun j => Subtype.ext ?_⟩
    rw [hf]
    exact congrFun hd j
  have : Module.IsTorsionFree 𝒪[k] ((D → 𝒪[k]) ⧸ LinearMap.range f) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q h => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact .inl hr
    · refine .inr ((Submodule.Quotient.mk_eq_zero _).2 (hsat r x hr ?_))
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  obtain ⟨l, hl⟩ : ∃ l : (D → 𝒪[k]) →ₗ[𝒪[k]] (A → 𝒪[k]), l ∘ₗ f = LinearMap.id := by
    have hs' : ∃ s : _ →ₗ[𝒪[k]] _, (LinearMap.range f).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
    have H := ((LinearMap.exact_map_mkQ_range f).split_tfae hinj (Submodule.mkQ_surjective _)).out 0 1
    exact H.1 hs'
  refine ⟨Matrix.of fun j i => (l (Pi.single j 1) i : k), fun j i => (l (Pi.single j 1) i).2, ?_⟩
  ext i i'
  have h1 : l (f (Pi.single i 1)) = Pi.single i 1 := LinearMap.congr_fun hl _
  have h2 : f (Pi.single i 1) = ∑ j, X' i j • Pi.single j 1 := by
    funext j; simp [f, Finset.sum_apply, Pi.single_apply]
  rw [h2, map_sum] at h1
  have h3 := congrArg Subtype.val (congrFun h1 i')
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  push_cast at h3
  rw [Matrix.mul_apply, Matrix.one_apply]
  refine h3.trans ?_
  rw [Pi.single_apply]
  by_cases h : i = i'
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Set `M' : Matrix D D 𝒪[k]` to `Matrix.of fun i j => ⟨M i j, (hM i j).trans hu.le⟩`. Establish `hK : IsUnit (1 + M')`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]`. Establish `: (IsLocalRing.residue 𝒪[k]).mapMatrix M' = 0`. Use extensionality with `r j`.

Simplify using `only [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply]`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Conclude with `(hM r j).trans_lt hu`. Rewrite using `[map_add, this]`. Simplify using the standard rewrite rules.

Take `⟨w, hw⟩` from `hK`. Establish `hv : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w).val = 1 + M` using `by show (algebraMap 𝒪[k] k).mapMatrix w.val = _`. Rewrite using `[hw, map_add, map_one]`. Both sides reduce to the same expression. Use `⟨_, GlobalTheory.FunObj.GivenAdm.mem_glLatCong.2 ⟨⟨w, rfl⟩, ?_⟩, hv⟩` and prove the remaining obligations.

Rewrite using `[hv, add_sub_cancel_left]`. Conclude with `hM`.
-/
theorem exists_mem_glLatCong {u : kˣ} (hu : valuation k (u : k) < 1) {M : Matrix D D k}
    (hM : ∀ i j, valuation k (M i j) ≤ valuation k (u : k)) :
    ∃ κ ∈ glLatCong u (SplitFlip.stdLat k D), κ.val = 1 + M := by
  let M' : Matrix D D 𝒪[k] := Matrix.of fun i j => ⟨M i j, (hM i j).trans hu.le⟩
  have hK : IsUnit (1 + M') := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = 0 := by
      ext r j
      simp only [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact (hM r j).trans_lt hu
    rw [map_add, this]; simp
  obtain ⟨w, hw⟩ := hK
  have hv : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w).val = 1 + M := by
    show (algebraMap 𝒪[k] k).mapMatrix w.val = _
    rw [hw, map_add, map_one]; rfl
  refine ⟨_, GlobalTheory.FunObj.GivenAdm.mem_glLatCong.2 ⟨⟨w, rfl⟩, ?_⟩, hv⟩
  rw [hv, add_sub_cancel_left]
  exact hM

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `forall_congr' fun j => ?_` and prove the remaining obligations. Establish `h0 : 0 < valuation k (c j : k)` using `zero_lt_iff.2 (by simp)`. Rewrite using `[diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]`. Conclude with `mul_le_mul_iff_left₀ h0`.
-/
theorem vecMul_diagGL_mem (a b c : D → kˣ) (h : ∀ j, b j = a j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat b ↔ x ∈ diagLat a := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

/- English proof (translation)
Use `set g : GL D k := diagGL c with hg`. Establish `h1 : ∀ x, x ᵥ* g.val ∈ diagLat c ↔ x ∈ SplitFlip.stdLat k D` using `vecMul_diagGL_mem 1 c c (by simp)`. Establish `h2 : ∀ x, x ᵥ* g.val ∈ u • diagLat c ↔ x ∈ u • SplitFlip.stdLat k D` using `fun x => by`. Rewrite using `[SplitFlip.stdLat, smul_diagLat, smul_diagLat]`. Conclude with `vecMul_diagGL_mem _ _ c (by simp) x`.

Establish `h1' : ∀ x, x ᵥ* (g⁻¹).val ∈ SplitFlip.stdLat k D ↔ x ∈ diagLat c` using `fun x => by`. Rewrite using `[← h1, vecMul_vecMul, Units.inv_mul, vecMul_one]`. Establish `h2' : ∀ x, x ᵥ* (g⁻¹).val ∈ u • SplitFlip.stdLat k D ↔ x ∈ u • diagLat c` using `fun x => by`. Rewrite using `[← h2, vecMul_vecMul, Units.inv_mul, vecMul_one]`. Take `⟨R, hR, hXR⟩` from `exists_rightInverse (SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1')`.

Establish `hZ' : GlobalTheory.FunObj.GivenAdm.CongM u (Z * (g⁻¹).val)` using `GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.1 fun i => (h2' (Z.row i)).2 (hZ i)`. Take `⟨κ, ⟨hκ, hκ'⟩, hv⟩` from `exists_mem_glLatCong hu (hZ'.mul_left (Y := R) hR)`. Use `⟨g⁻¹ * κ * g, ⟨fun x => ?_, fun x hx => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, h1, hκ, h1']`. Rewrite using `[show (g⁻¹ * κ * g).val - 1 = (g⁻¹).val * (κ.val - 1) * g.val by`.

Rewrite using `[mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul],`. Use the proof step `← vecMul_vecMul, ← vecMul_vecMul, h2]`. Conclude with `hκ' _ ((h1' x).2 hx)`. Rewrite using `[Units.val_mul, Units.val_mul, hv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_add, ← Matrix.mul_assoc _ R, hXR, Matrix.mul_one, Matrix.one_mul, ← Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.
-/
theorem exists_glLatCong_move (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (c : D → kˣ) (u : kˣ) (hu : valuation k (u : k) < 1) (X Z : Matrix A D k) (hX : IsPrimFrame (diagLat c) X)
    (hZ : Z ∈ matLat A (u • diagLat c)) : ∃ κ ∈ glLatCong u (diagLat c), X + Z = X * κ.val := by
  set g : GL D k := diagGL c with hg
  have h1 : ∀ x, x ᵥ* g.val ∈ diagLat c ↔ x ∈ SplitFlip.stdLat k D := vecMul_diagGL_mem 1 c c (by simp)
  have h2 : ∀ x, x ᵥ* g.val ∈ u • diagLat c ↔ x ∈ u • SplitFlip.stdLat k D := fun x => by
    rw [SplitFlip.stdLat, smul_diagLat, smul_diagLat]
    exact vecMul_diagGL_mem _ _ c (by simp) x
  have h1' : ∀ x, x ᵥ* (g⁻¹).val ∈ SplitFlip.stdLat k D ↔ x ∈ diagLat c := fun x => by
    rw [← h1, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have h2' : ∀ x, x ᵥ* (g⁻¹).val ∈ u • SplitFlip.stdLat k D ↔ x ∈ u • diagLat c := fun x => by
    rw [← h2, vecMul_vecMul, Units.inv_mul, vecMul_one]
  obtain ⟨R, hR, hXR⟩ := exists_rightInverse (SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1')
  have hZ' : GlobalTheory.FunObj.GivenAdm.CongM u (Z * (g⁻¹).val) :=
    GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.1 fun i => (h2' (Z.row i)).2 (hZ i)
  obtain ⟨κ, ⟨hκ, hκ'⟩, hv⟩ := exists_mem_glLatCong hu (hZ'.mul_left (Y := R) hR)
  refine ⟨g⁻¹ * κ * g, ⟨fun x => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, h1, hκ, h1']
  · rw [show (g⁻¹ * κ * g).val - 1 = (g⁻¹).val * (κ.val - 1) * g.val by
      rw [mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul],
      ← vecMul_vecMul, ← vecMul_vecMul, h2]
    exact hκ' _ ((h1' x).2 hx)
  · rw [Units.val_mul, Units.val_mul, hv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_add,
      ← Matrix.mul_assoc _ R, hXR, Matrix.mul_one, Matrix.one_mul, ← Matrix.add_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]

end GlobalTheory.PrimFrameMove
