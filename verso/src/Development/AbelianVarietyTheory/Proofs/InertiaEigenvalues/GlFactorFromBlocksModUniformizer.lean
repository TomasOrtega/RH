import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ _ r t ϖ hϖ g L hL B q hq`. Establish `hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Establish `hmem : ∀ x : O, IsLocalRing.residue O x = 0 → x ∈ Ideal.span {ϖ}` using `fun x hx => hmax ▸ (IsLocalRing.residue_eq_zero_iff x).mp hx`. Establish `hg : IsUnit (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det` using `(Matrix.isUnit_iff_isUnit_det _).mp g.isUnit`. Establish `hLdet : IsLocalRing.residue O L.det = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det`.

Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hL]`. Establish `hLu : IsUnit L.det` using `(IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hLdet]; exact hg.ne_zero)`. Use `set D : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L 0 0 1 with hDdef`. Establish `hDu : IsUnit D.det`. Rewrite using `[hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]`.

Conclude with `hLu`. Establish `hqmap : q.map (IsLocalRing.residue O) = (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O)).map (IsLocalRing.residue O)`. Use extensionality with `i j`. Conclude with `hq i j`. Establish `hqu : IsUnit q.det`.

Apply `(IsLocalRing.residue_ne_zero_iff_isUnit _).mp` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hqmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, hLdet]`. Conclude with `hg.ne_zero`. Establish `hHu : IsUnit (q * D⁻¹).det`. Rewrite using `[Matrix.det_mul]`.

Conclude with `hqu.mul (Matrix.isUnit_nonsing_inv_det D hDu)`. Establish `hHD : q * D⁻¹ * D = q`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDu, Matrix.mul_one]`. Establish `hMD : (q * D⁻¹).map (IsLocalRing.residue O) * D.map (IsLocalRing.residue O) = q.map (IsLocalRing.residue O)`. Rewrite using `[← Matrix.map_mul, hHD]`.

Rewrite `hMD` using `[hqmap, ← Matrix.fromBlocks_toBlocks ((q * D⁻¹).map (IsLocalRing.residue O)), hDdef, Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]`. Take `⟨h11, -, h21, -⟩` from `hMD`. Simplify using `only [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, add_zero, hL] at h11 h21`. Establish `e11 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₁₁ = 1`. Use `congrArg (· * ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _)) h11` as an intermediate fact.

Simplify `this` using `[Matrix.mul_assoc]`. Establish `e21 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₂₁ = 0`. Establish `hgg : (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) * ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _) = 1` using `Units.mul_inv g`. Rewrite using `[hDdef, ← Matrix.mul_one (Matrix.toBlocks₂₁ _), ← hgg, ← Matrix.mul_assoc, h21, Matrix.zero_mul]`. Use `⟨Matrix.nonsingInvUnit (q * D⁻¹) hHu, ?_, ?_, hHD⟩` and prove the remaining obligations.

Introduce `i j`. Apply `hmem` to reduce the goal to its premises. Use `congrFun (congrFun e11 i) j` as an intermediate fact. Simplify using `only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.map_apply] at this`. Use `show IsLocalRing.residue O ((q * D⁻¹) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j) = 0`.

Rewrite using `[map_sub, this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Introduce `i j show (q * D⁻¹) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}`. Apply `hmem` to reduce the goal to its premises. Use `congrFun (congrFun e21 i) j` as an intermediate fact.

Simplify `this` using `[Matrix.toBlocks₂₁]`.
-/
theorem gl_factor_fromBlocks_mod_uniformizer : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (g : GL (Fin r) (IsLocalRing.ResidueField O)) (L : Matrix (Fin r) (Fin r) O), L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∀ (B : Matrix (Fin r) (Fin t) O) (q : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O), (∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O) i j)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) = q := by
  intro O _ _ _ r t ϖ hϖ g L hL B q hq
  classical
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hmem : ∀ x : O, IsLocalRing.residue O x = 0 → x ∈ Ideal.span {ϖ} := fun x hx =>
    hmax ▸ (IsLocalRing.residue_eq_zero_iff x).mp hx
  have hg : IsUnit (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hLdet : IsLocalRing.residue O L.det = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hL]
  have hLu : IsUnit L.det :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hLdet]; exact hg.ne_zero)
  set D : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L 0 0 1 with hDdef
  have hDu : IsUnit D.det := by
    rw [hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact hLu
  have hqmap : q.map (IsLocalRing.residue O) =
      (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O)).map (IsLocalRing.residue O) := by
    ext i j; exact hq i j
  have hqu : IsUnit q.det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hqmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, hLdet]
    exact hg.ne_zero
  have hHu : IsUnit (q * D⁻¹).det := by
    rw [Matrix.det_mul]; exact hqu.mul (Matrix.isUnit_nonsing_inv_det D hDu)
  have hHD : q * D⁻¹ * D = q := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDu, Matrix.mul_one]
  have hMD : (q * D⁻¹).map (IsLocalRing.residue O) * D.map (IsLocalRing.residue O) =
      q.map (IsLocalRing.residue O) := by
    rw [← Matrix.map_mul, hHD]
  rw [hqmap, ← Matrix.fromBlocks_toBlocks ((q * D⁻¹).map (IsLocalRing.residue O)), hDdef,
    Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hMD
  obtain ⟨h11, -, h21, -⟩ := hMD
  simp only [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, add_zero, hL] at h11 h21
  have e11 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₁₁ = 1 := by
    have := congrArg (· * ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _)) h11
    simpa [Matrix.mul_assoc] using this
  have e21 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₂₁ = 0 := by
    have hgg : (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) *
        ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _) = 1 := Units.mul_inv g
    rw [hDdef, ← Matrix.mul_one (Matrix.toBlocks₂₁ _), ← hgg, ← Matrix.mul_assoc, h21, Matrix.zero_mul]
  refine ⟨Matrix.nonsingInvUnit (q * D⁻¹) hHu, ?_, ?_, hHD⟩
  · intro i j
    apply hmem
    have := congrFun (congrFun e11 i) j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.map_apply] at this
    show IsLocalRing.residue O ((q * D⁻¹) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j) = 0
    rw [map_sub, this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro i j
    show (q * D⁻¹) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}
    apply hmem
    have := congrFun (congrFun e21 i) j
    simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory
