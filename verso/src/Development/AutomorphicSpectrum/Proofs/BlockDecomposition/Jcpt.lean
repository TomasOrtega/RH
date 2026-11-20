import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2

open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo

/- English proof (translation)
Introduce `hS hG hT F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hGood hB hi hJ`. Use `show IsCompact (cK α j : Set (cover A ν ι))`. Establish `hj : Continuous j` using `(hT F E R A ε ν r δ α ω ι i j hGood hB hi hJ).1`. Take `⟨-, -, -, hUT2, -, -, hUK⟩` from `hG E R A hGood ι ε`. Establish `hν : Continuous ν` using `hB.cont`.

Establish `hmapν : Continuous (Matrix.GeneralLinearGroup.map (n` using `ι ⊕ ι) ν) := by`. Use `Continuous.units_map _ ?_` and prove the remaining obligations. Conclude with `Continuous.matrix_map continuous_id hν`. Set `D : GL (ι ⊕ ι) R` to `dg ι (Units.map A.i.toMonoidHom δ)`. Set `M : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → GL (ι ⊕ ι) R` to `fun h => D⁻¹ * Matrix.GeneralLinearGroup.map ν h * D`.

Establish `hM : Continuous M` using `(continuous_const.mul hmapν).mul continuous_const`. Set `φ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R` to `fun p => ((p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)`. Set `ψ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R` to `fun p => ((M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)`. Establish `hval : Continuous (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R)` using `continuous_subtype_val`. Establish `hφ : Continuous φ`.

Establish `: Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) => (p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R)` using `(hval.comp continuous_fst).mul (hM.comp continuous_snd).inv`. Conclude with `(Units.continuous_val.comp this).matrix_elem _ _`. Establish `hψ : Continuous ψ`. Establish `: Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) => (M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R)` using `(hM.comp continuous_snd).mul (hval.comp continuous_fst).inv`. Conclude with `(Units.continuous_val.comp this).matrix_elem _ _`.

Establish `hrel : ∀ x : cover A ν ι, ((j x).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • (M x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) R)` using `fun x => hJ x`. Establish `hφv : ∀ x : cover A ν ι, φ (j x, x.1.2) = (x.1.1 : R)`. Introduce `x`. Establish `e : (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • 1`. Rewrite using `[Units.val_mul, hrel x, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Use `show (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _`. Rewrite using `[e]`. Simplify using the standard rewrite rules. Establish `hψv : ∀ x : cover A ν ι, ψ (j x, x.1.2) = ((x.1.1⁻¹ : Rˣ) : R)`. Introduce `x`.

Establish `e0 : (x.1.1 : R) • ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1`. Rewrite using `[Units.val_mul, ← Matrix.smul_mul, ← hrel x, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `e : ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = ((x.1.1⁻¹ : Rˣ) : R) • 1`. Rewrite using `[← e0, smul_smul, Units.inv_mul, one_smul]`. Use `show ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _`.

Rewrite using `[e]`. Simplify using the standard rewrite rules. Set `C₂ : Set (GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))` to `((((adStd F).kGL (ι ⊕ ι)).map (MulAut.conj (dg ι α)).toMonoidHom : Subgroup _) : Set _)`. Establish `hC₂ : IsCompact C₂`. Establish `h0` using `((hS F).kcpt (ι ⊕ ι)).image (f := fun k => (MulAut.conj (dg ι α)).toMonoidHom k) (by show Continuous fun k => dg ι α * k * (dg ι α)⁻¹`.

Conclude with `(continuous_const.mul continuous_id).mul continuous_const)`. Conclude with `h0`. Set `C₁ : Set (A.U ε ι)` to `(A.uK ε ι : Set (A.U ε ι))`. Establish `hC : IsCompact (C₁ ×ˢ C₂)` using `hUK.prod hC₂`. Establish `hS₁` using `hC.image hφ`.

Establish `hS₂ : IsCompact (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂)))` using `(hC.image hψ).image MulOpposite.continuous_op`. Set `B : Set Rˣ` to `Units.embedProduct R ⁻¹' ((φ '' (C₁ ×ˢ C₂)) ×ˢ (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))))`. Establish `hBc : IsCompact B` using `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS₁.prod hS₂)`. Establish `hdet : Continuous (Matrix.GeneralLinearGroup.det (n` using `ι ⊕ ι) (R := NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) := by`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Use `show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) => (g : Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det`. Conclude with `Continuous.matrix_det Units.continuous_val`. Use `show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) => ((g⁻¹ : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) : Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det`. Conclude with `Continuous.matrix_det (Units.continuous_val.comp continuous_inv)`. Establish `hσ : Continuous A.σ` using `hGood.σcont`.

Establish `hUσ : Continuous (Units.map A.σ.toMonoidHom)` using `Continuous.units_map _ hσ`. Establish `hUν : Continuous (Units.map ν.toMonoidHom)` using `Continuous.units_map _ hν`. Establish `hcl : IsClosed ((cover A ν ι : Subgroup _) : Set (Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)))`. Establish `hf : Continuous fun p : Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) => p.1 * Units.map A.σ.toMonoidHom p.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det p.2)` using `(continuous_fst.mul (hUσ.comp continuous_fst)).mul (hUν.comp (hdet.comp continuous_snd))`. Conclude with `isClosed_singleton.preimage hf`.

Establish `hemb` using `hcl.isClosedEmbedding_subtypeVal`. Establish `hP : IsCompact ((Subtype.val : cover A ν ι → _) ⁻¹' (B ×ˢ C₂))` using `hemb.isCompact_preimage (hBc.prod hC₂)`. Establish `hprj : Continuous (prj A ν ι)` using `continuous_snd.comp continuous_subtype_val`. Establish `hclK : IsClosed (cK α j : Set (cover A ν ι))` using `(hUK.isClosed.preimage hj).inter (hC₂.isClosed.preimage hprj)`. Use `hP.of_isClosed_subset hclK ?_` and prove the remaining obligations.

Introduce `x hx`. Establish `h1 : j x ∈ C₁` using `hx.1`. Establish `h2 : x.1.2 ∈ C₂` using `hx.2`. Use `⟨?_, h2⟩` and prove the remaining obligations. Use `⟨⟨(j x, x.1.2), ⟨h1, h2⟩, hφv x⟩, ⟨ψ (j x, x.1.2), ⟨(j x, x.1.2), ⟨h1, h2⟩, rfl⟩, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hψv x]`. Both sides reduce to the same expression.
-/
theorem jcpt : StdGood → GrpTop → JTop → JCpt := by
  intro hS hG hT F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hGood hB hi hJ
  show IsCompact (cK α j : Set (cover A ν ι))
  have hj : Continuous j := (hT F E R A ε ν r δ α ω ι i j hGood hB hi hJ).1
  obtain ⟨-, -, -, hUT2, -, -, hUK⟩ := hG E R A hGood ι ε
  have hν : Continuous ν := hB.cont

  have hmapν : Continuous (Matrix.GeneralLinearGroup.map (n := ι ⊕ ι) ν) := by
    refine Continuous.units_map _ ?_
    exact Continuous.matrix_map continuous_id hν
  let D : GL (ι ⊕ ι) R := dg ι (Units.map A.i.toMonoidHom δ)
  let M : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → GL (ι ⊕ ι) R :=
    fun h => D⁻¹ * Matrix.GeneralLinearGroup.map ν h * D
  have hM : Continuous M := (continuous_const.mul hmapν).mul continuous_const
  let φ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  let ψ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  have hval : Continuous (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) := continuous_subtype_val
  have hφ : Continuous φ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) :=
      (hval.comp continuous_fst).mul (hM.comp continuous_snd).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _
  have hψ : Continuous ψ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) :=
      (hM.comp continuous_snd).mul (hval.comp continuous_fst).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _

  have hrel : ∀ x : cover A ν ι, ((j x).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • (M x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    fun x => hJ x
  have hφv : ∀ x : cover A ν ι, φ (j x, x.1.2) = (x.1.1 : R) := by
    intro x
    have e : (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • 1 := by
      rw [Units.val_mul, hrel x, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    show (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp
  have hψv : ∀ x : cover A ν ι, ψ (j x, x.1.2) = ((x.1.1⁻¹ : Rˣ) : R) := by
    intro x
    have e0 : (x.1.1 : R) • ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [Units.val_mul, ← Matrix.smul_mul, ← hrel x, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = ((x.1.1⁻¹ : Rˣ) : R) • 1 := by
      rw [← e0, smul_smul, Units.inv_mul, one_smul]
    show ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp

  let C₂ : Set (GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :=
    ((((adStd F).kGL (ι ⊕ ι)).map (MulAut.conj (dg ι α)).toMonoidHom : Subgroup _) : Set _)
  have hC₂ : IsCompact C₂ := by
    have h0 := ((hS F).kcpt (ι ⊕ ι)).image
      (f := fun k => (MulAut.conj (dg ι α)).toMonoidHom k)
      (by
        show Continuous fun k => dg ι α * k * (dg ι α)⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const)
    exact h0
  let C₁ : Set (A.U ε ι) := (A.uK ε ι : Set (A.U ε ι))
  have hC : IsCompact (C₁ ×ˢ C₂) := hUK.prod hC₂
  have hS₁ := hC.image hφ
  have hS₂ : IsCompact (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))) := (hC.image hψ).image MulOpposite.continuous_op
  let B : Set Rˣ := Units.embedProduct R ⁻¹' ((φ '' (C₁ ×ˢ C₂)) ×ˢ (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))))
  have hBc : IsCompact B := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS₁.prod hS₂)

  have hdet : Continuous (Matrix.GeneralLinearGroup.det (n := ι ⊕ ι) (R := NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (g : Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det Units.continuous_val
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        ((g⁻¹ : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
  have hσ : Continuous A.σ := hGood.σcont
  have hUσ : Continuous (Units.map A.σ.toMonoidHom) := Continuous.units_map _ hσ
  have hUν : Continuous (Units.map ν.toMonoidHom) := Continuous.units_map _ hν
  have hcl : IsClosed ((cover A ν ι : Subgroup _) : Set (Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) := by
    have hf : Continuous fun p : Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        p.1 * Units.map A.σ.toMonoidHom p.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det p.2) :=
      (continuous_fst.mul (hUσ.comp continuous_fst)).mul (hUν.comp (hdet.comp continuous_snd))
    exact isClosed_singleton.preimage hf
  have hemb := hcl.isClosedEmbedding_subtypeVal
  have hP : IsCompact ((Subtype.val : cover A ν ι → _) ⁻¹' (B ×ˢ C₂)) :=
    hemb.isCompact_preimage (hBc.prod hC₂)
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hclK : IsClosed (cK α j : Set (cover A ν ι)) :=
    (hUK.isClosed.preimage hj).inter (hC₂.isClosed.preimage hprj)
  refine hP.of_isClosed_subset hclK ?_
  intro x hx
  have h1 : j x ∈ C₁ := hx.1
  have h2 : x.1.2 ∈ C₂ := hx.2
  refine ⟨?_, h2⟩
  refine ⟨⟨(j x, x.1.2), ⟨h1, h2⟩, hφv x⟩, ⟨ψ (j x, x.1.2), ⟨(j x, x.1.2), ⟨h1, h2⟩, rfl⟩, ?_⟩⟩
  rw [hψv x]
  rfl

end GlobalTheory.CompanionTheory.RgEisSo
