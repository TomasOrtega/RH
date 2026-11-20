import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

open Matrix UpperTheory.V

/- English proof (translation)
Distinguish the cases in `h0 : v 0 = 0`. Establish `h1 : v 1 ≠ 0`. Introduce `h1`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `fin_cases i <;> simp [h0, h1]`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0] (by simp [Matrix.det_fin_two, h1]), ?_⟩` and prove the remaining obligations. Introduce `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩` and prove the remaining obligations.

Introduce `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
private theorem UpperTheory.exists_gl2_first_column {k : Type} [Field k] (v : Fin 2 → k) (hv : v ≠ 0) :
    ∃ h : GL (Fin 2) k, ∀ i, (h : Matrix (Fin 2) (Fin 2) k) i 0 = v i := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0] (by simp [Matrix.det_fin_two, h1]), ?_⟩
    intro i
    fin_cases i <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩
    intro i
    fin_cases i <;> rfl

/- English proof (translation)
Establish `r11 : ∀ s ∈ I, r s 1 1 = ((Ψ s)⁻¹ : kˣ)`. Introduce `s hs`. Establish `hd` using `hdet s hs`. Rewrite `hd` using `[Matrix.det_fin_two, h00 s hs, h10 s hs, mul_zero, sub_zero]`. Rewrite using `[Units.val_inv_eq_inv_val]`.

Conclude with `eq_inv_of_mul_eq_one_right hd`. Take `⟨s0, hs0, ha⟩` from `hex`. Establish `hane : (Ψ s0 : k) - (Ψ s0 : k)⁻¹ ≠ 0`. Introduce `h`. Apply `ha` to reduce the goal to its premises.

Rewrite `h` using `[sub_eq_zero]`. Combine the equalities or inequalities in the displayed calculation. Establish `low : ∀ d ∈ D, r d 1 0 = 0`. Introduce `d hd`. Establish `ht : d⁻¹ * s0 * d ∈ I` using `hn d hd s0 hs0`.

Establish `hΨ : Ψ (d⁻¹ * s0 * d) = Ψ s0`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]`. Establish `hm : r s0 * r d = r d * r (d⁻¹ * s0 * d)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`.

Use `group`. Establish `key` using `congrArg (fun M => M 1 0) hm`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two] at key`. Rewrite `key` using `[h10 s0 hs0, r11 s0 hs0, h10 _ ht, h00 _ ht, hΨ, Units.val_inv_eq_inv_val]`. Establish `: r d 1 0 * ((Ψ s0 : k) - (Ψ s0 : k)⁻¹) = 0`.

Rewrite using `[mul_sub]`. Take the linear combination `-key`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hane`.

Establish `diag : ∀ d ∈ D, ∀ e ∈ D, ∀ i, r (d * e) i i = r d i i * r e i i`. Introduce `d hd e he i`. Rewrite using `[map_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Use `fin_cases i`. Simplify using `[low e he]`.

Simplify using `[low d hd]`. Set `f : Fin 2 → ↥D →* k` to `fun i => { toFun := fun d => r d i i map_one' := by simp map_mul' := fun d e => diag _ d.2 _ e.2 i }`. Use `⟨fun i => (f i).toHomUnits, ?_, ?_⟩` and prove the remaining obligations. Introduce `s`. Use `⟨?_, fun i => rfl⟩` and prove the remaining obligations.

Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `absurd hij (by decide)`. Conclude with `absurd hij (by decide)`. Conclude with `low s s.2`.

Conclude with `absurd hij (by decide)`. Introduce `s hs`. Prove the components needed by the constructor for the conclusion. Use `ext`. Conclude with `h00 _ hs`.

Use `ext`. Conclude with `r11 _ hs`.
-/
private theorem UpperTheory.upper_triangular_characters {Γ k : Type} [Group Γ] [Field k] (D I : Subgroup Γ)
    (r : Γ →* Matrix (Fin 2) (Fin 2) k) (Ψ : Γ →* kˣ)
    (hn : ∀ d ∈ D, ∀ s ∈ I, d⁻¹ * s * d ∈ I)
    (h00 : ∀ s ∈ I, r s 0 0 = Ψ s) (h10 : ∀ s ∈ I, r s 1 0 = 0)
    (hdet : ∀ s ∈ I, (r s).det = 1) (hex : ∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) :
    ∃ κ : Fin 2 → ↥D →* kˣ, (∀ s : ↥D, (∀ i j, j < i → r s i j = 0) ∧ ∀ i, r s i i = (κ i s : k)) ∧
      ∀ s : ↥D, (s : Γ) ∈ I → κ 0 s = Ψ s ∧ κ 1 s = (Ψ s)⁻¹ := by
  have r11 : ∀ s ∈ I, r s 1 1 = ((Ψ s)⁻¹ : kˣ) := by
    intro s hs
    have hd := hdet s hs
    rw [Matrix.det_fin_two, h00 s hs, h10 s hs, mul_zero, sub_zero] at hd
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hd
  obtain ⟨s0, hs0, ha⟩ := hex
  have hane : (Ψ s0 : k) - (Ψ s0 : k)⁻¹ ≠ 0 := by
    intro h
    apply ha
    rw [sub_eq_zero] at h
    calc (Ψ s0 : k) ^ 2 = (Ψ s0 : k) * (Ψ s0 : k)⁻¹ := by rw [sq]; nth_rewrite 2 [h]; rfl
      _ = 1 := mul_inv_cancel₀ (Ψ s0).ne_zero
  have low : ∀ d ∈ D, r d 1 0 = 0 := by
    intro d hd
    have ht : d⁻¹ * s0 * d ∈ I := hn d hd s0 hs0
    have hΨ : Ψ (d⁻¹ * s0 * d) = Ψ s0 := by
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    have hm : r s0 * r d = r d * r (d⁻¹ * s0 * d) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have key := congrArg (fun M => M 1 0) hm
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at key
    rw [h10 s0 hs0, r11 s0 hs0, h10 _ ht, h00 _ ht, hΨ, Units.val_inv_eq_inv_val] at key
    have : r d 1 0 * ((Ψ s0 : k) - (Ψ s0 : k)⁻¹) = 0 := by
      rw [mul_sub]
      linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hane
  have diag : ∀ d ∈ D, ∀ e ∈ D, ∀ i, r (d * e) i i = r d i i * r e i i := by
    intro d hd e he i
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i
    · simp [low e he]
    · simp [low d hd]
  let f : Fin 2 → ↥D →* k := fun i =>
    { toFun := fun d => r d i i
      map_one' := by simp
      map_mul' := fun d e => diag _ d.2 _ e.2 i }
  refine ⟨fun i => (f i).toHomUnits, ?_, ?_⟩
  · intro s
    refine ⟨?_, fun i => rfl⟩
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact low s s.2
    · exact absurd hij (by decide)
  · intro s hs
    constructor
    · ext
      exact h00 _ hs
    · ext
      exact r11 _ hs

/- English proof (translation)
Introduce `Γ k _ _ D I W Ψ v hn hv heig hdet hex`. Take `⟨h, hh⟩` from `UpperTheory.exists_gl2_first_column v hv`. Establish `hcol : (h : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single 0 1 = v`. Rewrite using `[Matrix.mulVec_single_one]`. Use function extensionality and compare the values at `i`.

Conclude with `hh i`. Establish `hinv : ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Set `r : Γ →* Matrix (Fin 2) (Fin 2) k` to `(Units.coeHom _).comp ((MulAut.conj h⁻¹).toMonoidHom.comp W)`. Establish `hr2 : ∀ s, r s = ((h⁻¹ * W s * h⁻¹⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)` using `fun s => rfl`.

Establish `hr : ∀ s, r s = ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (W s : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k)`. Introduce `s`. Rewrite using `[hr2, inv_inv, Units.val_mul, Units.val_mul]`. Establish `hcol' : ∀ s ∈ I, r s *ᵥ Pi.single 0 1 = (Ψ s : k) • (Pi.single 0 1 : Fin 2 → k)`. Introduce `s hs`.

Rewrite using `[hr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, heig s hs, Matrix.mulVec_smul, ← hcol, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Establish `h00 : ∀ s ∈ I, r s 0 0 = Ψ s`. Introduce `s hs`. Use `congrFun (hcol' s hs) 0` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one]`.

Establish `h10 : ∀ s ∈ I, r s 1 0 = 0`. Introduce `s hs`. Use `congrFun (hcol' s hs) 1` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one]`. Establish `hdet' : ∀ s ∈ I, (r s).det = 1`.

Introduce `s hs`. Rewrite using `[hr, Matrix.det_mul, Matrix.det_mul, hdet s hs, mul_one, ← Matrix.det_mul, hinv, Matrix.det_one]`. Take `⟨κ, hκ, hI⟩` from `UpperTheory.upper_triangular_characters D I r Ψ hn h00 h10 hdet' hex`. Conclude with `⟨κ, ⟨h⁻¹, hκ⟩, hI⟩`.
-/
theorem UpperTheory.exists_isFlagOn_of_eigenvector_normal_subgroup :
    ∀ {Γ k : Type} [Group Γ] [Field k] (D I : Subgroup Γ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ) (v : Fin 2 → k), (∀ d ∈ D, ∀ s ∈ I, d⁻¹ * s * d ∈ I) → v ≠ 0 → (∀ s ∈ I, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v = (Ψ s : k) • v) → (∀ s ∈ I, (W s : Matrix (Fin 2) (Fin 2) k).det = 1) → (∃ s ∈ I, (Ψ s : k) ^ 2 ≠ 1) → ∃ κ : Fin 2 → ↥D →* kˣ, Af.IsFlagOn W D κ ∧ ∀ s : ↥D, (s : Γ) ∈ I → κ 0 s = Ψ s ∧ κ 1 s = (Ψ s)⁻¹ := by
  intro Γ k _ _ D I W Ψ v hn hv heig hdet hex
  obtain ⟨h, hh⟩ := UpperTheory.exists_gl2_first_column v hv
  have hcol : (h : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single 0 1 = v := by
    rw [Matrix.mulVec_single_one]
    funext i
    exact hh i
  have hinv : ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let r : Γ →* Matrix (Fin 2) (Fin 2) k := (Units.coeHom _).comp ((MulAut.conj h⁻¹).toMonoidHom.comp W)
  have hr2 : ∀ s, r s = ((h⁻¹ * W s * h⁻¹⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := fun s => rfl
  have hr : ∀ s, r s = ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (W s : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) := by
    intro s
    rw [hr2, inv_inv, Units.val_mul, Units.val_mul]
  have hcol' : ∀ s ∈ I, r s *ᵥ Pi.single 0 1 = (Ψ s : k) • (Pi.single 0 1 : Fin 2 → k) := by
    intro s hs
    rw [hr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, heig s hs, Matrix.mulVec_smul, ← hcol,
      Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h00 : ∀ s ∈ I, r s 0 0 = Ψ s := by
    intro s hs
    have := congrFun (hcol' s hs) 0
    simpa [Matrix.mulVec_single_one] using this
  have h10 : ∀ s ∈ I, r s 1 0 = 0 := by
    intro s hs
    have := congrFun (hcol' s hs) 1
    simpa [Matrix.mulVec_single_one] using this
  have hdet' : ∀ s ∈ I, (r s).det = 1 := by
    intro s hs
    rw [hr, Matrix.det_mul, Matrix.det_mul, hdet s hs, mul_one, ← Matrix.det_mul, hinv, Matrix.det_one]
  obtain ⟨κ, hκ, hI⟩ := UpperTheory.upper_triangular_characters D I r Ψ hn h00 h10 hdet' hex
  exact ⟨κ, ⟨h⁻¹, hκ⟩, hI⟩
