import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound

section Lattice

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Introduce `h` and use `valuation_uniformizer_ne_zero F (by rw [h, map_zero])`.
-/
theorem unif_ne_zero : (uniformizer F : F) ≠ 0 := fun h =>
  valuation_uniformizer_ne_zero F (by rw [h, map_zero])

/- English proof (translation)
The claim follows from `pow_ne_zero _ unif_ne_zero`.
-/
theorem unif_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 := pow_ne_zero _ unif_ne_zero

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Establish `hvx : ValuativeRel.valuation F x ≠ 0` using `(Valuation.ne_zero_iff _).mpr hx`. Take `⟨m, hm⟩` from `exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Establish `h1 : ValuativeRel.valuation F (uniformizer F : F) ^ m * ValuativeRel.valuation F x < 1`. Use `mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)` as an intermediate fact. Simplify `this` using `[hvx]`. Rewrite using `[Valuation.mem_integer_iff, map_mul, map_pow]`. Conclude with `h1.le`.
-/
theorem exists_unif_pow_mul_mem (x : F) : ∃ m : ℕ, (uniformizer F : F) ^ m * x ∈ 𝒪[F] := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : ValuativeRel.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, ?_⟩
  have h1 : ValuativeRel.valuation F (uniformizer F : F) ^ m * ValuativeRel.valuation F x < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  rw [Valuation.mem_integer_iff, map_mul, map_pow]
  exact h1.le

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Establish `h1 : (uniformizer F : F) ^ d ∈ 𝒪[F]` using `pow_mem (uniformizer F).2 d`. Use `mul_mem h1 hy` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← pow_add, add_comm d m]`. Then use the resulting hypothesis.
-/
theorem unif_pow_mul_mem_of_le {m m' : ℕ} (h : m ≤ m') {y : F}
    (hy : (uniformizer F : F) ^ m * y ∈ 𝒪[F]) : (uniformizer F : F) ^ m' * y ∈ 𝒪[F] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : (uniformizer F : F) ^ d ∈ 𝒪[F] := pow_mem (uniformizer F).2 d
  have := mul_mem h1 hy
  rwa [← mul_assoc, ← pow_add, add_comm d m] at this

/- English proof (translation)
Consider the cases of `nonempty_fintype ι`. Use `choose f hf using fun p : ι × ι => exists_unif_pow_mul_mem (A p.1 p.2)`. Use `⟨c + Finset.univ.sup f, fun M hM i j => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hM`. Establish `hle : f (i, j) ≤ Finset.univ.sup f + d` using `(Finset.le_sup (f := f) (Finset.mem_univ (i, j))).trans (Nat.le_add_right _ _)`.

Use `⟨_, unif_pow_mul_mem_of_le hle (hf (i, j)), ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← pow_add, add_assoc]`.
-/
theorem exists_div_unif_pow_smul {ι : Type} [Finite ι] (A : Matrix ι ι F) (c : ℕ) :
    ∃ N : ℕ, ∀ M, N ≤ M → Div c ((uniformizer F : F) ^ M • A) := by
  classical
  cases nonempty_fintype ι
  choose f hf using fun p : ι × ι => exists_unif_pow_mul_mem (A p.1 p.2)
  refine ⟨c + Finset.univ.sup f, fun M hM i j => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hle : f (i, j) ≤ Finset.univ.sup f + d :=
    (Finset.le_sup (f := f) (Finset.mem_univ (i, j))).trans (Nat.le_add_right _ _)
  refine ⟨_, unif_pow_mul_mem_of_le hle (hf (i, j)), ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_add, add_assoc]

def scG (m M : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F)
  inv := ((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  val_inv := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]
  inv_val := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]

/- English proof (translation)
Establish `hval : ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F)` using `rfl`. Use extensionality with `x`. Simplify using `only [Set.mem_image, hval, Matrix.smul_mulVec, Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ i`.

Use `hy i` as an intermediate fact. Simplify using `only [pow_zero, one_mul] at this`. Simplify `this` using `[unif_pow_ne_zero M]`. Introduce `hx`. Use `⟨(uniformizer F : F) ^ M • x, fun i => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using hx i`. Rewrite using `[smul_smul, inv_mul_cancel₀ (unif_pow_ne_zero M), one_smul]`.
-/
theorem image_scG_lat (m M : ℕ) :
    (fun x => ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 =
      lat F m M := by
  have hval : ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F) := rfl
  ext x
  simp only [Set.mem_image, hval, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have := hy i
    simp only [pow_zero, one_mul] at this
    simpa [unif_pow_ne_zero M] using this
  · intro hx
    refine ⟨(uniformizer F : F) ^ M • x, fun i => ?_, ?_⟩
    · simpa using hx i
    · rw [smul_smul, inv_mul_cancel₀ (unif_pow_ne_zero M), one_smul]

end Lattice

/- English proof (translation)
Introduce `h0 h3 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B B' hk hI hC g hg u' u`. Establish `H0` using `h0 F μ ψ hψ`. Take `⟨-, -, -, hPP, hT, -⟩` from `h3 F μ ψ hψ n k hk`. Establish `hg1` using `hPP g hg`. Take `⟨t, hdet, hcomm, hlast⟩` from `hT g hg1`.

Establish `hlast'` using `hlast hg`. Use `Measures.metrizableSpace F` as an intermediate fact. Take `⟨T, hTdef⟩ : ∃ T, T = (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F)` from `⟨_, rfl⟩`. Take `⟨Ti, hTidef⟩ : ∃ Ti, Ti = ((t⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F)` from `⟨_, rfl⟩`. Rewrite `hdet`, `hcomm`, `hlast'` using `[← hTdef]`.

Establish `hTTi : ∀ x, T *ᵥ (Ti *ᵥ x) = x` using `fun x => by`. Rewrite using `[Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hTiT : ∀ x, Ti *ᵥ (T *ᵥ x) = x` using `fun x => by`. Rewrite using `[Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Set `h : (Fin (k + 1) → F) → ℂ` to `fun x => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)`.

Establish `hpt : ∀ x, ψ (-x (Fin.last k)) * B (ρ g u') (ρ (col n k x) (ρ g u)) = (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) * h (Ti *ᵥ x)`. Introduce `x`. Establish `e1 : col n k x * g = g * col n k (Ti *ᵥ x)` using `by rw [hcomm, hTTi]`. Establish `e2 : ρ (col n k x) (ρ g u) = ρ g (ρ (col n k (Ti *ᵥ x)) u)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]`.

Establish `e3 : (Ti *ᵥ x) (Fin.last k) = x (Fin.last k)`. Use `hlast' (Ti *ᵥ x)` as an intermediate fact. Rewrite `this` using `[hTTi]`. Conclude with `this.symm`. Rewrite using `[e2, hI.quasi g hg1]`.

Simplify using `only [h, e3]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨M₁, hM₁⟩` from `hC (ρ g u) (ρ g u')`. Take `⟨M₂, hM₂⟩` from `hC u u'`. Take `⟨-, c, hc⟩` from `h4 F μ ψ hψ n V ρ hρ l k B hk hI u u'`.

Take `⟨N, hN⟩` from `exists_div_unif_pow_smul T (c + 1)`. Take `⟨N', hN'⟩` from `exists_div_unif_pow_smul (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (c + 1)`. Take `⟨M, hMM₁, hMN⟩ : ∃ M, M₁ ≤ M ∧ N ≤ M` from `⟨max M₁ N, le_max_left _ _, le_max_right _ _⟩`. Establish `step1 : B' (ρ g u') (ρ g u) = (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) * ∫ x in lat F (k + 1) M, h (Ti *ᵥ x) ∂(Measure.pi fun _ => μ)`. Rewrite using `[hM₁ M hMM₁, ← integral_const_mul]`.

Conclude with `integral_congr_ae (Filter.Eventually.of_forall hpt)`. Establish `hcont : Continuous fun x : Fin (k + 1) → F => Ti *ᵥ x` using `Continuous.matrix_mulVec continuous_const continuous_id`. Establish `hmeas : MeasurableSet ((fun x => Ti *ᵥ x) '' lat F (k + 1) M)` using `(((H0.2 (k + 1)).1 M).1.image hcont).measurableSet`. Establish `step2` using `(H0.2 (k + 1)).2 t ((fun x => Ti *ᵥ x) '' lat F (k + 1) M) (fun x => h (Ti *ᵥ x)) hmeas`. Rewrite `step2` using `[← hTdef, Set.image_image]`.

Simplify using `only [hTTi, hTiT, Set.image_id'] at step2`. Establish `hG : (fun x => (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F) : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0 = (fun x => Ti *ᵥ x) '' lat F (k + 1) M`. Rewrite using `[← image_scG_lat (k + 1) M, Set.image_image]`. Use `Set.image_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← hTidef, Matrix.mulVec_mulVec]`.

Establish `hGdiv : Div (c + 1) (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F)`. Establish `: (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = (uniformizer F : F) ^ M • T`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, hTdef]`. Express the relevant statement in the definitionally equal form `((uniformizer F : F) ^ M • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * _ = _`. Rewrite using `[Matrix.smul_mul, Matrix.one_mul]`.

Rewrite using `[this]`. Conclude with `hN M hMN`. Establish `step3` using `hc _ hGdiv`. Rewrite `step3` using `[hG]`. Take `⟨M', hM'₂, hM'N⟩ : ∃ M', M₂ ≤ M' ∧ N' ≤ M'` from `⟨max M₂ N', le_max_left _ _, le_max_right _ _⟩`.

Establish `hSdiv : Div (c + 1) (((scG (k + 1) M' : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F)` using `hN' M' hM'N`. Establish `step4` using `hc _ hSdiv`. Rewrite `step4` using `[image_scG_lat]`. Establish `step5` using `hM₂ M' hM'₂`. Establish `hmod : (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - k) = (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) * ((Measures.modulus T.det : ℝ) : ℂ)`.

Rewrite using `[hdet, ← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[step1, step2, hmod, mul_assoc]`. Use `congr 2`.

Rewrite using `[step5, step4]`. Conclude with `step3`.
-/
theorem column_average_quasi_invariant : L0 → ColumnsMirabolic → FormCoefficientStability → FormQuasiInvariantMirabolic := by
  intro h0 h3 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B B' hk hI hC g hg u' u
  have H0 := h0 F μ ψ hψ
  obtain ⟨-, -, -, hPP, hT, -⟩ := h3 F μ ψ hψ n k hk
  have hg1 := hPP g hg
  obtain ⟨t, hdet, hcomm, hlast⟩ := hT g hg1
  have hlast' := hlast hg
  have := Measures.metrizableSpace F
  obtain ⟨T, hTdef⟩ : ∃ T, T = (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) := ⟨_, rfl⟩
  obtain ⟨Ti, hTidef⟩ : ∃ Ti, Ti = ((t⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :=
    ⟨_, rfl⟩
  rw [← hTdef] at hdet hcomm hlast'
  have hTTi : ∀ x, T *ᵥ (Ti *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hTiT : ∀ x, Ti *ᵥ (T *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  let h : (Fin (k + 1) → F) → ℂ := fun x => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)
  have hpt : ∀ x, ψ (-x (Fin.last k)) * B (ρ g u') (ρ (col n k x) (ρ g u)) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        h (Ti *ᵥ x) := by
    intro x
    have e1 : col n k x * g = g * col n k (Ti *ᵥ x) := by rw [hcomm, hTTi]
    have e2 : ρ (col n k x) (ρ g u) = ρ g (ρ (col n k (Ti *ᵥ x)) u) := by
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    have e3 : (Ti *ᵥ x) (Fin.last k) = x (Fin.last k) := by
      have := hlast' (Ti *ᵥ x)
      rw [hTTi] at this
      exact this.symm
    rw [e2, hI.quasi g hg1]
    simp only [h, e3]
    ring
  obtain ⟨M₁, hM₁⟩ := hC (ρ g u) (ρ g u')
  obtain ⟨M₂, hM₂⟩ := hC u u'
  obtain ⟨-, c, hc⟩ := h4 F μ ψ hψ n V ρ hρ l k B hk hI u u'
  obtain ⟨N, hN⟩ := exists_div_unif_pow_smul T (c + 1)
  obtain ⟨N', hN'⟩ := exists_div_unif_pow_smul (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (c + 1)

  obtain ⟨M, hMM₁, hMN⟩ : ∃ M, M₁ ≤ M ∧ N ≤ M := ⟨max M₁ N, le_max_left _ _, le_max_right _ _⟩
  have step1 : B' (ρ g u') (ρ g u) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ∫ x in lat F (k + 1) M, h (Ti *ᵥ x) ∂(Measure.pi fun _ => μ) := by
    rw [hM₁ M hMM₁, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hcont : Continuous fun x : Fin (k + 1) → F => Ti *ᵥ x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hmeas : MeasurableSet ((fun x => Ti *ᵥ x) '' lat F (k + 1) M) :=
    (((H0.2 (k + 1)).1 M).1.image hcont).measurableSet
  have step2 := (H0.2 (k + 1)).2 t ((fun x => Ti *ᵥ x) '' lat F (k + 1) M)
    (fun x => h (Ti *ᵥ x)) hmeas
  rw [← hTdef, Set.image_image] at step2
  simp only [hTTi, hTiT, Set.image_id'] at step2

  have hG : (fun x => (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F) : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0 =
      (fun x => Ti *ᵥ x) '' lat F (k + 1) M := by
    rw [← image_scG_lat (k + 1) M, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [Units.val_mul, ← hTidef, Matrix.mulVec_mulVec]
  have hGdiv : Div (c + 1) (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := by
    have : (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) F) = (uniformizer F : F) ^ M • T := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hTdef]
      change ((uniformizer F : F) ^ M • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * _ = _
      rw [Matrix.smul_mul, Matrix.one_mul]
    rw [this]
    exact hN M hMN
  have step3 := hc _ hGdiv
  rw [hG] at step3

  obtain ⟨M', hM'₂, hM'N⟩ : ∃ M', M₂ ≤ M' ∧ N' ≤ M' :=
    ⟨max M₂ N', le_max_left _ _, le_max_right _ _⟩
  have hSdiv : Div (c + 1) (((scG (k + 1) M' : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := hN' M' hM'N
  have step4 := hc _ hSdiv
  rw [image_scG_lat] at step4
  have step5 := hM₂ M' hM'₂
  have hmod : (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - k) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ((Measures.modulus T.det : ℝ) : ℂ) := by
    rw [hdet, ← pow_succ]
    congr 1
    omega
  rw [step1, step2, hmod, mul_assoc]
  congr 2
  rw [step5, step4]
  exact step3

end GlobalTheory.CompanionTheory.JSBound

end
