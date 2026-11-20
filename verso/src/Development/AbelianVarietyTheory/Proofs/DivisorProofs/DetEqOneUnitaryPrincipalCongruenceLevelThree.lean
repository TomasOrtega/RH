import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Polynomial

namespace GlobalTheory.UnitaryCongruenceDet

noncomputable section

def ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cc_eq (x : E) : cc x = ccHom E x := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem transpose_mul_mul_map {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γᵀ * G * γ.map (ccHom E) = G := by
  ext i j
  have hs : ∀ k, γ *ᵥ Pi.single k 1 = fun a => γ a k := by
    intro k; funext a; simp [mulVec, dotProduct, Pi.single_apply]
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [herm, cc_eq, hs] at hij
  simp only [mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, hij]
  simp [Pi.single_apply]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem det_mul_cc_det {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γ.det * cc γ.det = 1 := by
  have e := congrArg Matrix.det (transpose_mul_mul_map G γ h)
  have hd : (γ.map (ccHom E)).det = ccHom E γ.det := by rw [RingHom.map_det]; rfl
  rw [det_mul, det_mul, det_transpose, hd] at e
  rw [cc_eq]
  apply mul_right_cancel₀ hG
  linear_combination e

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isIntegral_of_left_eigen {r : ℕ} {Ω : Type} [Field Ω] [Algebra E Ω]
    (C : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hC : ∀ x ∈ Λ, C *ᵥ x ∈ Λ)
    (μ : Ω) (u : Fin r → Ω) (hu : u ≠ 0) (hμ : u ᵥ* C.map (algebraMap E Ω) = μ • u) :
    IsIntegral ℤ μ := by
  classical
  let φ := algebraMap E Ω
  let g : (Fin r → E) →ₗ[E] Ω :=
    { toFun := fun x => u ⬝ᵥ (fun a => φ (x a))
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add]
        rw [← dotProduct_add]; rfl
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, dotProduct,
          Algebra.smul_def]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring }
  let N : Submodule ℤ Ω := (Λ.restrictScalars ℤ).map (g.restrictScalars ℤ)
  have hNfg : N.FG := (Submodule.FG.restrictScalars (R := ℤ) hfg).map _
  have hN : N ≠ ⊥ := by
    intro hN
    apply hu
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker g := by
      rw [Submodule.span_le]
      intro x hx
      have : g x ∈ N := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      rw [hN, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker] at this
    simpa [g, φ, dotProduct, Pi.single_apply, apply_ite] using this
  refine isIntegral_of_smul_mem_submodule N hN hNfg μ ?_
  rintro n hn
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨C *ᵥ x, hC x hx, ?_⟩
  change u ⬝ᵥ (fun a => φ ((C *ᵥ x) a)) = μ • (u ⬝ᵥ fun a => φ (x a))
  have h1 : (fun a => φ ((C *ᵥ x) a)) = C.map φ *ᵥ (fun a => φ (x a)) := by
    funext a; exact RingHom.map_mulVec φ C x a
  rw [h1, dotProduct_mulVec, hμ, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Proceed by induction. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem prod_eq_one_add {Ω : Type} [Field Ω] (M : ℕ) (hM : (M : Ω) ≠ 0) (s : Multiset Ω)
    (hs : ∀ l ∈ s, IsIntegral ℤ ((l - 1) / (M : Ω))) :
    ∃ z : Ω, IsIntegral ℤ z ∧ s.prod = 1 + M * z := by
  have hMint : IsIntegral ℤ (M : Ω) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Ω (M : ℤ)))
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | cons a s ih =>
    obtain ⟨z, hz, hprod⟩ := ih (fun l hl => hs l (Multiset.mem_cons_of_mem hl))
    have ha := hs a (Multiset.mem_cons_self a s)
    set w := (a - 1) / (M : Ω) with hw
    have ha' : a = 1 + M * w := by rw [hw]; field_simp; ring
    refine ⟨w + z + M * w * z, (ha.add hz).add ((hMint.mul ha).mul hz), ?_⟩
    rw [Multiset.prod_cons, hprod, ha']
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r),
    3 ≤ M →
    (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) →
    ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M X hM hΓ γ hγ
  classical
  obtain ⟨⟨hherm, -⟩, hcong⟩ := (hΓ γ).1 hγ
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ X.Λ, A *ᵥ x ∈ X.Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots, IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply isIntegral_of_left_eigen A X.Λ X.Λ_fg X.Λ_span hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _
  have hint : IsIntegral ℤ ((g.det - 1) / (M : E)) := by
    have h1 : φ ((g.det - 1) / (M : E)) = z := by
      rw [map_div₀, map_sub, map_one, map_natCast, hφdet]; field_simp; ring
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 (by change IsIntegral ℤ (φ _); rw [h1]; exact hz)
  have hc := det_mul_cc_det X.Gm g X.Gm_det hherm
  by_contra hne
  have hx : (⟨(g.det - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (g.det - 1) / (M : E) = 0 := congrArg Subtype.val h
    rcases div_eq_zero_iff.1 this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hME h
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((g.det - 1) / M)‖ := hσ
  have h1 : ‖σ g.det‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ g.det)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ g.det - 1‖ ≤ 2 := by
    have := norm_sub_le (σ g.det) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith

end

end GlobalTheory.UnitaryCongruenceDet
