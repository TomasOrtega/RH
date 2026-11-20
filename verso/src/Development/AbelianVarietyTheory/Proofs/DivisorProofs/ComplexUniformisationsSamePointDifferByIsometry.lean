import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

/- English proof (translation)
Use `choose f hf using hr`. Use `⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩` and prove the remaining obligations. Introduce `x y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_add, hf, hf, hf, map_add, map_add]`.

Introduce `a x`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[RingHom.id_apply, hP', hf, hf, hP, hc]`.
-/
theorem exists_linMap_of_periods {O : Type} [Ring O] {bar : O → O} {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D₁ D₂ : PLat O bar) (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x, P (a • x) = ρ a *ᵥ P x) (hP' : ∀ (a : O) x, P' (a • x) = ρ a *ᵥ P' x)
    (hinj : Function.Injective P') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hr : ∀ x, ∃ y, P' y = h (P x))
    (hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z) :
    ∃ w : D₁.La →ₗ[O] D₂.La, ∀ x, P' (w x) = h (P x) := by
  choose f hf using hr
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro x y
    apply hinj
    rw [map_add, hf, hf, hf, map_add, map_add]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, hP', hf, hf, hP, hc]

/- English proof (translation)
Use `set k : ℕ := (n - m).natAbs + 1 with hkdef`. Establish `hk : 0 < k` using `Nat.succ_pos _`. Take `⟨j, hj⟩` from `Complex.exp_eq_exp_iff_exists_int.mp (H k hk)`. Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`.

Establish `hkc : (k : ℂ) ≠ 0` using `by exact_mod_cast hk.ne'`. Establish `E : ((n - m : ℤ) : ℂ) = ((j * k : ℤ) : ℂ)`. Use `push_cast`. Clear denominators, using `at hj` for the nonvanishing conditions. Take the linear combination `hj`.

Establish `E' : n - m = j * k` using `by exact_mod_cast E`. Establish `hd : (k : ℤ) ∣ n - m` using `⟨j, by rw [E', mul_comm]⟩`. Establish `h0 : n - m = 0` using `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by rw [Int.natAbs_natCast]; omega)`. Use linear arithmetic over natural numbers and integers.
-/
theorem int_eq_of_exp_eq (m n : ℤ)
    (H : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set k : ℕ := (n - m).natAbs + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp (H k hk)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have E : ((n - m : ℤ) : ℂ) = ((j * k : ℤ) : ℂ) := by
    push_cast
    field_simp at hj
    linear_combination hj
  have E' : n - m = j * k := by exact_mod_cast E
  have hd : (k : ℤ) ∣ n - m := ⟨j, by rw [E', mul_comm]⟩
  have h0 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by rw [Int.natAbs_natCast]; omega)
  omega

/- English proof (translation)
Introduce `O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e e' hN U1 U2`. Take `⟨-, hper1, hexp1, hker1, hact1, hweil1, heta1⟩` from `U1`. Take `⟨-, hper2, hexp2, hker2, hact2, hweil2, heta2⟩` from `U2`. Establish `lift` using `fun (e₁ e₂ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) (α : F.A ⟶ F.A) (h1 : IsExp y e₁) (h2 : IsExp y e₂) (hα : IsMonHom α) => GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism F.X F.A g F.ab F.dim y e₁ e₂ α h1 h2 hα`. Take `⟨M, hM, -⟩` from `lift e e' (𝟙 _) hexp1 hexp2 inferInstance`.

Take `⟨M', hM', -⟩` from `lift e' e (𝟙 _) hexp2 hexp1 inferInstance`. Simplify using `only [Category.comp_id] at hM hM'`. Establish `h1 : M'.comp M = LinearMap.id`. Take `⟨K, -, hK⟩` from `lift e e (𝟙 _) hexp1 hexp1 inferInstance`. Rewrite using `[hK (M'.comp M) (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]`.

Establish `h2 : M.comp M' = LinearMap.id`. Take `⟨K, -, hK⟩` from `lift e' e' (𝟙 _) hexp2 hexp2 inferInstance`. Rewrite using `[hK (M.comp M') (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]`. Set `h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)` to `LinearEquiv.ofLinear M M' h2 h1`. Establish `hh : ∀ z, e' (h z) = e z` using `hM`.

Establish `hrange : ∀ z, z ∈ P.range ↔ h z ∈ P'.range` using `fun z => by rw [← hker1, ← hker2, hh]`. Establish `hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z`. Introduce `a z`. Take `⟨K, -, hK⟩` from `lift e e' (F.act a) hexp1 hexp2 (F.hom a)`. Establish `k1` using `hK ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (Matrix.mulVecLin (ρ a))) (fun z => by simp [hh, hact1])`.

Establish `k2` using `hK ((Matrix.mulVecLin (ρ a)).comp (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (fun z => by simp [hact2, hh])`. Use `congrArg (fun f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) => f z) (k1.trans k2.symm)` as an intermediate fact. Simplify using `using this`. Establish `hc' : ∀ (a : O) z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z`. Introduce `a z`.

Apply `h.injective` to reduce the goal to its premises. Rewrite using `[hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Take `⟨w₁, hw₁⟩` from `exists_linMap_of_periods ρ D' D'' P P' hper1.1 hper2.1 hper2.2.1 h (fun x => (AddMonoidHom.mem_range).mp ((hrange (P x)).mp ⟨x, rfl⟩)) hc`. Take `⟨w₂, hw₂⟩` from `exists_linMap_of_periods ρ D'' D' P' P hper2.1 hper1.1 hper1.2.1 h.symm (fun x => (AddMonoidHom.mem_range).mp ((hrange _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact ⟨x, rfl⟩))) hc'`. Set `w : D'.La ≃ₗ[O] D''.La` to `LinearEquiv.ofLinear w₁ w₂ (LinearMap.ext fun x => hper2.2.1 (by simp [hw₁, hw₂])) (LinearMap.ext fun x => hper1.2.1 (by simp [hw₁, hw₂]))`.

Establish `hw : ∀ x, P' (w x) = h (P x)` using `hw₁`. Use `⟨w, h, ⟨?_, ?_⟩, hw, hh⟩` and prove the remaining obligations. Introduce `x x'`. Use `(int_eq_of_exp_eq _ _ fun k hk => ?_)` and prove the remaining obligations. Establish `H1` using `hweil1 k x x' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`.

Establish `H2` using `hweil2 k (w x) (w x') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`. Rewrite `H2` using `[hw, hw, ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hh, hh]`. Use `GlobalTheory.T.weilPairing_complex_value_unique F.X F.A g F.ab F.dim F.L F.isLB y k _ _ _ _ H2 H1` as an intermediate fact. Simplify using `using congrArg Units.val this`. Introduce `a`.

Establish `e0 : e' 0 = 1` using `(hker2 0).mpr (zero_mem _)`. Use `set v := (N : ℂ)⁻¹ • P' (t' a)`. Use `set u := (N : ℂ)⁻¹ • P' (w (t a)) - v`. Establish `huv : e' (u + v) = e' v`. Rewrite using `[sub_add_cancel, hw, ← LinearEquiv.map_smul, hh, ← heta1, heta2]`.

Establish `hu : e' u = 1`. Use `(hexp2.1 (u + v) (-v)).symm` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right, huv, ← hexp2.1, add_neg_cancel, e0]`. Conclude with `this.symm`. Take `⟨x₀, hx₀⟩` from `(hker2 u).mp hu`.

Use `⟨x₀, ?_⟩` and prove the remaining obligations. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Apply `hper2.2.1` to reduce the goal to its premises. Establish `: P' (w (t a)) - P' (t' a) = (N : ℂ) • u`. Simplify using `only [u, v, ← smul_sub, smul_smul, mul_inv_cancel₀ hN', one_smul]`.

Rewrite using `[map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, hx₀, ← this]`. Normalize the expressions using the abelian group laws.
-/
theorem unifAt_cmp : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e e', 0 < N → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y e' → ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w ∧ (∀ x, P' (w x) = h (P x)) ∧ ∀ z, e' (h z) = e z := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e e' hN U1 U2
  obtain ⟨-, hper1, hexp1, hker1, hact1, hweil1, heta1⟩ := U1
  obtain ⟨-, hper2, hexp2, hker2, hact2, hweil2, heta2⟩ := U2
  have lift := fun (e₁ e₂ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) (α : F.A ⟶ F.A) (h1 : IsExp y e₁) (h2 : IsExp y e₂)
    (hα : IsMonHom α) => GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism F.X F.A g F.ab F.dim y e₁ e₂ α h1 h2 hα
  obtain ⟨M, hM, -⟩ := lift e e' (𝟙 _) hexp1 hexp2 inferInstance
  obtain ⟨M', hM', -⟩ := lift e' e (𝟙 _) hexp2 hexp1 inferInstance
  simp only [Category.comp_id] at hM hM'
  have h1 : M'.comp M = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e e (𝟙 _) hexp1 hexp1 inferInstance
    rw [hK (M'.comp M) (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  have h2 : M.comp M' = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e' e' (𝟙 _) hexp2 hexp2 inferInstance
    rw [hK (M.comp M') (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear M M' h2 h1
  have hh : ∀ z, e' (h z) = e z := hM
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ P'.range := fun z => by rw [← hker1, ← hker2, hh]
  have hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    obtain ⟨K, -, hK⟩ := lift e e' (F.act a) hexp1 hexp2 (F.hom a)
    have k1 := hK ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (Matrix.mulVecLin (ρ a)))
      (fun z => by simp [hh, hact1])
    have k2 := hK ((Matrix.mulVecLin (ρ a)).comp (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))
      (fun z => by simp [hact2, hh])
    have := congrArg (fun f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) => f z) (k1.trans k2.symm)
    simpa using this
  have hc' : ∀ (a : O) z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    apply h.injective
    rw [hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨w₁, hw₁⟩ := exists_linMap_of_periods ρ D' D'' P P' hper1.1 hper2.1 hper2.2.1 h
    (fun x => (AddMonoidHom.mem_range).mp ((hrange (P x)).mp ⟨x, rfl⟩)) hc
  obtain ⟨w₂, hw₂⟩ := exists_linMap_of_periods ρ D'' D' P' P hper2.1 hper1.1 hper1.2.1 h.symm
    (fun x => (AddMonoidHom.mem_range).mp ((hrange _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact ⟨x, rfl⟩))) hc'
  let w : D'.La ≃ₗ[O] D''.La := LinearEquiv.ofLinear w₁ w₂
    (LinearMap.ext fun x => hper2.2.1 (by simp [hw₁, hw₂]))
    (LinearMap.ext fun x => hper1.2.1 (by simp [hw₁, hw₂]))
  have hw : ∀ x, P' (w x) = h (P x) := hw₁
  refine ⟨w, h, ⟨?_, ?_⟩, hw, hh⟩
  · intro x x'
    refine (int_eq_of_exp_eq _ _ fun k hk => ?_)
    have H1 := hweil1 k x x' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have H2 := hweil2 k (w x) (w x') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hw, hw, ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hh, hh] at H2
    have := GlobalTheory.T.weilPairing_complex_value_unique F.X F.A g F.ab F.dim F.L F.isLB y k _ _ _ _ H2 H1
    simpa using congrArg Units.val this
  · intro a
    have e0 : e' 0 = 1 := (hker2 0).mpr (zero_mem _)
    set v := (N : ℂ)⁻¹ • P' (t' a)
    set u := (N : ℂ)⁻¹ • P' (w (t a)) - v
    have huv : e' (u + v) = e' v := by
      rw [sub_add_cancel, hw, ← LinearEquiv.map_smul, hh, ← heta1, heta2]
    have hu : e' u = 1 := by
      have := (hexp2.1 (u + v) (-v)).symm
      rw [add_neg_cancel_right, huv, ← hexp2.1, add_neg_cancel, e0] at this
      exact this.symm
    obtain ⟨x₀, hx₀⟩ := (hker2 u).mp hu
    refine ⟨x₀, ?_⟩
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    apply hper2.2.1
    have : P' (w (t a)) - P' (t' a) = (N : ℂ) • u := by
      simp only [u, v, ← smul_sub, smul_smul, mul_inv_cancel₀ hN', one_smul]
    rw [map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, hx₀, ← this]
    abel

end GlobalTheory.PELU
