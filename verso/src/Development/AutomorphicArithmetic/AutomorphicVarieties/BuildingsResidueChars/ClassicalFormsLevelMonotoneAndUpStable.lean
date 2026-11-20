import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul

open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Introduce `F hF`. Take `⟨⟨s, hs, hu⟩, h2⟩` from `uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) X.I.z X.I.z_mem`. Establish `hsum : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F = (((W.χ ⟨X.I.z, X.I.P_le _ X.I.z_mem⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * X.I.z) F`. Rewrite using `[← (h2 s hs hu).2 F hF.2.1]`. Both sides reduce to the same expression.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum]`. Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F i (X.glob γ * g * (1, u * X.I.z)) = _ *ᵥ F i (g * (1, u * X.I.z))`. Rewrite using `[mul_assoc]`.

Conclude with `hF.1.1 i trivial γ _`. Rewrite using `[(ctrlEq Γ Ga Gp X O Ω W m τ).2.2, hF.1.2 w hw]`. Conclude with `Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ hφ).2 F hF.2)`.
-/
private theorem lower_step {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
    [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) Ω) (φ : X.I.T →* Ωˣ) (U : Subgroup X.Ub) (c : ℕ)
    (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) :
    ∀ F ∈ X.Cl τ W.ξ U (c + 1) φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Cl τ W.ξ U c φ := by
  classical
  intro F hF
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) X.I.z X.I.z_mem
  have hsum : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F =
      (((W.χ ⟨X.I.z, X.I.P_le _ X.I.z_mem⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * X.I.z) F := by
    rw [← (h2 s hs hu).2 F hF.2.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [hsum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)
    · change F i (X.glob γ * g * (1, u * X.I.z)) = _ *ᵥ F i (g * (1, u * X.I.z))
      rw [mul_assoc]
      exact hF.1.1 i trivial γ _
    · rw [(ctrlEq Γ Ga Gp X O Ω W m τ).2.2, hF.1.2 w hw]
  · exact Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ hφ).2 F hF.2)

/- English proof (translation)
Introduce `Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hφ`. Establish `mono : ∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ`. Introduce `c' hc F hF`. Take `⟨h1, h2⟩` from `Submodule.mem_inf.1 hF`. Use `Submodule.mem_inf.2 ⟨h1, ?_⟩` and prove the remaining obligations.

Conclude with `⟨h2.1, fun y hy => h2.2.1 y (X.I.Nm_anti hc hy), h2.2.2⟩`. Establish `step : ∀ e, ∀ F ∈ X.ClO W τ U (c + e + 1) φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U (c + e) φ`. Introduce `e F hF`. Conclude with `lower_step X W _ _ U (c + e) (fun t ht => by simp [hφ t (X.I.Tc_anti (Nat.le_add_right c e) ht)]) F hF`. Establish `down : ∀ e, ∀ F ∈ X.ClO W τ U (c + e) φ, (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ e) F ∈ X.ClO W τ U c φ`.

Introduce `e`. Proceed by induction on `e with`. Consider the case `zero`. Introduce `F hF`. Simplify using `using hF`.

Consider the case `succ e ih`. Introduce `F hF`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (step e F hF)`. Establish `stay : ∀ k, ∀ F ∈ X.ClO W τ U c φ, (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ k) F ∈ X.ClO W τ U c φ`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `F hF`. Simplify using `using hF`.

Consider the case `succ k ih`. Introduce `F hF`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (step 0 F (mono _ (Nat.le_succ c) hF))`. Use `⟨mono, fun F hF => step 0 F (mono _ (Nat.le_succ c) hF), ?_⟩` and prove the remaining obligations.

Introduce `e n hen F hF`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hen`. Rewrite using `[add_comm e k, pow_add, Module.End.mul_apply]`. Conclude with `stay k _ (down e F hF)`.
-/
theorem UpperTheory.classicalForms_level_monotone_and_Up_stable :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ), (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) → (∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ) ∧ (∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ) ∧ ∀ e n : ℕ, e ≤ n → ∀ F ∈ X.ClO W τ U (c + e) φ, (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ n) F ∈ X.ClO W τ U c φ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hφ
  have mono : ∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ := by
    intro c' hc F hF
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hF
    refine Submodule.mem_inf.2 ⟨h1, ?_⟩
    exact ⟨h2.1, fun y hy => h2.2.1 y (X.I.Nm_anti hc hy), h2.2.2⟩
  have step : ∀ e, ∀ F ∈ X.ClO W τ U (c + e + 1) φ,
      X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U (c + e) φ := by
    intro e F hF
    exact lower_step X W _ _ U (c + e)
      (fun t ht => by simp [hφ t (X.I.Tc_anti (Nat.le_add_right c e) ht)]) F hF
  have down : ∀ e, ∀ F ∈ X.ClO W τ U (c + e) φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ e) F ∈ X.ClO W τ U c φ := by
    intro e
    induction e with
    | zero =>
      intro F hF
      simpa using hF
    | succ e ih =>
      intro F hF
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (step e F hF)
  have stay : ∀ k, ∀ F ∈ X.ClO W τ U c φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ k) F ∈ X.ClO W τ U c φ := by
    intro k
    induction k with
    | zero =>
      intro F hF
      simpa using hF
    | succ k ih =>
      intro F hF
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (step 0 F (mono _ (Nat.le_succ c) hF))
  refine ⟨mono, fun F hF => step 0 F (mono _ (Nat.le_succ c) hF), ?_⟩
  intro e n hen F hF
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hen
  rw [add_comm e k, pow_add, Module.End.mul_apply]
  exact stay k _ (down e F hF)
