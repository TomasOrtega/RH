import Mathlib

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.SesquilinearFlipConj.aux1 :
    SMulCommClass ℂ ℂ ℂ := by
  infer_instance

noncomputable def UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

private noncomputable def flipConj {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (by intro v₁ v₂ w; simp [map_add])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])
    (by intro v w₁ w₂; simp [map_add])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem flipConj_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (v w : V) :
    flipConj B v w = starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

open UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.SesquilinearFlipConj.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ hS
  obtain ⟨B, hB0, hBinv⟩ := hS
  classical
  by_cases hH : B + flipConj B = 0
  · have hrel : ∀ v w, B v w + starRingEnd ℂ (B w v) = 0 := by
      intro v w
      have := congrArg (fun F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ => F v w) hH
      simpa [flipConj_apply] using this
    refine ⟨Complex.I • B, ?_, ?_, ?_⟩
    · intro h
      apply hB0
      have : (-Complex.I) • (Complex.I • B) = B := by
        rw [smul_smul]; simp
      rw [← this, h, smul_zero]
    · intro v w
      have h1 := hrel v w
      have h2 : starRingEnd ℂ (B v w) = - B w v := by
        have := congrArg (starRingEnd ℂ) h1
        simp at this
        linear_combination this
      simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, h2]
      ring
    · intro g v w
      simp only [LinearMap.smul_apply, smul_eq_mul, hBinv]
  · refine ⟨B + flipConj B, hH, ?_, ?_⟩
    · intro v w
      simp only [LinearMap.add_apply, flipConj_apply, map_add, Complex.conj_conj]
      ring
    · intro g v w
      simp only [LinearMap.add_apply, flipConj_apply, hBinv]
