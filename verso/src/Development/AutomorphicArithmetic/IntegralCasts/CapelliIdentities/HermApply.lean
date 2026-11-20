import Mathlib

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Yoa6.aux1 :
    SMulCommClass ℂ ℂ ℂ := by
  infer_instance

noncomputable def UpperTheory.Reformulated.B.Yoa6.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.Yoa6.Helpers

private noncomputable def herm {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v))
    (by intro v v' w; simp only [map_add, LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)
    (by intro v w w'; simp only [map_add, LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma herm_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) (v w : V) :
    herm B c v w = c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.Yoa6.Helpers

open UpperTheory.Reformulated.B.Yoa6.Helpers in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Yoa6.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.Yoa6.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ h
  obtain ⟨B, hB0, hBinv⟩ := h
  have hherm : ∀ (c : ℂ) (v w : V), herm B c w v = starRingEnd ℂ (herm B c v w) := by
    intro c v w
    simp only [herm_apply, map_add, map_mul, Complex.conj_conj]
    ring
  have hinv : ∀ (c : ℂ) (g : G) (v w : V), herm B c (ρ g v) (ρ g w) = herm B c v w := by
    intro c g v w
    simp only [herm_apply, hBinv]
  by_cases h1 : herm B 1 = 0
  · refine ⟨herm B Complex.I, ?_, hherm Complex.I, hinv Complex.I⟩
    intro hI
    apply hB0
    ext v w
    have e1 := congrArg (fun f => f v w) h1
    have e2 := congrArg (fun f => f v w) hI
    simp only [herm_apply, LinearMap.zero_apply, map_one, one_mul, Complex.conj_I] at e1 e2
    simp only [LinearMap.zero_apply]
    have : (2 * Complex.I) * B v w = 0 := by
      linear_combination Complex.I * e1 + e2
    rcases mul_eq_zero.mp this with h | h
    · exfalso; simp [Complex.ext_iff] at h
    · exact h
  · exact ⟨herm B 1, h1, hherm 1, hinv 1⟩
