import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HypLineAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo FlagModelAlt

namespace FlagGenericPointScale

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {R : Type} [CommRing R]

def scaleHom (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) :
    MvPolynomial (GV D) R →ₐ[R] MvPolynomial (GV D) R :=
  aeval (Sum.elim (fun β => C (s β) * X (Sum.inl β)) (fun g => X (Sum.inr g)))

omit [DecidableEq Ψ] in
/- English proof (translation)
Simplify using `[scaleHom]`.
-/
theorem scaleHom_X_inl (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) (β) :
    scaleHom D s (X (Sum.inl β)) = C (s β) * X (Sum.inl β) := by
  simp [scaleHom]

omit [DecidableEq Ψ] in
/- English proof (translation)
Simplify using `[scaleHom]`.
-/
theorem scaleHom_X_inr (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) (g) :
    scaleHom D s (X (Sum.inr g)) = X (Sum.inr g) := by
  simp [scaleHom]

omit [DecidableEq Ψ] in
/- English proof (translation)
Simplify using `[scaleHom]`.
-/
theorem scaleHom_C (D : ComponentData II Ψ K ι Ω E) (s : K ⊕ (Ψ × Fin (D.N - 1)) → R) (c : R) :
    scaleHom D s (C c) = C c := by
  simp [scaleHom]

omit [DecidableEq Ψ] in

/- English proof (translation)
Establish `: (scaleHom D s).comp (scaleHom D t) = AlgHom.id R _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `(β | g)`. Simplify using `only [AlgHom.comp_apply, scaleHom_X_inl, map_mul, scaleHom_C, AlgHom.id_apply]`. Rewrite using `[← mul_assoc, ← C_mul, h, C_1, one_mul]`.

Simplify using `[scaleHom_X_inr]`. Conclude with `AlgHom.congr_fun this p`.
-/
theorem scaleHom_scaleHom (D : ComponentData II Ψ K ι Ω E) (s t : K ⊕ (Ψ × Fin (D.N - 1)) → R)
    (h : ∀ β, t β * s β = 1) (p : MvPolynomial (GV D) R) : scaleHom D s (scaleHom D t p) = p := by
  have : (scaleHom D s).comp (scaleHom D t) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    rintro (β | g)
    · simp only [AlgHom.comp_apply, scaleHom_X_inl, map_mul, scaleHom_C, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, h, C_1, one_mul]
    · simp [scaleHom_X_inr]
  exact AlgHom.congr_fun this p

omit [DecidableEq Ψ] in

/- English proof (translation)
Break down `j with ⟨k | q, t⟩` into its components or cases. Use `show scaleHom D α (X (Sum.inl (Sum.inl k)) * C (x ⟨k, t⟩)) = X (Sum.inl (Sum.inl k)) * C (α (Sum.inl k) * x ⟨k, t⟩)`. Rewrite using `[map_mul, scaleHom_X_inl, scaleHom_C, C_mul, mul_assoc]`. Conclude with `mul_left_comm _ _ _`. Use `show scaleHom D α (X (Sum.inl (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N, (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)) = X (Sum.inl (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N, (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (α ( …`.

Establish `hs : (∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N, (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (α (Sum.inr q) * V q t c) : MvPolynomial (GV D) R) = C (α (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N, (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[C_mul, mul_left_comm]`. Establish `hterm : ∀ c : Fin ((q.2 : ℕ) + 1) → Fin D.N, scaleHom D α ((∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)) = (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)` using `fun c => by`.

Rewrite using `[map_mul, map_prod, scaleHom_C]`. Simplify using `only [scaleHom_X_inr]`. Rewrite using `[hs, map_mul, scaleHom_X_inl, map_sum, Finset.sum_congr rfl fun c _ => hterm c, mul_assoc]`. Conclude with `mul_left_comm _ _ _`.
-/
theorem scaleHom_genPtR {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (x : (Σ k, ι k) → R)
    (V : WedgeVals Pl R) (α : K ⊕ (Ψ × Fin (D.N - 1)) → R) (j : Σ k, Pl.ιY k) :
    scaleHom D α (genPtR Pl x V j) =
      genPtR Pl (fun p => α (Sum.inl p.1) * x p) (fun q m c => α (Sum.inr q) * V q m c) j := by
  rcases j with ⟨k | q, t⟩
  · show scaleHom D α (X (Sum.inl (Sum.inl k)) * C (x ⟨k, t⟩)) =
      X (Sum.inl (Sum.inl k)) * C (α (Sum.inl k) * x ⟨k, t⟩)
    rw [map_mul, scaleHom_X_inl, scaleHom_C, C_mul, mul_assoc]
    exact mul_left_comm _ _ _
  · show scaleHom D α (X (Sum.inl (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)) =
      X (Sum.inl (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (α (Sum.inr q) * V q t c)
    have hs : (∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (α (Sum.inr q) * V q t c) :
          MvPolynomial (GV D) R) =
        C (α (Sum.inr q)) * ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
          (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [C_mul, mul_left_comm]
    have hterm : ∀ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        scaleHom D α ((∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c)) =
          (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q t c) := fun c => by
      rw [map_mul, map_prod, scaleHom_C]
      simp only [scaleHom_X_inr]
    rw [hs, map_mul, scaleHom_X_inl, map_sum, Finset.sum_congr rfl fun c _ => hterm c, mul_assoc]
    exact mul_left_comm _ _ _

end FlagGenericPointScale

open FlagGenericPointScale in

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl R _ x V α hα F`. Establish `key : aeval (genPtR Pl (fun p => α (Sum.inl p.1) * x p) (fun q m c => α (Sum.inr q) * V q m c)) F = scaleHom D α (aeval (genPtR Pl x V) F)`. Use `comp_aeval_apply (f := genPtR Pl x V) ((scaleHom D α).restrictScalars ℤ) F` as an intermediate fact. Rewrite `this` using `[AlgHom.restrictScalars_apply]`. Rewrite using `[this]`.

Conclude with `congrArg (fun f => aeval f F) (funext fun j => by`. Rewrite using `[AlgHom.restrictScalars_apply, scaleHom_genPtR])`. Rewrite using `[key]`. Set `t : K ⊕ (Ψ × Fin (D.N - 1)) → R` to `fun β => ((hα β).unit⁻¹ : Rˣ)`. Establish `ht : ∀ β, α β * t β = 1` using `fun β => (hα β).mul_val_inv`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite using `[← scaleHom_scaleHom D t α ht (aeval (genPtR Pl x V) F), h0, map_zero]`. Introduce `h0`. Rewrite using `[h0, map_zero]`.
-/
theorem FlagGenericPointScale.proof : FlagGenericPointScale.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl R _ x V α hα F
  have key : aeval (genPtR Pl (fun p => α (Sum.inl p.1) * x p) (fun q m c => α (Sum.inr q) * V q m c)) F =
      scaleHom D α (aeval (genPtR Pl x V) F) := by
    have := comp_aeval_apply (f := genPtR Pl x V) ((scaleHom D α).restrictScalars ℤ) F
    rw [AlgHom.restrictScalars_apply] at this
    rw [this]
    exact congrArg (fun f => aeval f F) (funext fun j => by
      rw [AlgHom.restrictScalars_apply, scaleHom_genPtR])
  rw [key]
  let t : K ⊕ (Ψ × Fin (D.N - 1)) → R := fun β => ((hα β).unit⁻¹ : Rˣ)
  have ht : ∀ β, α β * t β = 1 := fun β => (hα β).mul_val_inv
  constructor
  · intro h0
    rw [← scaleHom_scaleHom D t α ht (aeval (genPtR Pl x V) F), h0, map_zero]
  · intro h0
    rw [h0, map_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree
