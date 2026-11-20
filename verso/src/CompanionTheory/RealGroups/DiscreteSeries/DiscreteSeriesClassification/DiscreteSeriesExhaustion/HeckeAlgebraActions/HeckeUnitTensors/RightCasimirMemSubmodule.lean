import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnitTensors.CommuteLeftRightCasimir

noncomputable section

open Finset Polynomial

namespace CompanionTheory.RgExh.Hk.UnitPf

open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh

variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_of_eig' {M : Type*} [AddCommGroup M] [Module ℂ M] {T : Module.End ℂ M} {μ : ℂ} {f : M}
    (h : T f = μ • f) : f ∈ T.maxGenEigenspace μ :=
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 h)

variable (X) in
def Isub : Submodule ℂ (Fin (m + 1) → Fin (m + 1) → X.V) :=
  ⨆ k : ℕ, LinearMap.range ((y1 X ^ k) ∘ₗ eta X)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_Isub (k : ℕ) (v : X.V) : (y1 X ^ k) (eta X v) ∈ Isub X :=
  Submodule.mem_iSup_of_mem k ⟨v, rfl⟩

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem eta_mem_Isub (v : X.V) : eta X v ∈ Isub X := by
  simpa using mem_Isub (X := X) 0 v

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem right_casimir_mem_submodule {H} (h : H ∈ Isub X) : y2 X H ∈ Isub X := by
  refine Submodule.iSup_induction _ (motive := fun H => y2 X H ∈ Isub X) h ?_ (by simp) ?_
  · rintro k _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← ((commute_left_right_casimir (X := X)).pow_left k).eq, Module.End.mul_apply, right_casimir_eta, map_neg,
      map_add, map_smul]
    refine neg_mem (add_mem ?_ (Submodule.smul_mem _ _ (mem_Isub k v)))
    have := mem_Isub (X := X) (k + 1) v
    rwa [pow_succ, Module.End.mul_apply] at this
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy

variable (X) in

def Om' : Module.End ℂ (Fin (m + 1) → Fin (m + 1) → X.V) := y2 X + (eta X).comp (psi X)

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem Om'_mem_Isub {H} (h : H ∈ Isub X) : Om' X H ∈ Isub X := by
  simp only [Om', LinearMap.add_apply, LinearMap.comp_apply]
  exact add_mem (right_casimir_mem_submodule h) (eta_mem_Isub _)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem Om'_pow_mem_Isub (k : ℕ) {H} (h : H ∈ Isub X) : (Om' X ^ k) H ∈ Isub X := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact Om'_mem_Isub ih

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aeval_mem_Isub (p : ℂ[X]) {H} (h : H ∈ Isub X) : aeval (Om' X) p H ∈ Isub X := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact add_mem hp hq
  | monomial k c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Om'_pow_mem_Isub k h)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem diff_mem_Isub (β : ℂ) (k : ℕ) (H) :
    ((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H ∈ Isub X := by
  induction k generalizing H with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    have e : (Om' X - β • 1) (((Om' X - β • 1) ^ k) H) - (y2 X - β • 1) (((y2 X - β • 1) ^ k) H) =
        (Om' X - β • 1) (((Om' X - β • 1) ^ k) H - ((y2 X - β • 1) ^ k) H) +
          eta X (psi X (((y2 X - β • 1) ^ k) H)) := by
      simp only [map_sub, Om', LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        Module.End.one_apply]
      abel
    rw [e]
    refine add_mem ?_ (eta_mem_Isub _)
    have hm := ih H
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact sub_mem (Om'_mem_Isub hm) (Submodule.smul_mem _ _ hm)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Both sides reduce to the same expression.
-/
theorem left_casimir_pow_apply (k : ℕ) (H : Fin (m + 1) → Fin (m + 1) → X.V) (c : Fin (m + 1)) :
    (y1 X ^ k) H c = (om X ^ k) (H c) := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem Pr_om_pow (hS : ScalChar X χ) (k : ℕ) (f : Fin (m + 1) → X.V) :
    Pr X χ s ((om X ^ k) f) = (χ s - cn (m + 1)) ^ k • Pr X χ s f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, Pr_om, ih, map_smul, om_Pr hS, smul_smul, pow_succ]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Supply the required witnesses or components.
-/
theorem Pr_Isub (hS : ScalChar X χ) {H} (h : H ∈ Isub X) :
    ∃ v : X.V, ∀ c, Pr X χ s (H c) = Pr X χ s (Pi.single c v) := by
  refine Submodule.iSup_induction _ (motive := fun H => ∃ v : X.V, ∀ c, Pr X χ s (H c) = Pr X χ s (Pi.single c v))
    h ?_ ⟨0, by simp⟩ ?_
  · rintro k _ ⟨v, rfl⟩
    refine ⟨(χ s - cn (m + 1)) ^ k • v, fun c => ?_⟩
    simp only [LinearMap.comp_apply, left_casimir_pow_apply, eta_apply, Pr_om_pow hS, Pi.single_smul, map_smul]
  · rintro x y ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v + w, fun c => by rw [Pi.add_apply, map_add, hv, hw, Pi.single_add, map_add]⟩

end CompanionTheory.RgExh.Hk.UnitPf
