import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

noncomputable section

namespace CompanionTheory.RgExh.Hk

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {n : ℕ}

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem iso_symm' {X X' : GMod n} (h : Iso X X') : Iso X' X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun a b x => ?_⟩
  apply e.injective
  rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem iso_trans' {X X' X'' : GMod n} (h : Iso X X') (h' : Iso X' X'') : Iso X X'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun a b x => by simp [he, he']⟩

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_maxGen {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (φ : M ≃ₗ[ℂ] M') (T : Module.End ℂ M) (T' : Module.End ℂ M') (hφ : ∀ x, φ (T x) = T' (φ x)) (μ : ℂ) :
    (T.maxGenEigenspace μ).map (φ : M →ₗ[ℂ] M') = T'.maxGenEigenspace μ := by
  have key : ∀ (k : ℕ) (x : M), φ (((T - μ • (1 : Module.End ℂ M)) ^ k) x) =
      ((T' - μ • (1 : Module.End ℂ M')) ^ k) (φ x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hφ]
  ext y
  rw [Submodule.mem_map_equiv, Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := key k (φ.symm y)
    rw [hk, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply φ.injective
    rw [key, LinearEquiv.apply_symm_apply, hk, map_zero]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem iso_sub' {X X' : GMod n} (φ : X.V ≃ₗ[ℂ] X'.V) (hφ : ∀ a b x, φ (X.E a b x) = X'.E a b (φ x))
    (S : Submodule ℂ X.V) (S' : Submodule ℂ X'.V) (hS : S.map (φ : X.V →ₗ[ℂ] X'.V) = S')
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (h' : ∀ a b, ∀ x ∈ S', X'.E a b x ∈ S') :
    Iso (X.sub S h) (X'.sub S' h') :=
  ⟨φ.ofSubmodules S S' hS, fun a b x => Subtype.ext (hφ a b x.1)⟩

def piIso {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) : (Fin n → X.V) ≃ₗ[ℂ] (Fin n → X'.V) :=
  LinearEquiv.piCongrRight fun _ : Fin n => e

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem piIso_tensVd {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (a b : Fin n) (f : Fin n → X.V) : piIso e (tensVd X.E a b f) = tensVd X'.E a b (piIso e f) := by
  funext d
  by_cases hd : d = b
  · subst hd
    simp [piIso, tensVd, he]
  · simp [piIso, tensVd, he, hd]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem piIso_eeVd {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (f : Fin n → X.V) : piIso e (eeVd X.E f) = eeVd X'.E (piIso e f) := by
  funext a
  simp [piIso, eeVd, he, map_sum]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem iso_back' {Y Y' : GMod n} (hY : Iso Y Y') (z : ℂ)
    (h : ∀ a b, ∀ x ∈ backSub Y z, (tensD Y).E a b x ∈ backSub Y z)
    (h' : ∀ a b, ∀ x ∈ backSub Y' z, (tensD Y').E a b x ∈ backSub Y' z) :
    Iso (back Y z h) (back Y' z h') := by
  obtain ⟨e, he⟩ := hY
  exact iso_sub' (X := tensD Y) (X' := tensD Y') (piIso e) (fun a b f => piIso_tensVd e he a b f) _ _
    (map_maxGen (piIso e) (omD Y) (omD Y') (fun f => piIso_eeVd e he f) _) h h'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem reflect_of' : QdetTens → OmScal → BackStable → DualFacts → Unit → Reflect := by
  intro _ hOm hB _ hU n X X' χ s hX hX' hfree hsimp hiso
  have h1 := hU n X χ s hB hX hfree hsimp (hOm n X χ s hX hsimp)
  have h2 := hU n X' χ s hB hX' hfree hsimp (hOm n X' χ s hX' hsimp)
  exact iso_trans' (iso_symm' h1) (iso_trans' (iso_back' hiso _ _ _) h2)

end CompanionTheory.RgExh.Hk
