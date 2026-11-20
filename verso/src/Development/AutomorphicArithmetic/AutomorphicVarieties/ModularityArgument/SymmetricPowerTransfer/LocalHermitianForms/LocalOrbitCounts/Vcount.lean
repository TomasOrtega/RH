import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.IntDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WCard

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Establish an intermediate fact. Replace the relevant objects with their definitions. Both sides reduce to the same expression. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Substitute using the available equality. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.vMax : UpperTheory.V.Z.Sym.Loc.VMax := by
  intro O K _ _ _ _ _ Δ τ hl hτ x htr hnm hdisc
  have hg : PK.Gen1 O x := ⟨htr, hnm, hdisc⟩
  letI := mulAct τ
  have hsm : ∀ (t : (Etau K τ)ˣ) (S : Set (Etau K τ)), t • cls τ S = cls τ (PS.ml t S) := by
    intro t S
    exact PS.cls_ml t S
  have hone : ∀ S : Set (Etau K τ), PS.ml 1 S = S := by
    intro S
    ext w
    simp [PS.mem_ml]
  let P : Set (Set (Set (Etau K τ))) :=
    {X | ∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S}
  have hv : vcount O τ x = wcount (Cint O τ) (P.indicator fun _ => (1 : ℂ)) := by
    unfold vcount
    rfl
  have h1 : ∀ (t : (Etau K τ)ˣ), ∀ X ∈ P, t • X ∈ P := by
    rintro t _ ⟨S, hS, hx, rfl⟩
    refine ⟨PS.ml t S, PS.lat_ml hS t, ?_, hsm t S⟩
    intro y hy
    rw [PS.mem_ml] at hy ⊢
    rw [mul_left_comm]
    exact hx _ hy
  have h2 : ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) ⊆ P := by
    intro X hX
    rw [Set.mem_singleton_iff] at hX
    subst hX
    exact ⟨PK.Mx O τ, PK.Gen1.lat hl hg, fun y hy => (PK.Gen1.int hg).mul hy, rfl⟩
  have h4 : ∀ c ∈ Cint O τ, ∀ X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))),
      c • X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) := by
    intro c hc X hX
    rw [Set.mem_singleton_iff] at hX ⊢
    subst hX
    obtain ⟨s, u, hu1, hu2, rfl⟩ := PK.Gen1.cint hl hg hc
    rw [hsm, PS.ml_mul, PK.ml_Mx hu1 hu2, PS.cls_sc]
  have h5 : ∀ X ∈ P, ∃ t : (Etau K τ)ˣ, t • X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) := by
    rintro _ ⟨S, hS, hx, rfl⟩
    obtain ⟨u, hu⟩ := PK.Gen1.princ hl hτ hg hS hx
    have hSu : S = PS.ml u (PK.Mx O τ) := by
      ext w
      rw [PS.mem_ml, hu]
      rfl
    refine ⟨u⁻¹, ?_⟩
    rw [Set.mem_singleton_iff, hsm, hSu, ← PS.ml_mul, inv_mul_cancel, hone]
  have h6 : ∀ (t : (Etau K τ)ˣ), ∀ X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))),
      t • X ∈ ({cls τ (PK.Mx O τ)} : Set (Set (Set (Etau K τ)))) → ∃ c ∈ Cint O τ, c • X = t • X := by
    intro t X hX htX
    refine ⟨1, (Cint O τ).one_mem, ?_⟩
    rw [Set.mem_singleton_iff] at hX htX
    rw [one_smul, htX, hX]
  rw [hv, wCard _ _ (Cint O τ) P _ h1 h2 (Set.finite_singleton _) h4 h5 h6, Set.ncard_singleton, Nat.cast_one]
