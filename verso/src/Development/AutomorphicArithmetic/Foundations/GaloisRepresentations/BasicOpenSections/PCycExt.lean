import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
private lemma sp_twist {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (u : gp Ω ⟶ Y) :
    sp a ≫ twist φ Y u = twist φ' Y (sp a ≫ u) := by
  have h : sp a ≫ sp φ = sp φ' ≫ sp a := by
    simp only [UpperTheory.Gal.Mod.sp, ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  change sp a ≫ sp φ ≫ u = sp φ' ≫ sp a ≫ u
  rw [← Category.assoc, h, Category.assoc]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
private lemma sp_iter {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (m : ℕ) (u : gp Ω ⟶ Y) :
    sp a ≫ (twist φ Y)^[m] u = (twist φ' Y)^[m] (sp a ≫ u) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, sp_twist a φ φ' hc]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private lemma pt_sp {Ω Ω' : Type} [Field Ω] [Field Ω'] {Z : Scheme.{0}} (a : Ω →+* Ω') (z : gp Ω ⟶ Z) :
    pt (sp a ≫ z) = pt z := by
  have h : ∀ c : gp Ω', (sp a ≫ z) c = z (sp a c) := fun c => Scheme.Hom.comp_apply _ _ _
  exact (h _).trans (congrArg (fun t : gp Ω => z t) (Subsingleton.elim (α := PrimeSpectrum Ω) _ _))

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
private lemma sum_eq (hF : FibExt) (hWt : TranscendenceTraces.WtPt) {p : ℕ} {Y : Scheme.{0}} (T : crystallineComparison.Corr p Y) (w : Wt T.Z)
    (hw : IsWt T.p w) (m : ℕ) {Ω Ω' : Type} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (x y : gp Ω ⟶ Y) :
    ∑ᶠ z ∈ {z : gp Ω ⟶ T.Z | z ≫ T.p = x ∧ (twist φ Y)^[m] (z ≫ T.r) = y}, w Ω z =
      ∑ᶠ z ∈ {z : gp Ω' ⟶ T.Z | z ≫ T.p = sp a ≫ x ∧ (twist φ' Y)^[m] (z ≫ T.r) = sp a ≫ y}, w Ω' z := by
  haveI : IsFinite T.p := T.fin
  obtain ⟨-, hb, hinj⟩ := hF T.p Ω Ω' a x
  refine finsum_mem_eq_of_bijOn (fun z => sp a ≫ z) ⟨?_, ?_, ?_⟩ ?_
  · rintro z ⟨h1, h2⟩
    refine ⟨by simp only [Category.assoc, h1], ?_⟩
    rw [Category.assoc, ← sp_iter a φ φ' hc, h2]
  · intro z hz z' hz' h
    exact hb.injOn (show z ∈ fib T.p x from hz.1) (show z' ∈ fib T.p x from hz'.1) h
  · rintro z' ⟨h1, h2⟩
    obtain ⟨z, hz, rfl⟩ := hb.surjOn (show z' ∈ fib T.p (sp a ≫ x) from h1)
    refine ⟨z, ⟨hz, hinj _ _ ?_⟩, rfl⟩
    rw [sp_iter a φ φ' hc, ← Category.assoc] at *
    simpa [Category.assoc] using h2
  · intro z _
    exact hWt T.p w hw Ω Ω' z (sp a ≫ z) (pt_sp a z).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Mod.cycExt :
    FibExt → CycExt := by
  intro hF p q n Y T w hw Ω Ω' _ _ _ _ a φ φ' hc x
  have hWt : TranscendenceTraces.WtPt := TranscendenceTraces.all_holds.1.2.2.2.2.1
  have hs := fun (j : Fin (n + 1)) y => sum_eq hF hWt (T j) (w j) (hw j) (n - j) a φ φ' hc x y
  constructor
  · intro h y'
    by_cases hy : ∃ y : gp Ω ⟶ Y, y' = sp a ≫ y
    · obtain ⟨y, rfl⟩ := hy
      have := h y
      simp only [hs] at this
      exact this
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : {z : gp Ω' ⟶ (T j).Z | z ≫ (T j).p = sp a ≫ x ∧ (twist φ' Y)^[n - j] (z ≫ (T j).r) = y'} = ∅ := by
        ext z'
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        haveI : IsFinite (T j).p := (T j).fin
        obtain ⟨z, -, rfl⟩ := (hF (T j).p Ω Ω' a x).2.1.surjOn (show z' ∈ fib (T j).p (sp a ≫ x) from h1)
        refine hy ⟨(twist φ Y)^[n - j] (z ≫ (T j).r), ?_⟩
        rw [sp_iter a φ φ' hc, ← h2, Category.assoc]
      rw [this]
      simp
  · intro h y
    have := h (sp a ≫ y)
    simp only [← hs] at this
    exact this
