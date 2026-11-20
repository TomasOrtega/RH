import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem pow_inj {R : Type*} [CommRing R] [_root_.IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (e : a ^ p = b ^ p) : a = b := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (a - b) b
  rw [sub_add_cancel, e, h] at hr
  have h0 : (a - b) ^ p = 0 := by
    simpa using hr.symm
  exact sub_eq_zero.mp (IsReduced.pow_eq_zero h0)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem step {p : ℕ} {A B C : CommRingCat} (u : A ⟶ B) (v : A ⟶ C) (FB : B ⟶ B) (FC : C ⟶ C)
    (r : B ⟶ C) (hB : ∀ x, FB x = x ^ p) (hC : ∀ x, FC x = x ^ p)
    (hU : v ≫ FC = (u ≫ FB) ≫ r) (a : A) : (u ≫ r).hom a ^ p = v.hom a ^ p := by
  have ha := ConcreteCategory.congr_hom hU a
  simp only [ConcreteCategory.comp_apply, hB, hC, map_pow] at ha
  simpa using ha.symm

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
private theorem frob_epi (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X]
    (h : (p : Γ(X, ⊤)) = 0) : Epi (GlobalTheory.VB.frob X p h) := by
  have hV (V : X.Opens) : (p : Γ(X, V)) = 0 := by
    have := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h
    simpa using this
  refine ⟨fun {Y} f g e => ?_⟩
  have hx (x : X) : f x = g x := by
    have := congrArg (fun φ : X ⟶ Y => φ x) e
    simpa using this
  refine Scheme.Hom.ext (by ext x; exact hx x) fun U => ?_
  have hU := Scheme.Hom.congr_app e.symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hU
  ext a
  apply pow_inj (Fact.out : p.Prime) (hV _)
  exact step (p := p) (f.app U) (g.app U) ((GlobalTheory.VB.frob X p h).app (f ⁻¹ᵁ U))
    ((GlobalTheory.VB.frob X p h).app (g ⁻¹ᵁ U)) _ (GlobalTheory.VB.frob_app p h _) (GlobalTheory.VB.frob_app p h _) hU a

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Ord.epi :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0), Epi (GlobalTheory.VB.frob X p h) ∧ ∀ j, Epi (frobN p X h j) := by
  intro p _ X _ h
  have hF := frob_epi p X h
  refine ⟨hF, fun j => ?_⟩
  induction j with
  | zero => exact (inferInstance : Epi (𝟙 X))
  | succ j ih =>
    have : Epi (frobN p X h j) := ih
    exact epi_comp (GlobalTheory.VB.frob X p h) (frobN p X h j)
