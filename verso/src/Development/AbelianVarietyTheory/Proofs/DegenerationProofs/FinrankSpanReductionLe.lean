import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmooth
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankSpanResidueLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

namespace ModHilb

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le`. Consider the case `exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le`. Consider the case `(apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le ..)`.
-/
theorem finrank_span_reduction_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K) (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i, f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O) (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | (apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le ..)

/- English proof (translation)
Unfold `hilb`. Establish `: (MvPolynomial.homogeneousSubmodule J k d).map (LinearMap.pi fun v : C => (MvPolynomial.aeval (R` using `k) v.1).toLinearMap) = Submodule.span k (Set.range fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n) := by`. Rewrite using `[MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]`. Rewrite using `[AddMonoidAlgebra.supported_eq_span_single, Submodule.map_span]`. Use `congr 1`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨m, hm, rfl⟩, rfl⟩`. Use `⟨⟨m, hm⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`.

Express the relevant statement in the definitionally equal form `_ = MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k))`. Simplify using `[MvPolynomial.aeval_monomial]`. Introduce and unpack `⟨⟨m, hm⟩, rfl⟩`. Use `⟨_, ⟨m, hm, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`.

Express the relevant statement in the definitionally equal form `MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k)) = _`. Simplify using `[MvPolynomial.aeval_monomial]`. Rewrite using `[this]`.
-/
theorem hilb_eq_finrank_span {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n)) := by
  unfold hilb
  have : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) =
      Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    rw [AddMonoidAlgebra.supported_eq_span_single, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨⟨m, hm⟩, ?_⟩
      funext v
      change _ = MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k))
      simp [MvPolynomial.aeval_monomial]
    · rintro ⟨⟨m, hm⟩, rfl⟩
      refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
      funext v
      change MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k)) = _
      simp [MvPolynomial.aeval_monomial]
  rw [this]

/- English proof (translation)
Introduce `O K J _ _ _ _ _ _ _ C C' h d`. Rewrite using `[hilb_eq_finrank_span, hilb_eq_finrank_span]`. Use `haveI : Finite {m : J →₀ ℕ // m.degree = d} := ((Finsupp.finite_of_degree_le d).subset fun m (hm : m.degree = d) => hm.le).to_subtype`. Apply `finrank_span_reduction_le` to reduce the goal to its premises. Introduce and unpack `⟨v', hv'⟩`.

Take `⟨w, hw, rfl⟩` from `h v' hv'`. Use `⟨⟨_, hw⟩, fun m => m.1.prod fun j n => w j ^ n, fun m => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `[Finsupp.prod]`. Simplify using `[Finsupp.prod]`.
-/
theorem hilb_reduction_le : (∀ (O K J : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Fintype J] (C : Set (J → K)) (C' : Set (J → IsLocalRing.ResidueField O)), (∀ v' ∈ C', ∃ w : J → O, (fun j => algebraMap O K (w j)) ∈ C ∧ v' = fun j => IsLocalRing.residue O (w j)) → ∀ d, hilb C' d ≤ hilb C d) := by
  intro O K J _ _ _ _ _ _ _ C C' h d
  rw [hilb_eq_finrank_span, hilb_eq_finrank_span]
  haveI : Finite {m : J →₀ ℕ // m.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun m (hm : m.degree = d) => hm.le).to_subtype
  apply finrank_span_reduction_le
  rintro ⟨v', hv'⟩
  obtain ⟨w, hw, rfl⟩ := h v' hv'
  refine ⟨⟨_, hw⟩, fun m => m.1.prod fun j n => w j ^ n, fun m => ⟨?_, ?_⟩⟩
  · simp [Finsupp.prod]
  · simp [Finsupp.prod]

end ModHilb

/- English proof (translation)
Introduce `p _ V _ j G _ g N _ X _ q H J _ σ cls m d`. Use `ModHilb.hilb_reduction_le (OO p) (PadicAlgCl p) J _ _ ?_ d` and prove the remaining obligations. Introduce and unpack `v ⟨x, hx, hv⟩`. Establish `hred : Crd H σ (x ≫ m.r) v` using `m.red (Over.homMk x hx) v hv`. Use `haveI := m.smooth`.

Use `haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom`. Take `⟨c, hc, hcx⟩` from `GlobalTheory.ZJ.exists_classical_lift_of_smooth p G.left (Sp V) G.hom (spMap j) (x ≫ m.r) (by`. Rewrite using `[Category.assoc, m.cart.1.w, ← Category.assoc, hx]`. Conclude with `Category.id_comp _)`. Take `⟨w, hw⟩` from `CrdCalc.crd_exists m.isLB σ c`.

Establish `hw' : Crd H σ (x ≫ m.r) (fun i => IsLocalRing.residue (OO p) (w i))`. Rewrite using `[← hcx]`. Conclude with `CrdCalc.crd_map _ hw`. Take `⟨u, hu⟩` from `CrdCalc.crd_unique hw' hred`. Take `⟨u₀, hu₀⟩` from `IsLocalRing.residue_surjective (u : kb p)`.

Establish `hunit : IsUnit u₀`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, hu₀]`. Conclude with `u.ne_zero`. Take `⟨u₁, rfl⟩` from `hunit`. Use `⟨fun i => (u₁ : OO p) * w i, ⟨gPt p ≫ c, by rw [Category.assoc, hc], ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `CrdCalc.crd_map (OO p).subtype (CrdCalc.crd_smul u₁ hw)`. Use function extensionality and compare the values at `i`. Rewrite using `[hu, map_mul, hu₀]`.
-/
theorem Mod.hilb_special_le_generic : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls) (d : ℕ), hilb (cone m.Φ.G.hom (m.Φ.H 1) m.F) d ≤ hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ G.left, a ≫ G.hom = gPt p ≫ spMap j ∧ Crd H σ a w} d := by
  intro p _ V _ j G _ g N _ X _ q H J _ σ cls m d
  refine ModHilb.hilb_reduction_le (OO p) (PadicAlgCl p) J _ _ ?_ d
  rintro v ⟨x, hx, hv⟩
  have hred : Crd H σ (x ≫ m.r) v := m.red (Over.homMk x hx) v hv
  haveI := m.smooth
  haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.ZJ.exists_classical_lift_of_smooth p G.left (Sp V) G.hom (spMap j)
    (x ≫ m.r) (by
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, hx]
      exact Category.id_comp _)
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists m.isLB σ c
  have hw' : Crd H σ (x ≫ m.r) (fun i => IsLocalRing.residue (OO p) (w i)) := by
    rw [← hcx]
    exact CrdCalc.crd_map _ hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw' hred
  obtain ⟨u₀, hu₀⟩ := IsLocalRing.residue_surjective (u : kb p)
  have hunit : IsUnit u₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu₀]
    exact u.ne_zero
  obtain ⟨u₁, rfl⟩ := hunit
  refine ⟨fun i => (u₁ : OO p) * w i, ⟨gPt p ≫ c, by rw [Category.assoc, hc], ?_⟩, ?_⟩
  · exact CrdCalc.crd_map (OO p).subtype (CrdCalc.crd_smul u₁ hw)
  · funext i
    rw [hu, map_mul, hu₀]

end GlobalTheory.ZH
