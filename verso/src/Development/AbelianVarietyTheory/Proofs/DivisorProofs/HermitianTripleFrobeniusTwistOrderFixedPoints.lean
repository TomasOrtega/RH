import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdIterateTwistedConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigKQFixedEqInclK
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Both sides reduce to the same expression.
-/
theorem iterate_fst (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    ((⇑(sigG G r))^[k] g).1 = (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Both sides reduce to the same expression.
-/
theorem iterate_snd (G : HTGroup p) (r k : ℕ) (g : Gr G r) (i : Fin G.m) :
    ((⇑(sigG G r))^[k] g).2 i = (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem unramifiedExtFrobeniusGL_one_iterate_degree (r : ℕ) (hr : 0 < r) (g : GL (Fin 1) (Qr p r)) :
    (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin 1), ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g).val i j
      = (⇑(frobQ p r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, GlobalTheory.LKResNrmConj.frobQ_iterate_self p r hr]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inclK_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    Function.Injective (inclK p K r) :=
  Algebra.TensorProduct.includeLeft_injective (S := ℚ_[p]) (algebraMap ℚ_[p] (Qr p r)).injective

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem iterate_self (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [iterate_fst, unramifiedExtFrobeniusGL_one_iterate_degree r hr]
  · rw [iterate_snd, GlobalTheory.LKResNrmConj.sigRes_iterate_self p (G.Fw i) G.n r hr]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fix_incl (G : HTGroup p) (r : ℕ) (γ : Gp G) : sigG G r (inclG G r γ) = inclG G r γ := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change frobQ p r (((inclG G r γ).1 : Matrix (Fin 1) (Fin 1) (Qr p r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe]
    by_cases h : a = b
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h]
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change sigKQ p (G.Fw i) r (((inclG G r γ).2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_snd, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact sigKQ_apply_inclK p (G.Fw i) r _

end GlobalTheory.LKMid.SigIter

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem incl_injective (G : HTGroup p) (r : ℕ) : Function.Injective (inclG G r) := by
  intro γ γ' h
  have h1 := congrArg (fun g : Gr G r => ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) h
  have h2 := fun i (a b : Fin G.n) =>
    congrArg (fun g : Gr G r => ((g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) h
  simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
    MonoidHom.coe_coe, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.diagonal_apply_eq] at h1 h2
  refine Prod.ext (Units.ext ((algebraMap ℚ_[p] (Qr p r)).injective h1)) (funext fun i => ?_)
  exact Units.ext (Matrix.ext fun a b => inclK_injective (G.Fw i) r (h2 i a b))

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem fixed_mem_range (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) (hg : sigG G r g = g) :
    g ∈ (inclG G r).range := by
  have hf : frobQ p r ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) = (g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 :=
    congrArg (fun x : Gr G r => ((x.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) hg
  obtain ⟨c, hc⟩ := frobQ_fixed_mem p r hr _ hf
  have hdet1 : IsUnit ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) := by
    have := Matrix.isUnits_det_units g.1
    rwa [Matrix.det_fin_one] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_isUnit_zero (hc ▸ hdet1)
  have hfix : ∀ i (a b : Fin G.n), ∃ x : G.Fw i,
      inclK p (G.Fw i) r x = (g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b := fun i a b =>
    sigKQ_fixed_eq_inclK p (G.Fw i) r hr _
      (congrArg (fun x : Gr G r => ((x.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) hg)
  choose M hM using hfix
  have hmap : ∀ i, (Matrix.of (M i)).map (inclK p (G.Fw i) r) = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
    fun i => Matrix.ext fun a b => hM i a b
  have hdet : ∀ i, (Matrix.of (M i)).det ≠ 0 := by
    intro i h0
    have e := RingHom.map_det (inclK p (G.Fw i) r).toRingHom (Matrix.of (M i))
    rw [h0, map_zero, RingHom.mapMatrix_apply] at e
    have e' : (Matrix.of (M i)).map (inclK p (G.Fw i) r).toRingHom = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
      hmap i
    rw [e'] at e
    have hu := Matrix.isUnits_det_units (g.2 i)
    rw [← e] at hu
    have hsub : Subsingleton (KQ p (G.Fw i) r) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
    have := inclK_injective (G.Fw i) r (Subsingleton.elim (inclK p (G.Fw i) r 1) (inclK p (G.Fw i) r 0))
    exact one_ne_zero this
  refine ⟨(Units.mk0 c hc0, fun i => GeneralLinearGroup.mkOfDetNeZero (Matrix.of (M i)) (hdet i)), ?_⟩
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (funext fun i => Units.ext ?_)
  · have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe, Matrix.diagonal_apply_eq, Units.val_mk0]
    exact hc
  · rw [← hmap i]
    rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
    (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧
      Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range :=
  fun _ _ G r hr => ⟨iterate_self G r hr, fix_incl G r, incl_injective G r, fixed_mem_range G r hr⟩

end GlobalTheory.LKMid.SigIter

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := GlobalTheory.LKMid.SigIter.main
