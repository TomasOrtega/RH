import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicativeStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.HTLinear

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt v ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (v.appTop.hom s) := by
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem valAt_spec_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (φ : B →+* C)
    (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ v) ⊤ le_top s = φ (valAt v ⊤ le_top s) := by
  rw [valAt_top, valAt_top, Scheme.Hom.comp_appTop]
  exact congrArg (fun f => f.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem valAt_mul [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (y z : Over.mk q ⟶ Γ.G) :
    valAt (B := B) (y * z).left ⊤ le_top s =
      valAt (B := B) y.left ⊤ le_top s * valAt (B := B) z.left ⊤ le_top s := by
  have h := (GlobalTheory.T.character_section_multiplicative R T Γ χ s hs (Over.mk q)).1 y z
  rw [valAt_top, valAt_top, valAt_top, ← map_mul]
  exact congrArg _ h

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem valAt_one [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    valAt (B := B) (1 : Over.mk q ⟶ Γ.G).left ⊤ le_top s = 1 := by
  have h := (GlobalTheory.T.character_section_multiplicative R T Γ χ s hs (Over.mk q)).2
  rw [valAt_top]
  refine (congrArg _ h).trans ?_
  exact map_one _

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem tors_one {Γ : QFGroup R T} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i)
    (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    show ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w])
  have h1 := h.mul Y 1 1 y₀ y₀ rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : y₀ * y₀ = y₀ * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h1
  have h3 : y₀ = 1 := mul_left_cancel h2
  exact congrArg (fun f => f.left) h3

section Tangent

variable {A : Type} [CommRing A] (π : R →+* A)

abbrev qMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp π))

abbrev dMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (dualMap π))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dMap_over : dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = qMap π := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dualMap_epsMul (c : R) :
    (epsMul (π c)).comp (dualMap π) = (dualMap π).comp (epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem epsMul_algebraMap (c : A) : (epsMul c).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem fst_dualMap : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp (dualMap π) =
    π.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem fst_q : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp ((algebraMap A (DualNumber A)).comp π) = π := by
  refine RingHom.ext fun a => ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

def IsTan (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (M : LieModel G x L) (e : L)
    (v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = qMap π ∧ v ≫ i = dMap π ≫ (M.pt e).left

variable {π} {N : ℕ} {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left} {M : LieModel G x L}

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem fst_valAt [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e : L}
    {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v) :
    (valAt v ⊤ le_top s).fst = 1 := by
  let r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom π)
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (DualNumber A)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)
  have hpq : p ≫ qMap π = r := by
    simp only [p, r, qMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_q]
  let y : Over.mk r ⟶ Γ.G := Over.homMk (p ≫ v) (by
    show (p ≫ v) ≫ Γ.G.hom = r
    rw [Category.assoc, hv.1, hpq])
  have hy : y = 1 := by
    apply h.inj (Over.mk r)
    rw [tors_one h]
    have hp : p ≫ dMap π = r ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      simp only [p, r, dMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fst_dualMap]
    let w : Over.mk (r ≫ x) ⟶ Over.mk x := Over.homMk r rfl
    have h1 : (w ≫ (1 : Over.mk x ⟶ G)).left = r ≫ (1 : Over.mk x ⟶ G).left := rfl
    rw [comp_one] at h1
    show (p ≫ v) ≫ i = (1 : Over.mk (r ≫ x) ⟶ G).left
    rw [h1, Category.assoc, hv.2, ← Category.assoc, hp, Category.assoc]
    exact congrArg (r ≫ ·) (M.tan e)
  have h2 : valAt (p ≫ v) ⊤ le_top s = 1 := by
    have h3 := valAt_one Γ χ s hs r
    rw [← hy] at h3
    exact h3
  have h4 := valAt_spec_comp (TrivSqZeroExt.fstHom A A A).toRingHom v s
  exact h4.symm.trans h2

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.
-/
theorem isTan_add [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e e' : L}
    {v v' : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v)
    (hv' : IsTan π Γ i M e' v') :
    ∃ w, IsTan π Γ i M (e + e') w ∧ valAt w ⊤ le_top s = valAt v ⊤ le_top s * valAt v' ⊤ le_top s := by
  let y : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v hv.1
  let z : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v' hv'.1
  let ρ : Over.mk (qMap π ≫ x) ⟶ epsAt x := Over.homMk (dMap π) (by
    show dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x = qMap π ≫ x
    rw [← Category.assoc, dMap_over])
  have hm := h.mul (Over.mk (qMap π)) y z (ρ ≫ M.pt e) (ρ ≫ M.pt e') hv.2.symm hv'.2.symm
  rw [← comp_mul, ← M.add] at hm
  exact ⟨(y * z).left, ⟨Over.w (y * z), hm.symm⟩, valAt_mul Γ χ s hs (qMap π) y z⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem isTan_smul (c : R) {e : L} {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left}
    (hv : IsTan π Γ i M e v) :
    IsTan π Γ i M (c • e) (Spec.map (CommRingCat.ofHom (epsMul (π c))) ≫ v) := by
  constructor
  · rw [Category.assoc, hv.1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, epsMul_algebraMap]
  · rw [Category.assoc, hv.2, M.smul, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_epsMul]

end Tangent

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem snd_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fst_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).fst = a.fst := by
  simp [epsMul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem char_on_tangent_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ s hs
  have hex : ∀ e : L, ∃ v, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e v ∧
      ∀ w, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e w → w = v :=
    fun e => GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
  choose v hv hu using hex
  have hfst : ∀ e, (valAt (v e) ⊤ le_top s).fst = 1 := fun e => fst_valAt h χ s hs (hv e)
  refine ⟨{ toFun := fun e => (valAt (v e) ⊤ le_top s).snd, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro e e'
    obtain ⟨w, hw, hval⟩ := isTan_add h χ s hs (hv e) (hv e')
    rw [← hu _ w hw, hval, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [add_comm]
  · intro c e
    have h1 := hu _ _ (isTan_smul c (hv e))
    rw [← h1, valAt_spec_comp, snd_epsMul]
    simp [Algebra.smul_def]
  · intro e w hw
    rw [hu e w hw]
    ext
    · simp [hfst]
    · simp

end GlobalTheory.CompanionTheory.Ar.BT.HTLinear
