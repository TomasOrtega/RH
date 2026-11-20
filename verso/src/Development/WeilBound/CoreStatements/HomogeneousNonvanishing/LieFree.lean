import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieB
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Set `_` to `c.toAlgebra`. Set `_` to `u.toAlgebra`. Set `_` to `(u.comp c).toAlgebra`. Establish `: IsScalarTower B A R` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Algebra.IsStandardSmoothOfRelativeDimension g B A` using `hc`.

Establish `: Algebra.IsStandardSmooth B A` using `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g`. Establish `: Nontrivial A` using `u.domain_nontrivial`. Establish `hr` using `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := B) (S := A) g`. Establish `: Module.Finite A (KaehlerDifferential B A)` using `inferInstance`. Set `β : Module.Basis (Fin g) A (KaehlerDifferential B A)` to `Module.finBasisOfFinrankEq A _ (Module.finrank_eq_of_rank_eq hr)`.

Establish `hsm : ∀ (a : A) (r : R), a • r = u a * r` using `fun a r => Algebra.smul_def a r`. Establish `key : ∀ (e : Fin g → R) (w : KaehlerDifferential B A), ∑ i, e i * u (β.repr w i) = β.constr A e w`. Introduce `e w`. Rewrite using `[Module.Basis.constr_apply_fintype]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hsm, mul_comm]; rfl`.

Use `⟨fun i a => u (β.repr (KaehlerDifferential.D B A a) i), fun i a b => by simp, fun i a b => by simp, fun i b => ?_, fun e e' h => ?_, fun δ h1 h2 h3 => ?_⟩` and prove the remaining obligations. Establish `: KaehlerDifferential.D B A (c b) = 0` using `Derivation.map_algebraMap _ b`. Simplify using `[this]`. Establish `h' : β.constr A e = β.constr A e'`. Use `Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)` and prove the remaining obligations.

Simplify `h a` using `[key]`. Conclude with `(β.constr A).injective h'`. Set `D : Derivation B A R` to `Derivation.mk' { toFun := δ map_add' := h1 map_smul' := fun b a => by`. Rewrite using `[Algebra.smul_def, h2, RingHom.id_apply, Algebra.smul_def]`. Establish `: δ (algebraMap B A b) = 0` using `h3 b`.

Rewrite using `[this, mul_zero, add_zero]`. Use `rfl }`. Use the proof step `(fun a b => by simpa [hsm] using h2 a b)`. Use `⟨fun i => D.liftKaehlerDifferential (β i), fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`.

Establish `: β.constr A (fun i => D.liftKaehlerDifferential (β i)) = D.liftKaehlerDifferential` using `β.ext fun i => by simp`. Rewrite using `[this, Derivation.liftKaehlerDifferential_comp_D]`. Both sides reduce to the same expression.
-/
theorem der_coords {B A R : Type} [CommRing B] [CommRing A] [CommRing R] [Nontrivial R] (c : B →+* A) (g : ℕ)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (u : A →+* R) :
    ∃ d : Fin g → A → R, (∀ i a b, d i (a + b) = d i a + d i b) ∧
      (∀ i a b, d i (a * b) = u a * d i b + u b * d i a) ∧ (∀ i b, d i (c b) = 0) ∧
      (∀ e e' : Fin g → R, (∀ a, ∑ i, e i * d i a = ∑ i, e' i * d i a) → e = e') ∧
      ∀ δ : A → R, (∀ a b, δ (a + b) = δ a + δ b) → (∀ a b, δ (a * b) = u a * δ b + u b * δ a) →
        (∀ b, δ (c b) = 0) → ∃ e : Fin g → R, ∀ a, ∑ i, e i * d i a = δ a := by
  classical
  let _ := c.toAlgebra
  let _ := u.toAlgebra
  let _ := (u.comp c).toAlgebra
  have : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsStandardSmoothOfRelativeDimension g B A := hc
  have : Algebra.IsStandardSmooth B A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Nontrivial A := u.domain_nontrivial
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := B) (S := A) g
  have : Module.Finite A (KaehlerDifferential B A) := inferInstance
  let β : Module.Basis (Fin g) A (KaehlerDifferential B A) :=
    Module.finBasisOfFinrankEq A _ (Module.finrank_eq_of_rank_eq hr)
  have hsm : ∀ (a : A) (r : R), a • r = u a * r := fun a r => Algebra.smul_def a r
  have key : ∀ (e : Fin g → R) (w : KaehlerDifferential B A), ∑ i, e i * u (β.repr w i) = β.constr A e w := by
    intro e w
    rw [Module.Basis.constr_apply_fintype]
    exact Finset.sum_congr rfl fun i _ => by rw [hsm, mul_comm]; rfl
  refine ⟨fun i a => u (β.repr (KaehlerDifferential.D B A a) i), fun i a b => by simp, fun i a b => by simp,
    fun i b => ?_, fun e e' h => ?_, fun δ h1 h2 h3 => ?_⟩
  · have : KaehlerDifferential.D B A (c b) = 0 := Derivation.map_algebraMap _ b
    simp [this]
  · have h' : β.constr A e = β.constr A e' := by
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
      simpa [key] using h a
    exact (β.constr A).injective h'
  · let D : Derivation B A R := Derivation.mk'
      { toFun := δ
        map_add' := h1
        map_smul' := fun b a => by
          rw [Algebra.smul_def, h2, RingHom.id_apply, Algebra.smul_def]
          have : δ (algebraMap B A b) = 0 := h3 b
          rw [this, mul_zero, add_zero]; rfl }
      (fun a b => by simpa [hsm] using h2 a b)
    refine ⟨fun i => D.liftKaehlerDifferential (β i), fun a => ?_⟩
    rw [key]
    have : β.constr A (fun i => D.liftKaehlerDifferential (β i)) = D.liftKaehlerDifferential :=
      β.ext fun i => by simp
    rw [this, Derivation.liftKaehlerDifferential_comp_D]
    rfl

/- English proof (translation)
Introduce `S G _ g hG R _ _ x E _ _ M`. Set `t : Spec (CommRingCat.of R) ⟶ G.left` to `(1 : Over.mk x ⟶ G).left`. Take `⟨V, hV, U, hU, hq, hUV, hs⟩` from `hG.exists_isStandardSmoothOfRelativeDimension (t (IsLocalRing.closedPoint R))`. Establish `hrange : Set.range t ⊆ Set.range hU.fromSpec`. Rewrite using `[hU.range_fromSpec]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `(IsLocalRing.specializes_closedPoint y).mem_open (t ⁻¹ᵁ U).isOpen hq`. Set `l` to `IsOpenImmersion.lift hU.fromSpec t hrange`. Establish `hl : spMap (Spec.preimage l).hom = l` using `by simp [spMap]`. Establish `h1 : (1 : Over.mk x ⟶ G).left = spMap (Spec.preimage l).hom ≫ hU.fromSpec`.

Rewrite using `[hl]`. Conclude with `(IsOpenImmersion.lift_fac _ _ _).symm`. Take `⟨d, d1, d2, d3, d4, d5⟩` from `der_coords (G.hom.appLE V U hUV).hom g hs (Spec.preimage l).hom`. Take `⟨M', -⟩` from `PositivityTheory.HtPt.Htat.Lie.exists_lieModel (E := Fin g → R) G U V hU hV hUV R x _ h1 (fun e a => ∑ i, e i * d i a) (fun e a b => by simp only [d1, mul_add, Finset.sum_add_distrib]) (fun e a b => by`. Simplify using `only [d2, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring)`. Use the proof step `(fun e b => by simp only [d3, mul_zero, Finset.sum_const_zero])`. Use the proof step `(fun e e' a => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])`. Use the proof step `(fun c e a => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_assoc _ _ _) d4 d5`. Take `⟨f, -, -⟩` from `GlobalTheory.T.lie_model_existsUnique_equiv S G R x E (Fin g → R) M M'`. Conclude with `⟨Module.Basis.ofEquivFun f⟩`.
-/
theorem lie_free : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  intro S G _ g hG R _ _ x E _ _ M
  let t : Spec (CommRingCat.of R) ⟶ G.left := (1 : Over.mk x ⟶ G).left
  obtain ⟨V, hV, U, hU, hq, hUV, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (t (IsLocalRing.closedPoint R))
  have hrange : Set.range t ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_open (t ⁻¹ᵁ U).isOpen hq
  let l := IsOpenImmersion.lift hU.fromSpec t hrange
  have hl : spMap (Spec.preimage l).hom = l := by simp [spMap]
  have h1 : (1 : Over.mk x ⟶ G).left = spMap (Spec.preimage l).hom ≫ hU.fromSpec := by
    rw [hl]; exact (IsOpenImmersion.lift_fac _ _ _).symm
  obtain ⟨d, d1, d2, d3, d4, d5⟩ := der_coords (G.hom.appLE V U hUV).hom g hs (Spec.preimage l).hom
  obtain ⟨M', -⟩ := PositivityTheory.HtPt.Htat.Lie.exists_lieModel (E := Fin g → R) G U V hU hV hUV R x _ h1
    (fun e a => ∑ i, e i * d i a)
    (fun e a b => by simp only [d1, mul_add, Finset.sum_add_distrib])
    (fun e a b => by
      simp only [d2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun e b => by simp only [d3, mul_zero, Finset.sum_const_zero])
    (fun e e' a => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c e a => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _) d4 d5
  obtain ⟨f, -, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv S G R x E (Fin g → R) M M'
  exact ⟨Module.Basis.ofEquivFun f⟩

end PositivityTheory.UnitarySelfGeneration
