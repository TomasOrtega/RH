import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEquivariantConstantFibreStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Set `e` to `Subgroup.quotientEquivProdOfLE (α := G) h`. Establish `he : ∀ y, (e y).1 = Subgroup.quotientMapOfLE h y`. Introduce `y`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H a => rfl`.

Set `e2 : {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ≃ (H ⧸ D.subgroupOf H)` to `{ toFun := fun y => (e y.1).2 invFun := fun c => ⟨e.symm (z, c), by rw [← he, Equiv.apply_symm_apply]⟩ left_inv := fun y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[Equiv.apply_symm_apply]`. Conclude with `Prod.ext ((he y.1).trans y.2).symm rfl`.

Use `right_inv := fun c => by simp }`. Use `haveI : (D.subgroupOf H).FiniteIndex := ⟨hDH⟩`. Use `⟨Finite.of_equiv _ e2.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr e2]`. Both sides reduce to the same expression.
-/
theorem coset_fibre_card {G : Type} [Group G] (D H : Subgroup G) (h : D ≤ H) (hDH : D.relIndex H ≠ 0)
    (z : G ⧸ H) : Finite {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ∧
      Nat.card {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} = D.relIndex H := by
  let e := Subgroup.quotientEquivProdOfLE (α := G) h
  have he : ∀ y, (e y).1 = Subgroup.quotientMapOfLE h y := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H a => rfl
  let e2 : {y : G ⧸ D // Subgroup.quotientMapOfLE h y = z} ≃ (H ⧸ D.subgroupOf H) :=
    { toFun := fun y => (e y.1).2
      invFun := fun c => ⟨e.symm (z, c), by rw [← he, Equiv.apply_symm_apply]⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply e.injective
        rw [Equiv.apply_symm_apply]
        exact Prod.ext ((he y.1).trans y.2).symm rfl
      right_inv := fun c => by simp }
  haveI : (D.subgroupOf H).FiniteIndex := ⟨hDH⟩
  refine ⟨Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e2]
  rfl

/- English proof (translation)
Introduce `G _ Γ K0`. Set `M : Subgroup G → ℝ≥0∞` to `fun U => ∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ U), ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹`. Establish `hq : ∀ (D H : Subgroup G) (h : D ≤ H), D.relIndex H ≠ 0 → M D = (D.relIndex H : ℝ≥0∞) * M H`. Introduce `D H h hDH`. Establish `e` using `GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ D) (G ⧸ H) (Subgroup.quotientMapOfLE h) Set.univ (D.relIndex H) ?_ (fun _ _ _ => trivial) (fun z _ => coset_fibre_card D H h hDH z) (fun z hz => absurd trivial hz)`.

Simplify using `only [Set.mem_univ, ite_true] at e`. Conclude with `e`. Introduce `g y`. Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H a => rfl`.

Use `⟨M K0, fun X _ x h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hX : (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = M (MulAction.stabilizer G x)`. Establish `e` using `GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ MulAction.stabilizer G x) X (MulAction.ofQuotientStabilizer G x) (MulAction.orbit G x) 1 (fun g y => MulAction.ofQuotientStabilizer_smul G x g y) (fun g z hz => by obtain ⟨a, rfl⟩ := hz; exact ⟨g * a, mul_smul g a x⟩) ?_ …`. Rewrite `e` using `[Nat.cast_one, one_mul]`. Conclude with `e.symm`.

Introduce `z hz`. Establish `hs : Subsingleton {y // MulAction.ofQuotientStabilizer G x y = z}` using `⟨fun a b => Subtype.ext (MulAction.injective_ofQuotientStabilizer G x (a.2.trans b.2.symm))⟩`. Take `⟨a, rfl⟩` from `hz`. Establish `hn : Nonempty {y // MulAction.ofQuotientStabilizer G x y = a • x}` using `⟨⟨(a : G ⧸ MulAction.stabilizer G x), MulAction.ofQuotientStabilizer_mk G x a⟩⟩`. Conclude with `⟨inferInstance, Nat.card_unique⟩`.

Introduce `z hz`. Use `⟨fun y => hz ?_⟩` and prove the remaining obligations. Rewrite using `[← y.2]`. Proceed by induction on `y.1 using QuotientGroup.induction_on with`. Consider the case `H a => exact ⟨a, (MulAction.ofQuotientStabilizer_mk G x a).symm⟩`.

Rewrite using `[hX]`. Use `set U := MulAction.stabilizer G x`. Establish `ha` using `hq (U ⊓ K0) U inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact h1)`. Establish `hb` using `hq (U ⊓ K0) K0 inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact h2)`. Rewrite `ha` using `[Subgroup.inf_relIndex_left]`.

Rewrite `hb` using `[Subgroup.inf_relIndex_right]`. Rewrite `hb` using `[ha]`. Establish `hr : ENNReal.ofReal (invVol K0 U) = (U.relIndex K0 : ℝ≥0∞) / (K0.relIndex U : ℝ≥0∞)`. Rewrite using `[invVol, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h1), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]`. Establish `hA : (K0.relIndex U : ℝ≥0∞) ≠ 0` using `by exact_mod_cast h1`.

Establish `hA' : (K0.relIndex U : ℝ≥0∞) ≠ ⊤` using `ENNReal.natCast_ne_top _`. Rewrite using `[hr, ← mul_div_assoc, ENNReal.eq_div_iff hA hA', mul_comm (M K0), ← hb]`.
-/
theorem mass_orbit_eq : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V₀ : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V₀ * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0
  let M : Subgroup G → ℝ≥0∞ := fun U => ∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ U),
    ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹
  have hq : ∀ (D H : Subgroup G) (h : D ≤ H), D.relIndex H ≠ 0 → M D = (D.relIndex H : ℝ≥0∞) * M H := by
    intro D H h hDH
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ D) (G ⧸ H) (Subgroup.quotientMapOfLE h) Set.univ (D.relIndex H) ?_
      (fun _ _ _ => trivial) (fun z _ => coset_fibre_card D H h hDH z) (fun z hz => absurd trivial hz)
    · simp only [Set.mem_univ, ite_true] at e
      exact e
    · intro g y
      induction y using QuotientGroup.induction_on with
      | H a => rfl
  refine ⟨M K0, fun X _ x h1 h2 => ?_⟩
  have hX : (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) =
      M (MulAction.stabilizer G x) := by
    have e := GlobalTheory.T.orbit_mass_equivariant_constant_fibre Γ (G ⧸ MulAction.stabilizer G x) X (MulAction.ofQuotientStabilizer G x)
      (MulAction.orbit G x) 1 (fun g y => MulAction.ofQuotientStabilizer_smul G x g y)
      (fun g z hz => by obtain ⟨a, rfl⟩ := hz; exact ⟨g * a, mul_smul g a x⟩) ?_ ?_
    · rw [Nat.cast_one, one_mul] at e
      exact e.symm
    · intro z hz
      have hs : Subsingleton {y // MulAction.ofQuotientStabilizer G x y = z} :=
        ⟨fun a b => Subtype.ext (MulAction.injective_ofQuotientStabilizer G x (a.2.trans b.2.symm))⟩
      obtain ⟨a, rfl⟩ := hz
      have hn : Nonempty {y // MulAction.ofQuotientStabilizer G x y = a • x} :=
        ⟨⟨(a : G ⧸ MulAction.stabilizer G x), MulAction.ofQuotientStabilizer_mk G x a⟩⟩
      exact ⟨inferInstance, Nat.card_unique⟩
    · intro z hz
      refine ⟨fun y => hz ?_⟩
      rw [← y.2]
      induction y.1 using QuotientGroup.induction_on with
      | H a => exact ⟨a, (MulAction.ofQuotientStabilizer_mk G x a).symm⟩
  rw [hX]
  set U := MulAction.stabilizer G x
  have ha := hq (U ⊓ K0) U inf_le_left (by rw [Subgroup.inf_relIndex_left]; exact h1)
  have hb := hq (U ⊓ K0) K0 inf_le_right (by rw [Subgroup.inf_relIndex_right]; exact h2)
  rw [Subgroup.inf_relIndex_left] at ha
  rw [Subgroup.inf_relIndex_right] at hb
  rw [ha] at hb
  have hr : ENNReal.ofReal (invVol K0 U) = (U.relIndex K0 : ℝ≥0∞) / (K0.relIndex U : ℝ≥0∞) := by
    rw [invVol, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h1),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  have hA : (K0.relIndex U : ℝ≥0∞) ≠ 0 := by exact_mod_cast h1
  have hA' : (K0.relIndex U : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hr, ← mul_div_assoc, ENNReal.eq_div_iff hA hA', mul_comm (M K0), ← hb]

end GlobalTheory.HL
