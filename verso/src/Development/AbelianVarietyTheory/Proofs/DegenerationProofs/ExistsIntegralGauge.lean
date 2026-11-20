import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralGauge

/- English proof (translation)
Establish `h : ψ (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i)` using `by rw [hL.1]; trivial`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Conclude with `⟨j, fun w _ => (IsLocalRing.specializes_closedPoint (R := V) w).mem_open (ψ ⁻¹ᵁ L.U j).isOpen hj⟩`.
-/
theorem exists_chart_local {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (ψ : Sp V ⟶ X) : ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j := by
  have h : ψ (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, fun w _ => (IsLocalRing.specializes_closedPoint (R := V) w).mem_open (ψ ⁻¹ᵁ L.U j).isOpen hj⟩

/- English proof (translation)
Use `haveI := D.P.isAb.proper`. Establish `hE : ValuativeCriterion.Existence D.P.A.hom`. Establish `h : UniversallyClosed D.P.A.hom` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Set `f : R →+* S` to `((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS`. Set `Q : ValuativeCommSq D.P.A.hom` to `{ R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f), commSq := ⟨by`. Use `(Over.w x).trans ?_` and prove the remaining obligations. Use `show Spec.map _ ≫ Spec.map _ = _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`.

Use the proof step `rfl⟩ }`. Take `⟨⟨l, h1, -⟩⟩` from `hE Q`. Conclude with `⟨l, h1⟩`.
-/
theorem exists_extension {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  haveI := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let f : R →+* S := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS
  let Q : ValuativeCommSq D.P.A.hom :=
    { R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f),
      commSq := ⟨by
        refine (Over.w x).trans ?_
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, h1, -⟩⟩ := hE Q
  exact ⟨l, h1⟩

/- English proof (translation)
Establish `key : ∀ ψ : Sp F ⟶ D.P.A.left, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U j ∧ ((∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ) → ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U j)` using `fun ψ => by`. Distinguish the cases in `h : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ`. Take `⟨x₀, rfl⟩` from `h`. Take `⟨j, hj⟩` from `exists_chart_local D.P.isLB x₀`. Conclude with `⟨j, fun w _ => hj (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, hj⟩⟩`.

Take `⟨j, hj⟩` from `exists_chart_local D.P.isLB ψ`. Conclude with `⟨j, hj, fun h' => (h h').elim⟩`. Use `choose J h₁ h₂ using key`. Conclude with `⟨J, h₁, fun x => h₂ x.left (exists_extension D S hS x)⟩`.
-/
theorem exists_integral_gauge (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) :
    ∃ J : (Sp F ⟶ D.P.A.left) → D.P.L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) ∧ ∀ x : TF (R := R) F ⟶ D.P.A,
      ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (J x.left) := by
  have key : ∀ ψ : Sp F ⟶ D.P.A.left, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U j ∧
      ((∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ) →
        ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB x₀
      exact ⟨j, fun w _ => hj (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, hj⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB ψ
      exact ⟨j, hj, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, fun x => h₂ x.left (exists_extension D S hS x)⟩

end GlobalTheory.IntegralGauge
