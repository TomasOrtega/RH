import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace Resolution

inductive IsBlowupSeq {X : Scheme.{0}} : ∀ {X' : Scheme.{0}}, (X' ⟶ X) → Prop

  | id : IsBlowupSeq (𝟙 X)

  | step {X₁ X₂ : Scheme.{0}} {s : X₁ ⟶ X} (J : X₁.IdealSheafData) (π : X₂ ⟶ X₁) :
      IsBlowupSeq s → FinalTheorems.Blowup π J → IsBlowupSeq (π ≫ s)

/- English proof (translation)
Simplify using `using IsBlowupSeq.step J π .id h`.
-/
theorem IsBlowupSeq.single {X X' : Scheme.{0}} (J : X.IdealSheafData) (π : X' ⟶ X) (h : FinalTheorems.Blowup π J) :
    IsBlowupSeq π := by
  simpa using IsBlowupSeq.step J π .id h

/- English proof (translation)
Proceed by induction on `ht with`. Consider the case `id => simpa using hs`. Consider the case `step J π _ h ih => rw [Category.assoc]`. Conclude with `.step J π ih h`.
-/
theorem IsBlowupSeq.comp {X X' X'' : Scheme.{0}} {s : X' ⟶ X} {t : X'' ⟶ X'} (hs : IsBlowupSeq s)
    (ht : IsBlowupSeq t) : IsBlowupSeq (t ≫ s) := by
  induction ht with
  | id => simpa using hs
  | step J π _ h ih => rw [Category.assoc]; exact .step J π ih h

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `id => exact .id`. Consider the case `step J π _ _ _ h ih => exact .step J π ih h`.
-/
theorem IsBlowupSeq.of_smooth {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B : Set Y} {s : Y' ⟶ Y}
    (h : IsSmoothBlowupSeq f B s) : IsBlowupSeq s := by
  induction h with
  | id => exact .id
  | step J π _ _ _ h ih => exact .step J π ih h

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `id => simpa using hg`. Consider the case `@step X₁ X₂ s J π _ hπ ih`. Take `⟨G, b, hb, ⟨N, i, hi, e⟩, -⟩` from `ProjBlowup.exists_blowup (s ≫ g) ih J`. Take `⟨φ, hφ, rfl⟩` from `ProjBlowup.exists_iso_of_blowup J π b hπ hb`.

Conclude with `⟨N, φ ≫ i, inferInstance, by simp [e]⟩`.
-/
theorem IsBlowupSeq.isProjOver {R : Type} [CommRing R] [IsNoetherianRing R] {X X' : Scheme.{0}} {g : X ⟶ Sp R}
    {s : X' ⟶ X} (h : IsBlowupSeq s) (hg : IsProjOver g) : IsProjOver (s ≫ g) := by
  induction h with
  | id => simpa using hg
  | @step X₁ X₂ s J π _ hπ ih =>
    obtain ⟨G, b, hb, ⟨N, i, hi, e⟩, -⟩ := ProjBlowup.exists_blowup (s ≫ g) ih J
    obtain ⟨φ, hφ, rfl⟩ := ProjBlowup.exists_iso_of_blowup J π b hπ hb
    exact ⟨N, φ ≫ i, inferInstance, by simp [e]⟩

end Resolution

open Resolution

def ResolutionCharZero : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (g : X ⟶ Sp k) [LocallyOfFiniteType g],
    QuasiCompact g → IsSeparated g → IsReduced X →
    ∃ (X' : Scheme.{0}) (s : X' ⟶ X),
      IsBlowupSeq s ∧ Smooth (s ≫ g) ∧ IsIso (s ∣_ g.smoothLocus) ∧
        FinalTheorems.Snc (preRed s (g.smoothLocus : Set X)ᶜ g.smoothLocus.isOpen.isClosed_compl)

/- English proof (translation)
Assemble the required witnesses or components as `⟨.id, inferInstance, inferInstance, fun y => sncAt_of_not_mem _ y (fun h => h (g.smoothLocus_eq_top.ge (Set.mem_univ y))) (GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field g y)⟩`.
-/
theorem Resolution.conclusion_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) [Smooth g] :
    IsBlowupSeq (𝟙 X) ∧ Smooth (𝟙 X ≫ g) ∧ IsIso (𝟙 X ∣_ g.smoothLocus) ∧
      FinalTheorems.Snc (preRed (𝟙 X) (g.smoothLocus : Set X)ᶜ g.smoothLocus.isOpen.isClosed_compl) :=
  ⟨.id, inferInstance, inferInstance, fun y => sncAt_of_not_mem _ y
    (fun h => h (g.smoothLocus_eq_top.ge (Set.mem_univ y))) (GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field g y)⟩

/- English proof (translation)
Establish `hp : IsProper g`. Take `⟨N, i, hi, rfl⟩` from `hg`. Establish `: IsProper (PSpace.str k N)` using `isProper_str k N`. Use `infer_instance`. Take `⟨X', s, h₁, h₂⟩` from `h k X g inferInstance inferInstance inferInstance`.

Conclude with `⟨X', s, h₁, h₁.isProjOver hg, h₂⟩`.
-/
theorem ResolutionCharZero.projective (h : ResolutionCharZero) {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
    (g : X ⟶ Sp k) [LocallyOfFiniteType g] [IsReduced X] (hg : IsProjOver g) :
    ∃ (X' : Scheme.{0}) (s : X' ⟶ X),
      IsBlowupSeq s ∧ IsProjOver (s ≫ g) ∧ Smooth (s ≫ g) ∧ IsIso (s ∣_ g.smoothLocus) ∧
        FinalTheorems.Snc (preRed s (g.smoothLocus : Set X)ᶜ g.smoothLocus.isOpen.isClosed_compl) := by
  have hp : IsProper g := by
    obtain ⟨N, i, hi, rfl⟩ := hg
    have : IsProper (PSpace.str k N) := isProper_str k N
    infer_instance
  obtain ⟨X', s, h₁, h₂⟩ := h k X g inferInstance inferInstance inferInstance
  exact ⟨X', s, h₁, h₁.isProjOver hg, h₂⟩

end GlobalTheory.CompanionTheory.Hypotheses₂
