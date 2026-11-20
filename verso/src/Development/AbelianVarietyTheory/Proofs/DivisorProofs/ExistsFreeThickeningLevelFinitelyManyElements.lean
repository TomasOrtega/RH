import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeCrystallineThickeningOneElementLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.FreeFin

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}

/- English proof (translation)
Use `⟨hT, fun i ↦ i.elim0, fun S _ a c _ ↦ ⟨a, ⟨Category.id_comp a, fun i ↦ i.elim0⟩, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hg, -⟩`. Rewrite using `[← hg, Category.id_comp]`.
-/
theorem isFree_id (n : ℕ) (T : Thick κ t) (hT : IsLev T.δ n) :
    IsFree n (𝟙 T) (Fin.elim0 : Fin 0 → T.B) := by
  refine ⟨hT, fun i ↦ i.elim0, fun S _ a c _ ↦ ⟨a, ⟨Category.id_comp a, fun i ↦ i.elim0⟩, ?_⟩⟩
  rintro g ⟨hg, -⟩
  rw [← hg, Category.id_comp]

/- English proof (translation)
Take `⟨-, hτ, hU⟩` from `hu`. Take `⟨hF', hτ', hU'⟩` from `hu'`. Use `⟨hF', fun i ↦ Fin.cases (hτ' ()) (fun j ↦ Thick.Hom.mem u' (hτ j)) i, ?_⟩` and prove the remaining obligations. Introduce `S hS a c hc`. Take `⟨g₁, ⟨hg₁a, hg₁c⟩, hg₁u⟩` from `hU S hS a (fun j ↦ c j.succ) (fun j ↦ hc j.succ)`.

Take `⟨g, ⟨hga, hgc⟩, hgu⟩` from `hU' S hS g₁ (fun _ ↦ c 0) (fun _ ↦ hc 0)`. Use `⟨g, ⟨?_, fun i ↦ ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hga, hg₁a]`. Use `Fin.cases ?_ (fun j ↦ ?_) i` and prove the remaining obligations. Simplify using `using hgc ()`.

Simplify using `only [Fin.cons_succ]`. Rewrite using `[← Thick.comp_φ, hga, hg₁c]`. Introduce and unpack `g' ⟨hg'a, hg'c⟩`. Establish `h1 : u' ≫ g' = g₁`. Use `hg₁u _ ⟨by rw [← Category.assoc, hg'a], fun j ↦ ?_⟩` and prove the remaining obligations.

Use `hg'c j.succ` as an intermediate fact. Simplify using `only [Fin.cons_succ] at this`. Rewrite using `[Thick.comp_φ, this]`. Use `hgu _ ⟨h1, fun _ ↦ ?_⟩` and prove the remaining obligations. Simplify using `using hg'c 0`.
-/
theorem isFree_cons (n m : ℕ) {T F F' : Thick κ t} (u : T ⟶ F) (τ : Fin m → F.B) (hu : IsFree n u τ)
    (u' : F ⟶ F') (τ' : Unit → F'.B) (hu' : IsFree n u' τ') :
    IsFree n (u ≫ u') (Fin.cons (τ' ()) (fun i ↦ u'.φ (τ i)) : Fin (m + 1) → F'.B) := by
  obtain ⟨-, hτ, hU⟩ := hu
  obtain ⟨hF', hτ', hU'⟩ := hu'
  refine ⟨hF', fun i ↦ Fin.cases (hτ' ()) (fun j ↦ Thick.Hom.mem u' (hτ j)) i, ?_⟩
  intro S hS a c hc
  obtain ⟨g₁, ⟨hg₁a, hg₁c⟩, hg₁u⟩ := hU S hS a (fun j ↦ c j.succ) (fun j ↦ hc j.succ)
  obtain ⟨g, ⟨hga, hgc⟩, hgu⟩ := hU' S hS g₁ (fun _ ↦ c 0) (fun _ ↦ hc 0)
  refine ⟨g, ⟨?_, fun i ↦ ?_⟩, ?_⟩
  · rw [Category.assoc, hga, hg₁a]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hgc ()
    · simp only [Fin.cons_succ]
      rw [← Thick.comp_φ, hga, hg₁c]
  · rintro g' ⟨hg'a, hg'c⟩
    have h1 : u' ≫ g' = g₁ := by
      refine hg₁u _ ⟨by rw [← Category.assoc, hg'a], fun j ↦ ?_⟩
      have := hg'c j.succ
      simp only [Fin.cons_succ] at this
      rw [Thick.comp_φ, this]
    refine hgu _ ⟨h1, fun _ ↦ ?_⟩
    simpa using hg'c 0

/- English proof (translation)
Introduce `R _ I κ X t n m T hT`. Proceed by induction on `m with`. Consider the case `zero => exact ⟨T, 𝟙 T, Fin.elim0, isFree_id _ T hT, QAtFormal.qAt_ident _ T⟩`. Consider the case `succ m ih`. Take `⟨F, u, τ, hu, hq⟩` from `ih`.

Take `⟨F', u', τ', hu', hq'⟩` from `GlobalTheory.T.exists_freeCrystallineThickening_oneElement_level R I κ X t n F hu.1`. Conclude with `⟨F', u ≫ u', _, isFree_cons (n + 1) m u τ hu u' τ' hu', QAtFormal.qAt_comp _ u u' hq hq'⟩`.
-/
theorem exists_free : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (n m : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) →
    ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Fin m → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  intro R _ I κ X t n m T hT
  induction m with
  | zero => exact ⟨T, 𝟙 T, Fin.elim0, isFree_id _ T hT, QAtFormal.qAt_ident _ T⟩
  | succ m ih =>
    obtain ⟨F, u, τ, hu, hq⟩ := ih
    obtain ⟨F', u', τ', hu', hq'⟩ := GlobalTheory.T.exists_freeCrystallineThickening_oneElement_level R I κ X t n F hu.1
    exact ⟨F', u ≫ u', _, isFree_cons (n + 1) m u τ hu u' τ' hu', QAtFormal.qAt_comp _ u u' hq hq'⟩

end GlobalTheory.PDForm.FreeFin
