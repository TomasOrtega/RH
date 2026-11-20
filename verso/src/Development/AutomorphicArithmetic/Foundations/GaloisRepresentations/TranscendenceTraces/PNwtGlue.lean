import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `hr : Set.range (z ≫ p) ⊆ Set.range A.u`. Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[pt_eq]`. Conclude with `hz`. Conclude with `⟨A.pb.lift z (IsOpenImmersion.lift A.u (z ≫ p) hr) (IsOpenImmersion.lift_fac _ _ _).symm, A.pb.lift_fst _ _ _⟩`.
-/
private theorem lift_ex {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) [IsOpenImmersion A.u] {Ω : Type} [Field Ω]
    (z : gp Ω ⟶ Z) (hz : pt (z ≫ p) ∈ Set.range A.u) : ∃ l : gp Ω ⟶ A.V, l ≫ A.v = z := by
  have hr : Set.range (z ≫ p) ⊆ Set.range A.u := by
    rintro _ ⟨t, rfl⟩
    rw [pt_eq]
    exact hz
  exact ⟨A.pb.lift z (IsOpenImmersion.lift A.u (z ≫ p) hr) (IsOpenImmersion.lift_fac _ _ _).symm,
    A.pb.lift_fst _ _ _⟩

/- English proof (translation)
Introduce `hAg hLoc hBC hGen Z S p _ h`. Use `choose A w hopen hmem hw using h`. Establish `hl : ∀ (Ω : Type) [Field Ω] (z : gp Ω ⟶ Z), ∃ l : gp Ω ⟶ (A (pt (z ≫ p))).V, l ≫ (A (pt (z ≫ p))).v = z`. Introduce `Ω _ z`. Use `haveI := hopen (pt (z ≫ p))`.

Conclude with `lift_ex _ z (hmem _)`. Use `choose l hlv using hl`. Set `W : Wt Z` to `fun Ω _ _ z => w (pt (z ≫ p)) Ω (l Ω z)`. Establish `hcomap : ∀ t, W.comap (A t).v = w t`. Introduce `t`.

Use function extensionality and compare the values at `Ω _ _ z`. Use `haveI := hopen t`. Use `haveI := hopen (pt ((z ≫ (A t).v) ≫ p))`. Conclude with `hAg p (A _) (A t) (w _) (w t) (hw _) (hw t) Ω (l Ω (z ≫ (A t).v)) z (hlv Ω _)`. Use `⟨W, hLoc p W fun s => ⟨A s, hopen s, hmem s, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcomap s]`. Conclude with `(hw s).1`. Introduce `Ω _ _ z hz set s := pt (z ≫ p) with hs haveI := hopen s`. Establish `hz' : GenPt (pt (l Ω z ≫ (A s).r))`. Rewrite using `[← hGen.2.1 (A s).u, ← pt_comp, Category.assoc, ← (A s).pb.w, ← Category.assoc, hlv Ω z]`.

Conclude with `hz`. Establish `h1` using `(hw s).2 Ω (l Ω z) hz'`. Establish `h2` using `hBC (A s).v (A s).r p (A s).u (A s).pb`. Express the relevant statement in the definitionally equal form `w s Ω (l Ω z) = _`. Rewrite using `[h1, h2]`.

Express the relevant statement in the definitionally equal form `mult p Ω (l Ω z ≫ (A s).v) = _`. Rewrite using `[hlv Ω z]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.nwtGlue_of :
    NwtAgree → WtLocal → MultBC → GenBasic → NwtGlue := by
  intro hAg hLoc hBC hGen Z S p _ h
  choose A w hopen hmem hw using h
  have hl : ∀ (Ω : Type) [Field Ω] (z : gp Ω ⟶ Z), ∃ l : gp Ω ⟶ (A (pt (z ≫ p))).V, l ≫ (A (pt (z ≫ p))).v = z := by
    intro Ω _ z
    haveI := hopen (pt (z ≫ p))
    exact lift_ex _ z (hmem _)
  choose l hlv using hl
  let W : Wt Z := fun Ω _ _ z => w (pt (z ≫ p)) Ω (l Ω z)
  have hcomap : ∀ t, W.comap (A t).v = w t := by
    intro t
    funext Ω _ _ z
    haveI := hopen t
    haveI := hopen (pt ((z ≫ (A t).v) ≫ p))
    exact hAg p (A _) (A t) (w _) (w t) (hw _) (hw t) Ω (l Ω (z ≫ (A t).v)) z (hlv Ω _)
  refine ⟨W, hLoc p W fun s => ⟨A s, hopen s, hmem s, ?_⟩, ?_⟩
  · rw [hcomap s]
    exact (hw s).1
  · intro Ω _ _ z hz
    set s := pt (z ≫ p) with hs
    haveI := hopen s
    have hz' : GenPt (pt (l Ω z ≫ (A s).r)) := by
      rw [← hGen.2.1 (A s).u, ← pt_comp, Category.assoc, ← (A s).pb.w, ← Category.assoc, hlv Ω z]
      exact hz
    have h1 := (hw s).2 Ω (l Ω z) hz'
    have h2 := hBC (A s).v (A s).r p (A s).u (A s).pb
    change w s Ω (l Ω z) = _
    rw [h1, h2]
    change mult p Ω (l Ω z ≫ (A s).v) = _
    rw [hlv Ω z]
