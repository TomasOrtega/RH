import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSecChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatchVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSnBasic
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `O _ Y q hq V hV`. Establish `hlft : LocallyOfFiniteType q` using `inferInstance`. Establish `htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of O)).Opens)` using `isAffineOpen_top _`. Establish `hle : V ≤ q ⁻¹ᵁ ⊤` using `le_top`. Establish `hψ : (q.appLE ⊤ V hle).hom.FiniteType` using `HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q hlft ⟨⊤, htop⟩ ⟨V, hV⟩ hle`.

Set `ι : O →+* Γ(Spec (CommRingCat.of O), ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom`. Establish `hι : Function.Surjective ι` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2`. Set `φ : O →+* Γ(Y, V)` to `(q.appLE ⊤ V hle).hom.comp ι`. Establish `hφ : φ.FiniteType` using `hψ.comp (RingHom.FiniteType.of_surjective ι hι)`. Use `letI : Algebra O Γ(Y, V) := φ.toAlgebra`.

Establish `hft : Algebra.FiniteType O Γ(Y, V)` using `hφ`. Take `⟨s, hs⟩` from `hft.out`. Use `⟨s.card, fun i => (s.equivFin.symm i : Γ(Y, V)), ?_⟩` and prove the remaining obligations. Introduce `R _ f₁ f₂ hpt hgen`. Establish `hcomp : f₁.comp (q.appLE ⊤ V hle).hom = f₂.comp (q.appLE ⊤ V hle).hom`.

Establish `e : ∀ f : Γ(Y, V) →+* R, ptOf hV R f ≫ q = Spec.map (CommRingCat.ofHom (f.comp (q.appLE ⊤ V hle).hom)) ≫ htop.fromSpec`. Introduce `f`. Unfold `ptOf`. Rewrite using `[Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q htop hV hle, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.

Rewrite `hpt` using `[e, e]`. Establish `h1` using `Spec.map_injective ((cancel_mono htop.fromSpec).1 hpt)`. Conclude with `congrArg CommRingCat.Hom.hom h1`. Establish `hO : ∀ a : O, f₁ (algebraMap O Γ(Y, V) a) = f₂ (algebraMap O Γ(Y, V) a)` using `fun a => congrArg (fun g : Γ(Spec (CommRingCat.of O), ⊤) →+* R => g (ι a)) hcomp`. Establish `hx : ∀ a ∈ s, f₁ a = f₂ a` using `fun a ha => by`.

Use `hgen (s.equivFin ⟨a, ha⟩)` as an intermediate fact. Simplify using `using this`. Use extensionality with `a`. Establish `ha : a ∈ Algebra.adjoin O (s : Set Γ(Y, V))` using `by rw [hs]; trivial`. Proceed by induction on `ha using Algebra.adjoin_induction with`.

Consider the case `mem b hb => exact hx b hb`. Consider the case `algebraMap r => exact hO r`. Consider the case `add b c _ _ hb hc => rw [map_add, map_add, hb, hc]`. Consider the case `mul b c _ _ hb hc => rw [map_mul, map_mul, hb, hc]`.
-/
theorem UpperTheory.exists_finite_sections_determining_ringHom_of_smooth :
    ∀ {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)), Smooth q →
        ∀ {V : Y.Opens} (hV : IsAffineOpen V),
        ∃ (k : ℕ) (x : Fin k → Γ(Y, V)), ∀ (R : Type) [CommRing R] (f₁ f₂ : Γ(Y, V) →+* R),
          ptOf hV R f₁ ≫ q = ptOf hV R f₂ ≫ q → (∀ i, f₁ (x i) = f₂ (x i)) → f₁ = f₂ := by
  intro O _ Y q hq V hV
  have hlft : LocallyOfFiniteType q := inferInstance
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of O)).Opens) := isAffineOpen_top _
  have hle : V ≤ q ⁻¹ᵁ ⊤ := le_top
  have hψ : (q.appLE ⊤ V hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q hlft ⟨⊤, htop⟩ ⟨V, hV⟩ hle
  let ι : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hι : Function.Surjective ι :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2
  let φ : O →+* Γ(Y, V) := (q.appLE ⊤ V hle).hom.comp ι
  have hφ : φ.FiniteType := hψ.comp (RingHom.FiniteType.of_surjective ι hι)
  letI : Algebra O Γ(Y, V) := φ.toAlgebra
  have hft : Algebra.FiniteType O Γ(Y, V) := hφ
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s.card, fun i => (s.equivFin.symm i : Γ(Y, V)), ?_⟩
  intro R _ f₁ f₂ hpt hgen
  have hcomp : f₁.comp (q.appLE ⊤ V hle).hom = f₂.comp (q.appLE ⊤ V hle).hom := by
    have e : ∀ f : Γ(Y, V) →+* R, ptOf hV R f ≫ q =
        Spec.map (CommRingCat.ofHom (f.comp (q.appLE ⊤ V hle).hom)) ≫ htop.fromSpec := by
      intro f
      unfold ptOf
      rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q htop hV hle, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    rw [e, e] at hpt
    have h1 := Spec.map_injective ((cancel_mono htop.fromSpec).1 hpt)
    exact congrArg CommRingCat.Hom.hom h1
  have hO : ∀ a : O, f₁ (algebraMap O Γ(Y, V) a) = f₂ (algebraMap O Γ(Y, V) a) := fun a =>
    congrArg (fun g : Γ(Spec (CommRingCat.of O), ⊤) →+* R => g (ι a)) hcomp
  have hx : ∀ a ∈ s, f₁ a = f₂ a := fun a ha => by
    have := hgen (s.equivFin ⟨a, ha⟩)
    simpa using this
  ext a
  have ha : a ∈ Algebra.adjoin O (s : Set Γ(Y, V)) := by rw [hs]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem b hb => exact hx b hb
  | algebraMap r => exact hO r
  | add b c _ _ hb hc => rw [map_add, map_add, hb, hc]
  | mul b c _ _ hb hc => rw [map_mul, map_mul, hb, hc]
