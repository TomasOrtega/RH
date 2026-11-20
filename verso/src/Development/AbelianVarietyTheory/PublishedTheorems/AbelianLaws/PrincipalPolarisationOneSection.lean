import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def principalPolarisationOneSection : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1

namespace principalPolarisationOneSection

/- English proof (translation)
Introduce `K _ _ P`. Simplify using `using h K P 1 le_rfl`.
-/
theorem of_h0Field (h : GlobalSectionsRankAlgClosed) : principalPolarisationOneSection := by
  intro K _ _ P
  simpa using h K P 1 le_rfl

/- English proof (translation)
Assume the negation of the conclusion as `hs`. Use `push Not at hs`. Establish `: Subsingleton (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K))))` using `⟨fun a b => (hs a).trans (hs b).symm⟩`. Establish `: Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial`. Establish `h1` using `h K P`.

Rewrite `h1` using `[Module.finrank_zero_of_subsingleton]`. Conclude with `zero_ne_one h1`.
-/
theorem exists_ne_zero (h : principalPolarisationOneSection) (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) :
    ∃ s : SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K))), s ≠ 0 := by
  by_contra hs
  push Not at hs
  have : Subsingleton (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) :=
    ⟨fun a b => (hs a).trans (hs b).symm⟩
  have : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  have h1 := h K P
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

/- English proof (translation)
Establish `: Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial`. Use `set S := Spec (CommRingCat.of K)`. Use `set P := Inh.zeroPolAV S with hP`. Establish `hU : ∀ j, (LPow P.A P.L 1 (baseOver S)).U j = ⊤` using `fun j => top_unique fun x _ => Set.mem_iInter.2 fun _ => trivial`. Establish `hbij : ∀ j, Function.Bijective (liftHom P.A (T` using `baseOver S) ((LPow P.A P.L 1 (baseOver S)).U j)) := by`.

Introduce `j`. Rewrite using `[hU j]`. Establish `: IsIso (fst (baseOver S) P.A)`. Express the relevant statement in the definitionally equal form `IsIso (fst (baseOver S) (𝟙_ (Over S)))`. Rewrite using `[← rightUnitor_hom]`.

Use `infer_instance`. Establish `: IsIso (fst (baseOver S) P.A).left` using `inferInstanceAs (IsIso ((Over.forget S).map (fst (baseOver S) P.A)))`. Establish `h2` using `ConcreteCategory.bijective_of_isIso ((fst (baseOver S) P.A).left.app ⊤)`. Establish `h3 : Function.Bijective (fst (baseOver S) P.A).left.appTop.hom` using `h2`. Simplify `h3` using `[liftHom]`.

Set `one : SecM P.A P.L 1 (baseOver S)` to `⟨fun _ => 1, by`. Introduce `i j`. Use `erw [Inh.linComb_triv_g]`. Simplify using `only [map_one]`. Conclude with `(_root_.mul_one _).symm⟩`.

Set `j₀ : (LPow P.A P.L 1 (baseOver S)).ι` to `fun _ => PUnit.unit`. Establish `hj : ∀ j, j = j₀` using `fun j => funext fun _ => rfl`. Establish `hsm : ∀ r : Γ((baseOver S).left, ⊤), (r • one).1 j₀ = liftHom P.A _ r` using `fun r => _root_.mul_one _`. Establish `hb : Function.Bijective (LinearMap.toSpanSingleton Γ((baseOver S).left, ⊤) _ one)`. Prove the components needed by the constructor for the conclusion.

Introduce `r r' e`. Apply `(hbij j₀).1` to reduce the goal to its premises. Rewrite using `[← hsm, ← hsm]`. Conclude with `congrArg (fun s : SecM P.A P.L 1 (baseOver S) => s.1 j₀) e`. Introduce `s`.

Take `⟨r, hr⟩` from `(hbij j₀).2 (s.1 j₀)`. Use `⟨r, Subtype.ext (funext fun j => ?_)⟩` and prove the remaining obligations. Take `rfl` from `hj j`. Conclude with `(hsm r).trans hr`. Rewrite using `[← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]`.
-/
theorem zero_case (K : Type) [Field K] :
    Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM (Inh.zeroPolAV (Spec (CommRingCat.of K))).A (Inh.zeroPolAV (Spec (CommRingCat.of K))).L 1
        (baseOver (Spec (CommRingCat.of K)))) = 1 := by
  have : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
  set S := Spec (CommRingCat.of K)
  set P := Inh.zeroPolAV S with hP
  have hU : ∀ j, (LPow P.A P.L 1 (baseOver S)).U j = ⊤ := fun j =>
    top_unique fun x _ => Set.mem_iInter.2 fun _ => trivial
  have hbij : ∀ j, Function.Bijective
      (liftHom P.A (T := baseOver S) ((LPow P.A P.L 1 (baseOver S)).U j)) := by
    intro j
    rw [hU j]
    have : IsIso (fst (baseOver S) P.A) := by
      change IsIso (fst (baseOver S) (𝟙_ (Over S)))
      rw [← rightUnitor_hom]; infer_instance
    have : IsIso (fst (baseOver S) P.A).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (fst (baseOver S) P.A)))
    have h2 := ConcreteCategory.bijective_of_isIso ((fst (baseOver S) P.A).left.app ⊤)
    have h3 : Function.Bijective (fst (baseOver S) P.A).left.appTop.hom := h2
    simpa [liftHom] using h3
  let one : SecM P.A P.L 1 (baseOver S) := ⟨fun _ => 1, by
    intro i j
    erw [Inh.linComb_triv_g]; simp only [map_one]; exact (_root_.mul_one _).symm⟩
  let j₀ : (LPow P.A P.L 1 (baseOver S)).ι := fun _ => PUnit.unit
  have hj : ∀ j, j = j₀ := fun j => funext fun _ => rfl
  have hsm : ∀ r : Γ((baseOver S).left, ⊤), (r • one).1 j₀ = liftHom P.A _ r := fun r =>
    _root_.mul_one _
  have hb : Function.Bijective (LinearMap.toSpanSingleton Γ((baseOver S).left, ⊤) _ one) := by
    constructor
    · intro r r' e
      apply (hbij j₀).1
      rw [← hsm, ← hsm]
      exact congrArg (fun s : SecM P.A P.L 1 (baseOver S) => s.1 j₀) e
    · intro s
      obtain ⟨r, hr⟩ := (hbij j₀).2 (s.1 j₀)
      refine ⟨r, Subtype.ext (funext fun j => ?_)⟩
      obtain rfl := hj j
      exact (hsm r).trans hr
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]

end principalPolarisationOneSection

end GlobalTheory.Published

abbrev GlobalTheory.AbLaw.principalPolarisationOneSection : Prop := GlobalTheory.Published.principalPolarisationOneSection

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
example : GlobalTheory.AbLaw.principalPolarisationOneSection ↔ ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1 := Iff.rfl
