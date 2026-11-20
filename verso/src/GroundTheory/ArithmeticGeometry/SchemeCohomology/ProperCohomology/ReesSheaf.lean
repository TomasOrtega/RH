import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

instance sectionsModuleA (A : Type u) [CommRing A] {X : Scheme.{u}} [X.Over (Spec (.of A))]
    (F : X.Modules) (V : X.Opens) : Module A Γ(F, V) :=
  Module.compHom _ (algV X V)

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V : X.Opens}

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma sectionsModuleA_smul (a : A) (m : Γ(F, V)) : a • m = algV X V a • m := rfl

variable (A) in

def toPolyA (q : PolynomialModule Γ(X, V) Γ(F, V)) : PolynomialModule A Γ(F, V) :=
  PolynomialModule.ofCoeff A q.coeff

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma coeff_toPolyA (q : PolynomialModule Γ(X, V) Γ(F, V)) (n : ℕ) :
    (toPolyA A q).coeff n = q.coeff n := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma toPolyA_add (q q' : PolynomialModule Γ(X, V) Γ(F, V)) :
    toPolyA A (q + q') = toPolyA A q + toPolyA A q' := rfl

/- English proof (translation)
Introduce `q q' h` and use `PolynomialModule.coeff_injective (R := Γ(X, V)) (show q.coeff = q'.coeff from congrArg (fun p : PolynomialModule A Γ(F, V) => p.coeff) h)`.
-/
lemma toPolyA_injective : Function.Injective (toPolyA A (F := F) (V := V)) := fun q q' h =>
  PolynomialModule.coeff_injective (R := Γ(X, V))
    (show q.coeff = q'.coeff from congrArg (fun p : PolynomialModule A Γ(F, V) => p.coeff) h)

/- English proof (translation)
Rewrite `hc` using `[← Ideal.map_pow]`. Establish `hstab : ∀ (d : Γ(X, V)) {k : ℕ} {x : Γ(F, V)}, x ∈ I ^ k • (⊤ : Submodule A Γ(F, V)) → d • x ∈ I ^ k • (⊤ : Submodule A Γ(F, V))`. Introduce `d k x hx`. Use `Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)` and prove the remaining obligations. Establish `: d • (a • y) = a • (d • y)`.

Rewrite using `[sectionsModuleA_smul, sectionsModuleA_smul, smul_smul, smul_smul, mul_comm]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul ha Submodule.mem_top`. Rewrite using `[smul_add]`. Conclude with `add_mem hy hy'`.

Use `Submodule.span_induction (p := fun c _ => c • m ∈ I ^ (i + j) • (⊤ : Submodule A Γ(F, V))) ?_ ?_ ?_ ?_ hc` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Rewrite using `[← sectionsModuleA_smul, pow_add, mul_smul]`. Conclude with `Submodule.smul_mem_smul ha hm`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[add_smul]`. Conclude with `add_mem hx hy`. Introduce `d x _ hx`. Rewrite using `[smul_eq_mul, mul_smul]`.

Conclude with `hstab d hx`.
-/
lemma smul_mem_pow_smul {i j : ℕ} {c : Γ(X, V)} (hc : c ∈ (I.map (algV X V)) ^ i)
    {m : Γ(F, V)} (hm : m ∈ I ^ j • (⊤ : Submodule A Γ(F, V))) :
    c • m ∈ I ^ (i + j) • (⊤ : Submodule A Γ(F, V)) := by
  rw [← Ideal.map_pow] at hc
  have hstab : ∀ (d : Γ(X, V)) {k : ℕ} {x : Γ(F, V)}, x ∈ I ^ k • (⊤ : Submodule A Γ(F, V)) →
      d • x ∈ I ^ k • (⊤ : Submodule A Γ(F, V)) := by
    intro d k x hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
    · have : d • (a • y) = a • (d • y) := by
        rw [sectionsModuleA_smul, sectionsModuleA_smul, smul_smul, smul_smul, mul_comm]
      rw [this]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [smul_add]
      exact add_mem hy hy'
  refine Submodule.span_induction (p := fun c _ => c • m ∈ I ^ (i + j) • (⊤ : Submodule A Γ(F, V)))
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨a, ha, rfl⟩
    rw [← sectionsModuleA_smul, pow_add, mul_smul]
    exact Submodule.smul_mem_smul ha hm
  · simp
  · intro x y _ _ hx hy
    rw [add_smul]
    exact add_mem hx hy
  · intro d x _ hx
    rw [smul_eq_mul, mul_smul]
    exact hstab d hx

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_toPolyA, PolynomialModule.smul_apply]`. Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Establish `hx : x.1 + x.2 = n` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hx`. Rewrite using `[← hx]`.

Conclude with `smul_mem_pow_smul (hp x.1) (hq x.2)`.
-/
lemma toPolyA_smul_mem {p : Polynomial Γ(X, V)} (hp : p ∈ reesCoeffRing I X V)
    {q : PolynomialModule Γ(X, V) Γ(F, V)} (hq : toPolyA A q ∈ reesSubmodule I Γ(F, V)) :
    toPolyA A (p • q) ∈ reesSubmodule I Γ(F, V) := by
  intro n
  rw [coeff_toPolyA, PolynomialModule.smul_apply]
  refine Submodule.sum_mem _ fun x hx => ?_
  have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  rw [← hx]
  exact smul_mem_pow_smul (hp x.1) (hq x.2)

/- English proof (translation)
Apply `PolynomialModule.coeff_injective` to reduce the goal to its premises. Use extensionality with `n`. Express the relevant statement in the definitionally equal form `(((r : Polynomial A).map (algV X V)) • q).coeff n = ((r : Polynomial A) • toPolyA A q).coeff n`. Rewrite using `[PolynomialModule.smul_apply, PolynomialModule.smul_apply]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.coeff_map, coeff_toPolyA]`. Both sides reduce to the same expression.
-/
lemma toPolyA_map_smul (r : reesAlgebra I) (q : PolynomialModule Γ(X, V) Γ(F, V)) :
    toPolyA A (((r : Polynomial A).map (algV X V)) • q) = r • toPolyA A q := by
  apply PolynomialModule.coeff_injective
  ext n
  change (((r : Polynomial A).map (algV X V)) • q).coeff n =
    ((r : Polynomial A) • toPolyA A q).coeff n
  rw [PolynomialModule.smul_apply, PolynomialModule.smul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.coeff_map, coeff_toPolyA]
  rfl

variable (hF : IsCoherent F) (hV : IsAffineOpen V)

def targetToPolySec (z : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) : polySec I F V := z

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma targetToPolySec_add (z z' : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec (z + z') = targetToPolySec z + targetToPolySec z' := rfl

/- English proof (translation)
Introduce `_ _ h` and use `h`.
-/
lemma targetToPolySec_injective :
    Function.Injective (targetToPolySec (I := I) (F := F) (V := V)) := fun _ _ h => h

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma targetToPolySec_smul (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V))
    (z : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec (s • z) = (reesPolyMap I X).app _ s • targetToPolySec z := rfl

/- English proof (translation)
Establish `h` using `congrArg (fun f => (Scheme.Modules.Hom.app f (reesPr I X ⁻¹ᵁ V)) y) (reesSheafπ_ι I F)`. Conclude with `h`.
-/
lemma targetToPolySec_ι_π (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    targetToPolySec ((reesSheafι I F).app _ ((reesSheafπ I F).app _ y)) = unitB I F V y := by
  have h := congrArg (fun f => (Scheme.Modules.Hom.app f (reesPr I X ⁻¹ᵁ V)) y) (reesSheafπ_ι I F)
  exact h

variable (I) in

def reesSectionsMap (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) : PolynomialModule A Γ(F, V) :=
  toPolyA A (thetaMap hF hV (targetToPolySec ((reesSheafι I F).app _ x)))

/- English proof (translation)
Rewrite using `[reesSectionsMap, map_add, targetToPolySec_add, map_add, toPolyA_add]`. Both sides reduce to the same expression.
-/
lemma reesSectionsMap_add (x x' : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV (x + x') = reesSectionsMap I hF hV x + reesSectionsMap I hF hV x' := by
  rw [reesSectionsMap, map_add, targetToPolySec_add, map_add, toPolyA_add]
  rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toPolyA A (thetaMap hF hV (targetToPolySec ((reesSheafι I F).app _ 0))) = 0`. Rewrite using `[map_zero, show targetToPolySec (0 : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) = 0 from rfl, map_zero]`. Both sides reduce to the same expression.
-/
lemma reesSectionsMap_zero : reesSectionsMap I hF hV 0 = 0 := by
  change toPolyA A (thetaMap hF hV (targetToPolySec ((reesSheafι I F).app _ 0))) = 0
  rw [map_zero, show targetToPolySec (0 : Γ(reesTarget I F, reesPr I X ⁻¹ᵁ V)) = 0 from rfl,
    map_zero]
  rfl

/- English proof (translation)
The claim follows from `toPolyA_injective.comp ((thetaMap_injective hF hV).comp (targetToPolySec_injective.comp (injective_reesSheafι_app _)))`.
-/
lemma reesSectionsMap_injective : Function.Injective (reesSectionsMap I hF hV) :=
  toPolyA_injective.comp ((thetaMap_injective hF hV).comp
    (targetToPolySec_injective.comp (injective_reesSheafι_app _)))

/- English proof (translation)
Rewrite using `[reesSectionsMap, targetToPolySec_ι_π, thetaMap_unitB]`.
-/
lemma reesSectionsMap_π (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV ((reesSheafπ I F).app _ y) = toPolyA A (theta₁ hF hV y) := by
  rw [reesSectionsMap, targetToPolySec_ι_π, thetaMap_unitB]

/- English proof (translation)
Take `⟨y, rfl⟩` from `surjective_reesSheafπ_app hF (hV.preimage (reesPr I X)) x`. Rewrite using `[reesSectionsMap_π]`. Establish `hy : y ∈ Submodule.span Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) (Set.range (unitPr I F V))`. Rewrite using `[(isBaseChangeAt_reesPr (I := I) hF hV).span_range]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨m, rfl⟩` from `hz`. Rewrite using `[theta₁_unitPr]`. Conclude with `single_zero_mem_reesSubmodule I Γ(F, V) m`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ hz hz'`. Rewrite using `[map_add, toPolyA_add]`. Conclude with `add_mem hz hz'`.

Consider the case `smul s z _ hz`. Rewrite using `[theta₁_smul]`. Conclude with `toPolyA_smul_mem (reesRingHom_mem hV s) hz`.
-/
lemma reesSectionsMap_mem (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV x ∈ reesSubmodule I Γ(F, V) := by
  obtain ⟨y, rfl⟩ := surjective_reesSheafπ_app hF (hV.preimage (reesPr I X)) x
  rw [reesSectionsMap_π]
  have hy : y ∈ Submodule.span Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)
      (Set.range (unitPr I F V)) := by
    rw [(isBaseChangeAt_reesPr (I := I) hF hV).span_range]
    trivial
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    rw [theta₁_unitPr]
    exact single_zero_mem_reesSubmodule I Γ(F, V) m
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    rw [map_add, toPolyA_add]
    exact add_mem hz hz'
  | smul s z _ hz =>
    rw [theta₁_smul]
    exact toPolyA_smul_mem (reesRingHom_mem hV s) hz

/- English proof (translation)
Rewrite using `[reesSectionsMap, Scheme.Modules.Hom.app_smul, targetToPolySec_smul, thetaMap_smul, ← RingHom.comp_apply, ← reesRingHom, reesRingHom_inr, toPolyA_map_smul]`. Both sides reduce to the same expression.
-/
lemma reesSectionsMap_smul (r : reesAlgebra I) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesSectionsMap I hF hV (reesInr I V r • x) = r • reesSectionsMap I hF hV x := by
  rw [reesSectionsMap, Scheme.Modules.Hom.app_smul, targetToPolySec_smul, thetaMap_smul,
    ← RingHom.comp_apply, ← reesRingHom, reesRingHom_inr, toPolyA_map_smul]
  rfl

/- English proof (translation)
Take `⟨p, hp⟩` from `p`. Rewrite `hp` using `[reesSubmodule_eq_span]`. Express the relevant statement in the definitionally equal form `∃ x, reesSectionsMap I hF hV x = p`. Use `Submodule.span_induction (p := fun z _ => ∃ x, reesSectionsMap I hF hV x = z) ?_ ?_ ?_ ?_ hp` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`.

Use `⟨(reesSheafπ I F).app _ (unitPr I F V m), ?_⟩` and prove the remaining obligations. Rewrite using `[reesSectionsMap_π, theta₁_unitPr]`. Both sides reduce to the same expression. Conclude with `⟨0, reesSectionsMap_zero hF hV⟩`. Introduce and unpack `z z' _ _ ⟨x, hx⟩ ⟨x', hx'⟩`.

Conclude with `⟨x + x', by rw [reesSectionsMap_add, hx, hx']⟩`. Introduce and unpack `r z _ ⟨x, hx⟩`. Conclude with `⟨reesInr I V r • x, by rw [reesSectionsMap_smul, hx]⟩`.
-/
lemma reesSectionsMap_surjective (p : reesSubmodule I Γ(F, V)) :
    ∃ x, reesSectionsMap I hF hV x = p := by
  obtain ⟨p, hp⟩ := p
  rw [reesSubmodule_eq_span] at hp
  change ∃ x, reesSectionsMap I hF hV x = p
  refine Submodule.span_induction (p := fun z _ => ∃ x, reesSectionsMap I hF hV x = z)
    ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨m, rfl⟩
    refine ⟨(reesSheafπ I F).app _ (unitPr I F V m), ?_⟩
    rw [reesSectionsMap_π, theta₁_unitPr]
    rfl
  · exact ⟨0, reesSectionsMap_zero hF hV⟩
  · rintro z z' _ _ ⟨x, hx⟩ ⟨x', hx'⟩
    exact ⟨x + x', by rw [reesSectionsMap_add, hx, hx']⟩
  · rintro r z _ ⟨x, hx⟩
    exact ⟨reesInr I V r • x, by rw [reesSectionsMap_smul, hx]⟩

variable (I) in

def reesSectionsEquiv : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) ≃+ reesSubmodule I Γ(F, V) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨reesSectionsMap I hF hV x, reesSectionsMap_mem hF hV x⟩
       map_zero' := Subtype.ext (reesSectionsMap_zero hF hV)
       map_add' := fun x x' => Subtype.ext (reesSectionsMap_add hF hV x x') } :
      Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ reesSubmodule I Γ(F, V))
    ⟨fun x x' h => reesSectionsMap_injective hF hV (congrArg Subtype.val h), fun p => by
      obtain ⟨x, hx⟩ := reesSectionsMap_surjective hF hV p
      exact ⟨x, Subtype.ext hx⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma reesSectionsEquiv_apply (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (reesSectionsEquiv I hF hV x : PolynomialModule A Γ(F, V)) = reesSectionsMap I hF hV x := rfl

end

end GroundTheory.Arith.SchemeCoh
