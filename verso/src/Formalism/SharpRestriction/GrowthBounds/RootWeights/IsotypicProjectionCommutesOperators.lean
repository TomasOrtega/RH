import Formalism.SharpRestriction.GrowthBounds.RootWeights.StableSubspaceCompleteReducibility

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section abstract

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `x ⟨u, hu, v, _, hv, rfl⟩`. Conclude with `⟨u, hu, v, hv, rfl⟩`.
-/
theorem isotypicPartIn_le (W : Submodule K V) (mu : Fin n → ℤ) : isotypicPartIn E W mu ≤ isoSub E mu := by
  apply Submodule.span_mono
  rintro x ⟨u, hu, v, _, hv, rfl⟩
  exact ⟨u, hu, v, hv, rfl⟩

/- English proof (translation)
The claim follows from `Submonoid.subset_closure ⟨(a, b), rfl⟩`.
-/
theorem operator_mem_envelopingMonoid (a b : Fin n) : E a b ∈ Umon E := Submonoid.subset_closure ⟨(a, b), rfl⟩

/- English proof (translation)
Establish `: (isoSub E mu).map (E a b) ≤ isoSub E mu`. Rewrite using `[isoSub, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩`. Conclude with `Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (operator_mem_envelopingMonoid E a b) hu, v, hv, rfl⟩`. Conclude with `this (Submodule.mem_map_of_mem hx)`.
-/
theorem isotypicSubmodule_stable (mu : Fin n → ℤ) (a b : Fin n) {x : V} (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  have : (isoSub E mu).map (E a b) ≤ isoSub E mu := by
    rw [isoSub, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (operator_mem_envelopingMonoid E a b) hu, v, hv, rfl⟩
  exact this (Submodule.mem_map_of_mem hx)

/- English proof (translation)
Establish `h : (⨆ ν, isoSub E ν) ≤ LinearMap.eqLocus ((e mu).comp (E a b)) ((E a b).comp (e mu))`. Use `iSup_le fun ν y hy => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_eqLocus]`. Simplify using `only [LinearMap.comp_apply]`. Distinguish the cases in `hν : ν = mu`.

Substitute `hν` using the available equality. Rewrite using `[(he ν).1 _ (isotypicSubmodule_stable E ν a b hy), (he ν).1 _ hy]`. Rewrite using `[(he mu).2 ν hν _ (isotypicSubmodule_stable E ν a b hy), (he mu).2 ν hν _ hy, map_zero]`. Establish `h2 : x ∈ ⨆ ν, isoSub E ν` using `by rw [htop]; exact Submodule.mem_top`. Use `h h2` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_eqLocus]`. Simplify using `using this`.
-/
theorem isotypic_projection_commutes_operators (htop : (⨆ mu, isoSub E mu) = ⊤) (e : (Fin n → ℤ) → Module.End K V)
    (he : ∀ mu, IsIsoProj E mu (e mu)) (mu : Fin n → ℤ) (a b : Fin n) (x : V) :
    e mu (E a b x) = E a b (e mu x) := by
  have h : (⨆ ν, isoSub E ν) ≤ LinearMap.eqLocus ((e mu).comp (E a b)) ((E a b).comp (e mu)) := by
    refine iSup_le fun ν y hy => ?_
    rw [LinearMap.mem_eqLocus]
    simp only [LinearMap.comp_apply]
    by_cases hν : ν = mu
    · subst hν
      rw [(he ν).1 _ (isotypicSubmodule_stable E ν a b hy), (he ν).1 _ hy]
    · rw [(he mu).2 ν hν _ (isotypicSubmodule_stable E ν a b hy), (he mu).2 ν hν _ hy, map_zero]
  have h2 : x ∈ ⨆ ν, isoSub E ν := by rw [htop]; exact Submodule.mem_top
  have := h h2
  rw [LinearMap.mem_eqLocus] at this
  simpa using this

/- English proof (translation)
Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction generalizing x with`. Consider the case `mem u hu`. Take `⟨⟨a, b⟩, rfl⟩` from `hu`. Conclude with `isotypic_projection_commutes_operators E htop e he mu a b x`.

Consider the case `one => rfl`. Consider the case `mul u w _ _ ihu ihw`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[ihu, ihw]`.
-/
theorem isotypic_projection_commutes_monoid (htop : (⨆ mu, isoSub E mu) = ⊤) (e : (Fin n → ℤ) → Module.End K V)
    (he : ∀ mu, IsIsoProj E mu (e mu)) (mu : Fin n → ℤ) {u : Module.End K V} (hu : u ∈ Umon E) (x : V) :
    e mu (u x) = u (e mu x) := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction generalizing x with
  | mem u hu =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hu
    exact isotypic_projection_commutes_operators E htop e he mu a b x
  | one => rfl
  | mul u w _ _ ihu ihw =>
    simp only [Module.End.mul_apply]
    rw [ihu, ihw]

/- English proof (translation)
Rewrite using `[map_finsuppSum, Finsupp.sum_eq_single mu]`. Conclude with `(he mu).1 _ (hf mu)`. Introduce `ν _ hne`. Conclude with `(he mu).2 ν hne _ (hf ν)`. Introduce `_`.

Conclude with `map_zero _`.
-/
theorem isotypic_projection_of_sum (e : (Fin n → ℤ) → Module.End K V) (he : ∀ mu, IsIsoProj E mu (e mu))
    (f : (Fin n → ℤ) →₀ V) (hf : ∀ ν, f ν ∈ isoSub E ν) (mu : Fin n → ℤ) :
    e mu (f.sum fun _ y => y) = f mu := by
  rw [map_finsuppSum, Finsupp.sum_eq_single mu]
  · exact (he mu).1 _ (hf mu)
  · intro ν _ hne
    exact (he mu).2 ν hne _ (hf ν)
  · intro _
    exact map_zero _

def generatedSubmodule (x : V) : Submodule K V := Submodule.span K {y | ∃ u ∈ Umon E, y = u x}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, (Umon E).one_mem, rfl⟩`.
-/
theorem mem_generatedSubmodule_self (x : V) : x ∈ generatedSubmodule E x := Submodule.subset_span ⟨1, (Umon E).one_mem, rfl⟩

/- English proof (translation)
Introduce `a b y hy`. Establish `: (generatedSubmodule E x).map (E a b) ≤ generatedSubmodule E x`. Rewrite using `[generatedSubmodule, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨u, hu, rfl⟩, rfl⟩`. Conclude with `Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (operator_mem_envelopingMonoid E a b) hu, rfl⟩`.

Conclude with `this (Submodule.mem_map_of_mem hy)`.
-/
theorem generatedSubmodule_isStable (x : V) : IsStableUnderOperators E (generatedSubmodule E x) := by
  intro a b y hy
  have : (generatedSubmodule E x).map (E a b) ≤ generatedSubmodule E x := by
    rw [generatedSubmodule, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (operator_mem_envelopingMonoid E a b) hu, rfl⟩
  exact this (Submodule.mem_map_of_mem hy)

variable {E}

/- English proof (translation)
Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction generalizing x with`. Consider the case `mem u hu`. Take `⟨⟨a, b⟩, rfl⟩` from `hu`. Conclude with `hT a b x hx`.

Consider the case `one => exact hx`. Consider the case `mul u w _ _ ihu ihw => exact ihu (ihw hx)`.
-/
theorem envelopingMonoid_preserves_stable {T : Submodule K V} (hT : IsStableUnderOperators E T) {u : Module.End K V} (hu : u ∈ Umon E) {x : V}
    (hx : x ∈ T) : u x ∈ T := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction generalizing x with
  | mem u hu =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hu
    exact hT a b x hx
  | one => exact hx
  | mul u w _ _ ihu ihw => exact ihu (ihw hx)

/- English proof (translation)
Rewrite using `[generatedSubmodule, Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Conclude with `envelopingMonoid_preserves_stable hT hu hx`.
-/
theorem generatedSubmodule_le_of_stable {T : Submodule K V} (hT : IsStableUnderOperators E T) {x : V} (hx : x ∈ T) : generatedSubmodule E x ≤ T := by
  rw [generatedSubmodule, Submodule.span_le]
  rintro _ ⟨u, hu, rfl⟩
  exact envelopingMonoid_preserves_stable hT hu hx

/- English proof (translation)
Unfold `divPowE`. Rewrite using `[LinearMap.smul_apply]`. Apply `W.smul_mem` to reduce the goal to its premises. Proceed by induction on `k generalizing x with`. Consider the case `zero => simpa using hx`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih (hW a b x hx)`.
-/
theorem divPowE_preserves_stable {W : Submodule K V} (hW : IsStableUnderOperators E W) (a b : Fin n) (k : ℕ) {x : V} (hx : x ∈ W) :
    divPowE E a b k x ∈ W := by
  unfold divPowE
  rw [LinearMap.smul_apply]
  apply W.smul_mem
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (hW a b x hx)

/- English proof (translation)
Proceed by induction on `L generalizing x with`. Consider the case `nil => simpa using hx`. Consider the case `cons f L ih`. Rewrite using `[List.prod_cons, Module.End.mul_apply]`. Conclude with `h f List.mem_cons_self _ (ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) hx)`.
-/
theorem list_prod_preserves_stable_alt {W : Submodule K V} (L : List (Module.End K V)) (h : ∀ f ∈ L, ∀ x ∈ W, f x ∈ W) {x : V}
    (hx : x ∈ W) : L.prod x ∈ W := by
  induction L generalizing x with
  | nil => simpa using hx
  | cons f L ih =>
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f List.mem_cons_self _ (ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) hx)

/- English proof (translation)
Unfold `binomE`. Rewrite using `[LinearMap.smul_apply]`. Apply `W.smul_mem` to reduce the goal to its premises. Apply `list_prod_preserves_stable_alt _ _ hx` to reduce the goal to its premises. Introduce `f hf y hy`.

Take `⟨j, _, rfl⟩` from `List.mem_map.1 hf`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply]`. Conclude with `W.sub_mem (hW a a y hy) (W.smul_mem _ hy)`.
-/
theorem binomE_preserves_stable {W : Submodule K V} (hW : IsStableUnderOperators E W) (a : Fin n) (k : ℕ) {x : V} (hx : x ∈ W) :
    binomE E a k x ∈ W := by
  unfold binomE
  rw [LinearMap.smul_apply]
  apply W.smul_mem
  apply list_prod_preserves_stable_alt _ _ hx
  intro f hf y hy
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hf
  rw [LinearMap.sub_apply, LinearMap.smul_apply]
  exact W.sub_mem (hW a a y hy) (W.smul_mem _ hy)

end abstract

section concrete

variable {R : Type} [Field R] [CharZero R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[polGenSub]`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Establish `key : ∀ x ∈ generatedSubmodule (glOps R n LL S) G, u x ∈ generatedSubmodule (glOps R n LL S) G`.

Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem u hu`. Break down `hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩` into its components or cases. Introduce `x hx`. Rewrite using `[← hDP R ι LL n S a b k hab]`.

Conclude with `divPowE_preserves_stable (generatedSubmodule_isStable _ G) a b k hx`. Introduce `x hx`. Rewrite using `[← hBin R ι LL n S a k]`. Conclude with `binomE_preserves_stable (generatedSubmodule_isStable _ G) a k hx`. Consider the case `one => intro x hx`.

Conclude with `hx`. Consider the case `mul u w _ _ ihu ihw => intro x hx`. Conclude with `ihu _ (ihw _ hx)`. Conclude with `key G (mem_generatedSubmodule_self _ G)`. Rewrite using `[generatedSubmodule]`.

Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨u, ?_, rfl⟩` and prove the remaining obligations. Establish `: Umon (glOps R n LL S) ≤ Submonoid.closure (polUZgens R LL S)`.

Apply `Submonoid.closure_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨⟨a, b⟩, rfl⟩`. Apply `Submonoid.subset_closure` to reduce the goal to its premises. Distinguish the cases in `hab : a = b`. Substitute `hab right` using the available equality.

Use `⟨a, 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hBin R ι LL n S a 1]`. Simplify using `[binomE]`. Use `left`. Use `⟨a, b, 1, hab, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hDP R ι LL n S a b 1 hab]`. Simplify using `[divPowE]`. Conclude with `this hu`.
-/
theorem polynomial_generated_eq_enveloping (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero) (G : MvPolynomial (ι × Fin n) R) :
    polGenSub R LL S G = generatedSubmodule (glOps R n LL S) G := by
  apply le_antisymm
  · rw [polGenSub]
    apply Submodule.span_le.2
    rintro _ ⟨u, hu, rfl⟩
    have key : ∀ x ∈ generatedSubmodule (glOps R n LL S) G, u x ∈ generatedSubmodule (glOps R n LL S) G := by
      induction hu using Submonoid.closure_induction with
      | mem u hu =>
        rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
        · intro x hx
          rw [← hDP R ι LL n S a b k hab]
          exact divPowE_preserves_stable (generatedSubmodule_isStable _ G) a b k hx
        · intro x hx
          rw [← hBin R ι LL n S a k]
          exact binomE_preserves_stable (generatedSubmodule_isStable _ G) a k hx
      | one => intro x hx; exact hx
      | mul u w _ _ ihu ihw => intro x hx; exact ihu _ (ihw _ hx)
    exact key G (mem_generatedSubmodule_self _ G)
  · rw [generatedSubmodule]
    apply Submodule.span_le.2
    rintro _ ⟨u, hu, rfl⟩
    apply Submodule.subset_span
    refine ⟨u, ?_, rfl⟩
    have : Umon (glOps R n LL S) ≤ Submonoid.closure (polUZgens R LL S) := by
      apply Submonoid.closure_le.2
      rintro _ ⟨⟨a, b⟩, rfl⟩
      apply Submonoid.subset_closure
      by_cases hab : a = b
      · subst hab
        right
        refine ⟨a, 1, ?_⟩
        rw [← hBin R ι LL n S a 1]
        simp [binomE]
      · left
        refine ⟨a, b, 1, hab, ?_⟩
        rw [← hDP R ι LL n S a b 1 hab]
        simp [divPowE]
    exact this hu

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[x.as_sum]`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Conclude with `Submodule.mem_iSup_of_mem (wtS LL S m) ((hWt R ι LL n S).1 m _)`.
-/
theorem weightSpaces_span_polynomials (hWt : MonomialsAreWeightVectors) : (⨆ mu, weightSp (glOps R n LL S) mu) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [x.as_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact Submodule.mem_iSup_of_mem (wtS LL S m) ((hWt R ι LL n S).1 m _)

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨T, hT1, hxT, hT2⟩` from `hFin R ι LL n S x`. Establish `h` using `hCR R _ n (glOps R n LL S) (hRel R ι LL n S) T hT1 hT2 (by rw [weightSpaces_span_polynomials LL S hWt]; exact le_top) hxT`. Conclude with `(iSup_mono fun mu => isotypicPartIn_le _ T mu) h`.
-/
theorem polynomial_isotypic_span_top (hCR : StableSubspaceCompleteReducibility) (hRel : PolynomialOperatorsGLRelations) (hWt : MonomialsAreWeightVectors) (hFin : PolynomialLocallyFinite) :
    (⨆ mu, isoSub (glOps R n LL S) mu) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨T, hT1, hxT, hT2⟩ := hFin R ι LL n S x
  have h := hCR R _ n (glOps R n LL S) (hRel R ι LL n S) T hT1 hT2 (by rw [weightSpaces_span_polynomials LL S hWt]; exact le_top) hxT
  exact (iSup_mono fun mu => isotypicPartIn_le _ T mu) h

/- English proof (translation)
Take `⟨T, hT1, hxT, hT2⟩` from `hFin R ι LL n S G`. Conclude with `Submodule.finiteDimensional_of_le (generatedSubmodule_le_of_stable hT2 hxT)`.
-/
theorem generatedSubmodule_finiteDimensional (hFin : PolynomialLocallyFinite) (G : MvPolynomial (ι × Fin n) R) :
    FiniteDimensional R (generatedSubmodule (glOps R n LL S) G) := by
  obtain ⟨T, hT1, hxT, hT2⟩ := hFin R ι LL n S G
  exact Submodule.finiteDimensional_of_le (generatedSubmodule_le_of_stable hT2 hxT)

/- English proof (translation)
Rewrite using `[polynomial_generated_eq_enveloping LL S hDP hBin]`. Establish `h` using `hCR R _ n (glOps R n LL S) (hRel R ι LL n S) _ (generatedSubmodule_finiteDimensional LL S hFin G) (generatedSubmodule_isStable _ G) (by rw [weightSpaces_span_polynomials LL S hWt]; exact le_top) (mem_generatedSubmodule_self _ G)`. Take `⟨f, hf, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 h`. Establish `h1 : e mu G = f mu`. Rewrite using `[← hsum]`.

Conclude with `isotypic_projection_of_sum _ e he f (fun ν => isotypicPartIn_le _ _ ν (hf ν)) mu`. Assume the negation of the conclusion as `hno`. Apply `hne` to reduce the goal to its premises. Rewrite using `[h1]`. Establish `hbot : isotypicPartIn (glOps R n LL S) (generatedSubmodule (glOps R n LL S) G) mu = ⊥`.

Rewrite using `[isotypicPartIn, Submodule.span_eq_bot]`. Introduce and unpack `x ⟨u, _, v, hv, hw, rfl⟩`. Conclude with `absurd ⟨v, hv, hw.1, fun m hm => (hWt R ι LL n S).2 mu v hw.2.1 m hm⟩ hno`. Use `hf mu` as an intermediate fact. Rewrite `this` using `[hbot]`.

Conclude with `(Submodule.mem_bot R).1 this`.
-/
theorem isotypic_component_weight_mem (hCR : StableSubspaceCompleteReducibility) (hRel : PolynomialOperatorsGLRelations) (hWt : MonomialsAreWeightVectors) (hFin : PolynomialLocallyFinite) (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero)
    (e : (Fin n → ℤ) → Module.End R (MvPolynomial (ι × Fin n) R))
    (he : ∀ mu, IsIsoProj (glOps R n LL S) mu (e mu)) (G : MvPolynomial (ι × Fin n) R) (mu : Fin n → ℤ)
    (hne : e mu G ≠ 0) : mu ∈ polWts LL S (polGenSub R LL S G) := by
  rw [polynomial_generated_eq_enveloping LL S hDP hBin]
  have h := hCR R _ n (glOps R n LL S) (hRel R ι LL n S) _ (generatedSubmodule_finiteDimensional LL S hFin G) (generatedSubmodule_isStable _ G)
    (by rw [weightSpaces_span_polynomials LL S hWt]; exact le_top) (mem_generatedSubmodule_self _ G)
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 h
  have h1 : e mu G = f mu := by
    rw [← hsum]
    exact isotypic_projection_of_sum _ e he f (fun ν => isotypicPartIn_le _ _ ν (hf ν)) mu
  by_contra hno
  apply hne
  rw [h1]
  have hbot : isotypicPartIn (glOps R n LL S) (generatedSubmodule (glOps R n LL S) G) mu = ⊥ := by
    rw [isotypicPartIn, Submodule.span_eq_bot]
    rintro x ⟨u, _, v, hv, hw, rfl⟩
    exact absurd ⟨v, hv, hw.1, fun m hm => (hWt R ι LL n S).2 mu v hw.2.1 m hm⟩ hno
  have := hf mu
  rw [hbot] at this
  exact (Submodule.mem_bot R).1 this

/- English proof (translation)
Rewrite using `[polynomial_generated_eq_enveloping LL S hDP hBin]`. Introduce and unpack `ν ⟨x, hx, hx0, hxν⟩`. Establish `htop` using `polynomial_isotypic_span_top (R := R) LL (n := n) S hCR hRel hWt hFin`. Establish `hxt : x ∈ ⨆ mu, isoSub (glOps R n LL S) mu` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨f, hf, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 hxt`.

Establish `hfe : ∀ mu, e mu x = f mu` using `fun mu => by`. Rewrite using `[← hsum]`. Conclude with `isotypic_projection_of_sum _ e he f hf mu`. Establish `hker : ∀ mu, e mu G = 0 → e mu x = 0`. Introduce `mu h0`.

Establish `hle : generatedSubmodule (glOps R n LL S) G ≤ LinearMap.ker (e mu)`. Rewrite using `[generatedSubmodule, Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Express the relevant statement in the definitionally equal form `e mu (u G) = 0`. Rewrite using `[isotypic_projection_commutes_monoid _ htop e he mu hu, h0, map_zero]`.

Conclude with `hle hx`. Establish `hiso : ∀ mu, cond mu → isoSub (glOps R n LL S) mu ≤ MvPolynomial.restrictSupport R {m | cond (wtS LL S m)}`. Introduce `mu hmu`. Rewrite using `[isoSub, Submodule.span_le]`. Introduce and unpack `_ ⟨u, hu, v, hv, rfl⟩`.

Establish `h1` using `hHW R _ n (glOps R n LL S) (hRel R ι LL n S) mu v hv u hu`. Use `(iSup₂_le fun ν' hν' => ?_ : (⨆ ν' ∈ {ν' : Fin n → ℤ | mu (lastIdx n) ≤ ν' (lastIdx n) ∧ ν' 0 ≤ mu 0}, weightSp (glOps R n LL S) ν') ≤ _) h1` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`.

Use `(hWt R ι LL n S).2 ν' y hy m (by simpa using hm)` as an intermediate fact. Express the relevant statement in the definitionally equal form `cond (wtS LL S m)`. Rewrite using `[this]`. Conclude with `hmono mu ν' hmu hν'.1 hν'.2`. Establish `hxZ : x ∈ MvPolynomial.restrictSupport R {m | cond (wtS LL S m)}`.

Rewrite using `[← hsum]`. Use `Submodule.sum_mem _ fun mu hmu => ?_` and prove the remaining obligations. Establish `hne : f mu ≠ 0` using `Finsupp.mem_support_iff.1 hmu`. Establish `hG : e mu G ≠ 0` using `fun h0 => hne (by rw [← hfe mu]; exact hker mu h0)`. Conclude with `hiso mu (h mu hG) (hf mu)`.

Take `⟨m, hm⟩` from `MvPolynomial.support_nonempty.2 hx0`. Establish `h2` using `(MvPolynomial.mem_restrictSupport_iff R).1 hxZ (by simpa using hm : m ∈ (x.support : Set _))`. Establish `h3 : cond (wtS LL S m)` using `h2`. Rewrite `h3` using `[hxν m hm]`. Then use the resulting hypothesis.
-/
theorem weight_type_of_isotypic_projections [NeZero n] (hCR : StableSubspaceCompleteReducibility) (hHW : HighestWeightModuleWeightBounds) (hRel : PolynomialOperatorsGLRelations) (hWt : MonomialsAreWeightVectors) (hFin : PolynomialLocallyFinite)
    (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero)
    (e : (Fin n → ℤ) → Module.End R (MvPolynomial (ι × Fin n) R))
    (he : ∀ mu, IsIsoProj (glOps R n LL S) mu (e mu)) (G : MvPolynomial (ι × Fin n) R)
    (cond : (Fin n → ℤ) → Prop)
    (hmono : ∀ mu ν : Fin n → ℤ, cond mu → mu (lastIdx n) ≤ ν (lastIdx n) → ν 0 ≤ mu 0 → cond ν)
    (h : ∀ mu, e mu G ≠ 0 → cond mu) : ∀ ν ∈ polWts LL S (polGenSub R LL S G), cond ν := by
  rw [polynomial_generated_eq_enveloping LL S hDP hBin]
  rintro ν ⟨x, hx, hx0, hxν⟩
  have htop := polynomial_isotypic_span_top (R := R) LL (n := n) S hCR hRel hWt hFin
  have hxt : x ∈ ⨆ mu, isoSub (glOps R n LL S) mu := by rw [htop]; exact Submodule.mem_top
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hxt
  have hfe : ∀ mu, e mu x = f mu := fun mu => by
    rw [← hsum]
    exact isotypic_projection_of_sum _ e he f hf mu

  have hker : ∀ mu, e mu G = 0 → e mu x = 0 := by
    intro mu h0
    have hle : generatedSubmodule (glOps R n LL S) G ≤ LinearMap.ker (e mu) := by
      rw [generatedSubmodule, Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      change e mu (u G) = 0
      rw [isotypic_projection_commutes_monoid _ htop e he mu hu, h0, map_zero]
    exact hle hx
  have hiso : ∀ mu, cond mu → isoSub (glOps R n LL S) mu ≤
      MvPolynomial.restrictSupport R {m | cond (wtS LL S m)} := by
    intro mu hmu
    rw [isoSub, Submodule.span_le]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    have h1 := hHW R _ n (glOps R n LL S) (hRel R ι LL n S) mu v hv u hu
    refine (iSup₂_le fun ν' hν' => ?_ : (⨆ ν' ∈ {ν' : Fin n → ℤ | mu (lastIdx n) ≤ ν' (lastIdx n) ∧ ν' 0 ≤ mu 0},
      weightSp (glOps R n LL S) ν') ≤ _) h1
    intro y hy
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    have := (hWt R ι LL n S).2 ν' y hy m (by simpa using hm)
    change cond (wtS LL S m)
    rw [this]
    exact hmono mu ν' hmu hν'.1 hν'.2
  have hxZ : x ∈ MvPolynomial.restrictSupport R {m | cond (wtS LL S m)} := by
    rw [← hsum]
    refine Submodule.sum_mem _ fun mu hmu => ?_
    have hne : f mu ≠ 0 := Finsupp.mem_support_iff.1 hmu
    have hG : e mu G ≠ 0 := fun h0 => hne (by rw [← hfe mu]; exact hker mu h0)
    exact hiso mu (h mu hG) (hf mu)
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx0
  have h2 := (MvPolynomial.mem_restrictSupport_iff R).1 hxZ (by simpa using hm : m ∈ (x.support : Set _))
  have h3 : cond (wtS LL S m) := h2
  rwa [hxν m hm] at h3

end concrete

/- English proof (translation)
Introduce `R _ _ ι _ LL n _ S e he`. Take `⟨_, _, _, _, h5, h6⟩` from `hV1 R ι LL n S`. Use `⟨fun G th => ?_, fun G M => ?_⟩` and prove the remaining obligations. Rewrite using `[h5 G th]`. Prove the components needed by the constructor for the conclusion.

Introduce `h mu hne`. Conclude with `h mu (isotypic_component_weight_mem LL S hCR hRel hWt hFin hDP hBin e he G mu hne)`. Introduce `h`. Conclude with `weight_type_of_isotypic_projections LL S hCR hHW hRel hWt hFin hDP hBin e he G (fun ν => th ≤ ν (lastIdx n)) (fun mu ν h1 h2 _ => le_trans h1 h2) h`. Rewrite using `[h6 G M]`.

Prove the components needed by the constructor for the conclusion. Introduce `h mu hne`. Conclude with `h mu (isotypic_component_weight_mem LL S hCR hRel hWt hFin hDP hBin e he G mu hne)`. Introduce `h`. Conclude with `weight_type_of_isotypic_projections LL S hCR hHW hRel hWt hFin hDP hBin e he G (fun ν => ν 0 ≤ M) (fun mu ν h1 _ h3 => le_trans h3 h1) h`.
-/
theorem generated_weight_lemma_char_zero (D : Formalism.BasicNotions.D7) (hV1 : ValuationsAdditive D) (hCR : StableSubspaceCompleteReducibility) (hHW : HighestWeightModuleWeightBounds) (hRel : PolynomialOperatorsGLRelations) (hWt : MonomialsAreWeightVectors)
    (hFin : PolynomialLocallyFinite) (hDP : DividedPowerFormulaCharZero) (hBin : BinomialFormulaCharZero) : ShaLengthVersionTwo D := by
  intro R _ _ ι _ LL n _ S e he
  obtain ⟨_, _, _, _, h5, h6⟩ := hV1 R ι LL n S
  refine ⟨fun G th => ?_, fun G M => ?_⟩
  · rw [h5 G th]
    constructor
    · intro h mu hne
      exact h mu (isotypic_component_weight_mem LL S hCR hRel hWt hFin hDP hBin e he G mu hne)
    · intro h
      exact weight_type_of_isotypic_projections LL S hCR hHW hRel hWt hFin hDP hBin e he G (fun ν => th ≤ ν (lastIdx n))
        (fun mu ν h1 h2 _ => le_trans h1 h2) h
  · rw [h6 G M]
    constructor
    · intro h mu hne
      exact h mu (isotypic_component_weight_mem LL S hCR hRel hWt hFin hDP hBin e he G mu hne)
    · intro h
      exact weight_type_of_isotypic_projections LL S hCR hHW hRel hWt hFin hDP hBin e he G (fun ν => ν 0 ≤ M)
        (fun mu ν h1 _ h3 => le_trans h3 h1) h

end Formalism.MainNotions.G.GLWeightTheory
