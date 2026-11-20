import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRetr

namespace GlobalTheory.CompanionTheory.FinPresDescent

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.FiniteTypeDescent.main R C D hinj`.
-/
theorem finiteType_of_finite_projective (R C D : Type*) [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [Module.Finite C D] [Module.Projective C D] (hinj : Function.Injective (algebraMap C D))
    [Algebra.FiniteType R D] : Algebra.FiniteType R C :=
  _root_.UpperTheory.Reformulated.B.FiniteTypeDescent.main R C D hinj

/- English proof (translation)
Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' P M`. Establish `hker : (LinearMap.ker π).FG` using `Module.FinitePresentation.fg_ker π hπ`. Set `b : Fin n → M` to `fun i => π (Pi.single i 1)`. Establish `hπb : ∀ x, π x = ∑ i, x i • b i` using `fun x => by`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ π x]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Use extensionality with `j`. Simplify using `[b, Pi.single_apply, eq_comm]`. Establish `hπC : ∀ x, π x = ∑ i, algebraMap P C (x i) • b i` using `fun x => by`.

Rewrite using `[hπb]`. Simplify using `only [algebraMap_smul]`. Set `πC : (Fin n → C) →ₗ[C] M` to `Fintype.linearCombination C b`. Establish `hπCs : Function.Surjective πC`. Introduce `m`.

Take `⟨x, rfl⟩` from `hπ m`. Use `⟨fun i => algebraMap P C (x i), ?_⟩` and prove the remaining obligations. Rewrite using `[hπC, Fintype.linearCombination_apply]`. Take `⟨s, hs⟩` from `Module.projective_lifting_property πC LinearMap.id hπCs`. Establish `hs' : ∀ m, ∑ i, s m i • b i = m` using `fun m => by`.

Use `LinearMap.congr_fun hs m` as an intermediate fact. Simplify `this` using `[πC, Fintype.linearCombination_apply]`. Use `choose v hv using fun (p : Fin n × Fin n) => hsurj (s (b p.1) p.2)`. Set `E : (Fin n → P) → Fin n → P` to `fun x j => ∑ i, x i * v (i, j)`. Establish `key1 : ∀ x j, algebraMap P C (E x j) = s (π x) j` using `fun x j => by`.

Establish `hsx : s (π x) = ∑ i, algebraMap P C (x i) • s (b i)`. Rewrite using `[hπC, map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[hsx, Finset.sum_apply]`. Simplify using `only [E, map_sum, map_mul, hv, Pi.smul_apply, smul_eq_mul]`.

Establish `key2 : ∀ x, π (fun j => E x j) = π x` using `fun x => by`. Rewrite using `[hπC]`. Simplify using `only [key1]`. Conclude with `hs' _`. Take `⟨G, hG⟩` from `hker`.

Set `I₀ : Ideal P` to `Ideal.span ((fun q : (Fin n → P) × Fin n => E q.1 q.2) '' ((G : Set (Fin n → P)) ×ˢ Set.univ))`. Establish `hI₀ : I₀.FG` using `⟨(G ×ˢ Finset.univ).image (fun q : (Fin n → P) × Fin n => E q.1 q.2), by`. Simplify using `[I₀]⟩`. Establish `key3 : ∀ x ∈ LinearMap.ker π, ∀ j, E x j ∈ I₀`. Introduce `x hx j`.

Rewrite `hx` using `[← hG]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Ideal.subset_span ⟨(x, j), ⟨hx, trivial⟩, rfl⟩`. Consider the case `zero => simp [E]`. Consider the case `add x y _ _ hx hy`.

Establish `: E (x + y) j = E x j + E y j` using `by simp [E, add_mul, Finset.sum_add_distrib]`. Rewrite using `[this]`. Conclude with `I₀.add_mem hx hy`. Consider the case `smul t x _ hx`. Establish `: E (t • x) j = t * E x j` using `by simp [E, Finset.mul_sum, mul_assoc]`.

Rewrite using `[this]`. Conclude with `I₀.mul_mem_left t hx`. Set `T : Ideal P` to `Ideal.span (Set.range v)`. Establish `hET : ∀ x j, E x j ∈ T` using `fun x j => T.sum_mem fun i _ => T.mul_mem_left _ (Ideal.subset_span ⟨(i, j), rfl⟩)`. Establish `hle : (⊤ : Submodule P M) ≤ T • (⊤ : Submodule P M)`.

Introduce `m _`. Take `⟨x, rfl⟩` from `hπ m`. Rewrite using `[← key2, hπb]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hET x i) trivial`. Take `⟨r, hr, hr0⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul T ⊤ Module.Finite.fg_top hle`.

Establish `hrI : r ∈ RingHom.ker (algebraMap P C)`. Rewrite using `[RingHom.mem_ker]`. Use `faith _ fun m => ?_` and prove the remaining obligations. Rewrite using `[algebraMap_smul]`. Conclude with `hr0 m trivial`.

Establish `key5 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ p, a * v p ∈ I₀`. Introduce and unpack `a ha ⟨i, j⟩`. Establish `hx : (Pi.single i a : Fin n → P) ∈ LinearMap.ker π`. Rewrite using `[LinearMap.mem_ker, hπC]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Rewrite using `[Pi.single_eq_same, RingHom.mem_ker.1 ha, zero_smul]`. Rewrite using `[Pi.single_eq_of_ne hk, map_zero, zero_smul]`. Use `key3 _ hx j` as an intermediate fact.

Simplify `this` using `[E, Pi.single_apply]`. Establish `key6 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ t ∈ T, a * t ∈ I₀`. Introduce `a ha t ht`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht => obtain ⟨p, rfl⟩ := ht`.

Conclude with `key5 a ha p`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `I₀.add_mem hx hy`. Consider the case `smul c x _ hx`.

Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `I₀.mul_mem_left c hx`. Establish `hI₀le : I₀ ≤ RingHom.ker (algebraMap P C)`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨g, j⟩, ⟨hg, -⟩, rfl⟩`.

Establish `hgk : g ∈ LinearMap.ker π`. Rewrite using `[← hG]`. Conclude with `Submodule.subset_span hg`. Express the relevant statement in the definitionally equal form `algebraMap P C (E g j) = 0`. Rewrite using `[key1, LinearMap.mem_ker.1 hgk, map_zero]`.

Both sides reduce to the same expression. Establish `heq : RingHom.ker (algebraMap P C) = I₀ ⊔ Ideal.span {r}`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Establish `h1 : a * (r - 1) ∈ I₀` using `key6 a ha _ hr`.

Establish `h2 : a * r ∈ Ideal.span {r}` using `Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self r)`. Establish `: a = a * r + -(a * (r - 1))` using `by ring`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup h2 (I₀.neg_mem h1) |> fun h => by`. Rewrite using `[sup_comm]`.

Conclude with `h`. Use `sup_le hI₀le ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `hrI`. Rewrite using `[heq]`.

Conclude with `Submodule.FG.sup hI₀ (Submodule.fg_span_singleton r)`.
-/
theorem ker_fg_of_projective {P C M : Type*} [CommRing P] [CommRing C] [Algebra P C]
    [AddCommGroup M] [Module P M] [Module C M] [IsScalarTower P C M]
    (hsurj : Function.Surjective (algebraMap P C))
    [Module.FinitePresentation P M] [Module.Projective C M]
    (faith : ∀ c : C, (∀ m : M, c • m = 0) → c = 0) :
    (RingHom.ker (algebraMap P C)).FG := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' P M
  have hker : (LinearMap.ker π).FG := Module.FinitePresentation.fg_ker π hπ
  let b : Fin n → M := fun i => π (Pi.single i 1)
  have hπb : ∀ x, π x = ∑ i, x i • b i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ π x]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [b, Pi.single_apply, eq_comm]
  have hπC : ∀ x, π x = ∑ i, algebraMap P C (x i) • b i := fun x => by
    rw [hπb]
    simp only [algebraMap_smul]
  let πC : (Fin n → C) →ₗ[C] M := Fintype.linearCombination C b
  have hπCs : Function.Surjective πC := by
    intro m
    obtain ⟨x, rfl⟩ := hπ m
    refine ⟨fun i => algebraMap P C (x i), ?_⟩
    rw [hπC, Fintype.linearCombination_apply]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property πC LinearMap.id hπCs
  have hs' : ∀ m, ∑ i, s m i • b i = m := fun m => by
    have := LinearMap.congr_fun hs m
    simpa [πC, Fintype.linearCombination_apply] using this
  choose v hv using fun (p : Fin n × Fin n) => hsurj (s (b p.1) p.2)
  let E : (Fin n → P) → Fin n → P := fun x j => ∑ i, x i * v (i, j)
  have key1 : ∀ x j, algebraMap P C (E x j) = s (π x) j := fun x j => by
    have hsx : s (π x) = ∑ i, algebraMap P C (x i) • s (b i) := by
      rw [hπC, map_sum]
      simp only [map_smul]
    rw [hsx, Finset.sum_apply]
    simp only [E, map_sum, map_mul, hv, Pi.smul_apply, smul_eq_mul]
  have key2 : ∀ x, π (fun j => E x j) = π x := fun x => by
    rw [hπC]
    simp only [key1]
    exact hs' _
  obtain ⟨G, hG⟩ := hker
  let I₀ : Ideal P := Ideal.span ((fun q : (Fin n → P) × Fin n => E q.1 q.2) ''
    ((G : Set (Fin n → P)) ×ˢ Set.univ))
  have hI₀ : I₀.FG := ⟨(G ×ˢ Finset.univ).image (fun q : (Fin n → P) × Fin n => E q.1 q.2), by
    simp [I₀]⟩
  have key3 : ∀ x ∈ LinearMap.ker π, ∀ j, E x j ∈ I₀ := by
    intro x hx j
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span ⟨(x, j), ⟨hx, trivial⟩, rfl⟩
    | zero => simp [E]
    | add x y _ _ hx hy =>
      have : E (x + y) j = E x j + E y j := by simp [E, add_mul, Finset.sum_add_distrib]
      rw [this]; exact I₀.add_mem hx hy
    | smul t x _ hx =>
      have : E (t • x) j = t * E x j := by simp [E, Finset.mul_sum, mul_assoc]
      rw [this]; exact I₀.mul_mem_left t hx
  let T : Ideal P := Ideal.span (Set.range v)
  have hET : ∀ x j, E x j ∈ T := fun x j =>
    T.sum_mem fun i _ => T.mul_mem_left _ (Ideal.subset_span ⟨(i, j), rfl⟩)
  have hle : (⊤ : Submodule P M) ≤ T • (⊤ : Submodule P M) := by
    intro m _
    obtain ⟨x, rfl⟩ := hπ m
    rw [← key2, hπb]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hET x i) trivial
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul T ⊤
    Module.Finite.fg_top hle
  have hrI : r ∈ RingHom.ker (algebraMap P C) := by
    rw [RingHom.mem_ker]
    refine faith _ fun m => ?_
    rw [algebraMap_smul]
    exact hr0 m trivial
  have key5 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ p, a * v p ∈ I₀ := by
    rintro a ha ⟨i, j⟩
    have hx : (Pi.single i a : Fin n → P) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, hπC]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = i
      · subst hk
        rw [Pi.single_eq_same, RingHom.mem_ker.1 ha, zero_smul]
      · rw [Pi.single_eq_of_ne hk, map_zero, zero_smul]
    have := key3 _ hx j
    simpa [E, Pi.single_apply] using this
  have key6 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ t ∈ T, a * t ∈ I₀ := by
    intro a ha t ht
    induction ht using Submodule.span_induction with
    | mem t ht => obtain ⟨p, rfl⟩ := ht; exact key5 a ha p
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact I₀.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, mul_left_comm]; exact I₀.mul_mem_left c hx
  have hI₀le : I₀ ≤ RingHom.ker (algebraMap P C) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, ⟨hg, -⟩, rfl⟩
    have hgk : g ∈ LinearMap.ker π := by
      rw [← hG]; exact Submodule.subset_span hg
    change algebraMap P C (E g j) = 0
    rw [key1, LinearMap.mem_ker.1 hgk, map_zero]
    rfl
  have heq : RingHom.ker (algebraMap P C) = I₀ ⊔ Ideal.span {r} := by
    apply le_antisymm
    · intro a ha
      have h1 : a * (r - 1) ∈ I₀ := key6 a ha _ hr
      have h2 : a * r ∈ Ideal.span {r} := Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self r)
      have : a = a * r + -(a * (r - 1)) := by ring
      rw [this]
      exact Submodule.add_mem_sup h2 (I₀.neg_mem h1) |> fun h => by
        rw [sup_comm]; exact h
    · refine sup_le hI₀le ?_
      rw [Ideal.span_singleton_le_iff_mem]
      exact hrI
  rw [heq]
  exact Submodule.FG.sup hI₀ (Submodule.fg_span_singleton r)

end GlobalTheory.CompanionTheory.FinPresDescent

open GlobalTheory.CompanionTheory.FinPresDescent in

/- English proof (translation)
Introduce `R C D _ _ _ _ _ _ _ hfin hproj hff hfp`. Establish `hinj : Function.Injective (algebraMap C D)` using `FaithfulSMul.algebraMap_injective C D`. Use `haveI : Algebra.FiniteType R D := inferInstance`. Use `haveI : Algebra.FiniteType R C := finiteType_of_finite_projective R C D hinj`. Take `⟨k, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R C›`.

Use `letI : Algebra (MvPolynomial (Fin k) R) C := f.toRingHom.toAlgebra`. Use `letI : Algebra (MvPolynomial (Fin k) R) D := ((algebraMap C D).comp f.toRingHom).toAlgebra`. Use `haveI : IsScalarTower (MvPolynomial (Fin k) R) C D := .of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower R (MvPolynomial (Fin k) R) D := .of_algebraMap_eq fun r => by`. Express the relevant statement in the definitionally equal form `algebraMap R D r = algebraMap C D (f (algebraMap R _ r))`.

Rewrite using `[f.commutes, ← IsScalarTower.algebraMap_apply]`. Use `haveI : Algebra.FinitePresentation (MvPolynomial (Fin k) R) D := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ D`. Use `haveI : Module.Finite (MvPolynomial (Fin k) R) C := Module.Finite.of_surjective (Algebra.linearMap _ C) hf`. Use `haveI : Module.Finite (MvPolynomial (Fin k) R) D := Module.Finite.trans C D`. Use `haveI : Module.FinitePresentation (MvPolynomial (Fin k) R) D := Module.FinitePresentation.of_finite_of_finitePresentation _ D`.

Establish `hker` using `ker_fg_of_projective (P := MvPolynomial (Fin k) R) (C := C) (M := D) hf (fun c hc => hinj (by simpa [Algebra.smul_def] using hc 1))`. Conclude with `⟨k, f, hf, hker⟩`.
-/
theorem GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat :
    ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D]
      [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D →
      Module.FaithfullyFlat C D → Algebra.FinitePresentation R D →
      Algebra.FinitePresentation R C := by
  intro R C D _ _ _ _ _ _ _ hfin hproj hff hfp
  have hinj : Function.Injective (algebraMap C D) := FaithfulSMul.algebraMap_injective C D
  haveI : Algebra.FiniteType R D := inferInstance
  haveI : Algebra.FiniteType R C := finiteType_of_finite_projective R C D hinj
  obtain ⟨k, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R C›
  letI : Algebra (MvPolynomial (Fin k) R) C := f.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin k) R) D := ((algebraMap C D).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin k) R) C D := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R (MvPolynomial (Fin k) R) D := .of_algebraMap_eq fun r => by
    change algebraMap R D r = algebraMap C D (f (algebraMap R _ r))
    rw [f.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.FinitePresentation (MvPolynomial (Fin k) R) D :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ D
  haveI : Module.Finite (MvPolynomial (Fin k) R) C :=
    Module.Finite.of_surjective (Algebra.linearMap _ C) hf
  haveI : Module.Finite (MvPolynomial (Fin k) R) D := Module.Finite.trans C D
  haveI : Module.FinitePresentation (MvPolynomial (Fin k) R) D :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ D
  have hker := ker_fg_of_projective (P := MvPolynomial (Fin k) R) (C := C) (M := D) hf
    (fun c hc => hinj (by simpa [Algebra.smul_def] using hc 1))
  exact ⟨k, f, hf, hker⟩
