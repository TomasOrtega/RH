import Mathlib
import Formalism.PeriodIntegrals.SelfDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis

namespace Bl.PaddedFamilies

open NumberField IsDedekindDomain

/- English proof (translation)
Take `⟨e⟩ : Nonempty (ι ↪ Fin n)` from `Function.Embedding.nonempty_of_card_le (by simpa using hcard)`. Use `⟨Function.extend e X 0, fun i => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : ∃ j, e j = i`. Take `⟨j, rfl⟩` from `h`. Rewrite using `[e.injective.extend_apply]`.

Conclude with `hX j`. Rewrite using `[Function.extend_apply' _ _ _ h]`. Conclude with `Lb.zero_mem`. Establish `hsub : Set.range X ⊆ Set.range (Function.extend e X 0)`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `⟨e j, e.injective.extend_apply _ _ _⟩`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp (Submodule.span_mono hsub (hc z hz))`. Conclude with `⟨a, ha.symm⟩`.
-/
private lemma pad_fam {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Lb : Submodule (𝓞 E) (Fin n → E)) {ι : Type} [Fintype ι] (hcard : Fintype.card ι ≤ n)
    (X : ι → Fin n → E) (hX : ∀ j, X j ∈ Lb) (c : E)
    (hc : ∀ z ∈ Lb, c • z ∈ Submodule.span (𝓞 E) (Set.range X)) :
    ∃ x : Fin n → Fin n → E, (∀ i, x i ∈ Lb) ∧
      ∀ z ∈ Lb, ∃ a : Fin n → 𝓞 E, c • z = ∑ i, ((a i : 𝓞 E) : E) • x i := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  refine ⟨Function.extend e X 0, fun i => ?_, fun z hz => ?_⟩
  · by_cases h : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := h
      rw [e.injective.extend_apply]
      exact hX j
    · rw [Function.extend_apply' _ _ _ h]
      exact Lb.zero_mem
  · have hsub : Set.range X ⊆ Set.range (Function.extend e X 0) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨e j, e.injective.extend_apply _ _ _⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp
      (Submodule.span_mono hsub (hc z hz))
    exact ⟨a, ha.symm⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ n v Lb hfin hspan`. Take `⟨S, hS⟩` from `(Module.Finite.iff_fg.mp hfin)`. Use `set M := Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl with hMdef`. Establish `hM : M ≤ nonZeroDivisors (𝓞 E)` using `map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _) v.asIdeal.primeCompl_le_nonZeroDivisors`. Set `A : Subalgebra (𝓞 E) E` to `Localization.subalgebra.ofField E M hM`.

Establish `: IsLocalization M A` using `inferInstance`. Establish `: IsDedekindDomain A` using `IsLocalization.isDedekindDomain (𝓞 E) hM A`. Set `: Algebra (𝓞 F) A` to `((algebraMap (𝓞 E) A).comp (algebraMap (𝓞 F) (𝓞 E))).toAlgebra`. Establish `: IsScalarTower (𝓞 F) (𝓞 E) A` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: IsPrincipalIdealRing A` using `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot`.

Establish `h1 : ∀ z : M, ((IsLocalization.mk' A (1 : 𝓞 E) z : A) : E) * ((z : 𝓞 E) : E) = 1`. Introduce `z`. Establish `h` using `IsLocalization.mk'_spec A (1 : 𝓞 E) z`. Rewrite `h` using `[map_one]`. Conclude with `congrArg Subtype.val h`.

Set `N : Submodule A (Fin n → E)` to `Submodule.span A (S : Set (Fin n → E))`. Establish `: Module.Free A N` using `Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.Free.chooseBasis A N`. Establish `hb : ∀ j, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ (algebraMap F E (t : F)) • (b j : Fin n → E) ∈ Lb`. Introduce `j`.

Take `⟨y, hy, z, hz⟩` from `(IsLocalization.mem_span_iff M).mp (b j).2`. Take `⟨t, ht, hzt⟩` from `z.2`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[hS]`. Establish `key : ((z : 𝓞 E) : E) • (b j : Fin n → E) = y`.

Rewrite using `[hz]`. Express the relevant statement in the definitionally equal form `((z : 𝓞 E) : E) • (((IsLocalization.mk' A (1 : 𝓞 E) z : A) : E) • y) = y`. Rewrite using `[smul_smul, mul_comm, h1, one_smul]`. Rewrite `key` using `[← hzt]`. Rewrite `hy` using `[← key]`.

Conclude with `hy`. Use `choose t ht hX using hb`. Establish `hlin : LinearIndependent E (fun j => (b j : Fin n → E))` using `(b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)).localization (Rₛ := E) (S := nonZeroDivisors A)`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex A N) ≤ n`. Use `hlin.fintype_card_le_finrank` as an intermediate fact.

Rewrite `this` using `[Module.finrank_fin_fun]`. Then use the resulting hypothesis. Set `ι` to `Module.Free.ChooseBasisIndex A N`. Set `zt : ι → M` to `fun j => ⟨algebraMap (𝓞 F) (𝓞 E) (t j), t j, ht j, rfl⟩`. Set `f : (↥S × ι) → A` to `fun p => b.repr ⟨p.1, Submodule.subset_span p.1.2⟩ p.2 * IsLocalization.mk' A (1 : 𝓞 E) (zt p.2)`. Take `⟨m, hm⟩` from `IsLocalization.exist_integer_multiples_of_finite M f`.

Take `⟨u, hu, hmu⟩` from `m.2`. Establish `hmE : ((m : 𝓞 E) : E) = algebraMap F E (u : F)`. Rewrite using `[← hmu]`. Both sides reduce to the same expression. Set `X : ι → Fin n → E` to `fun j => algebraMap F E (t j : F) • (b j : Fin n → E)`.

Establish `hc : ∀ z ∈ Lb, algebraMap F E (u : F) • z ∈ Submodule.span (𝓞 E) (Set.range X)`. Introduce `z hz`. Rewrite `hz` using `[← hS]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem g hg`.

Establish `hsum` using `congrArg Subtype.val (b.sum_repr ⟨g, Submodule.subset_span hg⟩)`. Rewrite `hsum` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at hsum`. Rewrite using `[← hsum, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Take `⟨r, hr⟩` from `hm (⟨g, hg⟩, j)`. Establish `hrE : (r : E) = ((m : 𝓞 E) : E) * (((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) : E) * ((IsLocalization.mk' A (1 : 𝓞 E) (zt j) : A) : E))` using `congrArg Subtype.val hr`. Establish `htE : ((IsLocalization.mk' A (1 : 𝓞 E) (zt j) : A) : E) * algebraMap F E (t j : F) = 1` using `h1 (zt j)`. Establish `heq : algebraMap F E (u : F) • ((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) • (b j : Fin n → E)) = r • X j`. Express the relevant statement in the definitionally equal form `algebraMap F E (u : F) • (((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) : E) • (b j : Fin n → E)) = (r : E) • (algebraMap F E (t j : F) • (b j : Fin n → E))`.

Rewrite using `[smul_smul, smul_smul, hrE, hmE, mul_assoc, mul_assoc, htE, mul_one]`. Rewrite using `[heq]`. Conclude with `Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)`. Consider the case `zero`. Rewrite using `[smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ a hx`. Take `⟨x, hx1, hx2⟩` from `pad_fam Lb hcard X hX _ hc`. Conclude with `⟨x, u, hu, hx1, hx2⟩`.
-/
theorem goal1 :
  PI.SelfDualLoc.W.LocBasis := by
  intro F E _ _ _ _ _ n v Lb hfin hspan
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.iff_fg.mp hfin)
  set M := Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl with hMdef
  have hM : M ≤ nonZeroDivisors (𝓞 E) := map_le_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective _ _) v.asIdeal.primeCompl_le_nonZeroDivisors
  let A : Subalgebra (𝓞 E) E := Localization.subalgebra.ofField E M hM
  have : IsLocalization M A := inferInstance
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain (𝓞 E) hM A
  let : Algebra (𝓞 F) A := ((algebraMap (𝓞 E) A).comp (algebraMap (𝓞 F) (𝓞 E))).toAlgebra
  have : IsScalarTower (𝓞 F) (𝓞 E) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsPrincipalIdealRing A :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot
  have h1 : ∀ z : M, ((IsLocalization.mk' A (1 : 𝓞 E) z : A) : E) * ((z : 𝓞 E) : E) = 1 := by
    intro z
    have h := IsLocalization.mk'_spec A (1 : 𝓞 E) z
    rw [map_one] at h
    exact congrArg Subtype.val h
  let N : Submodule A (Fin n → E) := Submodule.span A (S : Set (Fin n → E))
  have : Module.Free A N := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis A N
  have hb : ∀ j, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      (algebraMap F E (t : F)) • (b j : Fin n → E) ∈ Lb := by
    intro j
    obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff M).mp (b j).2
    obtain ⟨t, ht, hzt⟩ := z.2
    refine ⟨t, ht, ?_⟩
    rw [hS] at hy
    have key : ((z : 𝓞 E) : E) • (b j : Fin n → E) = y := by
      rw [hz]
      change ((z : 𝓞 E) : E) • (((IsLocalization.mk' A (1 : 𝓞 E) z : A) : E) • y) = y
      rw [smul_smul, mul_comm, h1, one_smul]
    rw [← hzt] at key
    rw [← key] at hy
    exact hy
  choose t ht hX using hb
  have hlin : LinearIndependent E (fun j => (b j : Fin n → E)) :=
    (b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)).localization
      (Rₛ := E) (S := nonZeroDivisors A)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A N) ≤ n := by
    have := hlin.fintype_card_le_finrank
    rwa [Module.finrank_fin_fun] at this
  let ι := Module.Free.ChooseBasisIndex A N
  let zt : ι → M := fun j => ⟨algebraMap (𝓞 F) (𝓞 E) (t j), t j, ht j, rfl⟩
  let f : (↥S × ι) → A := fun p =>
    b.repr ⟨p.1, Submodule.subset_span p.1.2⟩ p.2 * IsLocalization.mk' A (1 : 𝓞 E) (zt p.2)
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite M f
  obtain ⟨u, hu, hmu⟩ := m.2
  have hmE : ((m : 𝓞 E) : E) = algebraMap F E (u : F) := by
    rw [← hmu]
    rfl
  let X : ι → Fin n → E := fun j => algebraMap F E (t j : F) • (b j : Fin n → E)
  have hc : ∀ z ∈ Lb, algebraMap F E (u : F) • z ∈ Submodule.span (𝓞 E) (Set.range X) := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem g hg =>
      have hsum := congrArg Subtype.val (b.sum_repr ⟨g, Submodule.subset_span hg⟩)
      rw [Submodule.coe_sum] at hsum
      simp only [Submodule.coe_smul] at hsum
      rw [← hsum, Finset.smul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      obtain ⟨r, hr⟩ := hm (⟨g, hg⟩, j)
      have hrE : (r : E) = ((m : 𝓞 E) : E) *
          (((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) : E) *
            ((IsLocalization.mk' A (1 : 𝓞 E) (zt j) : A) : E)) := congrArg Subtype.val hr
      have htE : ((IsLocalization.mk' A (1 : 𝓞 E) (zt j) : A) : E) * algebraMap F E (t j : F) = 1 :=
        h1 (zt j)
      have heq : algebraMap F E (u : F) •
          ((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) • (b j : Fin n → E)) = r • X j := by
        change algebraMap F E (u : F) •
          (((b.repr ⟨g, Submodule.subset_span hg⟩ j : A) : E) • (b j : Fin n → E)) =
            (r : E) • (algebraMap F E (t j : F) • (b j : Fin n → E))
        rw [smul_smul, smul_smul, hrE, hmE, mul_assoc, mul_assoc, htE, mul_one]
      rw [heq]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx
  obtain ⟨x, hx1, hx2⟩ := pad_fam Lb hcard X hX _ hc
  exact ⟨x, u, hu, hx1, hx2⟩

end Bl.PaddedFamilies
