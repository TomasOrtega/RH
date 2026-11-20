import Mathlib

namespace GlobalTheory

open Algebra

/- English proof (translation)
Use `set M : Submonoid S := Algebra.algebraMapSubmonoid S (nonZeroDivisors R) with hM`. Set `T` to `Localization M`. Establish `hinj : Function.Injective (algebraMap R S)` using `FaithfulSMul.algebraMap_injective R S`. Establish `hMle : M ≤ nonZeroDivisors S`. Introduce and unpack `_ ⟨r, hr, rfl⟩`.

Conclude with `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr))`. Use `haveI : IsDomain T := IsLocalization.isDomain_localization hMle`. Establish `hTinj : Function.Injective (algebraMap S T)` using `IsLocalization.injective T hMle`. Establish `hbot : (⊥ : Ideal T).IsMaximal`. Take `⟨m, hm⟩` from `Ideal.exists_maximal T`.

Establish `hmp` using `hm.isPrime`. Use `set Q := m.comap (algebraMap S T)`. Establish `hQ : Q.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hdisj : Disjoint (M : Set S) Q` using `((IsLocalization.isPrime_iff_isPrime_disjoint M T m).1 hmp).2`. Establish `hQc : Q.comap (algebraMap R S) = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `r hr`. Rewrite using `[Ideal.mem_bot]`. Assume the negation of the conclusion as `hr0`. Establish `hrM : algebraMap R S r ∈ M` using `⟨r, mem_nonZeroDivisors_of_ne_zero hr0, rfl⟩`.

Conclude with `Set.disjoint_left.1 hdisj hrM hr`. Establish `hQb : Q = ⊥` using `h Q hQ hQc`. Establish `: m = ⊥`. Rewrite using `[← IsLocalization.map_comap M T m]`. Express the relevant statement in the definitionally equal form `Ideal.map (algebraMap S T) Q = ⊥`.

Rewrite using `[hQb, Ideal.map_bot]`. Rewrite using `[← this]`. Conclude with `hm`. Establish `hfield : IsField T` using `Ring.isField_iff_maximal_bot.2 hbot`. Use `letI : Field T := hfield.toField`.

Set `K` to `Localization (nonZeroDivisors R)`. Use `haveI : IsScalarTower R K T := inferInstance`. Use `haveI : Algebra.FiniteType K T := by`. Take `⟨s, hs⟩` from `(inferInstance : Algebra.FiniteType R S).out`. Use `⟨⟨s.image (algebraMap S T), ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[_root_.eq_top_iff]`. Introduce `t _`. Take `⟨x, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩` from `IsLocalization.exists_mk'_eq M t`. Establish `hx : algebraMap S T x ∈ Algebra.adjoin K ((s.image (algebraMap S T) : Finset T) : Set T)`. Establish `hxs : x ∈ Algebra.adjoin R (s : Set S)` using `hs ▸ Algebra.mem_top`.

Use `Algebra.adjoin_induction (fun y hy => ?_) (fun r' => ?_) (fun a b _ _ ha hb => ?_) (fun a b _ _ ha hb => ?_) hxs` and prove the remaining obligations. Conclude with `Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hy)))`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K T]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Rewrite using `[map_add]`.

Conclude with `add_mem ha hb`. Rewrite using `[map_mul]`. Conclude with `mul_mem ha hb`. Establish `he : IsLocalization.mk' T x (⟨algebraMap R S r, ⟨r, hr, rfl⟩⟩ : M) = algebraMap K T (IsLocalization.mk' K (1 : R) (⟨r, hr⟩ : nonZeroDivisors R)) * algebraMap S T x`. Rewrite using `[IsLocalization.mk'_eq_iff_eq_mul]`.

Establish `h3 : algebraMap K T (IsLocalization.mk' K (1 : R) (⟨r, hr⟩ : nonZeroDivisors R)) * algebraMap S T (algebraMap R S r) = 1`. Rewrite using `[← IsScalarTower.algebraMap_apply R S T, IsScalarTower.algebraMap_apply R K T, ← map_mul]`. Use `IsLocalization.mk'_spec K (1 : R) (⟨r, hr⟩ : nonZeroDivisors R)` as an intermediate fact. Simplify using `only [map_one] at this`. Rewrite using `[this, map_one]`.

Express the relevant statement in the definitionally equal form `_ = _ * _ * algebraMap S T (algebraMap R S r)`. Rewrite using `[mul_right_comm, h3, one_mul]`. Rewrite using `[he]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ _) hx`. Use `haveI : Module.Finite K T := finite_of_finite_type_of_isJacobsonRing K T`.

Use `haveI : Algebra.IsAlgebraic K T := Algebra.IsAlgebraic.of_finite K T`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : IsAlgebraic K (algebraMap S T x)` using `Algebra.IsAlgebraic.isAlgebraic _`. Establish `h2 : IsAlgebraic R (algebraMap S T x)` using `(IsFractionRing.isAlgebraic_iff R K T).2 h1`. Conclude with `(isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S T) hTinj).1 h2`.
-/
theorem isAlgebraic_of_finiteType_of_comap_eq_bot
    (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [FaithfulSMul R S] [Algebra.FiniteType R S]
    (h : ∀ Q : Ideal S, Q.IsPrime → Q.comap (algebraMap R S) = ⊥ → Q = ⊥) :
    Algebra.IsAlgebraic R S := by
  classical
  set M : Submonoid S := Algebra.algebraMapSubmonoid S (nonZeroDivisors R) with hM
  let T := Localization M
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have hMle : M ≤ nonZeroDivisors S := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr))
  haveI : IsDomain T := IsLocalization.isDomain_localization hMle
  have hTinj : Function.Injective (algebraMap S T) := IsLocalization.injective T hMle

  have hbot : (⊥ : Ideal T).IsMaximal := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal T
    have hmp := hm.isPrime
    set Q := m.comap (algebraMap S T)
    have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
    have hdisj : Disjoint (M : Set S) Q := ((IsLocalization.isPrime_iff_isPrime_disjoint M T m).1 hmp).2
    have hQc : Q.comap (algebraMap R S) = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      rw [Ideal.mem_bot]
      by_contra hr0
      have hrM : algebraMap R S r ∈ M := ⟨r, mem_nonZeroDivisors_of_ne_zero hr0, rfl⟩
      exact Set.disjoint_left.1 hdisj hrM hr
    have hQb : Q = ⊥ := h Q hQ hQc
    have : m = ⊥ := by
      rw [← IsLocalization.map_comap M T m]
      change Ideal.map (algebraMap S T) Q = ⊥
      rw [hQb, Ideal.map_bot]
    rw [← this]; exact hm
  have hfield : IsField T := Ring.isField_iff_maximal_bot.2 hbot
  letI : Field T := hfield.toField

  let K := Localization (nonZeroDivisors R)
  haveI : IsScalarTower R K T := inferInstance
  haveI : Algebra.FiniteType K T := by
    obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S).out
    refine ⟨⟨s.image (algebraMap S T), ?_⟩⟩
    rw [_root_.eq_top_iff]
    intro t _
    obtain ⟨x, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩ := IsLocalization.exists_mk'_eq M t
    have hx : algebraMap S T x ∈ Algebra.adjoin K ((s.image (algebraMap S T) : Finset T) : Set T) := by
      have hxs : x ∈ Algebra.adjoin R (s : Set S) := hs ▸ Algebra.mem_top
      refine Algebra.adjoin_induction (fun y hy => ?_) (fun r' => ?_) (fun a b _ _ ha hb => ?_)
        (fun a b _ _ ha hb => ?_) hxs
      · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hy)))
      · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K T]
        exact Subalgebra.algebraMap_mem _ _
      · rw [map_add]; exact add_mem ha hb
      · rw [map_mul]; exact mul_mem ha hb
    have he : IsLocalization.mk' T x (⟨algebraMap R S r, ⟨r, hr, rfl⟩⟩ : M)
        = algebraMap K T (IsLocalization.mk' K (1 : R) (⟨r, hr⟩ : nonZeroDivisors R)) * algebraMap S T x := by
      rw [IsLocalization.mk'_eq_iff_eq_mul]
      have h3 : algebraMap K T (IsLocalization.mk' K (1 : R) (⟨r, hr⟩ : nonZeroDivisors R))
          * algebraMap S T (algebraMap R S r) = 1 := by
        rw [← IsScalarTower.algebraMap_apply R S T, IsScalarTower.algebraMap_apply R K T, ← map_mul]
        have := IsLocalization.mk'_spec K (1 : R) (⟨r, hr⟩ : nonZeroDivisors R)
        simp only [map_one] at this
        rw [this, map_one]
      change _ = _ * _ * algebraMap S T (algebraMap R S r)
      rw [mul_right_comm, h3, one_mul]
    rw [he]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hx
  haveI : Module.Finite K T := finite_of_finite_type_of_isJacobsonRing K T
  haveI : Algebra.IsAlgebraic K T := Algebra.IsAlgebraic.of_finite K T
  refine ⟨fun x => ?_⟩
  have h1 : IsAlgebraic K (algebraMap S T x) := Algebra.IsAlgebraic.isAlgebraic _
  have h2 : IsAlgebraic R (algebraMap S T x) := (IsFractionRing.isAlgebraic_iff R K T).2 h1
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S T) hTinj).1 h2

end GlobalTheory
