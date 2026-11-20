import Mathlib

open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing

namespace GlobalTheory

section Gauss

variable {F X : Type*} [Field F] [AddCommMonoid X] [UniqueSums X]

/- English proof (translation)
Distinguish the cases in `hi : f.coeff i = 0`. Conclude with `⟨0, by simp [hi]⟩`. Distinguish the cases in `hj : g.coeff j = 0`. Conclude with `⟨0, by simp [hj]⟩`. Take `⟨a, ha, hamax⟩` from `f.coeff.support.exists_max_image (fun x => v (f.coeff x)) ⟨i, Finsupp.mem_support_iff.mpr hi⟩`.

Take `⟨b, hb, hbmax⟩` from `g.coeff.support.exists_max_image (fun x => v (g.coeff x)) ⟨j, Finsupp.mem_support_iff.mpr hj⟩`. Take `⟨a₀, ha₀, b₀, hb₀, hu⟩` from `UniqueSums.uniqueAdd_of_nonempty (A := f.coeff.support.filter fun x => v (f.coeff x) = v (f.coeff a)) (B := g.coeff.support.filter fun x => v (g.coeff x) = v (g.coeff b)) ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩ ⟨b, Finset.mem_filter.mpr ⟨hb, rfl⟩⟩`. Rewrite `ha₀`, `hb₀` using `[Finset.mem_filter]`. Establish `hapos : 0 < v (f.coeff a)` using `zero_lt_iff.mpr ((map_ne_zero v).mpr (Finsupp.mem_support_iff.mp ha))`. Establish `hbpos : 0 < v (g.coeff b)` using `zero_lt_iff.mpr ((map_ne_zero v).mpr (Finsupp.mem_support_iff.mp hb))`.

Use `⟨a₀ + b₀, ?_⟩` and prove the remaining obligations. Establish `key : v ((f * g).coeff (a₀ + b₀)) = v (f.coeff a) * v (g.coeff b)`. Repeatedly rewrite using `[coeff_mul, Finsupp.sum, ← Finset.sum_product']`. Rewrite using `[v.map_sum_eq_of_lt (j := (a₀, b₀)) (Finset.mem_product.mpr ⟨ha₀.1, hb₀.1⟩)]`. Simplify using `[ha₀.2, hb₀.2]`.

Introduce and unpack `⟨x, y⟩ hxy`. Rewrite `hxy` using `[Finset.mem_sdiff, Finset.mem_product, Finset.mem_singleton]`. Take `⟨⟨hx, hy⟩, hne⟩` from `hxy`. Simplify using `only [if_true, map_mul, ha₀.2, hb₀.2]`. Use `split_ifs with h`.

Rewrite using `[map_mul]`. Break down `(hamax x hx).lt_or_eq with h1 | h1` into its components or cases. Conclude with `mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h1 (hbmax y hy) zero_le hbpos`. Break down `(hbmax y hy).lt_or_eq with h2 | h2` into its components or cases. Rewrite using `[h1]`.

Conclude with `mul_lt_mul_of_pos_left h2 hapos`. Take `⟨rfl, rfl⟩` from `hu (Finset.mem_filter.mpr ⟨hx, h1⟩) (Finset.mem_filter.mpr ⟨hy, h2⟩) h`. Conclude with `absurd rfl hne`. Rewrite using `[map_zero]`. Conclude with `mul_pos hapos hbpos`.

Rewrite using `[key, map_mul]`. Conclude with `mul_le_mul' (hamax i (Finsupp.mem_support_iff.mpr hi)) (hbmax j (Finsupp.mem_support_iff.mpr hj))`.
-/
theorem exists_valuation_coeff_mul_coeff_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) (f g : AddMonoidAlgebra F X) (i j : X) :
    ∃ k, v (f.coeff i * g.coeff j) ≤ v ((f * g).coeff k) := by
  classical
  by_cases hi : f.coeff i = 0
  · exact ⟨0, by simp [hi]⟩
  by_cases hj : g.coeff j = 0
  · exact ⟨0, by simp [hj]⟩
  obtain ⟨a, ha, hamax⟩ := f.coeff.support.exists_max_image (fun x => v (f.coeff x))
    ⟨i, Finsupp.mem_support_iff.mpr hi⟩
  obtain ⟨b, hb, hbmax⟩ := g.coeff.support.exists_max_image (fun x => v (g.coeff x))
    ⟨j, Finsupp.mem_support_iff.mpr hj⟩
  obtain ⟨a₀, ha₀, b₀, hb₀, hu⟩ := UniqueSums.uniqueAdd_of_nonempty
    (A := f.coeff.support.filter fun x => v (f.coeff x) = v (f.coeff a))
    (B := g.coeff.support.filter fun x => v (g.coeff x) = v (g.coeff b))
    ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩ ⟨b, Finset.mem_filter.mpr ⟨hb, rfl⟩⟩
  rw [Finset.mem_filter] at ha₀ hb₀
  have hapos : 0 < v (f.coeff a) :=
    zero_lt_iff.mpr ((map_ne_zero v).mpr (Finsupp.mem_support_iff.mp ha))
  have hbpos : 0 < v (g.coeff b) :=
    zero_lt_iff.mpr ((map_ne_zero v).mpr (Finsupp.mem_support_iff.mp hb))
  refine ⟨a₀ + b₀, ?_⟩
  have key : v ((f * g).coeff (a₀ + b₀)) = v (f.coeff a) * v (g.coeff b) := by
    simp_rw [coeff_mul, Finsupp.sum, ← Finset.sum_product']
    rw [v.map_sum_eq_of_lt (j := (a₀, b₀)) (Finset.mem_product.mpr ⟨ha₀.1, hb₀.1⟩)]
    · simp [ha₀.2, hb₀.2]
    · rintro ⟨x, y⟩ hxy
      rw [Finset.mem_sdiff, Finset.mem_product, Finset.mem_singleton] at hxy
      obtain ⟨⟨hx, hy⟩, hne⟩ := hxy
      simp only [if_true, map_mul, ha₀.2, hb₀.2]
      split_ifs with h
      · rw [map_mul]
        rcases (hamax x hx).lt_or_eq with h1 | h1
        · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h1 (hbmax y hy) zero_le hbpos
        rcases (hbmax y hy).lt_or_eq with h2 | h2
        · rw [h1]
          exact mul_lt_mul_of_pos_left h2 hapos
        · obtain ⟨rfl, rfl⟩ := hu (Finset.mem_filter.mpr ⟨hx, h1⟩)
            (Finset.mem_filter.mpr ⟨hy, h2⟩) h
          exact absurd rfl hne
      · rw [map_zero]
        exact mul_pos hapos hbpos
  rw [key, map_mul]
  exact mul_le_mul' (hamax i (Finsupp.mem_support_iff.mpr hi))
    (hbmax j (Finsupp.mem_support_iff.mpr hj))

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `: IsIntegrallyClosedIn (algebraMap A F).range F`. Use `Subring.isIntegrallyClosedIn_iff.mpr fun x hx => ?_` and prove the remaining obligations. Set `` to `(algebraMap A F).rangeRestrict.toAlgebra`. Establish `: IsScalarTower A (algebraMap A F).range F` using `.of_algebraMap_eq fun _ => rfl`.

Establish `: Algebra.IsIntegral A (algebraMap A F).range` using `Algebra.isIntegral_of_surjective (algebraMap A F).rangeRestrict_surjective`. Conclude with `IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_trans (R := A) x hx)`. Take `⟨V, hV, hxV⟩` from `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx`. Take `⟨k, hk⟩` from `exists_valuation_coeff_mul_coeff_le V.valuation f g i j`. Conclude with `hxV ((V.valuation_le_one_iff _).mp (hk.trans ((V.valuation_le_one_iff _).mpr (hV (h k)))))`.
-/
theorem coeff_mul_coeff_mem_range_of_isIntegrallyClosed (A : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra A F] [IsFractionRing A F] {f g : AddMonoidAlgebra F X}
    (h : ∀ k, (f * g).coeff k ∈ (algebraMap A F).range) (i j : X) :
    f.coeff i * g.coeff j ∈ (algebraMap A F).range := by
  by_contra hx
  have : IsIntegrallyClosedIn (algebraMap A F).range F := by
    refine Subring.isIntegrallyClosedIn_iff.mpr fun x hx => ?_
    let := (algebraMap A F).rangeRestrict.toAlgebra
    have : IsScalarTower A (algebraMap A F).range F := .of_algebraMap_eq fun _ => rfl
    have : Algebra.IsIntegral A (algebraMap A F).range :=
      Algebra.isIntegral_of_surjective (algebraMap A F).rangeRestrict_surjective
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_trans (R := A) x hx)
  obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx
  obtain ⟨k, hk⟩ := exists_valuation_coeff_mul_coeff_le V.valuation f g i j
  exact hxV ((V.valuation_le_one_iff _).mp
    (hk.trans ((V.valuation_le_one_iff _).mpr (hV (h k)))))

end Gauss

section Content

variable {A F X : Type*} [CommRing A] [CommRing F] [Algebra A F] [AddCommMonoid X]

def coeffSpan (I : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)) : Submodule A F :=
  Submodule.span A {c | ∃ f ∈ I, ∃ x, f.coeff x = c}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨f, hf, x, rfl⟩`.
-/
theorem coeff_mem_coeffSpan {I : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)}
    {f : AddMonoidAlgebra F X} (hf : f ∈ I) (x : X) : f.coeff x ∈ coeffSpan I :=
  Submodule.subset_span ⟨f, hf, x, rfl⟩

/- English proof (translation)
Use `Submodule.mul_induction_on hf (fun g hg h hh => ?_) fun g h hg hh => ?_` and prove the remaining obligations. Repeatedly rewrite using `[coeff_mul, Finsupp.sum]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Submodule.mul_mem_mul (coeff_mem_coeffSpan hg i) (coeff_mem_coeffSpan hh j)`.

Conclude with `Submodule.zero_mem _`. Simplify using `using Submodule.add_mem _ hg hh`.
-/
theorem coeff_mem_coeffSpan_mul {I J : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)}
    {f : AddMonoidAlgebra F X} (hf : f ∈ I * J) (x : X) :
    f.coeff x ∈ coeffSpan I * coeffSpan J := by
  classical
  refine Submodule.mul_induction_on hf (fun g hg h hh => ?_) fun g h hg hh => ?_
  · simp_rw [coeff_mul, Finsupp.sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    split_ifs
    · exact Submodule.mul_mem_mul (coeff_mem_coeffSpan hg i) (coeff_mem_coeffSpan hh j)
    · exact Submodule.zero_mem _
  · simpa using Submodule.add_mem _ hg hh

/- English proof (translation)
Rewrite using `[Submodule.mem_one]`. Conclude with `Set.ext_iff.mp (range_map (M := X) (algebraMap A F : A →+ F)) f`.
-/
theorem mem_one_iff_forall_coeff_mem_range {f : AddMonoidAlgebra F X} :
    f ∈ (1 : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)) ↔
      ∀ x, f.coeff x ∈ (algebraMap A F).range := by
  rw [Submodule.mem_one]
  exact Set.ext_iff.mp (range_map (M := X) (algebraMap A F : A →+ F)) f

noncomputable def constantsLift (X : Type*) [AddCommMonoid X] (M : Submodule A F) :
    AddMonoidAlgebra A X ⊗[A] M →ₗ[AddMonoidAlgebra A X] AddMonoidAlgebra F X :=
  ((singleZeroAlgHom (R := A) (A := F) (M := X)).toLinearMap ∘ₗ M.subtype).liftBaseChange _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem constantsLift_tmul (M : Submodule A F) (r : AddMonoidAlgebra A X) (m : M) :
    constantsLift X M (r ⊗ₜ m) = r • single 0 (m : F) := rfl

/- English proof (translation)
Introduce `f hf` and use `by rw [← f.sum_coeff_single, Finsupp.sum] refine Submodule.sum_mem _ fun x _ => ⟨single x 1 ⊗ₜ ⟨_, coeff_mem_coeffSpan hf x⟩, ?_⟩ rw [constantsLift_tmul, Algebra.smul_def] change mapRingHom X (algebraMap A F) _ * _ = _ simp [single_mul_single]`.
-/
theorem le_range_constantsLift (I : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)) :
    I ≤ LinearMap.range (constantsLift X (coeffSpan I)) := fun f hf => by
  rw [← f.sum_coeff_single, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ => ⟨single x 1 ⊗ₜ ⟨_, coeff_mem_coeffSpan hf x⟩, ?_⟩
  rw [constantsLift_tmul, Algebra.smul_def]
  change mapRingHom X (algebraMap A F) _ * _ = _
  simp [single_mul_single]

/- English proof (translation)
Rewrite using `[constantsLift, LinearMap.range_liftBaseChange, Submodule.span_le]`. Introduce and unpack `_ ⟨m, rfl⟩`. Express the relevant statement in the definitionally equal form `single 0 (m : F) ∈ I`. Establish `h1 : (1 : AddMonoidAlgebra F X) ∈ I * J` using `hIJ ▸ Submodule.one_le.mp le_rfl`. Rewrite using `[← mul_one (single 0 (m : F))]`.

Use `Submodule.mul_induction_on h1 (fun f hf g hg => ?_) fun f g hf hg => ?_` and prove the remaining obligations. Establish `hr : single 0 (m : F) * g ∈ (1 : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X))`. Use `mem_one_iff_forall_coeff_mem_range.mpr fun x => ?_` and prove the remaining obligations. Rewrite using `[coeff_single_zero_mul]`. Conclude with `Submodule.mem_one.mp (h (Submodule.mul_mem_mul m.2 (coeff_mem_coeffSpan hg x)))`.

Take `⟨r, hr⟩` from `Submodule.mem_one.mp hr`. Rewrite using `[mul_left_comm, ← hr, mul_comm, ← Algebra.smul_def]`. Conclude with `I.smul_mem r hf`. Rewrite using `[mul_add]`. Conclude with `I.add_mem hf hg`.
-/
theorem range_constantsLift_le {I J : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)}
    (hIJ : I * J = 1) (h : coeffSpan I * coeffSpan J ≤ 1) :
    LinearMap.range (constantsLift X (coeffSpan I)) ≤ I := by
  rw [constantsLift, LinearMap.range_liftBaseChange, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  change single 0 (m : F) ∈ I
  have h1 : (1 : AddMonoidAlgebra F X) ∈ I * J := hIJ ▸ Submodule.one_le.mp le_rfl
  rw [← mul_one (single 0 (m : F))]
  refine Submodule.mul_induction_on h1 (fun f hf g hg => ?_) fun f g hf hg => ?_
  · have hr : single 0 (m : F) * g ∈
        (1 : Submodule (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)) := by
      refine mem_one_iff_forall_coeff_mem_range.mpr fun x => ?_
      rw [coeff_single_zero_mul]
      exact Submodule.mem_one.mp (h (Submodule.mul_mem_mul m.2 (coeff_mem_coeffSpan hg x)))
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hr
    rw [mul_left_comm, ← hr, mul_comm, ← Algebra.smul_def]
    exact I.smul_mem r hf
  · rw [mul_add]
    exact I.add_mem hf hg

end Content

section Factorial

variable {K P X : Type*} [CommRing K] [AddCommMonoid P] [AddCommGroup X]

/- English proof (translation)
Set `` to `(mapDomainRingHom K f).toAlgebra`. Establish `hφ : ∀ p a, algebraMap (AddMonoidAlgebra K P) (AddMonoidAlgebra K X) (single p a) = single (f p) a` using `fun p a => mapDomain_single`. Establish `: IsLocalization (MonoidHom.mrange (of K P)) (AddMonoidAlgebra K X)`. Use `(isLocalization_iff _ _).mpr ⟨?_, fun s => ?_, fun {a c} h => ⟨1, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨_, p, rfl⟩`.

Use `IsUnit.of_mul_eq_one (single (-f p.toAdd) 1) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap _ _ (single p.toAdd (1 : K)) * _ = _`. Rewrite using `[hφ, single_mul_single, add_neg_cancel, one_mul, one_def]`. Proceed by induction on `s using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => exact ⟨⟨0, 1⟩, by simp⟩`.

Consider the case `add s t hs ht`. Take `⟨⟨a, n⟩, ha⟩` from `hs`. Take `⟨⟨c, m⟩, hc⟩` from `ht`. Use `⟨⟨a * m + c * n, n * m⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Submonoid.coe_mul, map_add, map_mul] at ha hc ⊢`.

Rewrite using `[← ha, ← hc]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `single x a`. Take `⟨p, q, h⟩` from `hs x`. Use `⟨⟨single p a, ⟨single q 1, Multiplicative.ofAdd q, rfl⟩⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[hφ, hφ, single_mul_single, h, mul_one]`. Rewrite using `[mapDomain_injective hf h]`. Conclude with `.of_isLocalization (MonoidHom.mrange (of K P)) _`.
-/
theorem uniqueFactorizationMonoid_addMonoidAlgebra_of_sub (f : P →+ X)
    (hf : Function.Injective f) (hs : ∀ x, ∃ p q, x + f q = f p)
    [UniqueFactorizationMonoid (AddMonoidAlgebra K P)] :
    UniqueFactorizationMonoid (AddMonoidAlgebra K X) := by
  let := (mapDomainRingHom K f).toAlgebra
  have hφ : ∀ p a, algebraMap (AddMonoidAlgebra K P) (AddMonoidAlgebra K X) (single p a) =
      single (f p) a := fun p a => mapDomain_single
  have : IsLocalization (MonoidHom.mrange (of K P)) (AddMonoidAlgebra K X) := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun s => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, p, rfl⟩
      refine IsUnit.of_mul_eq_one (single (-f p.toAdd) 1) ?_
      change algebraMap _ _ (single p.toAdd (1 : K)) * _ = _
      rw [hφ, single_mul_single, add_neg_cancel, one_mul, one_def]
    · induction s using AddMonoidAlgebra.induction_linear with
      | zero => exact ⟨⟨0, 1⟩, by simp⟩
      | add s t hs ht =>
        obtain ⟨⟨a, n⟩, ha⟩ := hs
        obtain ⟨⟨c, m⟩, hc⟩ := ht
        refine ⟨⟨a * m + c * n, n * m⟩, ?_⟩
        simp only [Submonoid.coe_mul, map_add, map_mul] at ha hc ⊢
        rw [← ha, ← hc]
        ring
      | single x a =>
        obtain ⟨p, q, h⟩ := hs x
        refine ⟨⟨single p a, ⟨single q 1, Multiplicative.ofAdd q, rfl⟩⟩, ?_⟩
        simp only
        rw [hφ, hφ, single_mul_single, h, mul_one]
    · rw [mapDomain_injective hf h]
  exact .of_isLocalization (MonoidHom.mrange (of K P)) _

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis ℤ X`. Set `f : (Module.Free.ChooseBasisIndex ℤ X →₀ ℕ) →+ X` to `b.repr.symm.toLinearMap.toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))`. Establish `hf : Function.Injective f` using `b.repr.symm.injective.comp (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)`. Establish `: UniqueFactorizationMonoid (AddMonoidAlgebra K (Module.Free.ChooseBasisIndex ℤ X →₀ ℕ))` using `inferInstanceAs (UniqueFactorizationMonoid (MvPolynomial _ K))`. Use `uniqueFactorizationMonoid_addMonoidAlgebra_of_sub f hf fun x => ⟨(b.repr x).mapRange Int.toNat rfl, (-b.repr x).mapRange Int.toNat rfl, ?_⟩` and prove the remaining obligations.

Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `[f]`. Use linear arithmetic over natural numbers and integers.
-/
theorem uniqueFactorizationMonoid_addMonoidAlgebra_of_free (K X : Type*) [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [AddCommGroup X] [Module.Free ℤ X] :
    UniqueFactorizationMonoid (AddMonoidAlgebra K X) := by
  let b := Module.Free.chooseBasis ℤ X
  let f : (Module.Free.ChooseBasisIndex ℤ X →₀ ℕ) →+ X :=
    b.repr.symm.toLinearMap.toAddMonoidHom.comp
      (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))
  have hf : Function.Injective f := b.repr.symm.injective.comp
    (Finsupp.mapRange_injective _ Nat.cast_zero Nat.cast_injective)
  have : UniqueFactorizationMonoid
      (AddMonoidAlgebra K (Module.Free.ChooseBasisIndex ℤ X →₀ ℕ)) :=
    inferInstanceAs (UniqueFactorizationMonoid (MvPolynomial _ K))
  refine uniqueFactorizationMonoid_addMonoidAlgebra_of_sub f hf fun x =>
    ⟨(b.repr x).mapRange Int.toNat rfl, (-b.repr x).mapRange Int.toNat rfl, ?_⟩
  apply b.repr.injective
  ext i
  simp [f]
  omega

/- English proof (translation)
The claim follows from `(AddEquiv.uniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance`.
-/
theorem uniqueSums_of_free_int (X : Type*) [AddCommGroup X] [Module.Free ℤ X] : UniqueSums X :=
  (AddEquiv.uniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance

end Factorial

section Picard

/- English proof (translation)
Use `Function.LeftInverse.injective (g := Pic.mapRingHom (ε : B →+* A)) fun M => ?_` and prove the remaining obligations. Rewrite using `[← Pic.mapRingHom_algebraMap, Pic.mapRingHom_mapRingHom, ε.comp_algebraMap, Pic.mapRingHom_algebraMap, Pic.mapAlgebra_self_apply]`.
-/
theorem pic_mapAlgebra_injective_of_algHom {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (ε : B →ₐ[A] A) : Function.Injective (Pic.mapAlgebra A B) := by
  refine Function.LeftInverse.injective (g := Pic.mapRingHom (ε : B →+* A)) fun M => ?_
  rw [← Pic.mapRingHom_algebraMap, Pic.mapRingHom_mapRingHom, ε.comp_algebraMap,
    Pic.mapRingHom_algebraMap, Pic.mapAlgebra_self_apply]

/- English proof (translation)
The claim follows from `pic_mapAlgebra_injective_of_algHom (AddMonoidAlgebra.lift A A X 1)`.
-/
theorem pic_mapAlgebra_addMonoidAlgebra_injective (A X : Type*) [CommRing A] [AddCommMonoid X] :
    Function.Injective (Pic.mapAlgebra A (AddMonoidAlgebra A X)) :=
  pic_mapAlgebra_injective_of_algHom (AddMonoidAlgebra.lift A A X 1)

/- English proof (translation)
Establish `: FaithfulSMul (AddMonoidAlgebra A X) (AddMonoidAlgebra F X)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr (map_injective (algebraMap A F : A →+ F) (IsFractionRing.injective A F))`. Rewrite using `[← Submodule.range_unitsToPic]`. Introduce and unpack `_ ⟨I, rfl⟩`. Establish `hle : coeffSpan I.1 * coeffSpan (I⁻¹).1 ≤ 1`. Rewrite using `[coeffSpan, coeffSpan, Submodule.span_mul_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨f, hf, i, rfl⟩, _, ⟨g, hg, j, rfl⟩, rfl⟩`. Use `Submodule.mem_one.mpr (coeff_mul_coeff_mem_range_of_isIntegrallyClosed A ?_ i j)` and prove the remaining obligations. Conclude with `mem_one_iff_forall_coeff_mem_range.mp (I.mul_inv ▸ Submodule.mul_mem_mul hf hg)`. Establish `hge : 1 ≤ coeffSpan I.1 * coeffSpan (I⁻¹).1`. Establish `h1 : (1 : AddMonoidAlgebra F X) ∈ I.1 * (I⁻¹).1` using `I.mul_inv ▸ Submodule.one_le.mp le_rfl`.

Simplify `coeff_mem_coeffSpan_mul h1 0` using `[one_def]`. Set `M : (Submodule A F)ˣ` to `Units.mkOfMulEqOne _ _ (le_antisymm hle hge)`. Establish `hrange : LinearMap.range (constantsLift X M.1) = I.1` using `le_antisymm (range_constantsLift_le I.mul_inv hle) (le_range_constantsLift _)`. Use `⟨Pic.mk A M, Pic.mk_eq_mk_iff.mpr ⟨TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M) ≪≫ₗ ?_⟩⟩` and prove the remaining obligations. Establish `hs : Function.Surjective ((LinearEquiv.ofEq _ _ hrange).toLinearMap ∘ₗ (constantsLift X M.1).rangeRestrict)` using `(LinearEquiv.ofEq _ _ hrange).surjective.comp (constantsLift X M.1).surjective_rangeRestrict`.

Conclude with `.ofBijective _ (Module.Invertible.bijective_of_surjective hs)`.
-/
theorem relPic_le_range_mapAlgebra (A F X : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F] [Algebra A F] [IsFractionRing A F] [AddCommMonoid X]
    [UniqueSums X] :
    relPic (AddMonoidAlgebra A X) (AddMonoidAlgebra F X) ≤
      (Pic.mapAlgebra A (AddMonoidAlgebra A X)).range := by
  have : FaithfulSMul (AddMonoidAlgebra A X) (AddMonoidAlgebra F X) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (map_injective (algebraMap A F : A →+ F) (IsFractionRing.injective A F))
  rw [← Submodule.range_unitsToPic]
  rintro _ ⟨I, rfl⟩
  have hle : coeffSpan I.1 * coeffSpan (I⁻¹).1 ≤ 1 := by
    rw [coeffSpan, coeffSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨f, hf, i, rfl⟩, _, ⟨g, hg, j, rfl⟩, rfl⟩
    refine Submodule.mem_one.mpr
      (coeff_mul_coeff_mem_range_of_isIntegrallyClosed A ?_ i j)
    exact mem_one_iff_forall_coeff_mem_range.mp (I.mul_inv ▸ Submodule.mul_mem_mul hf hg)
  have hge : 1 ≤ coeffSpan I.1 * coeffSpan (I⁻¹).1 := by
    have h1 : (1 : AddMonoidAlgebra F X) ∈ I.1 * (I⁻¹).1 :=
      I.mul_inv ▸ Submodule.one_le.mp le_rfl
    simpa [one_def] using coeff_mem_coeffSpan_mul h1 0
  let M : (Submodule A F)ˣ := Units.mkOfMulEqOne _ _ (le_antisymm hle hge)
  have hrange : LinearMap.range (constantsLift X M.1) = I.1 :=
    le_antisymm (range_constantsLift_le I.mul_inv hle) (le_range_constantsLift _)
  refine ⟨Pic.mk A M, Pic.mk_eq_mk_iff.mpr
    ⟨TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M) ≪≫ₗ ?_⟩⟩
  have hs : Function.Surjective
      ((LinearEquiv.ofEq _ _ hrange).toLinearMap ∘ₗ (constantsLift X M.1).rangeRestrict) :=
    (LinearEquiv.ofEq _ _ hrange).surjective.comp
      (constantsLift X M.1).surjective_rangeRestrict
  exact .ofBijective _ (Module.Invertible.bijective_of_surjective hs)

/- English proof (translation)
Assemble the required witnesses or components as `⟨pic_mapAlgebra_addMonoidAlgebra_injective A X, fun _ => relPic_le_range_mapAlgebra A F X (Subsingleton.elim _ _)⟩`.
-/
theorem pic_mapAlgebra_addMonoidAlgebra_bijective_of_subsingleton (A F X : Type*) [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Field F] [Algebra A F] [IsFractionRing A F]
    [AddCommMonoid X] [UniqueSums X] [Subsingleton (Pic (AddMonoidAlgebra F X))] :
    Function.Bijective (Pic.mapAlgebra A (AddMonoidAlgebra A X)) :=
  ⟨pic_mapAlgebra_addMonoidAlgebra_injective A X, fun _ =>
    relPic_le_range_mapAlgebra A F X (Subsingleton.elim _ _)⟩

/- English proof (translation)
Use `uniqueSums_of_free_int X` as an intermediate fact. Use `uniqueFactorizationMonoid_addMonoidAlgebra_of_free K X` as an intermediate fact. Use `infer_instance`.
-/
theorem subsingleton_pic_addMonoidAlgebra_of_free (K X : Type*) [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [AddCommGroup X] [Module.Free ℤ X] :
    Subsingleton (Pic (AddMonoidAlgebra K X)) := by
  have := uniqueSums_of_free_int X
  have := uniqueFactorizationMonoid_addMonoidAlgebra_of_free K X
  infer_instance

variable (A X : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

/- English proof (translation)
Establish `: Subsingleton (Pic (AddMonoidAlgebra (FractionRing A) (σ →₀ ℕ)))` using `inferInstanceAs (Subsingleton (Pic (MvPolynomial σ (FractionRing A))))`. Conclude with `pic_mapAlgebra_addMonoidAlgebra_bijective_of_subsingleton A (FractionRing A) (σ →₀ ℕ)`.
-/
theorem pic_mapAlgebra_mvPolynomial_bijective (σ : Type*) :
    Function.Bijective (Pic.mapAlgebra A (MvPolynomial σ A)) := by
  have : Subsingleton (Pic (AddMonoidAlgebra (FractionRing A) (σ →₀ ℕ))) :=
    inferInstanceAs (Subsingleton (Pic (MvPolynomial σ (FractionRing A))))
  exact pic_mapAlgebra_addMonoidAlgebra_bijective_of_subsingleton A (FractionRing A) (σ →₀ ℕ)

variable [AddCommGroup X] [Module.Free ℤ X]

/- English proof (translation)
Use `uniqueSums_of_free_int X` as an intermediate fact. Use `subsingleton_pic_addMonoidAlgebra_of_free (FractionRing A) X` as an intermediate fact. Conclude with `pic_mapAlgebra_addMonoidAlgebra_bijective_of_subsingleton A (FractionRing A) X`.
-/
theorem pic_mapAlgebra_groupAlgebra_bijective :
    Function.Bijective (Pic.mapAlgebra A (AddMonoidAlgebra A X)) := by
  have := uniqueSums_of_free_int X
  have := subsingleton_pic_addMonoidAlgebra_of_free (FractionRing A) X
  exact pic_mapAlgebra_addMonoidAlgebra_bijective_of_subsingleton A (FractionRing A) X

variable {X} (N : Type*) [AddCommGroup N] [Module (AddMonoidAlgebra A X) N]
  [Module.Invertible (AddMonoidAlgebra A X) N]

/- English proof (translation)
Take `⟨M, hM⟩` from `(pic_mapAlgebra_groupAlgebra_bijective A X).2 (Pic.mk _ N)`. Conclude with `⟨M, Pic.mk_eq_mk_iff.mp hM.symm⟩`.
-/
theorem exists_pic_linearEquiv_groupAlgebra_tensor :
    ∃ M : Pic A, Nonempty (N ≃ₗ[AddMonoidAlgebra A X] AddMonoidAlgebra A X ⊗[A] M) := by
  obtain ⟨M, hM⟩ := (pic_mapAlgebra_groupAlgebra_bijective A X).2 (Pic.mk _ N)
  exact ⟨M, Pic.mk_eq_mk_iff.mp hM.symm⟩

/- English proof (translation)
Take `⟨M, hM⟩` from `(pic_mapAlgebra_groupAlgebra_bijective A X).2 (Pic.mk _ N)`. Rewrite `h` using `[← hM, ← Pic.mapRingHom_algebraMap, Pic.mapRingHom_mapRingHom, ε.comp_algebraMap, Pic.mapRingHom_algebraMap, Pic.mapAlgebra_self_apply]`. Rewrite using `[← Pic.mk_eq_one_iff_free, ← hM, h, map_one]`.
-/
theorem free_of_mapRingHom_mk_eq_one (ε : AddMonoidAlgebra A X →ₐ[A] A)
    (h : Pic.mapRingHom (ε : AddMonoidAlgebra A X →+* A) (Pic.mk _ N) = 1) :
    Module.Free (AddMonoidAlgebra A X) N := by
  obtain ⟨M, hM⟩ := (pic_mapAlgebra_groupAlgebra_bijective A X).2 (Pic.mk _ N)
  rw [← hM, ← Pic.mapRingHom_algebraMap, Pic.mapRingHom_mapRingHom, ε.comp_algebraMap,
    Pic.mapRingHom_algebraMap, Pic.mapAlgebra_self_apply] at h
  rw [← Pic.mk_eq_one_iff_free, ← hM, h, map_one]

/- English proof (translation)
The claim follows from `(pic_mapAlgebra_groupAlgebra_bijective A X).2.subsingleton`.
-/
theorem subsingleton_pic_groupAlgebra (X : Type*) [AddCommGroup X] [Module.Free ℤ X]
    [Subsingleton (Pic A)] : Subsingleton (Pic (AddMonoidAlgebra A X)) :=
  (pic_mapAlgebra_groupAlgebra_bijective A X).2.subsingleton

end Picard

/- English proof (translation)
Use `⟨pic_mapAlgebra_groupAlgebra_bijective A X, fun N _ _ _ => ?_, fun M M' _ _ _ _ _ _ ⟨e⟩ => ?_⟩` and prove the remaining obligations. Take `⟨M, hM⟩` from `exists_pic_linearEquiv_groupAlgebra_tensor A (X := X) N`. Conclude with `⟨M, inferInstance, inferInstance, inferInstance, hM⟩`. Use `Pic.mk_eq_mk_iff.mp (pic_mapAlgebra_addMonoidAlgebra_injective A X (Pic.mk_eq_mk_iff.mpr ⟨?_⟩))` and prove the remaining obligations. Conclude with `TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M) ≪≫ₗ e ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M').symm`.
-/
theorem pic_groupAlgebra_of_isIntegrallyClosed.{u, v, w} (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (X : Type v) [AddCommGroup X] [Module.Free ℤ X] :
    Function.Bijective (Pic.mapAlgebra A (AddMonoidAlgebra A X)) ∧
    (∀ (N : Type w) [AddCommGroup N] [Module (AddMonoidAlgebra A X) N]
      [Module.Invertible (AddMonoidAlgebra A X) N],
      ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module A M), Module.Invertible A M ∧
        Nonempty (N ≃ₗ[AddMonoidAlgebra A X] AddMonoidAlgebra A X ⊗[A] M)) ∧
    (∀ (M M' : Type w) [AddCommGroup M] [Module A M] [Module.Invertible A M] [AddCommGroup M']
      [Module A M'] [Module.Invertible A M'],
      Nonempty (AddMonoidAlgebra A X ⊗[A] M ≃ₗ[AddMonoidAlgebra A X]
        AddMonoidAlgebra A X ⊗[A] M') → Nonempty (M ≃ₗ[A] M')) := by
  refine ⟨pic_mapAlgebra_groupAlgebra_bijective A X, fun N _ _ _ => ?_,
    fun M M' _ _ _ _ _ _ ⟨e⟩ => ?_⟩
  · obtain ⟨M, hM⟩ := exists_pic_linearEquiv_groupAlgebra_tensor A (X := X) N
    exact ⟨M, inferInstance, inferInstance, inferInstance, hM⟩
  · refine Pic.mk_eq_mk_iff.mp (pic_mapAlgebra_addMonoidAlgebra_injective A X
      (Pic.mk_eq_mk_iff.mpr ⟨?_⟩))
    exact TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M) ≪≫ₗ e ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (.refl _ _) (Pic.mk.linearEquiv A M').symm

/- English proof (translation)
The claim follows from `subsingleton_pic_groupAlgebra ℤ (Fin 2 → ℤ)`.
-/
example : Subsingleton (Pic (AddMonoidAlgebra ℤ (Fin 2 → ℤ))) :=
  subsingleton_pic_groupAlgebra ℤ (Fin 2 → ℤ)

end GlobalTheory
