import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt

section
variable (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

def redAs (m : Ideal A) : ↥(As O A) →ₐ[O] ↥(As O (A ⧸ m)) :=
  ((Ideal.Quotient.mkₐ O m).comp (As O A).val).codRestrict (As O (A ⧸ m))
    fun a => (show IsIntegral O (a : A) from a.2).map (Ideal.Quotient.mkₐ O m)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem redAs_coe (m : Ideal A) (a : ↥(As O A)) : (redAs O A m a : A ⧸ m) = Ideal.Quotient.mk m a := rfl

end

/- English proof (translation)
Use `haveI : Finite (MaximalSpectrum A) := by haveI := (IsArtinianRing.setOf_isMaximal_finite A).to_subtype`. Conclude with `Finite.of_injective (fun m : MaximalSpectrum A => (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal A | I.IsMaximal})) (fun x y hxy => MaximalSpectrum.ext (congrArg Subtype.val hxy))`. Use `letI := Fintype.ofFinite (MaximalSpectrum A)`. Use `choose p hp hpa using fun m : MaximalSpectrum A => h m`. Establish `hmem : ∀ m : MaximalSpectrum A, Polynomial.aeval a (p m) ∈ m.asIdeal`.

Introduce `m`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `e : (Ideal.Quotient.mk m.asIdeal) (Polynomial.aeval a (p m)) = Polynomial.aeval (Ideal.Quotient.mk m.asIdeal a) (p m)`. Rewrite using `[← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]`. Rewrite using `[e, Polynomial.aeval_def]`.

Conclude with `hpa m`. Establish `hzero : ∀ x : A, (∀ m : MaximalSpectrum A, x ∈ m.asIdeal) → x = 0`. Introduce `x hx`. Establish `hj : x ∈ Ideal.jacobson (⊥ : Ideal A)`. Rewrite using `[Ideal.jacobson]`.

Use `Ideal.mem_sInf.mpr ?_` and prove the remaining obligations. Introduce and unpack `J ⟨-, hJ⟩`. Conclude with `hx ⟨J, hJ⟩`. Take `⟨n, hn⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := A)`. Establish `hxn : x ^ n = 0`.

Use `Ideal.pow_mem_pow hj n` as an intermediate fact. Rewrite `this` using `[hn]`. Conclude with `(Submodule.mem_bot _).mp this`. Conclude with `IsReduced.eq_zero x ⟨n, hxn⟩`. Use `⟨∏ m, p m, Polynomial.monic_prod_of_monic _ _ fun m _ => hp m, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Polynomial.aeval_def, map_prod]`. Apply `hzero` to reduce the goal to its premises. Introduce `m`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]`. Conclude with `Ideal.mul_mem_right _ _ (hmem m)`.
-/
theorem isIntegral_of_all (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [IsArtinianRing A] [IsReduced A] (a : A)
    (h : ∀ m : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk m.asIdeal a)) : IsIntegral O a := by
  classical
  haveI : Finite (MaximalSpectrum A) := by
    haveI := (IsArtinianRing.setOf_isMaximal_finite A).to_subtype
    exact Finite.of_injective
      (fun m : MaximalSpectrum A => (⟨m.asIdeal, m.isMaximal⟩ : {I : Ideal A | I.IsMaximal}))
      (fun x y hxy => MaximalSpectrum.ext (congrArg Subtype.val hxy))
  letI := Fintype.ofFinite (MaximalSpectrum A)
  choose p hp hpa using fun m : MaximalSpectrum A => h m
  have hmem : ∀ m : MaximalSpectrum A, Polynomial.aeval a (p m) ∈ m.asIdeal := by
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e : (Ideal.Quotient.mk m.asIdeal) (Polynomial.aeval a (p m)) =
        Polynomial.aeval (Ideal.Quotient.mk m.asIdeal a) (p m) := by
      rw [← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
    rw [e, Polynomial.aeval_def]
    exact hpa m
  have hzero : ∀ x : A, (∀ m : MaximalSpectrum A, x ∈ m.asIdeal) → x = 0 := by
    intro x hx
    have hj : x ∈ Ideal.jacobson (⊥ : Ideal A) := by
      rw [Ideal.jacobson]
      refine Ideal.mem_sInf.mpr ?_
      rintro J ⟨-, hJ⟩
      exact hx ⟨J, hJ⟩
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    have hxn : x ^ n = 0 := by
      have := Ideal.pow_mem_pow hj n
      rw [hn] at this
      exact (Submodule.mem_bot _).mp this
    exact IsReduced.eq_zero x ⟨n, hxn⟩
  refine ⟨∏ m, p m, Polynomial.monic_prod_of_monic _ _ fun m _ => hp m, ?_⟩
  rw [← Polynomial.aeval_def, map_prod]
  apply hzero
  intro m
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
  exact Ideal.mul_mem_right _ _ (hmem m)

/- English proof (translation)
Introduce `O K A _ _ _ _ _ _ _ _ _ _ _ _ _`. Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite K A`. Use `haveI := Fintype.ofFinite (MaximalSpectrum A)`. Establish `hinj : ∀ a : A, (∀ m : MaximalSpectrum A, Ideal.Quotient.mk m.asIdeal a = 0) → a = 0` using `fun a h => by`. Apply `(IsArtinianRing.equivPi A).injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use function extensionality and compare the values at `m`. Conclude with `h m`. Establish `hsurj : ∀ b : (m : MaximalSpectrum A) → A ⧸ m.asIdeal, ∃ a : A, ∀ m, Ideal.Quotient.mk m.asIdeal a = b m` using `fun b => by`. Take `⟨a, ha⟩` from `(IsArtinianRing.equivPi A).surjective b`.

Conclude with `⟨a, fun m => congrFun ha m⟩`. Prove the components needed by the constructor for the conclusion. Use `haveI : ∀ m : MaximalSpectrum A, Module.Finite O ↥(As O (A ⧸ m.asIdeal)) := fun m => by haveI := m.isMaximal`. Use `letI := Ideal.Quotient.field m.asIdeal`. Conclude with `IsIntegralClosure.finite O K (A ⧸ m.asIdeal) _`.

Use `Module.Finite.of_injective (LinearMap.pi fun m : MaximalSpectrum A => (redAs O A m.asIdeal).toLinearMap) ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `a ha`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hinj _ fun m => congrArg Subtype.val (congrFun ha m)`.

Introduce `ζ choose e he using fun m : MaximalSpectrum A => hsurj (Pi.single m 1)`. Establish `hei : ∀ m, IsIntegral O (e m)` using `fun m => isIntegral_of_all O A _ fun m' => by`. Rewrite using `[he]`. Distinguish the cases in `h : m' = m`. Substitute `h` using the available equality.

Rewrite using `[Pi.single_eq_same]`. Conclude with `isIntegral_one`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `isIntegral_zero`. Establish `hsum : ∑ m, (⟨e m, hei m⟩ : ↥(As O A)) = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`. Apply `hinj` to reduce the goal to its premises. Introduce `m'`. Rewrite using `[map_sub]`.

Simplify using `only [AddSubmonoidClass.coe_finsetSum, map_sum, he, OneMemClass.coe_one, map_one]`. Rewrite using `[← Finset.sum_apply, Finset.univ_sum_single]`. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, (⟨e m, hei m⟩ : ↥(As O A)) ∉ ζ.asIdeal := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Conclude with `ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (hsum ▸ Ideal.sum_mem _ fun m _ => hc m))`. Use `haveI := m.isMaximal`. Use `letI := Ideal.Quotient.field m.asIdeal`. Set `f` to `redAs O A m.asIdeal`.

Establish `hf : Function.Surjective f` using `fun b => by`. Take `⟨a, ha⟩` from `hsurj (Pi.single m (b : A ⧸ m.asIdeal))`. Use `⟨⟨a, isIntegral_of_all O A _ fun m' => ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Distinguish the cases in `h : m' = m`.

Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `b.2`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `isIntegral_zero`.

Use `show Ideal.Quotient.mk m.asIdeal a = _`. Rewrite using `[ha, Pi.single_eq_same]`. Establish `hker : ∀ x, f x = 0 → (⟨e m, hei m⟩ : ↥(As O A)) * x = 0` using `fun x hx => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Introduce `m'`. Use `show Ideal.Quotient.mk m'.asIdeal (e m * x) = 0`. Rewrite using `[map_mul, he]`. Distinguish the cases in `h : m' = m`. Substitute `h` using the available equality.

Establish `: Ideal.Quotient.mk m'.asIdeal (x : A) = 0` using `congrArg Subtype.val hx`. Rewrite using `[this, mul_zero]`. Rewrite using `[Pi.single_eq_of_ne h, zero_mul]`. Establish `hkl : RingHom.ker f.toRingHom ≤ ζ.asIdeal` using `fun x hx => (ζ.isMaximal.isPrime.mem_or_mem (by rw [hker x hx]; exact zero_mem _)).resolve_left hm`. Establish `hcm : (ζ.asIdeal.map f.toRingHom).comap f.toRingHom = ζ.asIdeal`.

Rewrite using `[Ideal.comap_map_of_surjective f.toRingHom hf]`. Conclude with `sup_eq_left.2 hkl`. Establish `hmax : (ζ.asIdeal.map f.toRingHom).IsMaximal`. Break down `Ideal.map_eq_top_or_isMaximal_of_surjective f.toRingHom hf ζ.isMaximal with h | h` into its components or cases. Rewrite `hcm` using `[h, Ideal.comap_top]`.

Conclude with `absurd hcm.symm ζ.isMaximal.ne_top`. Conclude with `h`. Set `ζ' : Pts O (A ⧸ m.asIdeal)` to `⟨ζ.asIdeal.map f.toRingHom, hmax⟩`. Establish `hmem : ∀ x, f x ∈ ζ'.asIdeal ↔ x ∈ ζ.asIdeal` using `fun x => by`. Rewrite using `[← hcm]`.

Conclude with `Iff.rfl`. Establish `hD : IsDVRAt ζ'` using `isDVRAt_of_field_ext K ζ'`. Use `letI alg : Algebra ↥(As O A) (Loc ζ') := ((algebraMap _ (Loc ζ')).comp f.toRingHom).toAlgebra`. Establish `halg : ∀ x, algebraMap ↥(As O A) (Loc ζ') x = algebraMap _ (Loc ζ') (f x)` using `fun _ => rfl`. Use `haveI : IsLocalization.AtPrime (Loc ζ') ζ.asIdeal := by`.

Use `⟨⟨fun s => ?_, fun z => ?_, fun {x y} h => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[halg]`. Conclude with `IsLocalization.map_units (Loc ζ') (⟨f s, fun h => s.2 ((hmem _).1 h)⟩ : ζ'.asIdeal.primeCompl)`. Take `⟨⟨b, t⟩, hb⟩` from `IsLocalization.surj ζ'.asIdeal.primeCompl z`. Take `⟨a, rfl⟩` from `hf b`.

Take `⟨s, hs⟩` from `hf t`. Use `⟨⟨a, ⟨s, fun h => t.2 (hs ▸ (hmem _).2 h)⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [halg, hs]`. Conclude with `hb`. Rewrite `h` using `[halg, halg]`.

Take `⟨t, ht⟩` from `(IsLocalization.eq_iff_exists ζ'.asIdeal.primeCompl (Loc ζ')).1 h`. Take `⟨s, hs⟩` from `hf t`. Establish `hs' : s ∉ ζ.asIdeal` using `fun h => t.2 (hs ▸ (hmem _).2 h)`. Use `⟨⟨⟨e m, hei m⟩ * s, fun h => (ζ.isMaximal.isPrime.mem_or_mem h).elim hm hs'⟩, ?_⟩` and prove the remaining obligations. Use `hker (s * x - s * y) (by rw [map_sub, map_mul, map_mul, hs, ht, sub_self])` as an intermediate fact.

Use `show ⟨e m, hei m⟩ * s * x = ⟨e m, hei m⟩ * s * y`. Rewrite using `[← sub_eq_zero, ← this]`. Expand and normalize the polynomial expressions, which then agree. Set `E` to `(IsLocalization.algEquiv ζ.asIdeal.primeCompl (Loc ζ') (Loc ζ)).toRingEquiv`. Use `haveI := hD.isDomain`.

Use `haveI := hD.isDVR`. Use `haveI hd : IsDomain (Loc ζ) := E.symm.toMulEquiv.isDomain _`. Conclude with `⟨hd, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E⟩`.
-/
theorem integralClosure_dvr :
    ∀ (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A]
    [FiniteDimensional K A] [IsReduced A],
    Module.Finite O ↥(As O A) ∧ ∀ ζ : Pts O A, IsDVRAt ζ := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI := Fintype.ofFinite (MaximalSpectrum A)
  have hinj : ∀ a : A, (∀ m : MaximalSpectrum A, Ideal.Quotient.mk m.asIdeal a = 0) → a = 0 := fun a h => by
    apply (IsArtinianRing.equivPi A).injective
    rw [map_zero]
    funext m
    exact h m
  have hsurj : ∀ b : (m : MaximalSpectrum A) → A ⧸ m.asIdeal, ∃ a : A, ∀ m, Ideal.Quotient.mk m.asIdeal a = b m := fun b => by
    obtain ⟨a, ha⟩ := (IsArtinianRing.equivPi A).surjective b
    exact ⟨a, fun m => congrFun ha m⟩
  constructor
  · haveI : ∀ m : MaximalSpectrum A, Module.Finite O ↥(As O (A ⧸ m.asIdeal)) := fun m => by
      haveI := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      exact IsIntegralClosure.finite O K (A ⧸ m.asIdeal) _
    refine Module.Finite.of_injective (LinearMap.pi fun m : MaximalSpectrum A => (redAs O A m.asIdeal).toLinearMap) ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    exact hinj _ fun m => congrArg Subtype.val (congrFun ha m)
  · intro ζ
    choose e he using fun m : MaximalSpectrum A => hsurj (Pi.single m 1)
    have hei : ∀ m, IsIntegral O (e m) := fun m => isIntegral_of_all O A _ fun m' => by
      rw [he]
      by_cases h : m' = m
      · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
    have hsum : ∑ m, (⟨e m, hei m⟩ : ↥(As O A)) = 1 := by
      apply Subtype.ext
      rw [← sub_eq_zero]
      apply hinj
      intro m'
      rw [map_sub]
      simp only [AddSubmonoidClass.coe_finsetSum, map_sum, he, OneMemClass.coe_one, map_one]
      rw [← Finset.sum_apply, Finset.univ_sum_single]
      simp
    obtain ⟨m, hm⟩ : ∃ m, (⟨e m, hei m⟩ : ↥(As O A)) ∉ ζ.asIdeal := by
      by_contra hc
      push Not at hc
      exact ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (hsum ▸ Ideal.sum_mem _ fun m _ => hc m))
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    let f := redAs O A m.asIdeal
    have hf : Function.Surjective f := fun b => by
      obtain ⟨a, ha⟩ := hsurj (Pi.single m (b : A ⧸ m.asIdeal))
      refine ⟨⟨a, isIntegral_of_all O A _ fun m' => ?_⟩, Subtype.ext ?_⟩
      · rw [ha]
        by_cases h : m' = m
        · subst h; rw [Pi.single_eq_same]; exact b.2
        · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
      · show Ideal.Quotient.mk m.asIdeal a = _
        rw [ha, Pi.single_eq_same]
    have hker : ∀ x, f x = 0 → (⟨e m, hei m⟩ : ↥(As O A)) * x = 0 := fun x hx => by
      apply Subtype.ext
      apply hinj
      intro m'
      show Ideal.Quotient.mk m'.asIdeal (e m * x) = 0
      rw [map_mul, he]
      by_cases h : m' = m
      · subst h
        have : Ideal.Quotient.mk m'.asIdeal (x : A) = 0 := congrArg Subtype.val hx
        rw [this, mul_zero]
      · rw [Pi.single_eq_of_ne h, zero_mul]
    have hkl : RingHom.ker f.toRingHom ≤ ζ.asIdeal := fun x hx =>
      (ζ.isMaximal.isPrime.mem_or_mem (by rw [hker x hx]; exact zero_mem _)).resolve_left hm
    have hcm : (ζ.asIdeal.map f.toRingHom).comap f.toRingHom = ζ.asIdeal := by
      rw [Ideal.comap_map_of_surjective f.toRingHom hf]
      exact sup_eq_left.2 hkl
    have hmax : (ζ.asIdeal.map f.toRingHom).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective f.toRingHom hf ζ.isMaximal with h | h
      · rw [h, Ideal.comap_top] at hcm; exact absurd hcm.symm ζ.isMaximal.ne_top
      · exact h
    let ζ' : Pts O (A ⧸ m.asIdeal) := ⟨ζ.asIdeal.map f.toRingHom, hmax⟩
    have hmem : ∀ x, f x ∈ ζ'.asIdeal ↔ x ∈ ζ.asIdeal := fun x => by
      rw [← hcm]; exact Iff.rfl
    have hD : IsDVRAt ζ' := isDVRAt_of_field_ext K ζ'
    letI alg : Algebra ↥(As O A) (Loc ζ') := ((algebraMap _ (Loc ζ')).comp f.toRingHom).toAlgebra
    have halg : ∀ x, algebraMap ↥(As O A) (Loc ζ') x = algebraMap _ (Loc ζ') (f x) := fun _ => rfl
    haveI : IsLocalization.AtPrime (Loc ζ') ζ.asIdeal := by
      refine ⟨⟨fun s => ?_, fun z => ?_, fun {x y} h => ?_⟩⟩
      · rw [halg]
        exact IsLocalization.map_units (Loc ζ') (⟨f s, fun h => s.2 ((hmem _).1 h)⟩ : ζ'.asIdeal.primeCompl)
      · obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj ζ'.asIdeal.primeCompl z
        obtain ⟨a, rfl⟩ := hf b
        obtain ⟨s, hs⟩ := hf t
        refine ⟨⟨a, ⟨s, fun h => t.2 (hs ▸ (hmem _).2 h)⟩⟩, ?_⟩
        simp only [halg, hs]
        exact hb
      · rw [halg, halg] at h
        obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ'.asIdeal.primeCompl (Loc ζ')).1 h
        obtain ⟨s, hs⟩ := hf t
        have hs' : s ∉ ζ.asIdeal := fun h => t.2 (hs ▸ (hmem _).2 h)
        refine ⟨⟨⟨e m, hei m⟩ * s, fun h => (ζ.isMaximal.isPrime.mem_or_mem h).elim hm hs'⟩, ?_⟩
        have := hker (s * x - s * y) (by rw [map_sub, map_mul, map_mul, hs, ht, sub_self])
        show ⟨e m, hei m⟩ * s * x = ⟨e m, hei m⟩ * s * y
        rw [← sub_eq_zero, ← this]; ring
    let E := (IsLocalization.algEquiv ζ.asIdeal.primeCompl (Loc ζ') (Loc ζ)).toRingEquiv
    haveI := hD.isDomain
    haveI := hD.isDVR
    haveI hd : IsDomain (Loc ζ) := E.symm.toMulEquiv.isDomain _
    exact ⟨hd, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E⟩

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
