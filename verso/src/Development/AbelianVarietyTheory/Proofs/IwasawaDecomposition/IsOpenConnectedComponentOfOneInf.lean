import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

/- English proof (translation)
Assemble the required witnesses or components as `⟨F.toHomUnits, Units.continuous_iff.mpr ⟨hF, hF.comp continuous_inv⟩, fun _ => rfl⟩`.
-/
theorem exists_units_hom {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field K] [TopologicalSpace K]
    (F : Γ →* K) (hF : Continuous F) : ∃ f : Γ →* Kˣ, Continuous f ∧ ∀ x, ((f x : Kˣ) : K) = F x :=
  ⟨F.toHomUnits, Units.continuous_iff.mpr ⟨hF, hF.comp continuous_inv⟩, fun _ => rfl⟩

/- English proof (translation)
Introduce `E _ _ n`. Establish `h0 : ∀ (x : Ideles E) (w : InfinitePlace E), (x : AdeleRing (𝓞 E) E).1 w ≠ 0` using `fun x w => left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)`. Use `haveI : ∀ w : InfinitePlace E, Fintype {i : w.Completion →+* ℂ // Continuous i} := fun w => @Fintype.ofFinite _ (finite_contEmbInf w)`. Establish `e : ∀ x : Ideles E, infPow n x = ∏ w : InfinitePlace E, ∏ i : {i : w.Completion →+* ℂ // Continuous i}, i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion))` using `fun x => Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _`. Set `F : Ideles E →* ℂ` to `{ toFun := infPow n map_one' := by`.

Rewrite using `[e]`. Use `Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show ((1 : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 from rfl, map_one, one_zpow]`. Use the proof step `map_mul' := fun x y => by`. Rewrite using `[e, e, e, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow, ← map_mul]`. Use `rfl }`.

Use `exists_units_hom F ?_` and prove the remaining obligations. Use `show Continuous (infPow n)`. Rewrite using `[funext e]`. Use `continuous_finset_prod _ fun w _ => continuous_finset_prod _ fun i _ => ?_` and prove the remaining obligations. Use `Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))` and prove the remaining obligations.

Conclude with `i.2.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))`.
-/
theorem exists_infPow_hom : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* ℂˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : ℂˣ) : ℂ) = infPow n x := by
  intro E _ _ n
  have h0 : ∀ (x : Ideles E) (w : InfinitePlace E), (x : AdeleRing (𝓞 E) E).1 w ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)
  haveI : ∀ w : InfinitePlace E, Fintype {i : w.Completion →+* ℂ // Continuous i} := fun w =>
    @Fintype.ofFinite _ (finite_contEmbInf w)
  have e : ∀ x : Ideles E, infPow n x = ∏ w : InfinitePlace E, ∏ i : {i : w.Completion →+* ℂ // Continuous i},
      i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion)) := fun x =>
    Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
  let F : Ideles E →* ℂ :=
    { toFun := infPow n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (infPow n)
  rw [funext e]
  refine continuous_finset_prod _ fun w _ => continuous_finset_prod _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))

/- English proof (translation)
Introduce `E _ _ l _ ι n`. Establish `hl : l.Prime` using `Fact.out`. Establish `h0 : ∀ (x : Ideles E) (v : HeightOneSpectrum (𝓞 E)), (x : AdeleRing (𝓞 E) E).2 v ≠ 0` using `fun x w => left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) x.mul_inv)`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype {j : v.adicCompletion E →+* Qbar l // Continuous j} := fun v => @Fintype.ofFinite _ (finite_contEmb v)`. Establish `hI : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hl.ne_zero` after adjusting the coercions. Establish `e : ∀ x : Ideles E, lPow ι n x = ∏ v ∈ (Ideal.finite_factors hI).toFinset, ∏ j : {j : v.adicCompletion E →+* Qbar l // Continuous j}, j.1 ((x : AdeleRing (𝓞 E) E).2 v) ^ n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E)))` using `fun x => by`. Unfold `lPow`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := (Ideal.finite_factors hI).toFinset)]`.

Conclude with `Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Use `hv (locPow_of_notMem ι n (fun hm => h ?_) _)` and prove the remaining obligations. Conclude with `Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Ideal.dvd_span_singleton.mpr hm))`.

Set `F : Ideles E →* Qbar l` to `{ toFun := lPow ι n map_one' := by`. Rewrite using `[e]`. Use `Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show ((1 : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 from rfl, map_one, one_zpow]`. Use the proof step `map_mul' := fun x y => by`.

Rewrite using `[e, e, e, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_zpow, ← map_mul]`.

Use `rfl }`. Use `exists_units_hom F ?_` and prove the remaining obligations. Use `show Continuous (lPow ι n)`. Rewrite using `[funext e]`. Use `continuous_finset_prod _ fun w _ => continuous_finset_prod _ fun i _ => ?_` and prove the remaining obligations.

Use `Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))` and prove the remaining obligations. Conclude with `i.2.comp ((RestrictedProduct.continuous_eval w).comp (continuous_snd.comp Units.continuous_val))`.
-/
theorem exists_lPow_hom : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* (Qbar l)ˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : (Qbar l)ˣ) : Qbar l) = lPow ι n x := by
  intro E _ _ l _ ι n
  have hl : l.Prime := Fact.out
  have h0 : ∀ (x : Ideles E) (v : HeightOneSpectrum (𝓞 E)), (x : AdeleRing (𝓞 E) E).2 v ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) x.mul_inv)
  haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype {j : v.adicCompletion E →+* Qbar l // Continuous j} := fun v =>
    @Fintype.ofFinite _ (finite_contEmb v)
  have hI : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  have e : ∀ x : Ideles E, lPow ι n x = ∏ v ∈ (Ideal.finite_factors hI).toFinset,
      ∏ j : {j : v.adicCompletion E →+* Qbar l // Continuous j}, j.1 ((x : AdeleRing (𝓞 E) E).2 v) ^
        n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E))) := fun x => by
    unfold lPow
    rw [finprod_eq_prod_of_mulSupport_subset (s := (Ideal.finite_factors hI).toFinset)]
    · exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
    · intro v hv
      by_contra h
      refine hv (locPow_of_notMem ι n (fun hm => h ?_) _)
      exact Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Ideal.dvd_span_singleton.mpr hm))
  let F : Ideles E →* Qbar l :=
    { toFun := lPow ι n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (lPow ι n)
  rw [funext e]
  refine continuous_finset_prod _ fun w _ => continuous_finset_prod _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((RestrictedProduct.continuous_eval w).comp (continuous_snd.comp Units.continuous_val))

/- English proof (translation)
Introduce `E _ _ n k`. Set `J : InfinitePlace E → Type` to `fun w => {i : w.Completion →+* ℂ // Continuous i}`. Set `res : (Σ w, J w) → (E →+* ℂ)` to `fun p => p.2.1.comp (algebraMap E p.1.Completion)`. Establish `hd : ∀ w : InfinitePlace E, DenseRange (algebraMap E w.Completion)` using `fun w => by`. Use `Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨WithAbs.equiv w.1 a, rfl⟩`. Establish `hmk : ∀ p : Σ w, J w, InfinitePlace.mk (res p) = p.1`. Introduce and unpack `⟨w, i⟩`. Establish `hn : ∀ y : w.Completion, ‖i.1 y‖ = ‖y‖` using `fun y => by`.

Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Apply the tactic sequence `have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry`. Establish `h1` using `Complex.ringHom_eq_ofReal_of_continuous (f := i.1.comp e.symm.toRingHom) (i.2.comp he.continuous)`. Take `⟨z, rfl⟩` from `e.symm.surjective y`.

Rewrite using `[he.norm_map_of_map_zero (map_zero _)]`. Conclude with `(congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_real z)`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex hw`. Apply the tactic sequence `have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry`. Take `⟨z, rfl⟩` from `e.symm.surjective y`.

Rewrite using `[he.norm_map_of_map_zero (map_zero _)]`. Break down `Complex.ringHom_eq_id_or_conj_of_continuous (f := i.1.comp e.symm.toRingHom) (i.2.comp he.continuous) with h1 | h1` into its components or cases. Conclude with `congrArg norm (DFunLike.congr_fun h1 z)`. Conclude with `(congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_conj z)`. Use `InfinitePlace.ext _ _ fun a => ?_` and prove the remaining obligations.

Rewrite using `[InfinitePlace.apply]`. Conclude with `(hn _).trans (InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ a))`. Establish `hinj : Function.Injective res`. Introduce and unpack `⟨v, j⟩ ⟨v', j'⟩ h`. Take `rfl : v = v'` from `(hmk ⟨v, j⟩).symm.trans ((congrArg InfinitePlace.mk h).trans (hmk ⟨v', j'⟩))`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `DFunLike.coe_injective` to reduce the goal to its premises. Use `(hd v).equalizer j.2 j'.2 ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Conclude with `DFunLike.congr_fun h a`. Establish `hsurj : Function.Surjective res`. Introduce `φ`. Take `⟨j, hj, e⟩` from `GlobalTheory.InfTypeLocal.exists_ext φ`. Conclude with `⟨⟨_, j, hj⟩, RingHom.ext e⟩`.

Use `haveI : ∀ w, Fintype (J w) := fun w => @Fintype.ofFinite _ (finite_contEmbInf w)`. Rewrite using `[← Fintype.prod_bijective res ⟨hinj, hsurj⟩ (fun p => res p (k : E) ^ n (res p)) _ fun _ => rfl, Fintype.prod_sigma]`. Conclude with `Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _`.
-/
theorem infPow_diagUnits : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ), infPow n (diagUnits E k) = ∏ φ : E →+* ℂ, φ (k : E) ^ n φ := by
  intro E _ _ n k
  classical
  let J : InfinitePlace E → Type := fun w => {i : w.Completion →+* ℂ // Continuous i}
  let res : (Σ w, J w) → (E →+* ℂ) := fun p => p.2.1.comp (algebraMap E p.1.Completion)
  have hd : ∀ w : InfinitePlace E, DenseRange (algebraMap E w.Completion) := fun w => by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, rfl⟩
  have hmk : ∀ p : Σ w, J w, InfinitePlace.mk (res p) = p.1 := by
    rintro ⟨w, i⟩
    have hn : ∀ y : w.Completion, ‖i.1 y‖ = ‖y‖ := fun y => by
      rcases w.isReal_or_isComplex with hw | hw
      · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry
        have h1 := Complex.ringHom_eq_ofReal_of_continuous (f := i.1.comp e.symm.toRingHom) (i.2.comp he.continuous)
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_real z)
      · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := i.1.comp e.symm.toRingHom)
          (i.2.comp he.continuous) with h1 | h1
        · exact congrArg norm (DFunLike.congr_fun h1 z)
        · exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_conj z)
    refine InfinitePlace.ext _ _ fun a => ?_
    rw [InfinitePlace.apply]
    exact (hn _).trans (InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ a))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    obtain rfl : v = v' := (hmk ⟨v, j⟩).symm.trans ((congrArg InfinitePlace.mk h).trans (hmk ⟨v', j'⟩))
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (hd v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨j, hj, e⟩ := GlobalTheory.InfTypeLocal.exists_ext φ
    exact ⟨⟨_, j, hj⟩, RingHom.ext e⟩
  haveI : ∀ w, Fintype (J w) := fun w => @Fintype.ofFinite _ (finite_contEmbInf w)
  rw [← Fintype.prod_bijective res ⟨hinj, hsurj⟩ (fun p => res p (k : E) ^ n (res p)) _ fun _ => rfl,
    Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _

/- English proof (translation)
The claim follows from `Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)`.
-/
theorem isOpenEmbedding_val_inf (E : Type) [Field E] [NumberField E] :
    Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
  Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)

/- English proof (translation)
Introduce `E _ _`. Use `haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by`. Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Conclude with `(InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace`. Conclude with `(InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace`.

Use `haveI : LocallyConnectedSpace (InfiniteAdeleRing E) := inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))`. Use `haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := (isOpenEmbedding_val_inf E).locallyConnectedSpace`. Conclude with `isOpen_connectedComponent`.
-/
theorem isOpen_connectedComponentOfOne_inf : ∀ (E : Type) [Field E] [NumberField E], IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) : Set (InfiniteAdeleRing E)ˣ) := by
  intro E _ _
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := (isOpenEmbedding_val_inf E).locallyConnectedSpace
  exact isOpen_connectedComponent

/- English proof (translation)
Introduce `E _ _`. Rewrite using `[DenseRange, dense_iff_inter_open]`. Introduce and unpack `U hU ⟨u, hu⟩`. Take `⟨k, v, hv, hk⟩` from `(InfiniteAdeleRing.denseRange_algebraMap E).exists_mem_open ((isOpenEmbedding_val_inf E).isOpenMap U hU) ⟨_, u, hu, rfl⟩`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Rewrite `hk` using `[map_zero]`. Establish `h1` using `congrFun v.mul_inv w`. Rewrite `h1` using `[hk, zero_mul]`.

Conclude with `zero_ne_one (α := w.Completion) h1`. Conclude with `⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩`.
-/
theorem denseRange_units_inf : ∀ (E : Type) [Field E] [NumberField E], DenseRange (fun k : Eˣ => (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ)) := by
  intro E _ _
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap E).exists_mem_open
    ((isOpenEmbedding_val_inf E).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    rw [map_zero] at hk
    have h1 := congrFun v.mul_inv w
    rw [hk, zero_mul] at h1
    exact zero_ne_one (α := w.Completion) h1
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

/- English proof (translation)
Introduce `E _ _ k hk φ`. Take `⟨e, he, hek⟩` from `GlobalTheory.InfTypeLocal.exists_ext (Complex.ofRealHom.comp φ)`. Set `w` to `InfinitePlace.mk (Complex.ofRealHom.comp φ)`. Establish `hd : DenseRange (algebraMap E w.Completion)`. Use `Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨WithAbs.equiv w.1 a, rfl⟩`. Establish `him : ∀ y : w.Completion, (e y).im = 0` using `fun y => congrFun (hd.equalizer (g := fun y => (e y).im) (h := fun _ => 0) (Complex.continuous_im.comp he) continuous_const (funext fun a => (congrArg Complex.im (hek a)).trans (by simp))) y`. Set `g : (InfiniteAdeleRing E)ˣ → ℝ` to `fun u => (e ((u : InfiniteAdeleRing E) w)).re`. Establish `hg : Continuous g` using `Complex.continuous_re.comp (he.comp ((continuous_apply w).comp Units.continuous_val))`.

Establish `hg0 : ∀ u, g u ≠ 0` using `fun u h => by`. Establish `h1 : e ((u : InfiniteAdeleRing E) w) = 0` using `Complex.ext h (him _)`. Conclude with `left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) ((map_eq_zero e).mp h1)`. Establish `hg1 : g 1 = 1` using `by show (e 1).re = 1`. Simplify using the standard rewrite rules.

Establish `hgk : g (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = φ k` using `by show (e (algebraMap E _ (k : E))).re = _`. Rewrite using `[hek]`. Simplify using the standard rewrite rules. Assume the negation of the conclusion as `hneg`. Use `isPreconnected_connectedComponent.intermediate_value hk mem_connectedComponent hg.continuousOn (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by rw [hgk]; exact not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)` as an intermediate fact.

Take `⟨u, -, hu⟩` from `this`. Conclude with `hg0 u hu`.
-/
theorem pos_of_mem_connectedComponentOfOne : ∀ (E : Type) [Field E] [NumberField E] (k : Eˣ), (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ → ∀ φ : E →+* ℝ, 0 < φ (k : E) := by
  intro E _ _ k hk φ
  obtain ⟨e, he, hek⟩ := GlobalTheory.InfTypeLocal.exists_ext (Complex.ofRealHom.comp φ)
  let w := InfinitePlace.mk (Complex.ofRealHom.comp φ)
  have hd : DenseRange (algebraMap E w.Completion) := by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, rfl⟩
  have him : ∀ y : w.Completion, (e y).im = 0 := fun y =>
    congrFun (hd.equalizer (g := fun y => (e y).im) (h := fun _ => 0) (Complex.continuous_im.comp he)
      continuous_const (funext fun a => (congrArg Complex.im (hek a)).trans (by simp))) y
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => (e ((u : InfiniteAdeleRing E) w)).re
  have hg : Continuous g :=
    Complex.continuous_re.comp (he.comp ((continuous_apply w).comp Units.continuous_val))
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : e ((u : InfiniteAdeleRing E) w) = 0 := Complex.ext h (him _)
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) ((map_eq_zero e).mp h1)
  have hg1 : g 1 = 1 := by
    show (e 1).re = 1
    simp
  have hgk : g (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = φ k := by
    show (e (algebraMap E _ (k : E))).re = _
    rw [hek]
    simp
  by_contra hneg
  have := isPreconnected_connectedComponent.intermediate_value hk mem_connectedComponent hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by rw [hgk]; exact not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  obtain ⟨u, -, hu⟩ := this
  exact hg0 u hu

end GlobalTheory.HeckeGal

end
