import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

set_option linter.style.haveILetI false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1

namespace ReciprocityTheory.Neutral.Bridge.HCFR

variable (K : Type) [Field K] [NumberField K]

open Classical in

def infIdele (w : InfinitePlace K) : (w.Completion)ˣ →* Ideles K :=
  Units.map
    { toFun := fun x => ((Pi.mulSingle w x : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K))
      map_one' := Prod.ext (Pi.mulSingle_one w) rfl
      map_mul' := fun x y => Prod.ext (Pi.mulSingle_mul w x y) (mul_one 1).symm }

/- English proof (translation)
Conclude with `Pi.mulSingle_eq_same (M := fun v : InfinitePlace K => v.Completion) w (x : w.Completion)`.
-/
theorem infIdele_fst_self (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).1 w = x := by
  classical
  exact Pi.mulSingle_eq_same (M := fun v : InfinitePlace K => v.Completion) w (x : w.Completion)

/- English proof (translation)
Conclude with `Pi.mulSingle_eq_of_ne (M := fun v : InfinitePlace K => v.Completion) h (x : w.Completion)`.
-/
theorem infIdele_fst_ne (w w' : InfinitePlace K) (h : w' ≠ w) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).1 w' = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := fun v : InfinitePlace K => v.Completion) h (x : w.Completion)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infIdele_snd (w : InfinitePlace K) (x : (w.Completion)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 v = 1 := rfl

/- English proof (translation)
Use `⟨fun w' hw' => by simp at hw', fun v => ⟨?_, 0, Submodule.mem_top, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[infIdele_snd]`. Conclude with `map_one _`. Rewrite using `[infIdele_snd, sub_self]`. Simplify using the standard rewrite rules.
-/
theorem infIdele_mem_rayUnits (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infIdele K w x ∈ rayUnits K ⊤ ∅ := by
  refine ⟨fun w' hw' => by simp at hw', fun v => ⟨?_, 0, Submodule.mem_top, ?_⟩⟩
  · rw [infIdele_snd]
    exact map_one _
  · rw [infIdele_snd, sub_self]
    simp

/- English proof (translation)
Use `haveI := h.finiteDimensional`. Use `haveI := h.isGalois`. Establish `hk : ∀ g' : Field.absoluteGaloisGroup K, abRestrict K E h (QuotientGroup.mk g') = AlgEquiv.restrictNormalHom E g'` using `fun g' => abRestrict_mk K E h g'`. Establish `hS : ((abRestrict K E h).ker : Set (Field.absoluteGaloisGroupAbelianization K)) = (QuotientGroup.mk : Field.absoluteGaloisGroup K → Field.absoluteGaloisGroupAbelianization K) '' (SetLike.coe E.fixingSubgroup)`. Use extensionality with `y`.

Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective y`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨g, ?_, rfl⟩` and prove the remaining obligations.

Establish `hg : g ∈ (AlgEquiv.restrictNormalHom E).ker` using `MonoidHom.mem_ker.mpr ((hk g).symm.trans hy)`. Rewrite `hg` using `[IntermediateField.restrictNormalHom_ker E]`. Conclude with `hg`. Introduce and unpack `⟨g', hg', he⟩`. Rewrite using `[← he, hk]`.

Establish `hg : g' ∈ (AlgEquiv.restrictNormalHom E).ker`. Rewrite using `[IntermediateField.restrictNormalHom_ker E]`. Conclude with `hg'`. Conclude with `MonoidHom.mem_ker.mp hg`. Establish `hopen : IsOpen ((abRestrict K E h).ker : Set (Field.absoluteGaloisGroupAbelianization K))`.

Rewrite using `[hS]`. Conclude with `QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen E)`. Conclude with `hopen.preimage (hc.comp continuous_quot_mk)`.
-/
theorem isOpen_ker (Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K)
    (hc : Continuous Art) (E : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K E) :
    IsOpen ((((abRestrict K E h).comp Art).comp (QuotientGroup.mk' (diagUnits K).range)).ker :
      Set (Ideles K)) := by
  haveI := h.finiteDimensional
  haveI := h.isGalois
  have hk : ∀ g' : Field.absoluteGaloisGroup K,
      abRestrict K E h (QuotientGroup.mk g') = AlgEquiv.restrictNormalHom E g' :=
    fun g' => abRestrict_mk K E h g'

  have hS : ((abRestrict K E h).ker : Set (Field.absoluteGaloisGroupAbelianization K)) =
      (QuotientGroup.mk : Field.absoluteGaloisGroup K → Field.absoluteGaloisGroupAbelianization K) ''
        (SetLike.coe E.fixingSubgroup) := by
    ext y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_image]
    constructor
    · intro hy
      refine ⟨g, ?_, rfl⟩
      have hg : g ∈ (AlgEquiv.restrictNormalHom E).ker := MonoidHom.mem_ker.mpr ((hk g).symm.trans hy)
      rw [IntermediateField.restrictNormalHom_ker E] at hg
      exact hg
    · rintro ⟨g', hg', he⟩
      rw [← he, hk]
      have hg : g' ∈ (AlgEquiv.restrictNormalHom E).ker := by
        rw [IntermediateField.restrictNormalHom_ker E]
        exact hg'
      exact MonoidHom.mem_ker.mp hg
  have hopen : IsOpen ((abRestrict K E h).ker : Set (Field.absoluteGaloisGroupAbelianization K)) := by
    rw [hS]
    exact QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen E)
  exact hopen.preimage (hc.comp continuous_quot_mk)

def infPart : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K where
  toFun x := (x.1, 1)
  map_one' := rfl
  map_mul' x y := Prod.ext rfl (mul_one 1).symm

def finPart : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K where
  toFun x := (1, x.2)
  map_one' := rfl
  map_mul' x y := Prod.ext (mul_one 1).symm rfl

/- English proof (translation)
Establish `h` using `congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) a.mul_inv`. Express the relevant statement in the definitionally equal form `(a : AdeleRing (𝓞 K) K).1 w * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).1 w = 1 at h`. Conclude with `left_ne_zero_of_mul_eq_one h`.
-/
theorem inf_comp_ne_zero (a : Ideles K) (w : InfinitePlace K) : (a : AdeleRing (𝓞 K) K).1 w ≠ 0 := by
  have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) a.mul_inv
  change (a : AdeleRing (𝓞 K) K).1 w * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).1 w = 1 at h
  exact left_ne_zero_of_mul_eq_one h

/- English proof (translation)
Establish `key : ∀ z : (w.Completion)ˣ, infIdele K w (z ^ m) ∈ N` using `fun z => by`. Rewrite using `[map_pow]`. Conclude with `hpow _`. Break down `InfinitePlace.isReal_or_isComplex w with hw | hw` into its components or cases. Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hw`.

Establish `hr : e (y : w.Completion) ≠ 0` using `(map_ne_zero e).2 y.ne_zero`. Establish `hs : (|e (y : w.Completion)| ^ ((m : ℝ)⁻¹)) ^ m = |e (y : w.Completion)|` using `Real.rpow_inv_natCast_pow (abs_nonneg _) hm.ne'`. Establish `hs0 : e.symm (|e (y : w.Completion)| ^ ((m : ℝ)⁻¹)) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ e.symm.injective]`. Introduce `h0`.

Rewrite `hs` using `[h0, zero_pow hm.ne']`. Conclude with `hr (abs_eq_zero.1 hs.symm)`. Set `z : (w.Completion)ˣ` to `Units.mk0 _ hs0`. Break down `lt_or_gt_of_ne hr with hneg' | hpos` into its components or cases. Establish `hy : y = -1 * z ^ m`.

Apply `Units.ext` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises. Simplify using `only [z, Units.val_mul, Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_neg, map_one, map_pow, RingEquiv.apply_symm_apply]`. Rewrite using `[hs, abs_of_neg hneg']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hy, map_mul]`. Conclude with `N.mul_mem (hneg w hw) (key z)`. Establish `hy : y = z ^ m`. Apply `Units.ext` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises.

Simplify using `only [z, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, RingEquiv.apply_symm_apply]`. Rewrite using `[hs, abs_of_pos hpos]`. Rewrite using `[hy]`. Conclude with `key z`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex hw`.

Take `⟨c, hc⟩` from `IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hm`. Establish `hc0 : e.symm c ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ e.symm.injective]`. Introduce and unpack `rfl`. Rewrite `hc` using `[zero_pow hm.ne']`.

Conclude with `(map_ne_zero e).2 y.ne_zero hc.symm`. Set `z : (w.Completion)ˣ` to `Units.mk0 _ hc0`. Establish `hy : y = z ^ m`. Apply `Units.ext` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises.

Simplify using `only [z, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, RingEquiv.apply_symm_apply, hc]`. Rewrite using `[hy]`. Conclude with `key z`.
-/
theorem infIdele_mem (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m) (hpow : ∀ x : Ideles K, x ^ m ∈ N)
    (hneg : ∀ w : InfinitePlace K, w.IsReal → infIdele K w (-1) ∈ N) (w : InfinitePlace K)
    (y : (w.Completion)ˣ) : infIdele K w y ∈ N := by
  have key : ∀ z : (w.Completion)ˣ, infIdele K w (z ^ m) ∈ N := fun z => by
    rw [map_pow]
    exact hpow _
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  ·
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hr : e (y : w.Completion) ≠ 0 := (map_ne_zero e).2 y.ne_zero
    have hs : (|e (y : w.Completion)| ^ ((m : ℝ)⁻¹)) ^ m = |e (y : w.Completion)| :=
      Real.rpow_inv_natCast_pow (abs_nonneg _) hm.ne'
    have hs0 : e.symm (|e (y : w.Completion)| ^ ((m : ℝ)⁻¹)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ e.symm.injective]
      intro h0
      rw [h0, zero_pow hm.ne'] at hs
      exact hr (abs_eq_zero.1 hs.symm)
    let z : (w.Completion)ˣ := Units.mk0 _ hs0
    rcases lt_or_gt_of_ne hr with hneg' | hpos
    · have hy : y = -1 * z ^ m := by
        apply Units.ext
        apply e.injective
        simp only [z, Units.val_mul, Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val,
          Units.val_mk0, map_mul, map_neg, map_one, map_pow, RingEquiv.apply_symm_apply]
        rw [hs, abs_of_neg hneg']
        ring
      rw [hy, map_mul]
      exact N.mul_mem (hneg w hw) (key z)
    · have hy : y = z ^ m := by
        apply Units.ext
        apply e.injective
        simp only [z, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, RingEquiv.apply_symm_apply]
        rw [hs, abs_of_pos hpos]
      rw [hy]
      exact key z
  ·
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hm
    have hc0 : e.symm c ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ e.symm.injective]
      rintro rfl
      rw [zero_pow hm.ne'] at hc
      exact (map_ne_zero e).2 y.ne_zero hc.symm
    let z : (w.Completion)ˣ := Units.mk0 _ hc0
    have hy : y = z ^ m := by
      apply Units.ext
      apply e.injective
      simp only [z, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, RingEquiv.apply_symm_apply, hc]
    rw [hy]
    exact key z

def fstU : Ideles K →* InfiniteAdeleRing K :=
  (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (Units.coeHom (AdeleRing (𝓞 K) K))

def sndU : Ideles K →* FiniteAdeleRing (𝓞 K) K :=
  (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp (Units.coeHom (AdeleRing (𝓞 K) K))

/- English proof (translation)
Set `x : ∀ w : InfinitePlace K, (w.Completion)ˣ` to `fun w => Units.mk0 ((a : AdeleRing (𝓞 K) K).1 w) (inf_comp_ne_zero K a w)`. Establish `hext : ∀ b c : Ideles K, fstU K b = fstU K c → sndU K b = sndU K c → b = c` using `fun b c h1 h2 => Units.ext (Prod.ext h1 h2)`. Establish `ha' : a = ∏ w, infIdele K w (x w)`. Apply `hext` to reduce the goal to its premises. Rewrite using `[map_prod]`.

Use function extensionality and compare the values at `w'`. Establish `hpa : (∏ i, (fstU K (infIdele K i (x i)) : (v : InfinitePlace K) → v.Completion)) w' = ∏ i, (fstU K (infIdele K i (x i)) : (v : InfinitePlace K) → v.Completion) w'` using `Finset.prod_apply _ _ _`. Use `Eq.trans ?_ hpa.symm` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single w']`. Conclude with `(infIdele_fst_self K w' (x w')).symm`.

Introduce `w _ hw`. Conclude with `infIdele_fst_ne K w w' (Ne.symm hw) (x w)`. Introduce `hw'`. Conclude with `absurd (Finset.mem_univ _) hw'`. Rewrite using `[map_prod] show (a : AdeleRing (𝓞 K) K).2 = ∏ w, sndU K (infIdele K w (x w))`.

Rewrite using `[ha]`. Conclude with `(Finset.prod_eq_one fun w _ => rfl).symm`. Rewrite using `[ha']`. Conclude with `Subgroup.prod_mem _ fun w _ => infIdele_mem K N m hm hpow hneg w (x w)`.
-/
theorem mem_of_pow (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m) (hpow : ∀ x : Ideles K, x ^ m ∈ N)
    (hneg : ∀ w : InfinitePlace K, w.IsReal → infIdele K w (-1) ∈ N)
    (a : Ideles K) (ha : (a : AdeleRing (𝓞 K) K).2 = 1) : a ∈ N := by
  classical
  let x : ∀ w : InfinitePlace K, (w.Completion)ˣ :=
    fun w => Units.mk0 ((a : AdeleRing (𝓞 K) K).1 w) (inf_comp_ne_zero K a w)
  have hext : ∀ b c : Ideles K, fstU K b = fstU K c → sndU K b = sndU K c → b = c :=
    fun b c h1 h2 => Units.ext (Prod.ext h1 h2)
  have ha' : a = ∏ w, infIdele K w (x w) := by
    apply hext
    · rw [map_prod]
      funext w'
      have hpa : (∏ i, (fstU K (infIdele K i (x i)) : (v : InfinitePlace K) → v.Completion)) w' =
          ∏ i, (fstU K (infIdele K i (x i)) : (v : InfinitePlace K) → v.Completion) w' :=
        Finset.prod_apply _ _ _
      refine Eq.trans ?_ hpa.symm
      rw [Finset.prod_eq_single w']
      · exact (infIdele_fst_self K w' (x w')).symm
      · intro w _ hw
        exact infIdele_fst_ne K w w' (Ne.symm hw) (x w)
      · intro hw'
        exact absurd (Finset.mem_univ _) hw'
    · rw [map_prod]
      show (a : AdeleRing (𝓞 K) K).2 = ∏ w, sndU K (infIdele K w (x w))
      rw [ha]
      exact (Finset.prod_eq_one fun w _ => rfl).symm
  rw [ha']
  exact Subgroup.prod_mem _ fun w _ => infIdele_mem K N m hm hpow hneg w (x w)

end ReciprocityTheory.Neutral.Bridge.HCFR
