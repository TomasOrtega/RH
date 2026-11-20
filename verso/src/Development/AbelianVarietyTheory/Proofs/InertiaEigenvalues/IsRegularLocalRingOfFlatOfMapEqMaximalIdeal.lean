import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct

namespace GlobalTheory

namespace SerreRegular

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `M _ _ h`. Simplify using `only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one] at h ⊢`. Establish `: Module.Projective A M` using `(IsProjective.iff_projective M).mpr h`.

Conclude with `(IsProjective.iff_projective _).mp inferInstance`. Consider the case `succ n ih`. Introduce `M _ hM h`. Take `⟨r, f, hf⟩` from `Module.Finite.exists_fin' A M`. Take `⟨hK, hinj⟩` from `hG M r f hf hM`.

Establish `hS : f.shortComplexKer.ShortExact` using `LinearMap.shortExact_shortComplexKer hf`. Establish `hP : Projective f.shortComplexKer.X₂` using `(IsProjective.iff_projective (Fin r → A)).mp inferInstance`. Establish `hKn : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) n` using `(hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h`. Establish `h1` using `ih (ModuleCat.of A (LinearMap.ker f)) hK hKn`. Establish `hex : Function.Exact ((LinearMap.ker f).subtype.baseChange B) (f.baseChange B)` using `lTensor_exact B (LinearMap.exact_subtype_ker_map f) hf`.

Establish `hS' : (ModuleCat.shortComplexOfCompEqZero _ _ hex.linearMap_comp_eq_zero).ShortExact` using `ModuleCat.shortComplex_shortExact _ hex hinj (LinearMap.lTensor_surjective B hf)`. Establish `hP' : Projective (ModuleCat.shortComplexOfCompEqZero _ _ hex.linearMap_comp_eq_zero).X₂` using `(IsProjective.iff_projective (B ⊗[A] (Fin r → A))).mp inferInstance`. Conclude with `(hS'.hasProjectiveDimensionLT_X₃_iff n hP').2 h1`.
-/
theorem pd_baseChange {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (Good : ModuleCat.{0} A → Prop)
    (hG : ∀ (M : ModuleCat.{0} A) (r : ℕ) (f : (Fin r → A) →ₗ[A] M), Function.Surjective f →
      Good M → Good (ModuleCat.of A (LinearMap.ker f)) ∧
        Function.Injective ((LinearMap.ker f).subtype.lTensor B)) (n : ℕ) :
    ∀ (M : ModuleCat.{0} A) [Module.Finite A M], Good M → HasProjectiveDimensionLE M n →
      HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] M)) n := by
  induction n with
  | zero =>
    intro M _ _ h
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one] at h ⊢
    have : Module.Projective A M := (IsProjective.iff_projective M).mpr h
    exact (IsProjective.iff_projective _).mp inferInstance
  | succ n ih =>
    intro M _ hM h
    obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' A M
    obtain ⟨hK, hinj⟩ := hG M r f hf hM
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hP : Projective f.shortComplexKer.X₂ :=
      (IsProjective.iff_projective (Fin r → A)).mp inferInstance
    have hKn : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have h1 := ih (ModuleCat.of A (LinearMap.ker f)) hK hKn
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange B) (f.baseChange B) :=
      lTensor_exact B (LinearMap.exact_subtype_ker_map f) hf
    have hS' : (ModuleCat.shortComplexOfCompEqZero _ _ hex.linearMap_comp_eq_zero).ShortExact :=
      ModuleCat.shortComplex_shortExact _ hex hinj (LinearMap.lTensor_surjective B hf)
    have hP' : Projective (ModuleCat.shortComplexOfCompEqZero _ _ hex.linearMap_comp_eq_zero).X₂ :=
      (IsProjective.iff_projective (B ⊗[A] (Fin r → A))).mp inferInstance
    exact (hS'.hasProjectiveDimensionLT_X₃_iff n hP').2 h1

/- English proof (translation)
The claim follows from `pd_baseChange (fun _ => True) (fun _ _ f _ _ => ⟨trivial, Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)⟩) n M trivial h`.
-/
theorem pd_flat {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (n : ℕ) (M : ModuleCat.{0} A) [Module.Finite A M]
    (h : HasProjectiveDimensionLE M n) : HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] M)) n :=
  pd_baseChange (fun _ => True) (fun _ _ f _ _ =>
    ⟨trivial, Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)⟩)
    n M trivial h

/- English proof (translation)
Use `pd_baseChange (fun N => IsSMulRegular N x) ?_ n M hM h` and prove the remaining obligations. Introduce `N r f hf hN`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Conclude with `hx (congrFun (congrArg Subtype.val hab) i)`. Establish `e1 : Function.Exact (LinearMap.toSpanSingleton A A x) (Ideal.span {x}).mkQ`. Introduce `y`. Simplify using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`.

Use `lTensor_injective_of_exact_of_exact_of_rTensor_injective e1 (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map f) hf ?_ (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))` and prove the remaining obligations. Establish `e2 : ∀ t, TensorProduct.lid A N ((LinearMap.toSpanSingleton A A x).rTensor N t) = x • TensorProduct.lid A N t`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb, smul_add]`. Consider the case `tmul a m => simp [smul_smul, mul_comm]`. Introduce `a b hab`. Apply `(TensorProduct.lid A N).injective` to reduce the goal to its premises. Apply `hN` to reduce the goal to its premises.

Simplify using `only [← e2, hab]`.
-/
theorem pd_quot {A : Type} [CommRing A] [IsNoetherianRing A] {x : A} (hx : IsSMulRegular A x)
    (n : ℕ) (M : ModuleCat.{0} A) [Module.Finite A M] (hM : IsSMulRegular M x)
    (h : HasProjectiveDimensionLE M n) :
    HasProjectiveDimensionLE (ModuleCat.of (A ⧸ Ideal.span {x}) ((A ⧸ Ideal.span {x}) ⊗[A] M)) n := by
  refine pd_baseChange (fun N => IsSMulRegular N x) ?_ n M hM h
  intro N r f hf hN
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    funext i
    exact hx (congrFun (congrArg Subtype.val hab) i)
  · have e1 : Function.Exact (LinearMap.toSpanSingleton A A x) (Ideal.span {x}).mkQ := by
      intro y
      simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine lTensor_injective_of_exact_of_exact_of_rTensor_injective e1
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map f) hf ?_
      (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))
    have e2 : ∀ t, TensorProduct.lid A N ((LinearMap.toSpanSingleton A A x).rTensor N t) =
        x • TensorProduct.lid A N t := by
      intro t
      induction t with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb, smul_add]
      | tmul a m => simp [smul_smul, mul_comm]
    intro a b hab
    apply (TensorProduct.lid A N).injective
    apply hN
    simp only [← e2, hab]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `M _ h`. Simplify using `only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one] at h`. Conclude with `(IsProjective.iff_projective M).mpr h`.

Consider the case `succ n ih`. Introduce `M _ h`. Establish `hfr : Module.Free (ResidueField A) (ResidueField A ⊗[A] M)` using `Module.Free.of_divisionRing _ _`. Set `b` to `Module.finBasis (ResidueField A) (ResidueField A ⊗[A] M)`. Use `choose v hv using fun i => TensorProduct.mk_surjective A M (ResidueField A) residue_surjective (b i)`.

Establish `hsp` using `IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv`. Set `f` to `Fintype.linearCombination A v`. Establish `hf : Function.Surjective f`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]`. Establish `hS : f.shortComplexKer.ShortExact` using `LinearMap.shortExact_shortComplexKer hf`.

Establish `hP : Projective f.shortComplexKer.X₂` using `(IsProjective.iff_projective (_ → A)).mp inferInstance`. Establish `hKn : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) n` using `(hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h`. Establish `hK : Module.Projective A (LinearMap.ker f)` using `ih _ hKn`. Establish `hfree : Module.Free A (LinearMap.ker f)` using `Module.free_of_flat_of_isLocalRing`. Establish `hkill : ∀ c : LinearMap.ker f, a • c = 0`.

Introduce `c`. Establish `h0 : ∑ i, residue A (c.1 i) • b i = 0`. Establish `h1` using `congrArg (TensorProduct.mk A (ResidueField A) M 1) (LinearMap.mem_ker.mp c.2)`. Rewrite `h1` using `[Fintype.linearCombination_apply, map_sum, map_zero]`. Rewrite using `[← h1]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hv]`. Conclude with `algebraMap_smul (ResidueField A) (c.1 i) (b i)`. Establish `h2` using `Fintype.linearIndependent_iff.mp b.linearIndependent _ h0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Conclude with `hm _ ((residue_eq_zero_iff _).mp (h2 i))`. Establish `hsub : Subsingleton (LinearMap.ker f)`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_subsingleton_iff_nontrivial]`.

Establish `: a ∈ Module.annihilator A (LinearMap.ker f)` using `Module.mem_annihilator.mpr hkill`. Rewrite `this` using `[Module.annihilator_eq_bot.mpr inferInstance]`. Conclude with `ha this`. Establish `hinj : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot]`.

Conclude with `Submodule.subsingleton_iff_eq_bot.mp hsub`. Conclude with `Module.Projective.of_equiv' (LinearEquiv.ofBijective f ⟨hinj, hf⟩)`.
-/
theorem projective_of_socle {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {a : A}
    (ha : a ≠ 0) (hm : ∀ y ∈ maximalIdeal A, a * y = 0) (n : ℕ) :
    ∀ (M : ModuleCat.{0} A) [Module.Finite A M], HasProjectiveDimensionLE M n →
      Module.Projective A M := by
  induction n with
  | zero =>
    intro M _ h
    simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one] at h
    exact (IsProjective.iff_projective M).mpr h
  | succ n ih =>
    intro M _ h
    have hfr : Module.Free (ResidueField A) (ResidueField A ⊗[A] M) :=
      Module.Free.of_divisionRing _ _
    let b := Module.finBasis (ResidueField A) (ResidueField A ⊗[A] M)
    choose v hv using fun i => TensorProduct.mk_surjective A M (ResidueField A)
      residue_surjective (b i)
    have hsp := IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
    let f := Fintype.linearCombination A v
    have hf : Function.Surjective f := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hP : Projective f.shortComplexKer.X₂ :=
      (IsProjective.iff_projective (_ → A)).mp inferInstance
    have hKn : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker f)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h
    have hK : Module.Projective A (LinearMap.ker f) := ih _ hKn
    have hfree : Module.Free A (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
    have hkill : ∀ c : LinearMap.ker f, a • c = 0 := by
      intro c
      have h0 : ∑ i, residue A (c.1 i) • b i = 0 := by
        have h1 := congrArg (TensorProduct.mk A (ResidueField A) M 1) (LinearMap.mem_ker.mp c.2)
        rw [Fintype.linearCombination_apply, map_sum, map_zero] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hv]
        exact algebraMap_smul (ResidueField A) (c.1 i) (b i)
      have h2 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h0
      apply Subtype.ext
      funext i
      exact hm _ ((residue_eq_zero_iff _).mp (h2 i))
    have hsub : Subsingleton (LinearMap.ker f) := by
      by_contra hn
      rw [not_subsingleton_iff_nontrivial] at hn
      have : a ∈ Module.annihilator A (LinearMap.ker f) := Module.mem_annihilator.mpr hkill
      rw [Module.annihilator_eq_bot.mpr inferInstance] at this
      exact ha this
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.subsingleton_iff_eq_bot.mp hsub
    exact Module.Projective.of_equiv' (LinearEquiv.ofBijective f ⟨hinj, hf⟩)

/- English proof (translation)
Use `IsLocalHom.of_surjective f hf` as an intermediate fact. Conclude with `IsLocalRing.map_maximalIdeal_of_surjective f hf`.
-/
theorem map_maximalIdeal_eq {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) : (maximalIdeal A).map f = maximalIdeal B := by
  have := IsLocalHom.of_surjective f hf
  exact IsLocalRing.map_maximalIdeal_of_surjective f hf

/- English proof (translation)
Apply `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` to reduce the goal to its premises. Rewrite using `[← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hx hm, ← IsRegularLocalRing.spanFinrank_maximalIdeal]`. Take `⟨s, hs, hsp⟩` from `Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal (A ⧸ Ideal.span {x})))`. Use `choose g hg using Ideal.Quotient.mk_surjective (I := Ideal.span {x})`. Establish `hmap` using `map_maximalIdeal_eq (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective`.

Establish `h1 : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span (g '' s)) = maximalIdeal (A ⧸ Ideal.span {x})`. Rewrite using `[Ideal.map_span, Set.image_image]`. Simplify `hsp` using `[hg]`. Establish `h2 : maximalIdeal A = Ideal.span ((insert x (s.image g) : Finset A) : Set A)`. Establish `h3` using `congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x}))) (hmap.trans h1.symm)`.

Rewrite `h3` using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hm)]`. Rewrite using `[h3, Finset.coe_insert, Ideal.span_insert, Finset.coe_image, sup_comm]`. Establish `h4` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le (insert x (s.image g))`. Rewrite `h4` using `[← h2]`. Establish `h5` using `Finset.card_insert_le x (s.image g)`.

Establish `h6 : (s.image g).card ≤ s.card` using `Finset.card_image_le`. Establish `h7 : (maximalIdeal A).spanFinrank ≤ (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank + 1`. Use linear arithmetic over natural numbers and integers. Conclude with `h7` after adjusting the coercions.
-/
theorem regular_of_quotient {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hx : IsSMulRegular A x) (hm : x ∈ maximalIdeal A)
    [IsRegularLocalRing (A ⧸ Ideal.span {x})] : IsRegularLocalRing A := by
  classical
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hx hm,
    ← IsRegularLocalRing.spanFinrank_maximalIdeal]
  obtain ⟨s, hs, hsp⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (A ⧸ Ideal.span {x})))
  choose g hg using Ideal.Quotient.mk_surjective (I := Ideal.span {x})
  have hmap := map_maximalIdeal_eq (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have h1 : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span (g '' s)) =
      maximalIdeal (A ⧸ Ideal.span {x}) := by
    rw [Ideal.map_span, Set.image_image]
    simpa [hg] using hsp
  have h2 : maximalIdeal A = Ideal.span ((insert x (s.image g) : Finset A) : Set A) := by
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x}))) (hmap.trans h1.symm)
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hm)] at h3
    rw [h3, Finset.coe_insert, Ideal.span_insert, Finset.coe_image, sup_comm]
  have h4 := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le
    (insert x (s.image g))
  rw [← h2] at h4
  have h5 := Finset.card_insert_le x (s.image g)
  have h6 : (s.image g).card ≤ s.card := Finset.card_image_le
  have h7 : (maximalIdeal A).spanFinrank ≤ (maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank + 1 := by
    omega
  exact_mod_cast h7

/- English proof (translation)
Establish `hmap` using `map_maximalIdeal_eq (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective`. Establish `hx0 : Ideal.Quotient.mk (Ideal.span {x}) x = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)`. Use `set B := A ⧸ Ideal.span {x} with hB`. Establish `hv0 : (maximalIdeal A).toCotangent ⟨x, hm⟩ ≠ 0`. Rewrite using `[Ne, Ideal.toCotangent_eq_zero]`.

Conclude with `hm2`. Take `⟨l, hl⟩` from `Module.Projective.exists_dual_eq_one (ResidueField A) (V := CotangentSpace A) hv0`. Set `j : ResidueField A →ₗ[A] B ⧸ maximalIdeal B` to `Submodule.liftQ (maximalIdeal A) (Algebra.linearMap A (B ⧸ maximalIdeal B)) (by`. Introduce `a ha`. Rewrite using `[LinearMap.mem_ker]`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (maximalIdeal B) (Ideal.Quotient.mk (Ideal.span {x}) a) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← hmap]`. Conclude with `Ideal.mem_map_of_mem _ ha)`. Establish `hj : j 1 = 1` using `map_one (algebraMap A (B ⧸ maximalIdeal B))`. Set `r0 : maximalIdeal A →ₗ[A] B ⧸ maximalIdeal B` to `j ∘ₗ (l.restrictScalars A) ∘ₗ (maximalIdeal A).toCotangent`.

Establish `hr0 : r0 ⟨x, hm⟩ = 1`. Express the relevant statement in the definitionally equal form `j (l ((maximalIdeal A).toCotangent ⟨x, hm⟩)) = 1`. Rewrite using `[hl, hj]`. Set `r : B ⊗[A] maximalIdeal A →ₗ[B] B ⧸ maximalIdeal B` to `r0.liftBaseChange B`. Set `i : (B ⧸ maximalIdeal B) →ₗ[B] B ⊗[A] maximalIdeal A` to `Submodule.liftQ (maximalIdeal B) (LinearMap.toSpanSingleton B _ ((1 : B) ⊗ₜ[A] ⟨x, hm⟩)) (by`.

Introduce `b hb`. Rewrite `hb` using `[← hmap, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]`. Take `⟨a, ha, rfl⟩` from `hb`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Establish `e : a • (⟨x, hm⟩ : maximalIdeal A) = x • (⟨a, ha⟩ : maximalIdeal A)` using `Subtype.ext (mul_comm a x)`.

Express the relevant statement in the definitionally equal form `algebraMap A B a • _ = 0`. Rewrite using `[algebraMap_smul, ← TensorProduct.tmul_smul, e, TensorProduct.tmul_smul, ← algebraMap_smul B x]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {x}) x • _ = 0`. Rewrite using `[hx0, zero_smul])`. Establish `hri : r ∘ₗ i = LinearMap.id`.

Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `r (LinearMap.toSpanSingleton B _ ((1 : B) ⊗ₜ[A] (⟨x, hm⟩ : maximalIdeal A)) 1) = 1`. Rewrite using `[LinearMap.toSpanSingleton_apply, one_smul, LinearMap.liftBaseChange_tmul, hr0, one_smul]`. Set `ret : Retract (ModuleCat.of B (B ⧸ maximalIdeal B)) (ModuleCat.of B (B ⊗[A] maximalIdeal A))` to `⟨ModuleCat.ofHom i, ModuleCat.ofHom r, by`.

Rewrite using `[← ModuleCat.ofHom_comp, hri]`. Use the proof step `rfl⟩`. Conclude with `ret.hasProjectiveDimensionLT _`.
-/
theorem pd_residue_quot {A : Type} [CommRing A] [IsLocalRing A] {x : A}
    (hm : x ∈ maximalIdeal A) (hm2 : x ∉ maximalIdeal A ^ 2) [IsLocalRing (A ⧸ Ideal.span {x})]
    (n : ℕ) (h : HasProjectiveDimensionLE
      (ModuleCat.of (A ⧸ Ideal.span {x}) ((A ⧸ Ideal.span {x}) ⊗[A] maximalIdeal A)) n) :
    HasProjectiveDimensionLE (ModuleCat.of (A ⧸ Ideal.span {x})
      ((A ⧸ Ideal.span {x}) ⧸ maximalIdeal (A ⧸ Ideal.span {x}))) n := by
  have hmap := map_maximalIdeal_eq (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have hx0 : Ideal.Quotient.mk (Ideal.span {x}) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  set B := A ⧸ Ideal.span {x} with hB
  have hv0 : (maximalIdeal A).toCotangent ⟨x, hm⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    exact hm2
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one (ResidueField A) (V := CotangentSpace A) hv0
  let j : ResidueField A →ₗ[A] B ⧸ maximalIdeal B :=
    Submodule.liftQ (maximalIdeal A) (Algebra.linearMap A (B ⧸ maximalIdeal B)) (by
      intro a ha
      rw [LinearMap.mem_ker]
      change Ideal.Quotient.mk (maximalIdeal B) (Ideal.Quotient.mk (Ideal.span {x}) a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hmap]
      exact Ideal.mem_map_of_mem _ ha)
  have hj : j 1 = 1 := map_one (algebraMap A (B ⧸ maximalIdeal B))
  let r0 : maximalIdeal A →ₗ[A] B ⧸ maximalIdeal B :=
    j ∘ₗ (l.restrictScalars A) ∘ₗ (maximalIdeal A).toCotangent
  have hr0 : r0 ⟨x, hm⟩ = 1 := by
    change j (l ((maximalIdeal A).toCotangent ⟨x, hm⟩)) = 1
    rw [hl, hj]
  let r : B ⊗[A] maximalIdeal A →ₗ[B] B ⧸ maximalIdeal B := r0.liftBaseChange B
  let i : (B ⧸ maximalIdeal B) →ₗ[B] B ⊗[A] maximalIdeal A :=
    Submodule.liftQ (maximalIdeal B) (LinearMap.toSpanSingleton B _ ((1 : B) ⊗ₜ[A] ⟨x, hm⟩)) (by
      intro b hb
      rw [← hmap, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      have e : a • (⟨x, hm⟩ : maximalIdeal A) = x • (⟨a, ha⟩ : maximalIdeal A) :=
        Subtype.ext (mul_comm a x)
      change algebraMap A B a • _ = 0
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, e, TensorProduct.tmul_smul,
        ← algebraMap_smul B x]
      change Ideal.Quotient.mk (Ideal.span {x}) x • _ = 0
      rw [hx0, zero_smul])
  have hri : r ∘ₗ i = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext_ring
    change r (LinearMap.toSpanSingleton B _ ((1 : B) ⊗ₜ[A] (⟨x, hm⟩ : maximalIdeal A)) 1) = 1
    rw [LinearMap.toSpanSingleton_apply, one_smul, LinearMap.liftBaseChange_tmul, hr0, one_smul]
  let ret : Retract (ModuleCat.of B (B ⧸ maximalIdeal B)) (ModuleCat.of B (B ⊗[A] maximalIdeal A)) :=
    ⟨ModuleCat.ofHom i, ModuleCat.ofHom r, by
      rw [← ModuleCat.ofHom_comp, hri]; rfl⟩
  exact ret.hasProjectiveDimensionLT _

/- English proof (translation)
Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `A _ _ _ hd ⟨n, hn⟩`. Establish `hfield : maximalIdeal A = ⊥ → IsRegularLocalRing A` using `fun h => by`. Set `_` to `(isField_iff_maximalIdeal_eq.mpr h).toField`.

Use `infer_instance`. Establish `hS : (maximalIdeal A).mkQ.shortComplexKer.ShortExact` using `LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective _)`. Establish `hP : Projective (maximalIdeal A).mkQ.shortComplexKer.X₂` using `(IsProjective.iff_projective A).mp inferInstance`. Establish `hK : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker (maximalIdeal A).mkQ)) n` using `(hS.hasProjectiveDimensionLT_X₃_iff n hP).1 (hasProjectiveDimensionLT_of_ge (ModuleCat.of A (A ⧸ maximalIdeal A)) (n + 1) _ (by omega))`. Rewrite `hK` using `[Submodule.ker_mkQ]`.

Distinguish the cases in `hsq : maximalIdeal A ≤ maximalIdeal A ^ 2`. Conclude with `hfield (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq A hsq)`. Distinguish the cases in `hass : ∃ p ∈ associatedPrimes A A, maximalIdeal A ≤ p`. Take `⟨p, hp, hle⟩` from `hass`. Take `⟨hpp, a, ha⟩` from `isAssociatedPrime_iff.mp hp`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Apply `hpp.ne_top` to reduce the goal to its premises. Rewrite using `[ha, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton]`. Simplify using the standard rewrite rules.

Establish `hkill : ∀ y ∈ maximalIdeal A, a * y = 0`. Introduce `y hy`. Use `hle hy` as an intermediate fact. Rewrite `this` using `[ha, Submodule.mem_colon_singleton]`. Simplify `this` using `[mul_comm]`.

Establish `hpr : Module.Projective A (maximalIdeal A)` using `projective_of_socle ha0 hkill n _ hK`. Establish `hfree : Module.Free A (maximalIdeal A)` using `Module.free_of_flat_of_isLocalRing`. Apply `hfield` to reduce the goal to its premises. Rewrite using `[← Submodule.subsingleton_iff_eq_bot]`. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[not_subsingleton_iff_nontrivial]`. Establish `: a ∈ Module.annihilator A (maximalIdeal A)` using `Module.mem_annihilator.mpr fun y => Subtype.ext (hkill _ y.2)`. Rewrite `this` using `[Module.annihilator_eq_bot.mpr inferInstance]`. Conclude with `ha0 this`. Take `⟨x, hx, hx2, hreg⟩ : ∃ x ∈ maximalIdeal A, x ∉ maximalIdeal A ^ 2 ∧ IsSMulRegular A x` from `by classical`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨t, ht⟩` from `(associatedPrimes.finite A A).exists_finset_coe`. Establish `hsub : (maximalIdeal A : Set A) ⊆ ⋃ i ∈ ((insert (maximalIdeal A ^ 2) t : Finset (Ideal A)) : Set (Ideal A)), (i : Set A)`. Rewrite using `[Finset.coe_insert, Set.biUnion_insert, ht, biUnion_associatedPrimes_eq_compl_regular]`.

Introduce `y hy`. Distinguish the cases in `h2 : y ∈ maximalIdeal A ^ 2`. Conclude with `Or.inl h2`. Conclude with `Or.inr (hcon y hy h2)`. Take `⟨i, hi, hle⟩` from `(Ideal.subset_union_prime (maximalIdeal A ^ 2) (maximalIdeal A ^ 2) (fun i hi h1 _ => by`.

Establish `: i ∈ associatedPrimes A A` using `ht ▸ (Finset.mem_insert.mp hi).resolve_left h1`. Conclude with `this.isPrime)).mp hsub`. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `hsq hle`. Conclude with `hass ⟨i, ht ▸ hi, hle⟩`.

Use `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx` as an intermediate fact. Establish `hlt` using `ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le A hx hx2`. Rewrite `hlt` using `[← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd]`. Establish `hregm : IsSMulRegular (maximalIdeal A) x` using `fun a b hab => Subtype.ext (hreg (congrArg Subtype.val hab))`. Use `ih _ hlt (A ⧸ Ideal.span {x}) rfl ⟨n, pd_residue_quot hx hx2 n (pd_quot hreg n (ModuleCat.of A (maximalIdeal A)) hregm hK)⟩` as an intermediate fact.

Conclude with `regular_of_quotient hreg hx`.
-/
theorem regular_of_pd (d : ℕ) : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A],
    (maximalIdeal A).spanFinrank = d →
    (∃ n, HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ maximalIdeal A)) n) →
    IsRegularLocalRing A := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro A _ _ _ hd ⟨n, hn⟩
  have hfield : maximalIdeal A = ⊥ → IsRegularLocalRing A := fun h => by
    let _ := (isField_iff_maximalIdeal_eq.mpr h).toField
    infer_instance
  have hS : (maximalIdeal A).mkQ.shortComplexKer.ShortExact :=
    LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective _)
  have hP : Projective (maximalIdeal A).mkQ.shortComplexKer.X₂ :=
    (IsProjective.iff_projective A).mp inferInstance
  have hK : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker (maximalIdeal A).mkQ)) n :=
    (hS.hasProjectiveDimensionLT_X₃_iff n hP).1
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of A (A ⧸ maximalIdeal A)) (n + 1) _ (by omega))
  rw [Submodule.ker_mkQ] at hK
  by_cases hsq : maximalIdeal A ≤ maximalIdeal A ^ 2
  · exact hfield (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq A hsq)
  by_cases hass : ∃ p ∈ associatedPrimes A A, maximalIdeal A ≤ p
  · obtain ⟨p, hp, hle⟩ := hass
    obtain ⟨hpp, a, ha⟩ := isAssociatedPrime_iff.mp hp
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hpp.ne_top
      rw [ha, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton]
      simp
    have hkill : ∀ y ∈ maximalIdeal A, a * y = 0 := by
      intro y hy
      have := hle hy
      rw [ha, Submodule.mem_colon_singleton] at this
      simpa [mul_comm] using this
    have hpr : Module.Projective A (maximalIdeal A) := projective_of_socle ha0 hkill n _ hK
    have hfree : Module.Free A (maximalIdeal A) := Module.free_of_flat_of_isLocalRing
    apply hfield
    rw [← Submodule.subsingleton_iff_eq_bot]
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    have : a ∈ Module.annihilator A (maximalIdeal A) :=
      Module.mem_annihilator.mpr fun y => Subtype.ext (hkill _ y.2)
    rw [Module.annihilator_eq_bot.mpr inferInstance] at this
    exact ha0 this
  obtain ⟨x, hx, hx2, hreg⟩ : ∃ x ∈ maximalIdeal A, x ∉ maximalIdeal A ^ 2 ∧ IsSMulRegular A x := by
    classical
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht⟩ := (associatedPrimes.finite A A).exists_finset_coe
    have hsub : (maximalIdeal A : Set A) ⊆
        ⋃ i ∈ ((insert (maximalIdeal A ^ 2) t : Finset (Ideal A)) : Set (Ideal A)), (i : Set A) := by
      rw [Finset.coe_insert, Set.biUnion_insert, ht, biUnion_associatedPrimes_eq_compl_regular]
      intro y hy
      by_cases h2 : y ∈ maximalIdeal A ^ 2
      · exact Or.inl h2
      · exact Or.inr (hcon y hy h2)
    obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (maximalIdeal A ^ 2) (maximalIdeal A ^ 2)
      (fun i hi h1 _ => by
        have : i ∈ associatedPrimes A A := ht ▸ (Finset.mem_insert.mp hi).resolve_left h1
        exact this.isPrime)).mp hsub
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hsq hle
    · exact hass ⟨i, ht ▸ hi, hle⟩
  have := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
  have hlt := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le A hx hx2
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd] at hlt
  have hregm : IsSMulRegular (maximalIdeal A) x := fun a b hab =>
    Subtype.ext (hreg (congrArg Subtype.val hab))
  have := ih _ hlt (A ⧸ Ideal.span {x}) rfl
    ⟨n, pd_residue_quot hx hx2 n (pd_quot hreg n (ModuleCat.of A (maximalIdeal A)) hregm hK)⟩
  exact regular_of_quotient hreg hx

end SerreRegular

/- English proof (translation)
The claim follows from `SerreRegular.regular_of_pd _ A rfl ⟨n, h⟩`.
-/
theorem isRegularLocalRing_of_hasProjectiveDimensionLE_residueField (A : Type) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ maximalIdeal A)) n) :
    IsRegularLocalRing A :=
  SerreRegular.regular_of_pd _ A rfl ⟨n, h⟩

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_hasProjectiveDimensionLE_of_isRegularLocalRing R (R ⧸ q)`. Establish `h` using `SerreRegular.pd_flat (B := S) n (ModuleCat.of R (R ⧸ q)) hn`. Use `isRegularLocalRing_of_hasProjectiveDimensionLE_residueField S n ?_` and prove the remaining obligations. Rewrite using `[hq]`. Conclude with `hasProjectiveDimensionLT_of_iso (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S q).toLinearEquiv.toModuleIso.symm _`.
-/
theorem isRegularLocalRing_of_flat_of_map_eq_maximalIdeal (R S : Type) [CommRing R]
    [IsRegularLocalRing R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [Module.Flat R S] (q : Ideal R) (hq : maximalIdeal S = q.map (algebraMap R S)) :
    IsRegularLocalRing S := by
  obtain ⟨n, hn⟩ := exists_hasProjectiveDimensionLE_of_isRegularLocalRing R (R ⧸ q)
  have h := SerreRegular.pd_flat (B := S) n (ModuleCat.of R (R ⧸ q)) hn
  refine isRegularLocalRing_of_hasProjectiveDimensionLE_residueField S n ?_
  rw [hq]
  exact hasProjectiveDimensionLT_of_iso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S q).toLinearEquiv.toModuleIso.symm _

/- English proof (translation)
Rewrite using `[isRegularRing_iff]`. Introduce `p _`. Conclude with `isRegularLocalRing_of_flat_of_map_eq_maximalIdeal R _ p Localization.AtPrime.map_eq_maximalIdeal.symm`.
-/
theorem isRegularRing_of_isRegularLocalRing (R : Type) [CommRing R] [IsRegularLocalRing R] :
    IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p _
  exact isRegularLocalRing_of_flat_of_map_eq_maximalIdeal R _ p
    Localization.AtPrime.map_eq_maximalIdeal.symm

/- English proof (translation)
Introduce `R S _ _ _ _ q _ φ h`. Set `_ : Algebra R S` to `φ.toAlgebra`. Use `h.noeth` as an intermediate fact. Establish `: Module.Flat R S` using `h.flat`. Establish `hq : maximalIdeal S = q.map (algebraMap R S)` using `h.max_eq`.

Use `⟨isRegularLocalRing_of_flat_of_map_eq_maximalIdeal R S q hq, ?_⟩` and prove the remaining obligations. Establish `: (maximalIdeal S).LiesOver q` using `⟨h.comap_eq.symm⟩`. Establish `e` using `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q (maximalIdeal S)`. Establish `e0 : (Ideal.map (Ideal.Quotient.mk (q.map (algebraMap R S))) (maximalIdeal S)).height = 0`. Establish `hp : (q.map (algebraMap R S)).IsPrime` using `hq ▸ inferInstance`.

Rewrite using `[hq, Ideal.map_quotient_self, Ideal.height_bot]`. Rewrite `e` using `[e0, add_zero]`. Rewrite using `[← maximalIdeal_height_eq_ringKrullDim, e]`. Conclude with `(isCM_of_isRegularLocalRing R).height_add_ringKrullDim_quotient q`.
-/
theorem Pat.IsCplAt.isRegularLocalRing_and_ringKrullDim :
    ∀ (R S : Type) [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsLocalRing S] (q : Ideal R)
      [q.IsPrime] (φ : R →+* S), IsCplAt q φ →
      ∃ _ : IsRegularLocalRing S, ringKrullDim S + ringKrullDim (R ⧸ q) = ringKrullDim R := by
  intro R S _ _ _ _ q _ φ h
  let _ : Algebra R S := φ.toAlgebra
  have := h.noeth
  have : Module.Flat R S := h.flat
  have hq : maximalIdeal S = q.map (algebraMap R S) := h.max_eq
  refine ⟨isRegularLocalRing_of_flat_of_map_eq_maximalIdeal R S q hq, ?_⟩
  have : (maximalIdeal S).LiesOver q := ⟨h.comap_eq.symm⟩
  have e := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q (maximalIdeal S)
  have e0 : (Ideal.map (Ideal.Quotient.mk (q.map (algebraMap R S))) (maximalIdeal S)).height = 0 := by
    have hp : (q.map (algebraMap R S)).IsPrime := hq ▸ inferInstance
    rw [hq, Ideal.map_quotient_self, Ideal.height_bot]
  rw [e0, add_zero] at e
  rw [← maximalIdeal_height_eq_ringKrullDim, e]
  exact (isCM_of_isRegularLocalRing R).height_add_ringKrullDim_quotient q

end GlobalTheory
