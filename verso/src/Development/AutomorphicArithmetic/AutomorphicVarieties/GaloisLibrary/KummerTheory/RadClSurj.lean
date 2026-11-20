import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Proceed by induction on `hc using Subgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, rfl⟩` from `hx`. Use `⟨FractionalIdeal.mk0 K ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩, ClassGroup.mk_mk0 _ _, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[FractionalIdeal.coe_mk0]`.

Conclude with `FractionalIdeal.count_maximal_coprime K v (fun h : w = v => hv (h ▸ hw))`. Consider the case `one => exact ⟨1, map_one _, fun v _ => FractionalIdeal.count_one K v⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨I, rfl, hI⟩` from `hx`. Take `⟨J, rfl, hJ⟩` from `hy`.

Use `⟨I * J, map_mul _ _ _, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]`. Consider the case `inv x _ hx`. Take `⟨I, rfl, hI⟩` from `hx`. Use `⟨I⁻¹, map_inv _ _, fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI v hv, neg_zero]`.
-/
private theorem exists_frac_of_mem {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (c : ClassGroup (𝓞 K)) (hc : c ∈ clSub S) :
    ∃ J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K J = c ∧
      ∀ v ∉ S, FractionalIdeal.count K v J.1 = 0 := by
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨FractionalIdeal.mk0 K ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩,
      ClassGroup.mk_mk0 _ _, fun v hv => ?_⟩
    rw [FractionalIdeal.coe_mk0]
    exact FractionalIdeal.count_maximal_coprime K v (fun h : w = v => hv (h ▸ hw))
  | one => exact ⟨1, map_one _, fun v _ => FractionalIdeal.count_one K v⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, rfl, hI⟩ := hx
    obtain ⟨J, rfl, hJ⟩ := hy
    refine ⟨I * J, map_mul _ _ _, fun v hv => ?_⟩
    rw [Units.val_mul, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  | inv x _ hx =>
    obtain ⟨I, rfl, hI⟩ := hx
    refine ⟨I⁻¹, map_inv _ _, fun v hv => ?_⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI v hv, neg_zero]

/- English proof (translation)
Establish `hfm : ∀ f : HeightOneSpectrum (𝓞 K) → ℤ, {v | f v ≠ 0}.Finite → Function.HasFiniteMulSupport (fun v => primeCl v ^ f v)`. Introduce `f hf`. Unfold `Function.HasFiniteMulSupport`. Apply `hf.subset` to reduce the goal to its premises. Introduce `v hv`.

Simplify using `only [Set.mem_setOf_eq]`. Introduce `h0`. Conclude with `hv (by simp [h0])`. Establish `e1` using `(QuotientGroup.mk' (clSub S)).map_finprod (hfm f hf)`. Establish `e2` using `(QuotientGroup.mk' (clSub S)).map_finprod (hfm g hg)`.

Simplify using `only [QuotientGroup.mk'_apply] at e1 e2`. Rewrite using `[e1, e2]`. Apply `finprod_congr` to reduce the goal to its premises. Introduce `v`. Distinguish the cases in `hv : v ∈ S`.

Establish `h1 : (QuotientGroup.mk (primeCl v) : ClS S) = 1` using `(QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)`. Simplify using `[QuotientGroup.mk_zpow, h1]`. Rewrite using `[h v hv]`.
-/
private theorem mk_finprod_congr {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (f g : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite) (hg : {v | g v ≠ 0}.Finite)
    (h : ∀ v ∉ S, f v = g v) :
    (QuotientGroup.mk (∏ᶠ v, primeCl v ^ f v) : ClS S) = QuotientGroup.mk (∏ᶠ v, primeCl v ^ g v) := by
  have hfm : ∀ f : HeightOneSpectrum (𝓞 K) → ℤ, {v | f v ≠ 0}.Finite →
      Function.HasFiniteMulSupport (fun v => primeCl v ^ f v) := by
    intro f hf
    unfold Function.HasFiniteMulSupport
    apply hf.subset
    intro v hv
    simp only [Set.mem_setOf_eq]
    intro h0
    exact hv (by simp [h0])
  have e1 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm f hf)
  have e2 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm g hg)
  simp only [QuotientGroup.mk'_apply] at e1 e2
  rw [e1, e2]
  apply finprod_congr
  intro v
  by_cases hv : v ∈ S
  · have h1 : (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)
    simp [QuotientGroup.mk_zpow, h1]
  · rw [h v hv]

/- English proof (translation)
Introduce `K _ _ S n hn c hc`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective c`. Take `⟨I, rfl⟩ : ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = x` from `ClassGroup.induction K (fun I => ⟨I, rfl⟩) x`. Rewrite `hc` using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Take `⟨J, hJ, hJS⟩` from `exists_frac_of_mem S _ hc`.

Establish `hP : ClassGroup.mk K (I ^ n * J⁻¹) = 1`. Rewrite using `[map_mul, map_pow, map_inv, hJ, mul_inv_cancel]`. Rewrite `hP` using `[ClassGroup.mk_eq_one_iff]`. Take `⟨y, hy⟩` from `@Submodule.IsPrincipal.principal _ _ _ _ _ _ hP`. Establish `hx' : ((I ^ n * J⁻¹ : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = FractionalIdeal.spanSingleton _ y` using `FractionalIdeal.coeToSubmodule_injective (hy.trans (FractionalIdeal.coe_spanSingleton _ y).symm)`.

Establish `hy0 : y ≠ 0`. Introduce `h0`. Apply `Units.ne_zero (I ^ n * J⁻¹)` to reduce the goal to its premises. Rewrite using `[hx', h0, FractionalIdeal.spanSingleton_zero]`. Set `a : Kˣ` to `Units.mk0 y hy0`.

Establish `hcount : ∀ v ∉ S, ordv v a = n * FractionalIdeal.count K v (I : FractionalIdeal _ K)`. Introduce `v hv`. Rewrite using `[← (clProd K).2.1 v a]`. Use `show FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) = _`. Rewrite using `[← hx', Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _), Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hJS v hv, neg_zero, add_zero]`.

Establish `hn' : (n : ℤ) ≠ 0` using `by exact_mod_cast hn`. Use `⟨a, fun v hv => ⟨FractionalIdeal.count K v (I : FractionalIdeal _ K), hcount v hv⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[(clProd K).1 I]`. Unfold `radCl`. Apply `mk_finprod_congr S` to reduce the goal to its premises.

Apply `((clProd K).2.2.1 a).subset` to reduce the goal to its premises. Introduce `v hv h0`. Apply `hv` to reduce the goal to its premises. Simplify using `[h0]`. Establish `hf` using `FractionalIdeal.finite_factors (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)`.

Rewrite `hf` using `[Filter.eventually_cofinite]`. Conclude with `hf`. Introduce `v hv`. Rewrite using `[hcount v hv, Int.mul_ediv_cancel_left _ hn']`.
-/
theorem UpperTheory.V.Kum.radClSurj :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → ∀ c : ClS S, c ^ n = 1 → ∃ a ∈ SelK S n, QuotientGroup.mk (radCl n a) = c := by
  intro K _ _ S n hn c hc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨I, rfl⟩ : ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = x :=
    ClassGroup.induction K (fun I => ⟨I, rfl⟩) x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hc
  obtain ⟨J, hJ, hJS⟩ := exists_frac_of_mem S _ hc
  have hP : ClassGroup.mk K (I ^ n * J⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, hJ, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at hP
  obtain ⟨y, hy⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hP
  have hx' : ((I ^ n * J⁻¹ : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = FractionalIdeal.spanSingleton _ y :=
    FractionalIdeal.coeToSubmodule_injective (hy.trans (FractionalIdeal.coe_spanSingleton _ y).symm)
  have hy0 : y ≠ 0 := by
    intro h0
    apply Units.ne_zero (I ^ n * J⁻¹)
    rw [hx', h0, FractionalIdeal.spanSingleton_zero]
  let a : Kˣ := Units.mk0 y hy0
  have hcount : ∀ v ∉ S, ordv v a = n * FractionalIdeal.count K v (I : FractionalIdeal _ K) := by
    intro v hv
    rw [← (clProd K).2.1 v a]
    show FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) = _
    rw [← hx', Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_inv, hJS v hv, neg_zero, add_zero]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine ⟨a, fun v hv => ⟨FractionalIdeal.count K v (I : FractionalIdeal _ K), hcount v hv⟩, ?_⟩
  rw [(clProd K).1 I]
  unfold radCl
  apply mk_finprod_congr S
  · apply ((clProd K).2.2.1 a).subset
    intro v hv h0
    apply hv
    simp [h0]
  · have hf := FractionalIdeal.finite_factors (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [Filter.eventually_cofinite] at hf
    exact hf
  · intro v hv
    rw [hcount v hv, Int.mul_ediv_cancel_left _ hn']
