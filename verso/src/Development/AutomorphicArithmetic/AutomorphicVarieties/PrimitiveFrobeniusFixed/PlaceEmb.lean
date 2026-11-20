import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XMulConjIMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XNormDiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AlgStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationComapIsEquivOfLtOneIffMemPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.NormCyclotomicPrimeLayerEqNrmGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.RelNormCyclotomicPrimeEqPowDvdOrderOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationKummerElementEqOneOfNotOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ValuationKummerElementAtConjugatePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmissiblePrimeNotDvdOrderOfAndNotDvdLevel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Use `haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec N ℚ K`. Establish `e : f.toRatAlgHom = g.toRatAlgHom` using `AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `h _ hζ.pow_eq_one`.

Conclude with `RingHom.ext fun x => DFunLike.congr_fun e x`.
-/
private theorem hom_ext {K Ω : Type} [Field K] [CharZero K] [Field Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (f g : K →+* Ω) (h : ∀ x : K, x ^ N = 1 → f x = g x) : f = g := by
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have e : f.toRatAlgHom = g.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact h _ hζ.pow_eq_one
  exact RingHom.ext fun x => DFunLike.congr_fun e x

/- English proof (translation)
Use `DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) (ι.comp (sg N K b).toRingEquiv.toRingHom) fun y hy => ?_) x` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g (ι y) = ι (sg N K b y)`. Rewrite using `[hg _ (by rw [← map_pow, hy, map_one]), sg_apply N K b hy, map_pow]`.
-/
private theorem lift_sg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (b : (ZMod N)ˣ) (g : G ℚ Ω) (hg : Lifts N b g) (x : K) :
    g (ι x) = ι (sg N K b x) := by
  refine DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) (ι.comp (sg N K b).toRingEquiv.toRingHom)
    fun y hy => ?_) x
  change g (ι y) = ι (sg N K b y)
  rw [hg _ (by rw [← map_pow, hy, map_one]), sg_apply N K b hy, map_pow]

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) ι fun y hy => hg _ (by rw [← map_pow, hy, map_one])) x`.
-/
private theorem fix_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (g : G ℚ Ω) (hg : g ∈ fixMu ℚ Ω N) (x : K) :
    g (ι x) = ι x :=
  DFunLike.congr_fun (hom_ext N (g.toRingEquiv.toRingHom.comp ι) ι
    fun y hy => hg _ (by rw [← map_pow, hy, map_one])) x

/- English proof (translation)
Establish `h : Lifts N u g` using `fun y hy => by rw [hg y hy, hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hy]`. Apply `g.injective` to reduce the goal to its premises. Rewrite using `[lift_sg N ι u g h]`. Express the relevant statement in the definitionally equal form `g (g.symm _) = ι (sg N K u ((sg N K u).symm x))`. Rewrite using `[AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`.
-/
private theorem inv_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] (N q : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] (ι : K →+* Ω) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = q) (g : G ℚ Ω)
    (hg : Pows N q g) (x : K) : g⁻¹ (ι x) = ι ((sg N K u)⁻¹ x) := by
  have h : Lifts N u g := fun y hy => by rw [hg y hy, hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hy]
  apply g.injective
  rw [lift_sg N ι u g h]
  change g (g.symm _) = ι (sg N K u ((sg N K u).symm x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/- English proof (translation)
Use `letI : Algebra K Ω := ι.toAlgebra`. Use `haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq fun q => by simp`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`.

Conclude with `(UpperTheory.V.Kum.placeDict K Ω).2.1 A hA`.
-/
private theorem place_emb {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : K →+* Ω) (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
    ∃ w : HeightOneSpectrum (𝓞 K), ∀ y : 𝓞 K, A.valuation (ι (y : K)) < 1 ↔ y ∈ w.asIdeal := by
  letI : Algebra K Ω := ι.toAlgebra
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq fun q => by simp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact (UpperTheory.V.Kum.placeDict K Ω).2.1 A hA

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Introduce and unpack `rfl`. Establish `h1 : (⊤ : ValuationSubring Ω).valuation (n : Ω)⁻¹ ≤ 1` using `(ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)`. Establish `h2` using `mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1`. Rewrite `h2` using `[← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one]`.

Conclude with `lt_irrefl _ h2`.
-/
private theorem ne_top {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {n : ℕ} (hn : n ≠ 0)
    (h : Over A n) : A ≠ ⊤ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rintro rfl
  have h1 : (⊤ : ValuationSubring Ω).valuation (n : Ω)⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), map_one] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Establish `h (y : Ω) : (⊤ : ValuationSubring Ω).valuation y ≤ 1` using `(ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)`. Use `le_antisymm (h x) ?_` and prove the remaining obligations. Establish `h1` using `h x⁻¹`. Rewrite `h1` using `[map_inv₀]`. Conclude with `(inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h1`.
-/
private theorem val_top {Ω : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) : (⊤ : ValuationSubring Ω).valuation x = 1 := by
  have h (y : Ω) : (⊤ : ValuationSubring Ω).valuation y ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  refine le_antisymm (h x) ?_
  have h1 := h x⁻¹
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h1

/- English proof (translation)
Establish `hζ` using `IsCyclotomicExtension.zeta_spec M ℚ K`. Establish `hζ'` using `(IsCyclotomicExtension.zeta_spec N ℚ K').map_of_injective ι'.injective`. Establish `key : ∀ x : K, ι x ∈ ι'.fieldRange` using `fun x => by`. Establish `hx : x ∈ Algebra.adjoin ℚ {IsCyclotomicExtension.zeta M ℚ K}`. Rewrite using `[IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨c, rfl⟩` from `h`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one (ξ := ι x) (by rw [Set.mem_singleton_iff.1 hx, pow_mul, ← map_pow, hζ.pow_eq_one, map_one, one_pow])`.

Conclude with `⟨_, (map_pow ι' _ i).trans hi⟩`. Consider the case `algebraMap x => exact ⟨(x : K'), by simp⟩`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`.

Conclude with `mul_mem hx hy`. Use `choose j hj using key`. Conclude with `⟨{ toFun := j map_one' := ι'.injective (by rw [hj, map_one, map_one]) map_mul' := fun x y => ι'.injective (by rw [map_mul, hj, hj, hj, map_mul]) map_zero' := ι'.injective (by rw [hj, map_zero, map_zero]) map_add' := fun x y => ι'.injective (by rw [map_add, hj, hj, hj, map_add]) } …`.
-/
private theorem tower {K K' Ω : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field Ω] (M N : ℕ)
    [NeZero M] [NeZero N] [IsCyclotomicExtension {M} ℚ K] [IsCyclotomicExtension {N} ℚ K'] (h : M ∣ N)
    (ι : K →+* Ω) (ι' : K' →+* Ω) : ∃ j : K →+* K', ∀ x, ι' (j x) = ι x := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  have hζ' := (IsCyclotomicExtension.zeta_spec N ℚ K').map_of_injective ι'.injective
  have key : ∀ x : K, ι x ∈ ι'.fieldRange := fun x => by
    have hx : x ∈ Algebra.adjoin ℚ {IsCyclotomicExtension.zeta M ℚ K} := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := h
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := ι x)
        (by rw [Set.mem_singleton_iff.1 hx, pow_mul, ← map_pow, hζ.pow_eq_one, map_one, one_pow])
      exact ⟨_, (map_pow ι' _ i).trans hi⟩
    | algebraMap x => exact ⟨(x : K'), by simp⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  choose j hj using key
  exact ⟨{ toFun := j
           map_one' := ι'.injective (by rw [hj, map_one, map_one])
           map_mul' := fun x y => ι'.injective (by rw [map_mul, hj, hj, hj, map_mul])
           map_zero' := ι'.injective (by rw [hj, map_zero, map_zero])
           map_add' := fun x y => ι'.injective (by rw [map_add, hj, hj, hj, map_add]) }, hj⟩

private def XO {Ω : Type} [Field Ω] (N b : ℕ) (A₀ : ValuationSubring Ω) (x : Ω) : Prop :=
  ∃ (_ : NeZero N) (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCyclotomicExtension {N} ℚ K) (ι : K →+* Ω)
    (v : HeightOneSpectrum (𝓞 K)) (X : K), (∀ y : 𝓞 K, A₀.valuation (ι (y : K)) < 1 ↔ y ∈ v.asIdeal) ∧
    IsX N K b v.asIdeal X ∧ x = ι X

/- English proof (translation)
Use `haveI : NeZero N := ⟨by omega⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Set `K` to `CyclotomicField N ℚ`. Use `haveI : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra := by`. Establish `h` using `CyclotomicField.isCyclotomicExtension N ℚ`.

Establish `e : (DivisionRing.toRatAlgebra : Algebra ℚ K) = CyclotomicField.algebra N ℚ` using `Subsingleton.elim _ _`. Rewrite using `[e]`. Conclude with `h`. Set `ι : K →+* Ω` to `(IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom`. Take `⟨v, hv⟩` from `place_emb ι A₀ hA`.

Take `⟨X, hX⟩` from `xEx N K b v.asIdeal hb v.ne_bot`. Conclude with `⟨ι X, inferInstance, K, inferInstance, inferInstance, inferInstance, ι, v, X, hv, hX, rfl⟩`.
-/
private theorem xo_ex {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N b : ℕ) (hb : b < N)
    (A₀ : ValuationSubring Ω) (hA : A₀ ≠ ⊤) : ∃ x, XO N b A₀ x := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let K := CyclotomicField N ℚ
  haveI : @IsCyclotomicExtension {N} ℚ K _ _ DivisionRing.toRatAlgebra := by
    have h := CyclotomicField.isCyclotomicExtension N ℚ
    have e : (DivisionRing.toRatAlgebra : Algebra ℚ K) = CyclotomicField.algebra N ℚ := Subsingleton.elim _ _
    rw [e]
    exact h
  let ι : K →+* Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom
  obtain ⟨v, hv⟩ := place_emb ι A₀ hA
  obtain ⟨X, hX⟩ := xEx N K b v.asIdeal hb v.ne_bot
  exact ⟨ι X, inferInstance, K, inferInstance, inferInstance, inferInstance, ι, v, X, hv, hX, rfl⟩

/- English proof (translation)
Take `⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩` from `h`. Establish `h0 : ι X ≠ 0` using `(map_ne_zero ι).2 (left_ne_zero_of_mul_eq_one hX.1)`. Use `⟨h0, fun g hg => fix_emb N ι g hg X, fun A hA => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ht : A = ⊤`. Rewrite using `[ht]`.

Conclude with `val_top h0`. Take `⟨w, hw⟩` from `place_emb ι A ht`. Establish `h1` using `UpperTheory.valuation_kummerElement_eq_one_of_not_over N K b r v w X hX ((hv r).1 (by simpa using hr)) fun h => hA (by simpa using (hw r).2 h)`. Conclude with `(UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω ι A w hw).eq_one_iff_eq_one.2 h1`.
-/
private theorem xo_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {N b r : ℕ} {A₀ : ValuationSubring Ω}
    (hr : Over A₀ r) {x : Ω} (h : XO N b A₀ x) :
    x ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g x = x) ∧ ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  have h0 : ι X ≠ 0 := (map_ne_zero ι).2 (left_ne_zero_of_mul_eq_one hX.1)
  refine ⟨h0, fun g hg => fix_emb N ι g hg X, fun A hA => ?_⟩
  by_cases ht : A = ⊤
  · rw [ht]; exact val_top h0
  obtain ⟨w, hw⟩ := place_emb ι A ht
  have h1 := UpperTheory.valuation_kummerElement_eq_one_of_not_over N K b r v w X hX ((hv r).1 (by simpa using hr))
    fun h => hA (by simpa using (hw r).2 h)
  exact (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω ι A w hw).eq_one_iff_eq_one.2 h1

/- English proof (translation)
Take `⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩` from `h`. Introduce `t σ hσ`. Set `w : HeightOneSpectrum (𝓞 K)` to `v.comap (sgO F K t).toRingHom (sgO F K t).surjective`. Establish `hw : ∀ y : 𝓞 K, A₀.valuation ((σ.toRingEquiv.toRingHom.comp ι) (y : K)) < 1 ↔ y ∈ w.asIdeal` using `fun y => by`. Express the relevant statement in the definitionally equal form `A₀.valuation (σ (ι y)) < 1 ↔ sgO F K t y ∈ v.asIdeal`.

Rewrite using `[lift_sg F ι t σ hσ, ← hv]`. Both sides reduce to the same expression. Establish `h2` using `UpperTheory.valuation_kummerElement_at_conjugate_prime F K b r v w X t hp h1 hX ((hv r).1 (by simpa using hr)) rfl`. Rewrite `h2` using `[← map_zpow₀]`. Establish `h3` using `((UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω _ A₀ w hw).eq_iff).2 h2`.

Simplify using `using h3`.
-/
private theorem xo_ord {Ω : Type} [Field Ω] [Algebra ℚ Ω] {F b r : ℕ} (hp : r.Prime) (h1 : r ≡ 1 [MOD F])
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x : Ω} (h : XO F b A₀ x) : HasOrd F r A₀ x fun t => th F b t := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  intro t σ hσ
  let w : HeightOneSpectrum (𝓞 K) := v.comap (sgO F K t).toRingHom (sgO F K t).surjective
  have hw : ∀ y : 𝓞 K, A₀.valuation ((σ.toRingEquiv.toRingHom.comp ι) (y : K)) < 1 ↔ y ∈ w.asIdeal := fun y => by
    change A₀.valuation (σ (ι y)) < 1 ↔ sgO F K t y ∈ v.asIdeal
    rw [lift_sg F ι t σ hσ, ← hv]
    rfl
  have h2 := UpperTheory.valuation_kummerElement_at_conjugate_prime F K b r v w X t hp h1 hX ((hv r).1 (by simpa using hr)) rfl
  rw [← map_zpow₀] at h2
  have h3 := ((UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K Ω _ A₀ w hw).eq_iff).2 h2
  simpa using h3

/- English proof (translation)
Take `⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩` from `h`. Take `⟨_, K', _, _, _, ι', v', X', hv', hX', rfl⟩` from `h'`. Take `⟨j, hj⟩` from `tower M (q * M) (dvd_mul_left M q) ι ι'`. Use `letI : Algebra K K' := j.toAlgebra`. Establish `hj' : ∀ x, ι' (algebraMap K K' x) = ι x` using `hj`.

Take `⟨s, hs, hn⟩` from `UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf (q * M) r K K' hp hr' v v' ((hv' r).1 (by simpa using hr)) fun y => by`. Rewrite using `[← hv, ← hv', ← hj']`. Both sides reduce to the same expression. Establish `hXs` using `(xMul M K b).2.2.1 v.asIdeal X s v.ne_bot hX`. Rewrite `hXs` using `[← hn]`.

Establish `hu : ((ZMod.unitOfCoprime q hco : (ZMod M)ˣ) : ZMod M) = q` using `ZMod.coe_unitOfCoprime q hco`. Use `⟨s, hs, fun τ hτ hg φ hφ => ?_, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨ζ, hζ, he⟩` from `xNormDiv M q K K' hq _ hu b hbq v'.asIdeal X' (X ^ s) v'.ne_bot hX' hXs`. Use `⟨ι ζ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show 2 * (q * M) = 2 * M * q by ring, pow_mul, ← map_pow, hζ, map_one, one_pow]`.

Rewrite using `[UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator Ω M q K K' ι' hq hco τ hτ hg, hj', he, inv_emb M q ι _ hu φ hφ]`. Simplify using `only [map_mul, map_div₀, map_pow, div_pow]`. Establish `hqr : r.Coprime q` using `(Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hr' (h.mul_right M)`. Establish `hq' : (q : 𝓞 K') ∉ v'.asIdeal` using `fun h => (placeBasic Ω).2.2.2.1 A₀ r q hqr hr (by simpa using (hv' q).2 h)`. Establish `hc : IsCoprime v'.asIdeal (Ideal.span {(q : 𝓞 K')})`.

Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne`. Conclude with `hq' ((v'.isMaximal.eq_of_le hne le_sup_left).ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))`. Take `⟨ζ, hζ, he⟩` from `xCong M q K K' hq _ hu b hbM hbq v'.asIdeal X' (X ^ s) hc hX' hXs`. Use `⟨ι' ζ, by rw [← map_pow, hζ, map_one], fun A hA => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw⟩` from `place_emb ι' A (ne_top hq.ne_zero hA)`. Establish `h3` using `(UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K' Ω ι' A w hw).lt_one_iff_lt_one.2 (he w ((hw q).1 (by simpa using hA)))`. Rewrite `h3` using `[Valuation.comap_apply, map_sub, map_mul, hj', map_pow, map_pow, ← inv_emb M q ι _ hu φ hφ]`. Conclude with `h3`.
-/
private theorem xo_pair {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {M q b r : ℕ} (hp : r.Prime)
    (hq : q.Prime) (hco : q.Coprime M) (hr' : ¬ r ∣ q * M) (hbM : b < M) (hbq : b < q)
    {A₀ : ValuationSubring Ω} (hr : Over A₀ r) {x x' : Ω} (h : XO M b A₀ x) (h' : XO (q * M) b A₀ x') :
    ∃ s : ℕ, s ∣ orderOf (r : ZMod (q * M)) ∧
      (∀ τ ∈ fixMu ℚ Ω M, GenAt q τ → ∀ φ : G ℚ Ω, Pows M q φ →
        ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧ nrm q τ x' = ζ * (x / φ⁻¹ x) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows M q φ → ∃ ζ : Ω, ζ ^ (2 * (q * M)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (x' - ζ * φ⁻¹ x ^ s) < 1 := by
  obtain ⟨_, K, _, _, _, ι, v, X, hv, hX, rfl⟩ := h
  obtain ⟨_, K', _, _, _, ι', v', X', hv', hX', rfl⟩ := h'
  obtain ⟨j, hj⟩ := tower M (q * M) (dvd_mul_left M q) ι ι'
  letI : Algebra K K' := j.toAlgebra
  have hj' : ∀ x, ι' (algebraMap K K' x) = ι x := hj
  obtain ⟨s, hs, hn⟩ := UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf (q * M) r K K' hp hr' v v' ((hv' r).1 (by simpa using hr)) fun y => by
    rw [← hv, ← hv', ← hj']
    rfl
  have hXs := (xMul M K b).2.2.1 v.asIdeal X s v.ne_bot hX
  rw [← hn] at hXs
  have hu : ((ZMod.unitOfCoprime q hco : (ZMod M)ˣ) : ZMod M) = q := ZMod.coe_unitOfCoprime q hco
  refine ⟨s, hs, fun τ hτ hg φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨ζ, hζ, he⟩ := xNormDiv M q K K' hq _ hu b hbq v'.asIdeal X' (X ^ s) v'.ne_bot hX' hXs
    refine ⟨ι ζ, ?_, ?_⟩
    · rw [show 2 * (q * M) = 2 * M * q by ring, pow_mul, ← map_pow, hζ, map_one, one_pow]
    · rw [UpperTheory.norm_cyclotomic_prime_layer_eq_nrm_generator Ω M q K K' ι' hq hco τ hτ hg, hj', he, inv_emb M q ι _ hu φ hφ]
      simp only [map_mul, map_div₀, map_pow, div_pow]
  · have hqr : r.Coprime q := (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hr' (h.mul_right M)
    have hq' : (q : 𝓞 K') ∉ v'.asIdeal := fun h =>
      (placeBasic Ω).2.2.2.1 A₀ r q hqr hr (by simpa using (hv' q).2 h)
    have hc : IsCoprime v'.asIdeal (Ideal.span {(q : 𝓞 K')}) := by
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hq' ((v'.isMaximal.eq_of_le hne le_sup_left).ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    obtain ⟨ζ, hζ, he⟩ := xCong M q K K' hq _ hu b hbM hbq v'.asIdeal X' (X ^ s) hc hX' hXs
    refine ⟨ι' ζ, by rw [← map_pow, hζ, map_one], fun A hA => ?_⟩
    obtain ⟨w, hw⟩ := place_emb ι' A (ne_top hq.ne_zero hA)
    have h3 := (UpperTheory.valuation_comap_isEquiv_of_lt_one_iff_mem_prime K' Ω ι' A w hw).lt_one_iff_lt_one.2 (he w ((hw q).1 (by simpa using hA)))
    rw [Valuation.comap_apply, map_sub, map_mul, hj', map_pow, map_pow, ← inv_emb M q ι _ hu φ hφ] at h3
    exact h3

/- English proof (translation)
Introduce `Ω _ _ _ l F r b _ hl hr h1 hb A₀ hA`. Establish `hlt : ∀ d, d ≠ 0 → b < F * d` using `fun d hd => hb.trans_le (Nat.le_mul_of_pos_right F (Nat.pos_of_ne_zero hd))`. Establish `hX : ∀ d : ℕ, ∃ x : Ω, d ≠ 0 → XO (F * d) b A₀ x` using `fun d => by`. Distinguish the cases in `hd : d = 0`. Conclude with `⟨0, fun h => absurd hd h⟩`.

Take `⟨x, hx⟩` from `xo_ex (F * d) b (hlt d hd) A₀ (ne_top hr.ne_zero hA)`. Conclude with `⟨x, fun _ => hx⟩`. Use `choose X hX using hX`. Establish `hs : ∀ d q : ℕ, ∃ s : ℕ, q.Prime → ML.admitted l F r (q * d) → ¬ l ∣ s ∧ (∀ τ ∈ fixMu ℚ Ω (F * d), GenAt q τ → ∀ φ : G ℚ Ω, Pows (F * d) q φ → ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧ nrm q τ (X (q * d)) = ζ * (X d / φ⁻¹ (X d)) ^ s) ∧ ∀ φ : G ℚ Ω, Pows (F * d) q φ → ∃ ζ : Ω, ζ ^ (2 * …` using `fun d q => by`. Distinguish the cases in `h : q.Prime ∧ ML.admitted l F r (q * d)`.

Use `swap`. Conclude with `⟨0, fun a b => absurd ⟨a, b⟩ h⟩`. Take `⟨hq, ha⟩` from `h`. Establish `h0 : q * d ≠ 0` using `ha.1.ne_zero`. Establish `hd : d ≠ 0` using `right_ne_zero_of_mul h0`.

Establish `he : F * (q * d) = q * (F * d)` using `by ring`. Establish `hqF : q ≡ 1 [MOD F]` using `(ha.2 q hq (dvd_mul_right q d)).2.1`. Establish `hco : q.Coprime (F * d)` using `Nat.Coprime.mul_right (by rw [Nat.Coprime, hqF.gcd_eq]; exact Nat.gcd_one_left F) (Nat.coprime_of_squarefree_mul ha.1)`. Establish `hFq : F < q`. Establish `h2` using `Nat.le_of_dvd (by have := hq.two_le; omega) ((Nat.modEq_iff_dvd' hq.one_le).1 hqF.symm)`.

Use `hq.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨hc1, hc2⟩` from `UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level l F r (q * d) (NeZero.ne F) hl hr h1 ha`. Establish `hx'` using `hX (q * d) h0`. Rewrite `hc1`, `hc2`, `hx'` using `[he]`.

Take `⟨s, hs, h2, h3⟩` from `xo_pair hr hq hco hc2 (hlt d hd) (hb.trans hFq) hA (hX d hd) hx'`. Rewrite `h2`, `h3` using `[show 2 * (q * (F * d)) = 2 * F * (q * d) by ring]`. Conclude with `⟨s, fun _ _ => ⟨fun h => hc1 (h.trans hs), h2, h3⟩⟩`. Use `choose s hs using hs`. Use `⟨X, s, ⟨fun d hd => (xo_one hA (hX d hd.1.ne_zero)).1, fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.1, fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.2, fun d q hq ha => (hs d q hq ha).1, fun d q hq ha => (hs d q hq ha).2.1, fun d q hq ha => (hs d q hq ha).2.2⟩, ?_⟩` and prove the remaining obligations.

Establish `h` using `hX 1 one_ne_zero`. Rewrite `h` using `[mul_one]`. Conclude with `xo_ord hr h1 hA h`.
-/
theorem UpperTheory.V.ML.laxEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l F r b : ℕ) [NeZero F], l.Prime → r.Prime → r ≡ 1 [MOD F] → b < F → ∀ A₀ : ValuationSubring Ω, Over A₀ r →
    ∃ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s ∧ HasOrd F r A₀ (X 1) fun t => th F b t := by
  intro Ω _ _ _ l F r b _ hl hr h1 hb A₀ hA
  have hlt : ∀ d, d ≠ 0 → b < F * d := fun d hd => hb.trans_le (Nat.le_mul_of_pos_right F (Nat.pos_of_ne_zero hd))
  have hX : ∀ d : ℕ, ∃ x : Ω, d ≠ 0 → XO (F * d) b A₀ x := fun d => by
    by_cases hd : d = 0
    · exact ⟨0, fun h => absurd hd h⟩
    · obtain ⟨x, hx⟩ := xo_ex (F * d) b (hlt d hd) A₀ (ne_top hr.ne_zero hA)
      exact ⟨x, fun _ => hx⟩
  choose X hX using hX
  have hs : ∀ d q : ℕ, ∃ s : ℕ, q.Prime → ML.admitted l F r (q * d) → ¬ l ∣ s ∧
      (∀ τ ∈ fixMu ℚ Ω (F * d), GenAt q τ → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
        ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧ nrm q τ (X (q * d)) = ζ * (X d / φ⁻¹ (X d)) ^ s) ∧
      ∀ φ : G ℚ Ω, Pows (F * d) q φ → ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧
        ∀ A : ValuationSubring Ω, Over A q → A.valuation (X (q * d) - ζ * φ⁻¹ (X d) ^ s) < 1 := fun d q => by
    by_cases h : q.Prime ∧ ML.admitted l F r (q * d)
    swap
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ h⟩
    obtain ⟨hq, ha⟩ := h
    have h0 : q * d ≠ 0 := ha.1.ne_zero
    have hd : d ≠ 0 := right_ne_zero_of_mul h0
    have he : F * (q * d) = q * (F * d) := by ring
    have hqF : q ≡ 1 [MOD F] := (ha.2 q hq (dvd_mul_right q d)).2.1
    have hco : q.Coprime (F * d) := Nat.Coprime.mul_right
      (by rw [Nat.Coprime, hqF.gcd_eq]; exact Nat.gcd_one_left F) (Nat.coprime_of_squarefree_mul ha.1)
    have hFq : F < q := by
      have h2 := Nat.le_of_dvd (by have := hq.two_le; omega) ((Nat.modEq_iff_dvd' hq.one_le).1 hqF.symm)
      have := hq.two_le
      omega
    obtain ⟨hc1, hc2⟩ := UpperTheory.admissible_prime_not_dvd_orderOf_and_not_dvd_level l F r (q * d) (NeZero.ne F) hl hr h1 ha
    have hx' := hX (q * d) h0
    rw [he] at hc1 hc2 hx'
    obtain ⟨s, hs, h2, h3⟩ := xo_pair hr hq hco hc2 (hlt d hd) (hb.trans hFq) hA (hX d hd) hx'
    rw [show 2 * (q * (F * d)) = 2 * F * (q * d) by ring] at h2 h3
    exact ⟨s, fun _ _ => ⟨fun h => hc1 (h.trans hs), h2, h3⟩⟩
  choose s hs using hs
  refine ⟨X, s, ⟨fun d hd => (xo_one hA (hX d hd.1.ne_zero)).1, fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.1,
    fun d hd => (xo_one hA (hX d hd.1.ne_zero)).2.2, fun d q hq ha => (hs d q hq ha).1,
    fun d q hq ha => (hs d q hq ha).2.1, fun d q hq ha => (hs d q hq ha).2.2⟩, ?_⟩
  have h := hX 1 one_ne_zero
  rw [mul_one] at h
  exact xo_ord hr h1 hA h
