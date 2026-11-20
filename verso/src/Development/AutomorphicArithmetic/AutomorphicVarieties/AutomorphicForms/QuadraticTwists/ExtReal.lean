import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap)

/- English proof (translation)
Establish `hker : p.rangeRestrict.ker ≤ f.ker`. Introduce `c hc`. Rewrite `hc` using `[MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.mem_ker]`. Conclude with `h c hc`.

Set `ω' : p.range →* ℂˣ` to `p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩`. Establish `hω' : ∀ c, ω' (p.rangeRestrict c) = f c` using `fun c => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c`. Take `⟨F, hF⟩` from `KStar.Choice.isDiv_complex_circle.1.exists_extension p.range ω'`. Use `⟨F, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[← hω', ← hF]`.

Both sides reduce to the same expression.
-/
private theorem glue {G H : Type*} [CommGroup G] [CommGroup H] (p : G →* H)
    (f : G →* ℂˣ) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* ℂˣ, ∀ x, F (p x) = f x := by
  have hker : p.rangeRestrict.ker ≤ f.ker := by
    intro c hc
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hc
    rw [MonoidHom.mem_ker]
    exact h c hc
  let ω' : p.range →* ℂˣ :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩
  have hω' : ∀ c, ω' (p.rangeRestrict c) = f c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  obtain ⟨F, hF⟩ := KStar.Choice.isDiv_complex_circle.1.exists_extension p.range ω'
  refine ⟨F, fun c => ?_⟩
  rw [← hω', ← hF]
  rfl

private def lev (K : Type) [Field K] [NumberField K] (N : ℕ) : Subgroup (Ideles K) where
  carrier := {a | a ∈ GlobalTheory.Mem.Chr.unitIdl K ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤ Valued.v (N : v.adicCompletion K)}
  one_mem' := ⟨one_mem _, fun v => by
    show Valued.v ((1 : v.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v => by
    show Valued.v ((a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1) ≤ _
    have e : (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v - 1 =
        (a : AdeleRing (𝓞 K) K).2 v * ((b : AdeleRing (𝓞 K) K).2 v - 1) + ((a : AdeleRing (𝓞 K) K).2 v - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ (ha.2 v)
    rw [map_mul, ha.1 v, one_mul]
    exact hb.2 v⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v => by
    have h : (a : AdeleRing (𝓞 K) K).2 v * ((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
    have e : (a : AdeleRing (𝓞 K) K).2 v * (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v - 1) =
        -((a : AdeleRing (𝓞 K) K).2 v - 1) := by linear_combination h
    have h2 := congrArg (Valued.v : Valuation (v.adicCompletion K) _) e
    rw [map_mul, ha.1 v, one_mul, Valuation.map_neg] at h2
    rw [h2]
    exact ha.2 v⟩

/- English proof (translation)
Establish `hO : IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v, a v ∈ v.adicCompletionIntegers K}` using `RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) fun _ => Valued.isOpen_valuationSubring _`. Establish `h1 : Continuous fun x : Ideles K => x.val.2` using `continuous_snd.comp Units.continuous_val`. Establish `h2 : Continuous fun x : Ideles K => (x⁻¹).val.2` using `h1.comp continuous_inv`. Establish `h3 : Continuous fun x : Ideles K => (x.val.2 - 1) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (N : K)⁻¹` using `(h1.sub continuous_const).mul continuous_const`. Establish `hU` using `((hO.preimage h1).inter (hO.preimage h2)).inter (hO.preimage h3)`.

Use `Filter.mem_of_superset (hU.mem_nhds ⟨⟨fun v => one_mem _, fun v => one_mem _⟩, fun v => ?_⟩) ?_` and prove the remaining obligations. Establish `: ((1 : Ideles K).val.2 - 1) = 0` using `sub_self _`. Simplify using `only [this, zero_mul]`. Conclude with `zero_mem _`. Introduce and unpack `y ⟨⟨hy, hy'⟩, hy''⟩`.

Use `⟨fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `e : y.val.2 v * (y⁻¹).val.2 v = 1` using `congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) y.mul_inv`. Establish `e'` using `congrArg Valued.v e`. Rewrite `e'` using `[map_mul, map_one]`. Conclude with `eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge`.

Establish `e : Valued.v ((y.val.2 v - 1) * algebraMap K (v.adicCompletion K) (N : K)⁻¹) ≤ 1` using `hy'' v haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective`. Establish `h0 : Valued.v (N : v.adicCompletion K) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `Nat.cast_ne_zero.2 hN`. Rewrite `e` using `[map_inv₀, map_natCast, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul]`.

Conclude with `e`.
-/
private theorem lev_mem_nhds (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) :
    (lev K N : Set (Ideles K)) ∈ nhds (1 : Ideles K) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v, a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun x : Ideles K => x.val.2 := continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun x : Ideles K => (x⁻¹).val.2 := h1.comp continuous_inv
  have h3 : Continuous fun x : Ideles K =>
      (x.val.2 - 1) * algebraMap K (FiniteAdeleRing (𝓞 K) K) (N : K)⁻¹ :=
    (h1.sub continuous_const).mul continuous_const
  have hU := ((hO.preimage h1).inter (hO.preimage h2)).inter (hO.preimage h3)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨⟨fun v => one_mem _, fun v => one_mem _⟩, fun v => ?_⟩) ?_
  · have : ((1 : Ideles K).val.2 - 1) = 0 := sub_self _
    simp only [this, zero_mul]
    exact zero_mem _
  · rintro y ⟨⟨hy, hy'⟩, hy''⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have e : y.val.2 v * (y⁻¹).val.2 v = 1 :=
        congrArg (fun a : AdeleRing (𝓞 K) K => a.2 v) y.mul_inv
      have e' := congrArg Valued.v e
      rw [map_mul, map_one] at e'
      exact eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge
    · have e : Valued.v ((y.val.2 v - 1) * algebraMap K (v.adicCompletion K) (N : K)⁻¹) ≤ 1 := hy'' v
      haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
      have h0 : Valued.v (N : v.adicCompletion K) ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        exact Nat.cast_ne_zero.2 hN
      rw [map_inv₀, map_natCast, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul] at e
      exact e

/- English proof (translation)
Establish `he : ∀ w : HeightOneSpectrum (𝓞 L), (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0` using `fun w => Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot`. Establish `hc : ∀ w : HeightOneSpectrum (𝓞 L), (ideleMap K L y).val.2 w = finiteCompletionMap K L w (y.val.2 (w.under (𝓞 K)))` using `fun w => rfl`. Establish `h1 : ∀ w : HeightOneSpectrum (𝓞 L), Valued.v ((ideleMap K L y).val.2 w) = 1 ↔ Valued.v (y.val.2 (w.under (𝓞 K))) = 1` using `fun w => by`. Rewrite using `[hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)]`. Establish `h2 : ∀ w : HeightOneSpectrum (𝓞 L), Valued.v ((ideleMap K L y).val.2 w - 1) ≤ Valued.v (N : w.adicCompletion L) ↔ Valued.v (y.val.2 (w.under (𝓞 K)) - 1) ≤ Valued.v (N : (w.under (𝓞 K)).adicCompletion K)` using `fun w => by`.

Rewrite using `[hc, ← map_one (finiteCompletionMap K L w), ← map_sub, ← map_natCast (finiteCompletionMap K L w), GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_le_pow_iff_left₀ zero_le zero_le (he w)]`. Establish `hs : ∀ v : HeightOneSpectrum (𝓞 K), ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v` using `fun v => by haveI := v.isPrime`. Take `⟨⟨P, hP, hP'⟩⟩` from `(inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))`. Conclude with `⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, b⟩`. Use `⟨fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `hs v`. Conclude with `(h1 w).1 (a w)`. Take `⟨w, rfl⟩` from `hs v`.

Conclude with `(h2 w).1 (b w)`. Introduce and unpack `⟨a, b⟩`. Conclude with `⟨fun w => (h1 w).2 (a _), fun w => (h2 w).2 (b _)⟩`.
-/
private theorem ideleMap_mem_lev (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (N : ℕ) (y : Ideles K) : ideleMap K L y ∈ lev L N ↔ y ∈ lev K N := by
  have he : ∀ w : HeightOneSpectrum (𝓞 L), (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 L), (ideleMap K L y).val.2 w =
      finiteCompletionMap K L w (y.val.2 (w.under (𝓞 K))) := fun w => rfl
  have h1 : ∀ w : HeightOneSpectrum (𝓞 L), Valued.v ((ideleMap K L y).val.2 w) = 1 ↔
      Valued.v (y.val.2 (w.under (𝓞 K))) = 1 := fun w => by
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)]
  have h2 : ∀ w : HeightOneSpectrum (𝓞 L),
      Valued.v ((ideleMap K L y).val.2 w - 1) ≤ Valued.v (N : w.adicCompletion L) ↔
      Valued.v (y.val.2 (w.under (𝓞 K)) - 1) ≤ Valued.v (N : (w.under (𝓞 K)).adicCompletion K) := fun w => by
    rw [hc, ← map_one (finiteCompletionMap K L w), ← map_sub, ← map_natCast (finiteCompletionMap K L w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)]
  have hs : ∀ v : HeightOneSpectrum (𝓞 K), ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩
  constructor
  · rintro ⟨a, b⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · obtain ⟨w, rfl⟩ := hs v
      exact (h1 w).1 (a w)
    · obtain ⟨w, rfl⟩ := hs v
      exact (h2 w).1 (b w)
  · rintro ⟨a, b⟩
    exact ⟨fun w => (h1 w).2 (a _), fun w => (h2 w).2 (b _)⟩

/- English proof (translation)
Establish `hN0 : (N : K) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Assume the negation of the conclusion as `hne`. Establish `hb0 : ((ε : K) - 1) / N ≠ 0` using `div_ne_zero (sub_ne_zero.2 fun h => hne (Units.ext h)) hN0`. Establish `hint : IsIntegral ℤ (((ε : K) - 1) / N)`. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K (((ε : K) - 1) / N) fun v => by`.

Establish `e : Valued.v (algebraMap K (v.adicCompletion K) ε - 1) ≤ Valued.v (N : v.adicCompletion K)` using `h.2 v`. Rewrite `e` using `[← map_one (algebraMap K (v.adicCompletion K)), ← map_sub, ← map_natCast (algebraMap K (v.adicCompletion K)), GlobalTheory.UpIdeleMod.valued_algebraMap, GlobalTheory.UpIdeleMod.valued_algebraMap]`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ e zero_le`. Rewrite using `[← hr]`.

Conclude with `r.isIntegral_coe`. Establish `hlt : ∀ φ : K →+* ℂ, ‖φ (((ε : K) - 1) / N)‖ < 1` using `fun φ => by`. Establish `h3 : (3 : ℝ) ≤ N` using `by exact_mod_cast hN`. Rewrite using `[map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast, div_lt_one (by linarith)]`. Use `norm_sub_le (φ ε) 1` as an intermediate fact.

Rewrite `this` using `[hε, norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, hn, hp⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hb0 hint fun φ => (hlt φ).le`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Conclude with `(hlt φ).ne (Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hp, map_one]) hn.ne')`.
-/
private theorem eq_one_of_mem_lev (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : 3 ≤ N) (ε : Kˣ)
    (h : diagUnits K ε ∈ lev K N) (hε : ∀ φ : K →+* ℂ, ‖φ ε‖ = 1) : ε = 1 := by
  have hN0 : (N : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  by_contra hne
  have hb0 : ((ε : K) - 1) / N ≠ 0 := div_ne_zero (sub_ne_zero.2 fun h => hne (Units.ext h)) hN0
  have hint : IsIntegral ℤ (((ε : K) - 1) / N) := by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K (((ε : K) - 1) / N) fun v => by
      have e : Valued.v (algebraMap K (v.adicCompletion K) ε - 1) ≤ Valued.v (N : v.adicCompletion K) := h.2 v
      rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub, ← map_natCast (algebraMap K (v.adicCompletion K)),
        GlobalTheory.UpIdeleMod.valued_algebraMap, GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      rw [map_div₀]
      exact div_le_one_of_le₀ e zero_le
    rw [← hr]
    exact r.isIntegral_coe
  have hlt : ∀ φ : K →+* ℂ, ‖φ (((ε : K) - 1) / N)‖ < 1 := fun φ => by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast, div_lt_one (by linarith)]
    have := norm_sub_le (φ ε) 1
    rw [hε, norm_one] at this
    linarith
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hb0 hint fun φ => (hlt φ).le
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact (hlt φ).ne (Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hp, map_one]) hn.ne')

private noncomputable def crd (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) : Ideles K →* ℂˣ :=
  Units.map ((InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))).toMonoidHom

private noncomputable def kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Ideles K →* ℂˣ :=
  ∏ w : InfinitePlace K, crd K w ^ a

/- English proof (translation)
Rewrite using `[kap, MonoidHom.finsetProd_apply, Units.coe_prod]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression.
-/
private theorem coe_kap (K : Type) [Field K] [NumberField K] (a : ℤ) (x : Ideles K) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, InfinitePlace.Completion.extensionEmbedding w (x.val.1 w) ^ a := by
  rw [kap, MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [MonoidHom.zpow_apply, Units.val_zpow_eq_zpow_val]
  rfl

/- English proof (translation)
Establish `e : (kap K a : Ideles K → ℂˣ) = fun x => ∏ w : InfinitePlace K, (crd K w x) ^ a`. Use function extensionality and compare the values at `x`. Rewrite using `[kap, MonoidHom.finsetProd_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `continuous_finsetProd _ fun w _ => Continuous.zpow (f := crd K w) (Continuous.units_map _ ?_) a` and prove the remaining obligations. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst)`.
-/
private theorem continuous_kap (K : Type) [Field K] [NumberField K] (a : ℤ) : Continuous (kap K a) := by
  have e : (kap K a : Ideles K → ℂˣ) = fun x => ∏ w : InfinitePlace K, (crd K w x) ^ a := by
    funext x
    rw [kap, MonoidHom.finsetProd_apply]
    rfl
  rw [e]
  refine continuous_finsetProd _ fun w _ => Continuous.zpow (f := crd K w) (Continuous.units_map _ ?_) a
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

/- English proof (translation)
Rewrite using `[infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]`. Set `p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E` to `RingHom.fst _ _`. Set `p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E` to `RingHom.snd _ _`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p1 _ = _`.

Rewrite using `[map_prod]`. Express the relevant statement in the definitionally equal form `∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _`. Conclude with `Finset.univ_prod_mulSingle _`. Express the relevant statement in the definitionally equal form `p2 _ = _`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_eq_one fun _ _ => rfl`.
-/
private theorem coe_infDiag' {E : Type} [Field E] [NumberField E] (k : Eˣ) :
    (infDiag k : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
  classical
  rw [infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
  let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
  refine Prod.ext ?_ ?_
  · change p1 _ = _
    rw [map_prod]
    change ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E)) = _
    exact Finset.univ_prod_mulSingle _
  · change p2 _ = _
    rw [map_prod]
    exact Finset.prod_eq_one fun _ _ => rfl

/- English proof (translation)
Rewrite using `[coe_kap, h]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ k)`.
-/
private theorem kap_of_fst {K : Type} [Field K] [NumberField K] (a : ℤ) (x : Ideles K) (k : K)
    (h : x.val.1 = algebraMap K (InfiniteAdeleRing K) k) :
    (kap K a x : ℂ) = ∏ w : InfinitePlace K, w.embedding k ^ a := by
  rw [coe_kap, h]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ k)

/- English proof (translation)
Establish `hg : Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing F)ˣ → InfiniteAdeleRing F)` using `Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace F, v.Completion)`. Rewrite using `[DenseRange, dense_iff_inter_open]`. Introduce and unpack `U hU ⟨u, hu⟩`. Take `⟨k, v, hv, hk⟩` from `(InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hk` using `[map_zero]`. Conclude with `v.ne_zero hk`. Conclude with `⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩`.
-/
private theorem dense_inf (F : Type) [Field F] [NumberField F] :
    DenseRange (Units.map (algebraMap F (InfiniteAdeleRing F)).toMonoidHom) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing F)ˣ → InfiniteAdeleRing F) :=
    Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace F, v.Completion)
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ :=
    (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact v.ne_zero hk
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `w w' h`. Apply `(IsCMField.equivInfinitePlace E).injective` to reduce the goal to its premises. Rewrite using `[IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply, ← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk, InfinitePlace.comap_mk]`. Conclude with `congrArg _ h`.

Introduce `φ`. Use `⟨InfinitePlace.mk (ComplexEmbedding.lift E φ), ?_⟩` and prove the remaining obligations. Break down `InfinitePlace.embedding_mk_eq (ComplexEmbedding.lift E φ) with h | h` into its components or cases. Simplify using `only [h, ComplexEmbedding.lift_comp_algebraMap]`. Simplify using `only [h]`.

Rewrite using `[ComplexEmbedding.conjugate_comp, ComplexEmbedding.lift_comp_algebraMap]`. Conclude with `ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal φ)`.
-/
private theorem bij_emb (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Function.Bijective fun w : InfinitePlace E => w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  constructor
  · intro w w' h
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply, ← InfinitePlace.mk_embedding w,
      ← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk, InfinitePlace.comap_mk]
    exact congrArg _ h
  · intro φ
    refine ⟨InfinitePlace.mk (ComplexEmbedding.lift E φ), ?_⟩
    rcases InfinitePlace.embedding_mk_eq (ComplexEmbedding.lift E φ) with h | h
    · simp only [h, ComplexEmbedding.lift_comp_algebraMap]
    · simp only [h]
      rw [ComplexEmbedding.conjugate_comp, ComplexEmbedding.lift_comp_algebraMap]
      exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal φ)

/- English proof (translation)
Establish `c2 : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing (maximalRealSubfield E)) (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))))` using `Continuous.units_map _ (continuous_id.prodMk continuous_const)`. Use `(dense_inf _).induction_on z (isClosed_eq (ψ.2.1.comp c2) ((continuous_kap E a).comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E).comp c2))) fun k => ?_` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[kap_of_fst a _ (algebraMap _ E (k : maximalRealSubfield E)) (congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap _ E (k : maximalRealSubfield E)))]`. Use `Eq.trans ?_ ((hψ k).trans ?_)` and prove the remaining obligations.

Conclude with `congrArg (fun x => ((ψ.1 x : ℂˣ) : ℂ)) (Units.ext (coe_infDiag' k).symm)`. Conclude with `((bij_emb E).prod_comp fun φ => φ (k : maximalRealSubfield E) ^ a).symm`.
-/
private theorem psi_eq_kap (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E))
    (a : ℤ) (hψ : ψ.IsAlg fun _ => a) (z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ) :
    ψ.1 (Units.map (MonoidHom.inl _ _) z) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
  have c2 : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing (maximalRealSubfield E))
      (FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)))) :=
    Continuous.units_map _ (continuous_id.prodMk continuous_const)
  refine (dense_inf _).induction_on z (isClosed_eq (ψ.2.1.comp c2)
    ((continuous_kap E a).comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E).comp c2))) fun k => ?_
  apply Units.ext
  rw [kap_of_fst a _ (algebraMap _ E (k : maximalRealSubfield E))
    (congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap _ E (k : maximalRealSubfield E)))]
  refine Eq.trans ?_ ((hψ k).trans ?_)
  · exact congrArg (fun x => ((ψ.1 x : ℂˣ) : ℂ)) (Units.ext (coe_infDiag' k).symm)
  · exact ((bij_emb E).prod_comp fun φ => φ (k : maximalRealSubfield E) ^ a).symm

open Classical in
/- English proof (translation)
Rewrite using `[← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single_of_mem w.embedding (by simp)]`. Rewrite using `[InfinitePlace.mk_embedding, if_pos rfl]`. Introduce `φ hφ hne`.

Rewrite using `[(Finset.mem_filter.1 hφ).2, if_neg hne.symm, zpow_zero]`.
-/
private theorem prod_type (E : Type) [Field E] [NumberField E] (a : ℤ) (k : E) :
    ∏ w : InfinitePlace E, w.embedding k ^ a =
      ∏ φ : E →+* ℂ, φ k ^ (if (InfinitePlace.mk φ).embedding = φ then a else 0) := by
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Finset.prod_eq_single_of_mem w.embedding (by simp)]
  · rw [InfinitePlace.mk_embedding, if_pos rfl]
  · intro φ hφ hne
    rw [(Finset.mem_filter.1 hφ).2, if_neg hne.symm, zpow_zero]

end SlopeTestRemainingChoices

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj) in
/- English proof (translation)
Introduce `E _ _ _ ψ a hψ`. Take `⟨M, hM, hlev⟩` from `GlobalTheory.Mem.HeckeLevel.exists_level_nat _ ψ`. Establish `hF : ∀ b ∈ lev (maximalRealSubfield E) (3 * M), ψ.1 b = kap E a (ideleMap _ E b)`. Introduce `b hb`. Set `z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ` to `Units.map (MonoidHom.fst _ _) b`.

Establish `e : b = Units.map (MonoidHom.inl _ _) z * GlobalTheory.Mem.Chr.finPartI _ b` using `Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)`. Establish `h1 : ψ.1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1`. Use `hlev _ hb.1 (fun _ => rfl) fun P => (hb.2 P).trans ?_` and prove the remaining obligations. Establish `e2 : (((M : maximalRealSubfield E)) : P.adicCompletion (maximalRealSubfield E)) = (M : P.adicCompletion (maximalRealSubfield E))` using `map_natCast (algebraMap (maximalRealSubfield E) (P.adicCompletion (maximalRealSubfield E))) M`. Rewrite using `[e2, Nat.cast_mul, map_mul]`.

Conclude with `mul_le_of_le_one_left' (natCast_mem (P.adicCompletionIntegers (maximalRealSubfield E)) 3)`. Establish `h2 : kap E a (ideleMap _ E b) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z))`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_kap, coe_kap]`. Both sides reduce to the same expression.

Rewrite using `[h2, ← psi_eq_kap E ψ a hψ z]`. Use `conv_lhs => rw [e, map_mul, h1, mul_one]`. Take `⟨ξ, hξ⟩` from `glue (((ideleMap (maximalRealSubfield E) E).coprod (lev E (3 * M)).subtype).coprod (diagUnits E)) ((MonoidHom.coprod ψ.1 ((kap E a).comp (lev E (3 * M)).subtype)).coprod 1) (by`. Introduce and unpack `⟨⟨b, u, hu⟩, k⟩ h`. Express the relevant statement in the definitionally equal form `ideleMap (maximalRealSubfield E) E b * u * diagUnits E k = 1 at h`.

Express the relevant statement in the definitionally equal form `ψ.1 b * kap E a u * 1 = 1`. Set `c` to `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E`. Establish `h'` using `congrArg (ideleConj (maximalRealSubfield E) E) h`. Establish `c1 : ideleConj (maximalRealSubfield E) E (ideleMap _ E b) = ideleMap _ E b` using `Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _)`. Establish `c2 : ideleConj (maximalRealSubfield E) E (diagUnits E k) = diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k)` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele _ E k`.

Establish `c3 : ideleConj (maximalRealSubfield E) E u ∈ lev E (3 * M)` using `(@ideleMap_mem_lev E E _ _ _ _ c.toRingEquiv.toRingHom.toAlgebra _ u).2 hu`. Rewrite `h'` using `[map_mul, map_mul, map_one, c1, c2, ← h, mul_assoc, mul_assoc, mul_right_inj]`. Establish `h3 : diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k / k) = u / ideleConj (maximalRealSubfield E) E u`. Rewrite using `[_root_.map_div, div_eq_div_iff_mul_eq_mul, mul_comm, h']`. Establish `h4` using `eq_one_of_mem_lev E (N := 3 * M) (by omega) _ (h3 ▸ div_mem hu c3) fun φ => by`.

Rewrite using `[Units.val_div_eq_div_val, map_div₀, norm_div]`. Establish `: φ (Units.map c.toRingEquiv.toRingHom.toMonoidHom k : Eˣ) = starRingEnd ℂ (φ k)` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k`. Rewrite using `[this, Complex.norm_conj, div_self (by simp)]`. Establish `h5 : IsCMField.complexConj E k = k` using `congrArg Units.val (div_eq_one.1 h4)`. Establish `h6 : (k : E) ∈ maximalRealSubfield E` using `(IsCMField.complexConj_eq_self_iff E (k : E)).1 h5`.

Set `k0 : (maximalRealSubfield E)ˣ` to `Units.mk0 ⟨k, h6⟩ fun h0 => k.ne_zero (congrArg Subtype.val h0)`. Establish `h7 : ideleMap _ E (diagUnits _ k0) = diagUnits E k` using `(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k0).trans (congrArg (diagUnits E) (Units.ext rfl))`. Establish `h8 : ideleMap _ E (b * diagUnits _ k0) = u⁻¹`. Rewrite using `[map_mul, h7, eq_inv_iff_mul_eq_one, mul_right_comm, h]`. Establish `h9` using `hF _ ((ideleMap_mem_lev _ E _ _).1 (h8 ▸ inv_mem hu))`.

Rewrite `h9` using `[h8, map_mul, ψ.2.2, mul_one, map_inv]`. Rewrite using `[h9, inv_mul_cancel, one_mul])`. Establish `hu : ∀ u ∈ lev E (3 * M), ξ u = kap E a u` using `fun u hu => by`. Simplify using `using hξ ((1, ⟨u, hu⟩), 1)`. Use `⟨⟨ξ, ?_, fun k => by simpa using hξ ((1, 1), k)⟩, fun φ => if (InfinitePlace.mk φ).embedding = φ then a else 0, fun k => ?_, Subtype.ext (MonoidHom.ext fun b => ?_)⟩` and prove the remaining obligations.

Use `continuous_of_continuousAt_one ξ ((continuous_kap E a).continuousAt.congr ?_) filter_upwards [lev_mem_nhds E (N := 3 * M) (by omega)] with x hx` and prove the remaining obligations. Conclude with `(hu x hx).symm`. Establish `h1 : infDiag k ∈ lev E (3 * M)`. Use `⟨fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_infDiag']`.

Conclude with `map_one _`. Rewrite using `[coe_infDiag'] show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _`. Rewrite using `[sub_self, map_zero]`. Conclude with `zero_le`. Express the relevant statement in the definitionally equal form `((ξ (infDiag k) : ℂˣ) : ℂ) = _`.

Rewrite using `[hu _ h1, kap_of_fst a _ (k : E) (by rw [coe_infDiag']), prod_type]`. Express the relevant statement in the definitionally equal form `ξ (ideleMap _ E b) = ψ.1 b`. Simplify using `using hξ ((b, 1), 1)`.
-/
theorem UpperTheory.V.Af.Cq.extReal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (a : ℤ), ψ.IsAlg (fun _ => a) →
        ∃ (ξ : HChar E) (m : (E →+* ℂ) → ℤ), ξ.IsAlg m ∧ GlobalTheory.HeightCounting.Blocks.resReal ξ = ψ := by
  intro E _ _ _ ψ a hψ
  classical
  obtain ⟨M, hM, hlev⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat _ ψ
  have hF : ∀ b ∈ lev (maximalRealSubfield E) (3 * M), ψ.1 b = kap E a (ideleMap _ E b) := by
    intro b hb
    let z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ := Units.map (MonoidHom.fst _ _) b
    have e : b = Units.map (MonoidHom.inl _ _) z * GlobalTheory.Mem.Chr.finPartI _ b :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h1 : ψ.1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 := by
      refine hlev _ hb.1 (fun _ => rfl) fun P => (hb.2 P).trans ?_
      have e2 : (((M : maximalRealSubfield E)) : P.adicCompletion (maximalRealSubfield E)) =
          (M : P.adicCompletion (maximalRealSubfield E)) :=
        map_natCast (algebraMap (maximalRealSubfield E) (P.adicCompletion (maximalRealSubfield E))) M
      rw [e2, Nat.cast_mul, map_mul]
      exact mul_le_of_le_one_left' (natCast_mem (P.adicCompletionIntegers (maximalRealSubfield E)) 3)
    have h2 : kap E a (ideleMap _ E b) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
      apply Units.ext
      rw [coe_kap, coe_kap]
      rfl
    rw [h2, ← psi_eq_kap E ψ a hψ z]
    conv_lhs => rw [e, map_mul, h1, mul_one]
  obtain ⟨ξ, hξ⟩ := glue
    (((ideleMap (maximalRealSubfield E) E).coprod (lev E (3 * M)).subtype).coprod (diagUnits E))
    ((MonoidHom.coprod ψ.1 ((kap E a).comp (lev E (3 * M)).subtype)).coprod 1) (by
      rintro ⟨⟨b, u, hu⟩, k⟩ h
      change ideleMap (maximalRealSubfield E) E b * u * diagUnits E k = 1 at h
      change ψ.1 b * kap E a u * 1 = 1
      let c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E
      have h' := congrArg (ideleConj (maximalRealSubfield E) E) h
      have c1 : ideleConj (maximalRealSubfield E) E (ideleMap _ E b) = ideleMap _ E b :=
        Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _)
      have c2 : ideleConj (maximalRealSubfield E) E (diagUnits E k) =
          diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k) :=
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele _ E k
      have c3 : ideleConj (maximalRealSubfield E) E u ∈ lev E (3 * M) :=
        (@ideleMap_mem_lev E E _ _ _ _ c.toRingEquiv.toRingHom.toAlgebra _ u).2 hu
      rw [map_mul, map_mul, map_one, c1, c2, ← h, mul_assoc, mul_assoc, mul_right_inj] at h'
      have h3 : diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k / k) =
          u / ideleConj (maximalRealSubfield E) E u := by
        rw [_root_.map_div, div_eq_div_iff_mul_eq_mul, mul_comm, h']
      have h4 := eq_one_of_mem_lev E (N := 3 * M) (by omega) _ (h3 ▸ div_mem hu c3) fun φ => by
        rw [Units.val_div_eq_div_val, map_div₀, norm_div]
        have : φ (Units.map c.toRingEquiv.toRingHom.toMonoidHom k : Eˣ) = starRingEnd ℂ (φ k) :=
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
        rw [this, Complex.norm_conj, div_self (by simp)]
      have h5 : IsCMField.complexConj E k = k := congrArg Units.val (div_eq_one.1 h4)
      have h6 : (k : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E (k : E)).1 h5
      let k0 : (maximalRealSubfield E)ˣ := Units.mk0 ⟨k, h6⟩ fun h0 => k.ne_zero (congrArg Subtype.val h0)
      have h7 : ideleMap _ E (diagUnits _ k0) = diagUnits E k :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k0).trans (congrArg (diagUnits E) (Units.ext rfl))
      have h8 : ideleMap _ E (b * diagUnits _ k0) = u⁻¹ := by
        rw [map_mul, h7, eq_inv_iff_mul_eq_one, mul_right_comm, h]
      have h9 := hF _ ((ideleMap_mem_lev _ E _ _).1 (h8 ▸ inv_mem hu))
      rw [h8, map_mul, ψ.2.2, mul_one, map_inv] at h9
      rw [h9, inv_mul_cancel, one_mul])
  have hu : ∀ u ∈ lev E (3 * M), ξ u = kap E a u := fun u hu => by
    simpa using hξ ((1, ⟨u, hu⟩), 1)
  refine ⟨⟨ξ, ?_, fun k => by simpa using hξ ((1, 1), k)⟩,
    fun φ => if (InfinitePlace.mk φ).embedding = φ then a else 0, fun k => ?_,
    Subtype.ext (MonoidHom.ext fun b => ?_)⟩
  · refine continuous_of_continuousAt_one ξ ((continuous_kap E a).continuousAt.congr ?_)
    filter_upwards [lev_mem_nhds E (N := 3 * M) (by omega)] with x hx
    exact (hu x hx).symm
  · have h1 : infDiag k ∈ lev E (3 * M) := by
      refine ⟨fun v => ?_, fun v => ?_⟩
      · rw [coe_infDiag']
        exact map_one _
      · rw [coe_infDiag']
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    change ((ξ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hu _ h1, kap_of_fst a _ (k : E) (by rw [coe_infDiag']), prod_type]
  · change ξ (ideleMap _ E b) = ψ.1 b
    simpa using hξ ((b, 1), 1)
