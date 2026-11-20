import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.LocalToGlobal.UnitaryNorms.UnrAe

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host.CT

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

def plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.comap ((RingOfIntegers.mapRingEquiv j).symm : 𝓞 L →+* 𝓞 E)
    (RingOfIntegers.mapRingEquiv j).symm.surjective w

/- English proof (translation)
Unfold `plMap`. Simplify using `[IsDedekindDomain.HeightOneSpectrum.comap]`.
-/
theorem mem_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j x ∈ (plMap j w).asIdeal ↔ x ∈ w.asIdeal := by
  unfold plMap
  simp [IsDedekindDomain.HeightOneSpectrum.comap]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `[RingOfIntegers.mapRingEquiv]`.
-/
theorem mapRingEquiv_symm_apply (j : E ≃+* L) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j.symm (RingOfIntegers.mapRingEquiv j x) = x := by
  apply RingOfIntegers.ext
  simp [RingOfIntegers.mapRingEquiv]

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `y`. Establish `h` using `mem_plMap j.symm (plMap j w) (RingOfIntegers.mapRingEquiv j y)`. Rewrite `h` using `[mapRingEquiv_symm_apply]`. Rewrite using `[h, mem_plMap]`.
-/
theorem plMap_symm_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) : plMap j.symm (plMap j w) = w := by
  apply HeightOneSpectrum.ext
  ext y
  have h := mem_plMap j.symm (plMap j w) (RingOfIntegers.mapRingEquiv j y)
  rw [mapRingEquiv_symm_apply] at h
  rw [h, mem_plMap]

/- English proof (translation)
Establish `h` using `plMap_symm_plMap j.symm v`. Rewrite `h` using `[RingEquiv.symm_symm]`. Then use the resulting hypothesis.
-/
theorem plMap_plMap_symm (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : plMap j (plMap j.symm v) = v := by
  have h := plMap_symm_plMap j.symm v
  rwa [RingEquiv.symm_symm] at h

/- English proof (translation)
Introduce `a b h`. Rewrite using `[← plMap_symm_plMap j a, h, plMap_symm_plMap]`.
-/
theorem plMap_injective (j : E ≃+* L) : Function.Injective (plMap j) := by
  intro a b h
  rw [← plMap_symm_plMap j a, h, plMap_symm_plMap]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨(RingOfIntegers.mapRingEquiv j).symm y, ?_, RingEquiv.apply_symm_apply _ _⟩` and prove the remaining obligations.

Rewrite using `[← mem_plMap j w, RingEquiv.apply_symm_apply]`. Conclude with `hy`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mem_plMap j w x).2 hx`.
-/
theorem asIdeal_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    (plMap j w).asIdeal = w.asIdeal.map (RingOfIntegers.mapRingEquiv j) := by
  ext y
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hy
    refine ⟨(RingOfIntegers.mapRingEquiv j).symm y, ?_, RingEquiv.apply_symm_apply _ _⟩
    rw [← mem_plMap j w, RingEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    exact (mem_plMap j w x).2 hx

/- English proof (translation)
Rewrite using `[asIdeal_plMap, ← Ideal.map_pow, Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`. Rewrite `hy` using `[(RingOfIntegers.mapRingEquiv j).injective hxy]`. Then use the resulting hypothesis. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`.
-/
theorem mem_plMap_pow (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j x ∈ (plMap j w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [asIdeal_plMap, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [(RingOfIntegers.mapRingEquiv j).injective hxy] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a` from `⟨_, WithZero.exp_log ha⟩`. Take `⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b` from `⟨_, WithZero.exp_log hb⟩`. Establish `hm : m ≤ 0` using `by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1`. Establish `hk : k ≤ 0` using `by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at hb1`. Establish `e1 : (((-m).toNat : ℕ) : ℤ) = -m` using `Int.toNat_of_nonneg (by omega)`.

Establish `e2 : (((-k).toNat : ℕ) : ℤ) = -k` using `Int.toNat_of_nonneg (by omega)`. Establish `h1` using `h (-m).toNat`. Establish `h2` using `h (-k).toNat`. Rewrite `h1` using `[WithZero.exp_le_exp, WithZero.exp_le_exp, e1]`. Rewrite `h2` using `[WithZero.exp_le_exp, WithZero.exp_le_exp, e2]`.

Establish `i1` using `h1.1 (by omega)`. Establish `i2` using `h2.2 (by omega)`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_forall_le_exp {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  have hm : m ≤ 0 := by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1
  have hk : k ≤ 0 := by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at hb1
  have e1 : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
  have e2 : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  have h1 := h (-m).toNat
  have h2 := h (-k).toNat
  rw [WithZero.exp_le_exp, WithZero.exp_le_exp, e1] at h1
  rw [WithZero.exp_le_exp, WithZero.exp_le_exp, e2] at h2
  have i1 := h1.1 (by omega)
  have i2 := h2.2 (by omega)
  congr 1
  omega

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `hx' : RingOfIntegers.mapRingEquiv j x ≠ 0` using `(map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv j).injective).2 hx`. Use `eq_of_forall_le_exp ((plMap j w).intValuation_ne_zero _ hx') (w.intValuation_ne_zero _ hx) ((plMap j w).intValuation_le_one _) (w.intValuation_le_one _) ?_` and prove the remaining obligations.

Introduce `n`. Rewrite using `[HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, mem_plMap_pow]`.
-/
theorem intValuation_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    (plMap j w).intValuation (RingOfIntegers.mapRingEquiv j x) = w.intValuation x := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hx' : RingOfIntegers.mapRingEquiv j x ≠ 0 := (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv j).injective).2 hx
  refine eq_of_forall_le_exp ((plMap j w).intValuation_ne_zero _ hx') (w.intValuation_ne_zero _ hx) ((plMap j w).intValuation_le_one _) (w.intValuation_le_one _) ?_
  intro n
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, mem_plMap_pow]

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Establish `key : ∀ c : 𝓞 E, j (algebraMap (𝓞 E) E c) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv j c)` using `fun c => rfl`. Rewrite using `[map_div₀, key, key, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_plMap, intValuation_plMap]`.
-/
theorem valuation_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (plMap j w).valuation L (j x) = w.valuation E x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have key : ∀ c : 𝓞 E, j (algebraMap (𝓞 E) E c) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv j c) := fun c => rfl
  rw [map_div₀, key, key, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_plMap, intValuation_plMap]

/- English proof (translation)
Use `continuous_of_continuousAt_zero f ?_` and prove the remaining obligations. Introduce `s hs'`. Rewrite `hs'` using `[map_zero]`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.mp hs'`. Take `⟨x0, hx0⟩` from `hs (embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _))))`.

Establish `hpos : 0 < embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _)))`. Rewrite using `[← map_zero (embedding (f := .ofClass (Valued.v : Valuation (WithVal v') _)))]`. Conclude with `embedding_strictMono (Units.zero_lt γ)`. Establish `hx0' : 0 < Valued.v.restrict (WithVal.toVal v x0)`. Rewrite using `[Valuation.restrict_pos_iff, WithVal.valued_toVal, hx0]`.

Conclude with `hpos`. Use `Filter.mem_map.mpr (Valued.mem_nhds_zero.mpr ⟨Units.mk0 _ hx0'.ne', fun x hx => hγ ?_⟩)` and prove the remaining obligations. Establish `hx1 : Valued.v.restrict x < Valued.v.restrict (WithVal.toVal v x0)` using `hx`. Rewrite `hx1` using `[Valuation.restrict_lt_iff]`. Establish `e0 : Valued.v (WithVal.toVal v x0) = v x0` using `WithVal.valued_toVal _ _`.

Rewrite `hx1` using `[e0, hx0]`. Use `show Valued.v.restrict (f x) < (γ : ValueGroup₀ _)`. Rewrite using `[Valuation.restrict_lt_iff_lt_embedding, hf]`. Conclude with `hx1`.
-/
theorem continuous_withVal {R S : Type} [Field R] [Field S] {v : Valuation R (WithZero (Multiplicative ℤ))}
    {v' : Valuation S (WithZero (Multiplicative ℤ))} (hs : Function.Surjective v) (f : WithVal v →+* WithVal v')
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  intro s hs'
  rw [map_zero] at hs'
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs'
  obtain ⟨x0, hx0⟩ := hs (embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _))))
  have hpos : 0 < embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _))) := by
    rw [← map_zero (embedding (f := .ofClass (Valued.v : Valuation (WithVal v') _)))]
    exact embedding_strictMono (Units.zero_lt γ)
  have hx0' : 0 < Valued.v.restrict (WithVal.toVal v x0) := by
    rw [Valuation.restrict_pos_iff, WithVal.valued_toVal, hx0]
    exact hpos
  refine Filter.mem_map.mpr (Valued.mem_nhds_zero.mpr ⟨Units.mk0 _ hx0'.ne', fun x hx => hγ ?_⟩)
  have hx1 : Valued.v.restrict x < Valued.v.restrict (WithVal.toVal v x0) := hx
  rw [Valuation.restrict_lt_iff] at hx1
  have e0 : Valued.v (WithVal.toVal v x0) = v x0 := WithVal.valued_toVal _ _
  rw [e0, hx0] at hx1
  show Valued.v.restrict (f x) < (γ : ValueGroup₀ _)
  rw [Valuation.restrict_lt_iff_lt_embedding, hf]
  exact hx1

/- English proof (translation)
The claim follows from `continuous_withVal (HeightOneSpectrum.valuation_surjective E w) (WithVal.congr _ _ j).toRingHom fun x => by show Valued.v (WithVal.toVal _ (j x.ofVal)) = _ rw [WithVal.valued_toVal, valuation_plMap, WithVal.apply_ofVal]`.
-/
theorem continuous_congrVal (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective E w) (WithVal.congr _ _ j).toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j x.ofVal)) = _
    rw [WithVal.valued_toVal, valuation_plMap, WithVal.apply_ofVal]

/- English proof (translation)
The claim follows from `continuous_withVal (HeightOneSpectrum.valuation_surjective L (plMap j w)) (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm.toRingHom fun x => by show Valued.v (WithVal.toVal _ (j.symm x.ofVal)) = _ rw [WithVal.valued_toVal, ← WithVal.apply_ofVal, ← valuation_plMap …`.
-/
theorem continuous_congrVal_symm (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective L (plMap j w))
    (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm.toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j.symm x.ofVal)) = _
    rw [WithVal.valued_toVal, ← WithVal.apply_ofVal, ← valuation_plMap j w, RingEquiv.apply_symm_apply]

def compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    w.adicCompletion E ≃+* (plMap j w).adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv E w).trans ((UniformSpace.Completion.mapRingEquiv
    (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) (continuous_congrVal j w)
    (continuous_congrVal_symm j w)).trans (HeightOneSpectrum.adicCompletion.equiv L (plMap j w)).symm)

/- English proof (translation)
Establish `h : Continuous (fun y : w.adicCompletion E => (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) y.toCompletion) : (plMap j w).adicCompletion L))` using `(HeightOneSpectrum.adicCompletion.continuous_ofCompletion L (plMap j w)).comp (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w))`. Conclude with `h.congr fun y => rfl`.
-/
theorem continuous_compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) : Continuous (compEquiv j w) := by
  have h : Continuous (fun y : w.adicCompletion E =>
      (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map
        (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) y.toCompletion) : (plMap j w).adicCompletion L)) :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L (plMap j w)).comp
      (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w))
  exact h.congr fun y => rfl

/- English proof (translation)
Establish `h : Continuous (fun y : (plMap j w).adicCompletion L => (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm y.toCompletion) : w.adicCompletion E))` using `(HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion L (plMap j w)))`. Conclude with `h.congr fun y => rfl`.
-/
theorem continuous_compEquiv_symm (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (compEquiv j w).symm := by
  have h : Continuous (fun y : (plMap j w).adicCompletion L =>
      (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map
        (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j).symm y.toCompletion) : w.adicCompletion E)) :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L (plMap j w)))
  exact h.congr fun y => rfl

/- English proof (translation)
Apply `HeightOneSpectrum.adicCompletion.ext` to reduce the goal to its premises. Use `show UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j) ((algebraMap E (w.adicCompletion E) x).toCompletion) = _`. Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (cont …`. Both sides reduce to the same expression.
-/
theorem compEquiv_algebraMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    compEquiv j w (algebraMap E (w.adicCompletion E) x) = algebraMap L ((plMap j w).adicCompletion L) (j x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  show UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((plMap j w).valuation L) j)
    ((algebraMap E (w.adicCompletion E) x).toCompletion) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletion_toCompletion,
    HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (continuous_congrVal j w))]
  rfl

/- English proof (translation)
Rewrite using `[← compEquiv_algebraMap, RingEquiv.symm_apply_apply]`.
-/
theorem compEquiv_symm_algebraMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (compEquiv j w).symm (algebraMap L ((plMap j w).adicCompletion L) (j x)) = algebraMap E (w.adicCompletion E) x := by
  rw [← compEquiv_algebraMap, RingEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv j) (asIdeal_plMap j w)).toEquiv).symm`.
-/
theorem absNorm_plMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (plMap j w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv j) (asIdeal_plMap j w)).toEquiv).symm

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem toNNReal_congr {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) (z : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal ha z = WithZeroMulInt.toNNReal hb z := by
  subst h
  rfl

/- English proof (translation)
Establish `h` using `(HeightOneSpectrum.denseRange_algebraMap E w).equalizer (continuous_norm.comp (continuous_compEquiv j w)) continuous_norm (funext fun x => ?_)`. Conclude with `congrFun h y`. Simplify using `only [Function.comp_apply]`. Rewrite using `[compEquiv_algebraMap]`. Use `show ‖NumberField.FinitePlace.embedding (plMap j w) (j x)‖ = ‖NumberField.FinitePlace.embedding w x‖`.

Rewrite using `[NumberField.FinitePlace.norm_embedding, NumberField.FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.adicAbv_def, valuation_plMap]`. Use `congr 1`. Conclude with `toNNReal_congr _ _ (by rw [absNorm_plMap]) _`.
-/
theorem norm_compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ‖compEquiv j w y‖ = ‖y‖ := by
  have h := (HeightOneSpectrum.denseRange_algebraMap E w).equalizer (continuous_norm.comp (continuous_compEquiv j w))
    continuous_norm (funext fun x => ?_)
  · exact congrFun h y
  simp only [Function.comp_apply]
  rw [compEquiv_algebraMap]
  show ‖NumberField.FinitePlace.embedding (plMap j w) (j x)‖ = ‖NumberField.FinitePlace.embedding w x‖
  rw [NumberField.FinitePlace.norm_embedding, NumberField.FinitePlace.norm_embedding,
    HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.adicAbv_def, valuation_plMap]
  congr 1
  exact toNNReal_congr _ _ (by rw [absNorm_plMap]) _

/- English proof (translation)
Establish `h1 : ‖compEquiv j w y‖ ≤ 1 ↔ Valued.v (compEquiv j w y) ≤ 1` using `Valued.toNormedField.norm_le_one_iff`. Establish `h2 : ‖y‖ ≤ 1 ↔ Valued.v y ≤ 1` using `Valued.toNormedField.norm_le_one_iff`. Rewrite using `[← h1, ← h2, norm_compEquiv]`.
-/
theorem valued_le_one_iff (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    Valued.v (compEquiv j w y) ≤ 1 ↔ Valued.v y ≤ 1 := by
  have h1 : ‖compEquiv j w y‖ ≤ 1 ↔ Valued.v (compEquiv j w y) ≤ 1 := Valued.toNormedField.norm_le_one_iff
  have h2 : ‖y‖ ≤ 1 ↔ Valued.v y ≤ 1 := Valued.toNormedField.norm_le_one_iff
  rw [← h1, ← h2, norm_compEquiv]

/- English proof (translation)
Establish `h0 : Valued.v z ≠ 0` using `(Valuation.ne_zero_iff _).2 hz`. Rewrite using `[map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]`. Conclude with `⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩`.
-/
theorem valued_eq_one_iff_both_le_one {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (z : K) (hz : z ≠ 0) :
    Valued.v z = 1 ↔ Valued.v z ≤ 1 ∧ Valued.v z⁻¹ ≤ 1 := by
  have h0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 h0)]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using the standard rewrite rules. Establish `hy' : compEquiv j w y ≠ 0` using `(map_ne_zero_iff _ (compEquiv j w).injective).2 hy`. Rewrite using `[valued_eq_one_iff_both_le_one _ hy', valued_eq_one_iff_both_le_one _ hy, ← map_inv₀, valued_le_one_iff, valued_le_one_iff]`.
-/
theorem valued_eq_one_iff (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    Valued.v (compEquiv j w y) = 1 ↔ Valued.v y = 1 := by
  by_cases hy : y = 0
  · subst hy
    simp
  have hy' : compEquiv j w y ≠ 0 := (map_ne_zero_iff _ (compEquiv j w).injective).2 hy
  rw [valued_eq_one_iff_both_le_one _ hy', valued_eq_one_iff_both_le_one _ hy, ← map_inv₀, valued_le_one_iff, valued_le_one_iff]

/- English proof (translation)
Conclude with `(AddMonoidHomClass.isometry_of_norm (WithAbs.congr (u.comap j.toRingHom).1 u.1 j) fun x => rfl).continuous`.
-/
theorem continuous_congrAbs (j : E ≃+* L) (u : InfinitePlace L) :
    Continuous (WithAbs.congr (u.comap j.toRingHom).1 u.1 j) := by
  exact (AddMonoidHomClass.isometry_of_norm (WithAbs.congr (u.comap j.toRingHom).1 u.1 j) fun x => rfl).continuous

/- English proof (translation)
Conclude with `(AddMonoidHomClass.isometry_of_norm (WithAbs.congr (u.comap j.toRingHom).1 u.1 j).symm fun x => by`. Take `⟨y, rfl⟩` from `(WithAbs.congr (u.comap j.toRingHom).1 u.1 j).surjective x`. Rewrite using `[RingEquiv.symm_apply_apply]`. Use the proof step `rfl).continuous`.
-/
theorem continuous_congrAbs_symm (j : E ≃+* L) (u : InfinitePlace L) :
    Continuous (WithAbs.congr (u.comap j.toRingHom).1 u.1 j).symm := by
  exact (AddMonoidHomClass.isometry_of_norm (WithAbs.congr (u.comap j.toRingHom).1 u.1 j).symm fun x => by
    obtain ⟨y, rfl⟩ := (WithAbs.congr (u.comap j.toRingHom).1 u.1 j).surjective x
    rw [RingEquiv.symm_apply_apply]
    rfl).continuous

def infEquiv (j : E ≃+* L) (u : InfinitePlace L) : (u.comap j.toRingHom).Completion ≃+* u.Completion :=
  (InfinitePlace.Completion.equiv (u.comap j.toRingHom)).trans ((UniformSpace.Completion.mapRingEquiv
    (WithAbs.congr _ _ j) (continuous_congrAbs j u) (continuous_congrAbs_symm j u)).trans
    (InfinitePlace.Completion.equiv u).symm)

/- English proof (translation)
Establish `h : Continuous (fun y : (u.comap j.toRingHom).Completion => (InfinitePlace.Completion.ofCompletion (UniformSpace.Completion.map (WithAbs.congr (u.comap j.toRingHom).1 u.1 j) y.toCompletion) : u.Completion))` using `(InfinitePlace.Completion.continuous_ofCompletion u).comp (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion _))`. Conclude with `h.congr fun y => rfl`.
-/
theorem continuous_infEquiv (j : E ≃+* L) (u : InfinitePlace L) : Continuous (infEquiv j u) := by
  have h : Continuous (fun y : (u.comap j.toRingHom).Completion =>
      (InfinitePlace.Completion.ofCompletion (UniformSpace.Completion.map
        (WithAbs.congr (u.comap j.toRingHom).1 u.1 j)
          y.toCompletion) : u.Completion)) :=
    (InfinitePlace.Completion.continuous_ofCompletion u).comp
      (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion _))
  exact h.congr fun y => rfl

/- English proof (translation)
Apply `InfinitePlace.Completion.ext` to reduce the goal to its premises. Use `show UniformSpace.Completion.map (WithAbs.congr (u.comap j.toRingHom).1 u.1 j) ((algebraMap E (u.comap j.toRingHom).Completion x).toCompletion) = _`. Rewrite using `[InfinitePlace.Completion.algebraMap_toCompletion, InfinitePlace.Completion.algebraMap_toCompletion, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (continuous_congrAbs …`. Both sides reduce to the same expression.
-/
theorem infEquiv_algebraMap (j : E ≃+* L) (u : InfinitePlace L) (x : E) :
    infEquiv j u (algebraMap E (u.comap j.toRingHom).Completion x) = algebraMap L u.Completion (j x) := by
  apply InfinitePlace.Completion.ext
  show UniformSpace.Completion.map (WithAbs.congr (u.comap j.toRingHom).1
    u.1 j) ((algebraMap E (u.comap j.toRingHom).Completion x).toCompletion) = _
  rw [InfinitePlace.Completion.algebraMap_toCompletion, InfinitePlace.Completion.algebraMap_toCompletion,
    UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (continuous_congrAbs j u))]
  rfl

/- English proof (translation)
Introduce `x hx`. Establish `h` using `valued_le_one_iff j.symm v ((compEquiv j.symm v).symm x)`. Rewrite `h` using `[RingEquiv.apply_symm_apply]`. Conclude with `h.1 hx`.
-/
theorem mapsTo_integers (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) :
    Set.MapsTo (compEquiv j.symm v).symm ((plMap j.symm v).adicCompletionIntegers E : Set _)
      (v.adicCompletionIntegers L : Set _) := by
  intro x hx
  have h := valued_le_one_iff j.symm v ((compEquiv j.symm v).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.1 hx

def finMap (j : E ≃+* L) : FiniteAdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (plMap j.symm) (plMap_injective j.symm).tendsto_cofinite
    (fun v => (compEquiv j.symm v).symm.toRingHom) (Filter.Eventually.of_forall fun v => mapsTo_integers j v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finMap_apply (j : E ≃+* L) (a : FiniteAdeleRing (𝓞 E) E) (v : HeightOneSpectrum (𝓞 L)) :
    finMap j a v = (compEquiv j.symm v).symm (a (plMap j.symm v)) := rfl

/- English proof (translation)
The claim follows from `RestrictedProduct.mapAlong_continuous (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (plMap j.symm) (plMap_injective j.symm).tendsto_cofinite (fun v => (compEquiv j.symm v).symm) (Filter.Eventually.of_forall fun v = …`.
-/
theorem continuous_finMap (j : E ≃+* L) : Continuous (finMap j) :=
  RestrictedProduct.mapAlong_continuous (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) (plMap j.symm) (plMap_injective j.symm).tendsto_cofinite
    (fun v => (compEquiv j.symm v).symm) (Filter.Eventually.of_forall fun v => mapsTo_integers j v)
    fun v => continuous_compEquiv_symm j.symm v

def infMap (j : E ≃+* L) : InfiniteAdeleRing E →+* InfiniteAdeleRing L :=
  RingHom.pi fun u => (infEquiv j u).toRingHom.comp (Pi.evalRingHom _ (u.comap j.toRingHom))

/- English proof (translation)
Conclude with `continuous_pi fun u => (continuous_infEquiv j u).comp (continuous_apply _)`.
-/
theorem continuous_infMap (j : E ≃+* L) : Continuous (infMap j) := by
  exact continuous_pi fun u => (continuous_infEquiv j u).comp (continuous_apply _)

def adMap (j : E ≃+* L) : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infMap j) (finMap j)

/- English proof (translation)
Conclude with `(continuous_infMap j).prodMap (continuous_finMap j)`.
-/
theorem continuous_adMap (j : E ≃+* L) : Continuous (adMap j) := by
  exact (continuous_infMap j).prodMap (continuous_finMap j)

def idMap (j : E ≃+* L) : Ideles E →* Ideles L := Units.map (adMap j).toMonoidHom

/- English proof (translation)
Conclude with `Units.continuous_map (continuous_adMap j)`.
-/
theorem continuous_idMap (j : E ≃+* L) : Continuous (idMap j) := by
  exact Units.continuous_map (continuous_adMap j)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show adMap j (algebraMap E (AdeleRing (𝓞 E) E) (k : E)) = algebraMap L (AdeleRing (𝓞 L) L) (j k)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Conclude with `infEquiv_algebraMap j u (k : E)`.

Use `ext1 v show (compEquiv j.symm v).symm (algebraMap E _ (k : E)) = algebraMap L _ (j k)`. Establish `h` using `compEquiv_symm_algebraMap j.symm v (j (k : E))`. Rewrite `h` using `[RingEquiv.symm_apply_apply]`. Conclude with `h`.
-/
theorem idMap_diag (j : E ≃+* L) (k : Eˣ) : idMap j (diagUnits E k) = diagUnits L (Units.map j.toMonoidHom k) := by
  apply Units.ext
  show adMap j (algebraMap E (AdeleRing (𝓞 E) E) (k : E)) = algebraMap L (AdeleRing (𝓞 L) L) (j k)
  refine Prod.ext ?_ ?_
  · funext u
    exact infEquiv_algebraMap j u (k : E)
  · ext1 v
    show (compEquiv j.symm v).symm (algebraMap E _ (k : E)) = algebraMap L _ (j k)
    have h := compEquiv_symm_algebraMap j.symm v (j (k : E))
    rw [RingEquiv.symm_apply_apply] at h
    exact h

def locMap (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) :
    ((plMap j.symm v).adicCompletion E)ˣ →* (v.adicCompletion L)ˣ :=
  Units.map (compEquiv j.symm v).symm.toMonoidHom

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use `show infMap j 1 = 1`. Conclude with `map_one _`. Apply `RestrictedProduct.ext` to reduce the goal to its premises.

Introduce `v'`. Use `show (compEquiv j.symm v').symm (Pi.mulSingle (plMap j.symm v) (x : (plMap j.symm v).adicCompletion E) (plMap j.symm v')) = Pi.mulSingle v ((compEquiv j.symm v).symm (x : (plMap j.symm v).adicCompletion E)) v'`. Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality. Rewrite using `[Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]`.

Establish `h' : plMap j.symm v' ≠ plMap j.symm v` using `fun e => h (plMap_injective j.symm e)`. Rewrite using `[Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]`.
-/
theorem idMap_localIdele (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) (x : ((plMap j.symm v).adicCompletion E)ˣ) :
    idMap j (localIdele E (plMap j.symm v) x) = localIdele L v (locMap j v x) := by
  classical
  apply Units.ext
  apply Prod.ext
  · show infMap j 1 = 1
    exact map_one _
  · apply RestrictedProduct.ext
    intro v'
    show (compEquiv j.symm v').symm (Pi.mulSingle (plMap j.symm v) (x : (plMap j.symm v).adicCompletion E)
      (plMap j.symm v')) = Pi.mulSingle v ((compEquiv j.symm v).symm (x : (plMap j.symm v).adicCompletion E)) v'
    by_cases h : v' = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · have h' : plMap j.symm v' ≠ plMap j.symm v := fun e => h (plMap_injective j.symm e)
      rw [Pi.mulSingle_eq_of_ne h', Pi.mulSingle_eq_of_ne h, map_one]

/- English proof (translation)
Establish `h` using `valued_eq_one_iff j.symm v ((compEquiv j.symm v).symm (x : (plMap j.symm v).adicCompletion E))`. Rewrite `h` using `[RingEquiv.apply_symm_apply]`. Conclude with `h.symm`.
-/
theorem isUnitAt_locMap (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) (x : ((plMap j.symm v).adicCompletion E)ˣ) :
    IsUnitAt v (locMap j v x) ↔ IsUnitAt (plMap j.symm v) x := by
  have h := valued_eq_one_iff j.symm v ((compEquiv j.symm v).symm (x : (plMap j.symm v).adicCompletion E))
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/- English proof (translation)
Introduce `y`. Use `⟨Units.map (compEquiv j.symm v).toMonoidHom y, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(compEquiv j.symm v).symm_apply_apply (y : v.adicCompletion L)`.
-/
theorem locMap_surjective (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : Function.Surjective (locMap j v) := by
  intro y
  refine ⟨Units.map (compEquiv j.symm v).toMonoidHom y, ?_⟩
  apply Units.ext
  exact (compEquiv j.symm v).symm_apply_apply (y : v.adicCompletion L)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `h` using `compEquiv_symm_algebraMap j.symm v (j (k : E))`. Rewrite `h` using `[RingEquiv.symm_apply_apply]`. Conclude with `h`.
-/
theorem locMap_atFin (j : E ≃+* L) (v : HeightOneSpectrum (𝓞 L)) (k : Eˣ) :
    locMap j v (atFin (plMap j.symm v) k) = atFin v (Units.map j.toMonoidHom k) := by
  apply Units.ext
  have h := compEquiv_symm_algebraMap j.symm v (j (k : E))
  rw [RingEquiv.symm_apply_apply] at h
  exact h

def transport (j : E ≃+* L) : HChar L →* HChar E where
  toFun χ := ⟨χ.1.comp (idMap j), χ.2.1.comp (continuous_idMap j), fun k => by
    rw [MonoidHom.comp_apply, idMap_diag, χ.2.2]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem transport_apply (j : E ≃+* L) (χ : HChar L) (a : Ideles E) : (transport j χ).1 a = χ.1 (idMap j a) := rfl

/- English proof (translation)
Conclude with `congrArg χ.1 (idMap_localIdele j v x)`.
-/
theorem transport_loc (j : E ≃+* L) (χ : HChar L) (v : HeightOneSpectrum (𝓞 L))
    (x : ((plMap j.symm v).adicCompletion E)ˣ) : (transport j χ).loc (plMap j.symm v) x = χ.loc v (locMap j v x) := by
  exact congrArg χ.1 (idMap_localIdele j v x)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Take `⟨x, rfl⟩` from `locMap_surjective j v y`. Rewrite using `[← transport_loc]`. Conclude with `h x ((isUnitAt_locMap j v x).1 hy)`.

Introduce `h x hx`. Rewrite using `[transport_loc]`. Conclude with `h _ ((isUnitAt_locMap j v x).2 hx)`.
-/
theorem transport_unrAt_symm (j : E ≃+* L) (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (transport j χ).UnrAt (plMap j.symm v) ↔ χ.UnrAt v := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := locMap_surjective j v y
    rw [← transport_loc]
    exact h x ((isUnitAt_locMap j v x).1 hy)
  · intro h x hx
    rw [transport_loc]
    exact h _ ((isUnitAt_locMap j v x).2 hx)

/- English proof (translation)
Establish `h` using `transport_unrAt_symm j χ (plMap j w)`. Rewrite `h` using `[plMap_symm_plMap]`. Then use the resulting hypothesis.
-/
theorem transport_unrAt_iff (j : E ≃+* L) (χ : HChar L) (w : HeightOneSpectrum (𝓞 E)) :
    (transport j χ).UnrAt w ↔ χ.UnrAt (plMap j w) := by
  have h := transport_unrAt_symm j χ (plMap j w)
  rwa [plMap_symm_plMap] at h

/- English proof (translation)
Establish `hu` using `unif_spec (plMap j.symm v)`. Establish `key : IsUnifAt v (locMap j v (atFin (plMap j.symm v) (unif (plMap j.symm v))))`. Rewrite using `[locMap_atFin]`. Unfold `IsUnifAt at hu ⊢`. Rewrite using `[← hu]`.

Establish `e1 : Valued.v (algebraMap L (v.adicCompletion L) (j (unif (plMap j.symm v) : E))) = v.valuation L (j (unif (plMap j.symm v) : E))` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _`. Establish `e2 : Valued.v (algebraMap E ((plMap j.symm v).adicCompletion E) (unif (plMap j.symm v) : E)) = (plMap j.symm v).valuation E (unif (plMap j.symm v) : E)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (plMap j.symm v) _`. Establish `e3` using `valuation_plMap j.symm v (j (unif (plMap j.symm v) : E))`. Rewrite `e3` using `[RingEquiv.symm_apply_apply]`. Conclude with `e1.trans (e3.symm.trans e2.symm)`.

Rewrite using `[← χ.val_eq h _ key, ← transport_loc]`. Both sides reduce to the same expression.
-/
theorem transport_val_symm (j : E ≃+* L) (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) (h : χ.UnrAt v) :
    (transport j χ).val (plMap j.symm v) = χ.val v := by
  have hu := unif_spec (plMap j.symm v)
  have key : IsUnifAt v (locMap j v (atFin (plMap j.symm v) (unif (plMap j.symm v)))) := by
    rw [locMap_atFin]
    unfold IsUnifAt at hu ⊢
    rw [← hu]
    have e1 : Valued.v (algebraMap L (v.adicCompletion L) (j (unif (plMap j.symm v) : E))) = v.valuation L (j (unif (plMap j.symm v) : E)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    have e2 : Valued.v (algebraMap E ((plMap j.symm v).adicCompletion E) (unif (plMap j.symm v) : E)) = (plMap j.symm v).valuation E (unif (plMap j.symm v) : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (plMap j.symm v) _
    have e3 := valuation_plMap j.symm v (j (unif (plMap j.symm v) : E))
    rw [RingEquiv.symm_apply_apply] at e3
    exact e1.trans (e3.symm.trans e2.symm)
  rw [← χ.val_eq h _ key, ← transport_loc]
  rfl

/- English proof (translation)
Establish `h'` using `transport_val_symm j χ (plMap j w) h`. Rewrite `h'` using `[plMap_symm_plMap]`. Then use the resulting hypothesis.
-/
theorem transport_val (j : E ≃+* L) (χ : HChar L) (w : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap j w)) :
    (transport j χ).val w = χ.val (plMap j w) := by
  have h' := transport_val_symm j χ (plMap j w) h
  rwa [plMap_symm_plMap] at h'

/- English proof (translation)
Unfold `HChar.valTw`. Rewrite using `[transport_val j χ w h, absNorm_plMap]`.
-/
theorem transport_valTw (j : E ≃+* L) (χ : HChar L) (s : ℝ) (w : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt (plMap j w)) :
    (transport j χ).valTw s w = χ.valTw s (plMap j w) := by
  unfold HChar.valTw
  rw [transport_val j χ w h, absNorm_plMap]

/- English proof (translation)
Introduce `a`. Conclude with `h (idMap j a)`.
-/
theorem transport_isUnitary (j : E ≃+* L) (χ : HChar L) (h : χ.IsUnitary) : (transport j χ).IsUnitary := by
  intro a
  exact h (idMap j a)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Establish `hv' : (transport j χ).UnrAt (plMap j.symm v)` using `(transport_unrAt_symm j χ v).2 hv`. Take `⟨y, hy⟩` from `h _ hv'`. Use `⟨y, hy.trans ?_⟩` and prove the remaining obligations.

Establish `h2` using `transport_valTw j χ s (plMap j.symm v) (by rwa [plMap_plMap_symm])`. Rewrite `h2` using `[plMap_plMap_symm]`. Then use the resulting hypothesis. Introduce `h w hw`. Establish `hw' : χ.UnrAt (plMap j w)` using `(transport_unrAt_iff j χ w).1 hw`. Take `⟨y, hy⟩` from `h _ hw'`.

Conclude with `⟨y, hy.trans (transport_valTw j χ s w hw').symm⟩`.
-/
theorem transport_valuesIn (j : E ≃+* L) (χ : HChar L) (s : ℝ) {C : Type} [Field C] (e : C →+* ℂ) :
    (transport j χ).ValuesIn s e ↔ χ.ValuesIn s e := by
  constructor
  · intro h v hv
    have hv' : (transport j χ).UnrAt (plMap j.symm v) := (transport_unrAt_symm j χ v).2 hv
    obtain ⟨y, hy⟩ := h _ hv'
    refine ⟨y, hy.trans ?_⟩
    have h2 := transport_valTw j χ s (plMap j.symm v) (by rwa [plMap_plMap_symm])
    rwa [plMap_plMap_symm] at h2
  · intro h w hw
    have hw' : χ.UnrAt (plMap j w) := (transport_unrAt_iff j χ w).1 hw
    obtain ⟨y, hy⟩ := h _ hw'
    exact ⟨y, hy.trans (transport_valTw j χ s w hw').symm⟩

/- English proof (translation)
Rewrite using `[transport_unrAt_iff, transport_unrAt_iff, plMap_symm_plMap]`.
-/
theorem transport_symm_unrAt_iff (j : E ≃+* L) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    (transport j (transport j.symm χ)).UnrAt w ↔ χ.UnrAt w := by
  rw [transport_unrAt_iff, transport_unrAt_iff, plMap_symm_plMap]

/- English proof (translation)
Establish `h1 : (transport j.symm χ).UnrAt (plMap j w)`. Rewrite using `[transport_unrAt_iff, plMap_symm_plMap]`. Conclude with `h`. Rewrite using `[transport_val j _ w h1, transport_val j.symm χ (plMap j w) (by rw [plMap_symm_plMap]; exact h), plMap_symm_plMap]`.
-/
theorem transport_symm_val (j : E ≃+* L) (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (h : χ.UnrAt w) :
    (transport j (transport j.symm χ)).val w = χ.val w := by
  have h1 : (transport j.symm χ).UnrAt (plMap j w) := by
    rw [transport_unrAt_iff, plMap_symm_plMap]
    exact h
  rw [transport_val j _ w h1, transport_val j.symm χ (plMap j w) (by rw [plMap_symm_plMap]; exact h), plMap_symm_plMap]

/- English proof (translation)
Apply `hS` to reduce the goal to its premises. Use `filter_upwards [hU χ.1 χ.2.1] with v hv`. Establish `hχ : χ.UnrAt v` using `fun x hx => hv x hx`. Conclude with `⟨(transport_symm_unrAt_iff j χ v).2 hχ, hχ, transport_symm_val j χ v hχ⟩`.
-/
theorem transport_transport_symm (hS : SMOne E) (hU : UnrAE E) (j : E ≃+* L) (χ : HChar E) :
    transport j (transport j.symm χ) = χ := by
  apply hS
  filter_upwards [hU χ.1 χ.2.1] with v hv
  have hχ : χ.UnrAt v := fun x hx => hv x hx
  exact ⟨(transport_symm_unrAt_iff j χ v).2 hχ, hχ, transport_symm_val j χ v hχ⟩

def transportEquiv (hS : SMOne E) (hU : UnrAE E) (hS' : SMOne L) (hU' : UnrAE L) (j : E ≃+* L) : HChar L ≃* HChar E where
  toFun := transport j
  invFun := transport j.symm
  left_inv χ := by
    have h := transport_transport_symm hS' hU' j.symm χ
    rwa [RingEquiv.symm_symm] at h
  right_inv χ := transport_transport_symm hS hU j χ
  map_mul' := map_mul _

/- English proof (translation)
Unfold `infDiag`. Rewrite using `[MonoidHom.finsetProd_apply, Units.coe_prod]`. Apply `Prod.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `u`. Establish `h` using `map_prod ((Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) u).comp (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) : AdeleRing (𝓞 E) E →+* u.Completion) (fun i => ((((infIdele E i).comp (atInf i)) k : Ideles E) : AdeleRing (𝓞 E) E)) Finset.univ`.

Use `h.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single u]`. Use `show Pi.mulSingle u _ u = _`. Rewrite using `[Pi.mulSingle_eq_same]`. Both sides reduce to the same expression.

Introduce `w _ hw show Pi.mulSingle w _ u = 1`. Conclude with `Pi.mulSingle_eq_of_ne (Ne.symm hw) _`. Introduce `h`. Conclude with `absurd (Finset.mem_univ u) h`. Establish `h` using `map_prod ((RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E) (fun i => ((((infIdele E i).comp (atInf i)) k : Ideles E) : AdeleRing (𝓞 E) E)) Finset.univ`.

Use `h.trans ?_` and prove the remaining obligations. Conclude with `Finset.prod_eq_one fun w _ => rfl`.
-/
theorem infDiag_coe (k : Eˣ) :
    ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) (k : E), 1) := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  apply Prod.ext
  · funext u
    have h := map_prod ((Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) u).comp
      (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) : AdeleRing (𝓞 E) E →+* u.Completion)
      (fun i => ((((infIdele E i).comp (atInf i)) k : Ideles E) : AdeleRing (𝓞 E) E)) Finset.univ
    refine h.trans ?_
    rw [Finset.prod_eq_single u]
    · show Pi.mulSingle u _ u = _
      rw [Pi.mulSingle_eq_same]
      rfl
    · intro w _ hw
      show Pi.mulSingle w _ u = 1
      exact Pi.mulSingle_eq_of_ne (Ne.symm hw) _
    · intro h
      exact absurd (Finset.mem_univ u) h
  · have h := map_prod ((RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) :
      AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E)
      (fun i => ((((infIdele E i).comp (atInf i)) k : Ideles E) : AdeleRing (𝓞 E) E)) Finset.univ
    refine h.trans ?_
    exact Finset.prod_eq_one fun w _ => rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show adMap j ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = _`. Rewrite using `[infDiag_coe, infDiag_coe]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `u`.

Conclude with `infEquiv_algebraMap j u (k : E)`. Conclude with `map_one (finMap j)`.
-/
theorem idMap_infDiag (j : E ≃+* L) (k : Eˣ) : idMap j (infDiag k) = infDiag (Units.map j.toMonoidHom k) := by
  apply Units.ext
  show adMap j ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = _
  rw [infDiag_coe, infDiag_coe]
  refine Prod.ext ?_ ?_
  · funext u
    exact infEquiv_algebraMap j u (k : E)
  · exact map_one (finMap j)

/- English proof (translation)
Conclude with `congrArg χ.1 (idMap_infDiag j k)`.
-/
theorem transport_inf (j : E ≃+* L) (χ : HChar L) (k : Eˣ) :
    (transport j χ).inf k = χ.inf (Units.map j.toMonoidHom k) := by
  exact congrArg χ.1 (idMap_infDiag j k)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k'`. Establish `h2` using `h (Units.map j.symm.toMonoidHom k')`. Rewrite `h2` using `[transport_inf]`. Establish `e : Units.map j.toMonoidHom (Units.map j.symm.toMonoidHom k') = k'`.

Use `ext`. Simplify using the standard rewrite rules. Rewrite `h2` using `[e]`. Simplify using `using h2`. Introduce `h k`.

Rewrite using `[transport_inf, h]`. Simplify using the standard rewrite rules.
-/
theorem transport_hasInf (j : E ≃+* L) (χ : HChar L) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ) :
    (transport j χ).HasInf φ n ↔ χ.HasInf (fun i => (φ i).comp j.symm.toRingHom) n := by
  constructor
  · intro h k'
    have h2 := h (Units.map j.symm.toMonoidHom k')
    rw [transport_inf] at h2
    have e : Units.map j.toMonoidHom (Units.map j.symm.toMonoidHom k') = k' := by
      ext
      simp
    rw [e] at h2
    simpa using h2
  · intro h k
    rw [transport_inf, h]
    simp

end Formalism.L2.Host.CT
