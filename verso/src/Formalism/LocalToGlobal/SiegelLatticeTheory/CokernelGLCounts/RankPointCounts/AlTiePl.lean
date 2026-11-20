import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.LocalToGlobal.SiegelLatticeTheory.AFTransport
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous

noncomputable section

namespace Formalism.L2.SG.Pf.AlTie

open NumberField IsDedekindDomain
open scoped TensorProduct

def mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) :
    HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.comap ((RingOfIntegers.mapRingEquiv j).symm : 𝓞 L →+* 𝓞 F)
    (RingOfIntegers.mapRingEquiv j).symm.surjective v

/- English proof (translation)
Use `show (RingOfIntegers.mapRingEquiv j).symm (RingOfIntegers.mapRingEquiv j x) ∈ v.asIdeal ↔ x ∈ v.asIdeal`. Rewrite using `[RingEquiv.symm_apply_apply]`.
-/
theorem mem_mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    RingOfIntegers.mapRingEquiv j x ∈ (mapPl j v).asIdeal ↔ x ∈ v.asIdeal := by
  show (RingOfIntegers.mapRingEquiv j).symm (RingOfIntegers.mapRingEquiv j x) ∈ v.asIdeal ↔ x ∈ v.asIdeal
  rw [RingEquiv.symm_apply_apply]

section comp

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

/- English proof (translation)
Use extensionality with `y`. Take `⟨x, rfl⟩` from `(RingOfIntegers.mapRingEquiv j).surjective y`. Rewrite using `[mem_mapPl, Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`. Introduce and unpack `⟨x', hx', hxx⟩`. Rewrite `hx'` using `[(RingOfIntegers.mapRingEquiv j).injective hxx]`. Then use the resulting hypothesis.
-/
theorem asIdeal_mapPl (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    (mapPl j w).asIdeal = w.asIdeal.map (RingOfIntegers.mapRingEquiv j) := by
  ext y
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv j).surjective y
  rw [mem_mapPl, Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hxx⟩
    rwa [(RingOfIntegers.mapRingEquiv j).injective hxx] at hx'

/- English proof (translation)
Rewrite using `[asIdeal_mapPl, ← Ideal.map_pow, Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x', hx', hxx⟩`. Rewrite `hx'` using `[(RingOfIntegers.mapRingEquiv j).injective hxx]`. Then use the resulting hypothesis. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`.
-/
theorem mem_mapPl_pow (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j x ∈ (mapPl j w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [asIdeal_mapPl, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x', hx', hxx⟩
    rwa [(RingOfIntegers.mapRingEquiv j).injective hxx] at hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

/- English proof (translation)
Establish `hA` using `WithZero.exp_log ha`. Establish `hB` using `WithZero.exp_log hb`. Establish `la : WithZero.log a ≤ 0`. Rewrite using `[← WithZero.exp_le_exp, hA, WithZero.exp_zero]`. Conclude with `ha1`.

Establish `lb : WithZero.log b ≤ 0`. Rewrite using `[← WithZero.exp_le_exp, hB, WithZero.exp_zero]`. Conclude with `hb1`. Take `⟨ka, hka⟩` from `Int.exists_eq_neg_ofNat la`. Take `⟨kb, hkb⟩` from `Int.exists_eq_neg_ofNat lb`.

Establish `h1 : WithZero.log b ≤ WithZero.log a`. Establish `h3` using `(h ka).1 (by rw [← hA, WithZero.exp_le_exp, hka])`. Rewrite `h3` using `[← hB, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : WithZero.log a ≤ WithZero.log b`.

Establish `h3` using `(h kb).2 (by rw [← hB, WithZero.exp_le_exp, hkb])`. Rewrite `h3` using `[← hA, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hA, ← hB, le_antisymm h2 h1]`.
-/
theorem eq_of_forall_le_exp {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have hA := WithZero.exp_log ha
  have hB := WithZero.exp_log hb
  have la : WithZero.log a ≤ 0 := by
    rw [← WithZero.exp_le_exp, hA, WithZero.exp_zero]
    exact ha1
  have lb : WithZero.log b ≤ 0 := by
    rw [← WithZero.exp_le_exp, hB, WithZero.exp_zero]
    exact hb1
  obtain ⟨ka, hka⟩ := Int.exists_eq_neg_ofNat la
  obtain ⟨kb, hkb⟩ := Int.exists_eq_neg_ofNat lb
  have h1 : WithZero.log b ≤ WithZero.log a := by
    have h3 := (h ka).1 (by rw [← hA, WithZero.exp_le_exp, hka])
    rw [← hB, WithZero.exp_le_exp] at h3
    omega
  have h2 : WithZero.log a ≤ WithZero.log b := by
    have h3 := (h kb).2 (by rw [← hB, WithZero.exp_le_exp, hkb])
    rw [← hA, WithZero.exp_le_exp] at h3
    omega
  rw [← hA, ← hB, le_antisymm h2 h1]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Apply `eq_of_forall_le_exp` to reduce the goal to its premises. Conclude with `(mapPl j w).intValuation_ne_zero _ ((map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv j).injective).2 hx)`.

Conclude with `w.intValuation_ne_zero x hx`. Conclude with `(mapPl j w).intValuation_le_one _`. Conclude with `w.intValuation_le_one x`. Introduce `n`. Rewrite using `[HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, mem_mapPl_pow]`.
-/
theorem intValuation_mapPl (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    (mapPl j w).intValuation (RingOfIntegers.mapRingEquiv j x) = w.intValuation x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · apply eq_of_forall_le_exp
    · exact (mapPl j w).intValuation_ne_zero _ ((map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv j).injective).2 hx)
    · exact w.intValuation_ne_zero x hx
    · exact (mapPl j w).intValuation_le_one _
    · exact w.intValuation_le_one x
    · intro n
      rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
        mem_mapPl_pow]

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Establish `ha' : j (algebraMap (𝓞 E) E a) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv j a)` using `by first`. Consider the case `rfl`. Consider the case `simp`. Establish `hb' : j (algebraMap (𝓞 E) E b) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv j b)` using `by first`.

Consider the case `rfl`. Consider the case `simp`. Rewrite using `[map_div₀, map_div₀, map_div₀, ha', hb', HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_mapPl, intValuation_mapPl]`.
-/
theorem valuation_mapPl (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (mapPl j w).valuation L (j x) = w.valuation E x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have ha' : j (algebraMap (𝓞 E) E a) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv j a) := by
    first
      | rfl
      | simp
  have hb' : j (algebraMap (𝓞 E) E b) = algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv j b) := by
    first
      | rfl
      | simp
  rw [map_div₀, map_div₀, map_div₀, ha', hb', HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_mapPl, intValuation_mapPl]

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
The claim follows from `continuous_withVal (HeightOneSpectrum.valuation_surjective E w) (WithVal.congr _ _ j).toRingHom fun x => by show Valued.v (WithVal.toVal _ (j x.ofVal)) = _ rw [WithVal.valued_toVal, valuation_mapPl, WithVal.apply_ofVal]`.
-/
theorem continuous_congrVal (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j) :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective E w) (WithVal.congr _ _ j).toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j x.ofVal)) = _
    rw [WithVal.valued_toVal, valuation_mapPl, WithVal.apply_ofVal]

/- English proof (translation)
The claim follows from `continuous_withVal (HeightOneSpectrum.valuation_surjective L (mapPl j w)) (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j).symm.toRingHom fun x => by show Valued.v (WithVal.toVal _ (j.symm x.ofVal)) = _ rw [WithVal.valued_toVal, ← WithVal.apply_ofVal, ← valuation_mapPl …`.
-/
theorem continuous_congrVal_symm (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j).symm :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective L (mapPl j w))
    (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j).symm.toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j.symm x.ofVal)) = _
    rw [WithVal.valued_toVal, ← WithVal.apply_ofVal, ← valuation_mapPl j w, RingEquiv.apply_symm_apply]

def compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    w.adicCompletion E ≃+* (mapPl j w).adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv E w).trans ((UniformSpace.Completion.mapRingEquiv
    (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j) (continuous_congrVal j w)
    (continuous_congrVal_symm j w)).trans (HeightOneSpectrum.adicCompletion.equiv L (mapPl j w)).symm)

/- English proof (translation)
Establish `h : Continuous (fun y : w.adicCompletion E => (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j) y.toCompletion) : (mapPl j w).adicCompletion L))` using `(HeightOneSpectrum.adicCompletion.continuous_ofCompletion L (mapPl j w)).comp (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w))`. Conclude with `h.congr fun y => rfl`.
-/
theorem continuous_compEquiv (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) : Continuous (compEquiv j w) := by
  have h : Continuous (fun y : w.adicCompletion E =>
      (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map
        (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j) y.toCompletion) : (mapPl j w).adicCompletion L)) :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L (mapPl j w)).comp
      (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w))
  exact h.congr fun y => rfl

/- English proof (translation)
Establish `h : Continuous (fun y : (mapPl j w).adicCompletion L => (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j).symm y.toCompletion) : w.adicCompletion E))` using `(HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion L (mapPl j w)))`. Conclude with `h.congr fun y => rfl`.
-/
theorem continuous_compEquiv_symm (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (compEquiv j w).symm := by
  have h : Continuous (fun y : (mapPl j w).adicCompletion L =>
      (HeightOneSpectrum.adicCompletion.ofCompletion (UniformSpace.Completion.map
        (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j).symm y.toCompletion) : w.adicCompletion E)) :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
      (UniformSpace.Completion.continuous_map.comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion L (mapPl j w)))
  exact h.congr fun y => rfl

/- English proof (translation)
Apply `HeightOneSpectrum.adicCompletion.ext` to reduce the goal to its premises. Use `show UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j) ((algebraMap E (w.adicCompletion E) x).toCompletion) = _`. Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (cont …`. Both sides reduce to the same expression.
-/
theorem compEquiv_algebraMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    compEquiv j w (algebraMap E (w.adicCompletion E) x) = algebraMap L ((mapPl j w).adicCompletion L) (j x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  show UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((mapPl j w).valuation L) j)
    ((algebraMap E (w.adicCompletion E) x).toCompletion) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletion_toCompletion,
    HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (continuous_congrVal j w))]
  rfl

/- English proof (translation)
Rewrite using `[RingEquiv.symm_apply_eq, compEquiv_algebraMap]`.
-/
theorem compEquiv_symm_algebraMap (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (compEquiv j w).symm (algebraMap L ((mapPl j w).adicCompletion L) (j x)) = algebraMap E (w.adicCompletion E) x := by
  rw [RingEquiv.symm_apply_eq, compEquiv_algebraMap]

end comp

section Tens

variable {F E F' E' : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [CommRing E] [Algebra F E]
  [CommRing E'] [Algebra F' E'] (j : F ≃+* F') (k : E ≃+* E')
  (hjk : ∀ a : F, k (algebraMap F E a) = algebraMap F' E' (j a)) (v : HeightOneSpectrum (𝓞 F))

def tensTo : v.adicCompletion F ⊗[F] E →+* (mapPl j v).adicCompletion F' ⊗[F'] E' :=
  letI : Algebra F ((mapPl j v).adicCompletion F' ⊗[F'] E') :=
    ((algebraMap F' ((mapPl j v).adicCompletion F' ⊗[F'] E')).comp j.toRingHom).toAlgebra
  (Algebra.TensorProduct.productMap
    ({ toRingHom := (Algebra.TensorProduct.includeLeftRingHom :
          (mapPl j v).adicCompletion F' →+* (mapPl j v).adicCompletion F' ⊗[F'] E').comp (compEquiv j v).toRingHom
       commutes' := fun a => by
          show (Algebra.TensorProduct.includeLeftRingHom :
              (mapPl j v).adicCompletion F' →+* (mapPl j v).adicCompletion F' ⊗[F'] E')
            (compEquiv j v (algebraMap F (v.adicCompletion F) a)) =
            algebraMap F' ((mapPl j v).adicCompletion F' ⊗[F'] E') (j a)
          rw [compEquiv_algebraMap, Algebra.TensorProduct.algebraMap_apply]
          rfl } : v.adicCompletion F →ₐ[F] (mapPl j v).adicCompletion F' ⊗[F'] E')
    ({ toRingHom := (Algebra.TensorProduct.includeRight :
          E' →ₐ[F'] (mapPl j v).adicCompletion F' ⊗[F'] E').toRingHom.comp k.toRingHom
       commutes' := fun a => by
          show (Algebra.TensorProduct.includeRight : E' →ₐ[F'] (mapPl j v).adicCompletion F' ⊗[F'] E')
            (k (algebraMap F E a)) = algebraMap F' ((mapPl j v).adicCompletion F' ⊗[F'] E') (j a)
          rw [hjk, AlgHom.commutes] } : E →ₐ[F] (mapPl j v).adicCompletion F' ⊗[F'] E')).toRingHom

def tensFrom : (mapPl j v).adicCompletion F' ⊗[F'] E' →+* v.adicCompletion F ⊗[F] E :=
  letI : Algebra F' (v.adicCompletion F ⊗[F] E) :=
    ((algebraMap F (v.adicCompletion F ⊗[F] E)).comp j.symm.toRingHom).toAlgebra
  (Algebra.TensorProduct.productMap
    ({ toRingHom := (Algebra.TensorProduct.includeLeftRingHom :
          v.adicCompletion F →+* v.adicCompletion F ⊗[F] E).comp (compEquiv j v).symm.toRingHom
       commutes' := fun a => by
          show (Algebra.TensorProduct.includeLeftRingHom : v.adicCompletion F →+* v.adicCompletion F ⊗[F] E)
            ((compEquiv j v).symm (algebraMap F' ((mapPl j v).adicCompletion F') a)) =
            algebraMap F (v.adicCompletion F ⊗[F] E) (j.symm a)
          have ha : a = j (j.symm a) := (j.apply_symm_apply a).symm
          conv_lhs => rw [ha]
          rw [compEquiv_symm_algebraMap, Algebra.TensorProduct.algebraMap_apply]
          rfl } : (mapPl j v).adicCompletion F' →ₐ[F'] v.adicCompletion F ⊗[F] E)
    ({ toRingHom := (Algebra.TensorProduct.includeRight :
          E →ₐ[F] v.adicCompletion F ⊗[F] E).toRingHom.comp k.symm.toRingHom
       commutes' := fun a => by
          show (Algebra.TensorProduct.includeRight : E →ₐ[F] v.adicCompletion F ⊗[F] E)
            (k.symm (algebraMap F' E' a)) = algebraMap F (v.adicCompletion F ⊗[F] E) (j.symm a)
          have hk : k.symm (algebraMap F' E' a) = algebraMap F E (j.symm a) := by
            apply k.injective
            rw [RingEquiv.apply_symm_apply, hjk, RingEquiv.apply_symm_apply]
          rw [hk, AlgHom.commutes] } : E' →ₐ[F'] v.adicCompletion F ⊗[F] E)).toRingHom

/- English proof (translation)
Use `letI : Algebra F ((mapPl j v).adicCompletion F' ⊗[F'] E') := ((algebraMap F' ((mapPl j v).adicCompletion F' ⊗[F'] E')).comp j.toRingHom).toAlgebra`. Unfold `tensTo`. Use `erw [Algebra.TensorProduct.productMap_apply_tmul]`. Use `show (compEquiv j v a ⊗ₜ[F'] (1 : E')) * ((1 : (mapPl j v).adicCompletion F') ⊗ₜ[F'] k e) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem tensTo_tmul (a : v.adicCompletion F) (e : E) :
    tensTo j k hjk v (a ⊗ₜ e) = compEquiv j v a ⊗ₜ k e := by
  letI : Algebra F ((mapPl j v).adicCompletion F' ⊗[F'] E') :=
    ((algebraMap F' ((mapPl j v).adicCompletion F' ⊗[F'] E')).comp j.toRingHom).toAlgebra
  unfold tensTo
  erw [Algebra.TensorProduct.productMap_apply_tmul]
  show (compEquiv j v a ⊗ₜ[F'] (1 : E')) * ((1 : (mapPl j v).adicCompletion F') ⊗ₜ[F'] k e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Use `letI : Algebra F' (v.adicCompletion F ⊗[F] E) := ((algebraMap F (v.adicCompletion F ⊗[F] E)).comp j.symm.toRingHom).toAlgebra`. Unfold `tensFrom`. Use `erw [Algebra.TensorProduct.productMap_apply_tmul]`. Use `show ((compEquiv j v).symm b ⊗ₜ[F] (1 : E)) * ((1 : v.adicCompletion F) ⊗ₜ[F] k.symm e) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem tensFrom_tmul (b : (mapPl j v).adicCompletion F') (e : E') :
    tensFrom j k hjk v (b ⊗ₜ e) = (compEquiv j v).symm b ⊗ₜ k.symm e := by
  letI : Algebra F' (v.adicCompletion F ⊗[F] E) :=
    ((algebraMap F (v.adicCompletion F ⊗[F] E)).comp j.symm.toRingHom).toAlgebra
  unfold tensFrom
  erw [Algebra.TensorProduct.productMap_apply_tmul]
  show ((compEquiv j v).symm b ⊗ₜ[F] (1 : E)) * ((1 : v.adicCompletion F) ⊗ₜ[F] k.symm e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rw [tensTo_tmul, tensFrom_tmul, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem tensFrom_tensTo (x : v.adicCompletion F ⊗[F] E) : tensFrom j k hjk v (tensTo j k hjk v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rw [tensTo_tmul, tensFrom_tmul, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rw [tensFrom_tmul, tensTo_tmul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem tensTo_tensFrom (y : (mapPl j v).adicCompletion F' ⊗[F'] E') : tensTo j k hjk v (tensFrom j k hjk v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rw [tensFrom_tmul, tensTo_tmul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Tens

def IdemNT (R : Type) [Ring R] : Prop := ∃ x : R, x * x = x ∧ x ≠ 0 ∧ x ≠ 1

/- English proof (translation)
Introduce and unpack `⟨x, hx, h0, h1⟩`. Use `⟨f x, by rw [← map_mul, hx], fun hz => h0 ?_, fun hz => h1 ?_⟩` and prove the remaining obligations. Rewrite using `[← h x, hz, map_zero]`. Rewrite using `[← h x, hz, map_one]`.
-/
theorem idemNT_of {R S : Type} [Ring R] [Ring S] (f : R →+* S) (g : S →+* R) (h : ∀ x, g (f x) = x) :
    IdemNT R → IdemNT S := by
  rintro ⟨x, hx, h0, h1⟩
  refine ⟨f x, by rw [← map_mul, hx], fun hz => h0 ?_, fun hz => h1 ?_⟩
  · rw [← h x, hz, map_zero]
  · rw [← h x, hz, map_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨idemNT_of (tensTo j k hjk v) (tensFrom j k hjk v) (tensFrom_tensTo j k hjk v), idemNT_of (tensFrom j k hjk v) (tensTo j k hjk v) (tensTo_tensFrom j k hjk v)⟩`.
-/
theorem idemNT_iff {F E F' E' : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [CommRing E] [Algebra F E]
    [CommRing E'] [Algebra F' E'] (j : F ≃+* F') (k : E ≃+* E')
    (hjk : ∀ a : F, k (algebraMap F E a) = algebraMap F' E' (j a)) (v : HeightOneSpectrum (𝓞 F)) :
    IdemNT (v.adicCompletion F ⊗[F] E) ↔ IdemNT ((mapPl j v).adicCompletion F' ⊗[F'] E') := ⟨idemNT_of (tensTo j k hjk v) (tensFrom j k hjk v) (tensFrom_tensTo j k hjk v),
    idemNT_of (tensFrom j k hjk v) (tensTo j k hjk v) (tensTo_tensFrom j k hjk v)⟩

end Formalism.L2.SG.Pf.AlTie

namespace Formalism.L2.SG.Pf.AlTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting
open scoped TensorProduct

/- English proof (translation)
The claim follows from `asIdeal_mapPl j v`.
-/
theorem asIdeal_mapPl' {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] (j : F ≃+* L)
    (v : HeightOneSpectrum (𝓞 F)) : (mapPl j v).asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv j) := asIdeal_mapPl j v

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_congr (Ideal.quotientEquiv v.asIdeal (mapPl j v).asIdeal (RingOfIntegers.mapRingEquiv j) (asIdeal_mapPl' j v)).toEquiv.symm`.
-/
theorem absNorm_mapPl {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] (j : F ≃+* L)
    (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm (mapPl j v).asIdeal = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal (mapPl j v).asIdeal (RingOfIntegers.mapRingEquiv j)
    (asIdeal_mapPl' j v)).toEquiv.symm

/- English proof (translation)
Rewrite using `[← map_natCast (RingOfIntegers.mapRingEquiv j) n, mem_mapPl]`.
-/
theorem natCast_mem_mapPl {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] (j : F ≃+* L)
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : ((n : 𝓞 L) ∈ (mapPl j v).asIdeal) ↔ ((n : 𝓞 F) ∈ v.asIdeal) := by
  rw [← map_natCast (RingOfIntegers.mapRingEquiv j) n, mem_mapPl]

/- English proof (translation)
Establish `: p.asIdeal.IsPrime` using `p.isPrime`. Unfold `Formalism.MainNotions.S.Loc.resChar`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec, h]`.

Introduce `h`. Establish `h0 : ((g : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h`. Rewrite `h0` using `[ringChar.spec]`.

Break down `(Nat.dvd_prime hg).1 h0 with h1 | h1` into its components or cases. It suffices to derive a contradiction. Establish `h2 : ((1 : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0` using `by rw [ringChar.spec, h1]`. Rewrite `h2` using `[Nat.cast_one]`. Conclude with `one_ne_zero h2`.

Conclude with `h1`.
-/
theorem resChar_eq_iff {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) {g : ℕ} (hg : g.Prime) :
    Formalism.MainNotions.S.Loc.resChar p = g ↔ ((g : 𝓞 F) ∈ p.asIdeal) := by
  have : p.asIdeal.IsPrime := p.isPrime
  unfold Formalism.MainNotions.S.Loc.resChar
  constructor
  · intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec, h]
  · intro h
    have h0 : ((g : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact h
    rw [ringChar.spec] at h0
    rcases (Nat.dvd_prime hg).1 h0 with h1 | h1
    · exfalso
      have h2 : ((1 : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by rw [ringChar.spec, h1]
      rw [Nat.cast_one] at h2
      exact one_ne_zero h2
    · exact h1

variable {D : D7} (X : HidaSetting D)

def plEquiv : HeightOneSpectrum (𝓞 X.B.I.F) ≃ PlF D where
  toFun := mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)
  invFun w := HeightOneSpectrum.comap
    (RingOfIntegers.mapRingEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) : 𝓞 X.B.I.F →+* 𝓞 D.host.F)
    (RingOfIntegers.mapRingEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)).surjective w
  left_inv v := by
    apply HeightOneSpectrum.ext
    ext x
    show (RingOfIntegers.mapRingEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)).symm
      (RingOfIntegers.mapRingEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) x) ∈ v.asIdeal ↔ x ∈ v.asIdeal
    rw [RingEquiv.symm_apply_apply]
  right_inv w := by
    apply HeightOneSpectrum.ext
    ext x
    show RingOfIntegers.mapRingEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)
      ((RingOfIntegers.mapRingEquiv (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X)).symm x) ∈ w.asIdeal ↔ x ∈ w.asIdeal
    rw [RingEquiv.apply_symm_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem plEquiv_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    plEquiv X v = mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) v := rfl

/- English proof (translation)
The claim follows from `absNorm_mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) v`.
-/
theorem absNorm_plEquiv (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Ideal.absNorm (plEquiv X v).asIdeal = Ideal.absNorm v.asIdeal := absNorm_mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) v

/- English proof (translation)
The claim follows from `natCast_mem_mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) v n`.
-/
theorem natCast_mem_plEquiv (v : HeightOneSpectrum (𝓞 X.B.I.F)) (n : ℕ) :
    ((n : 𝓞 D.host.F) ∈ (plEquiv X v).asIdeal) ↔ ((n : 𝓞 X.B.I.F) ∈ v.asIdeal) := natCast_mem_mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) v n

/- English proof (translation)
Unfold `Formalism.L2.SG.LocVol.TypAt`. Rewrite using `[Formalism.L2.SG.TypedSets.mem_typSet _ _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero, resChar_eq_iff _ (D.host.g_prime 0), resChar_eq_iff _ (D.host.g_prime 1), natCast_mem_plEquiv, natCast_mem_plEquiv]`. Both sides reduce to the same expression.
-/
theorem typAt_iff (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Formalism.L2.SG.LocVol.TypAt X v ↔
      (Formalism.MainNotions.S.Loc.resChar (plEquiv X v) = D.host.g 0 ∨ Formalism.MainNotions.S.Loc.resChar (plEquiv X v) = D.host.g 1) := by
  unfold Formalism.L2.SG.LocVol.TypAt
  rw [Formalism.L2.SG.TypedSets.mem_typSet _ _ _ (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero,
    resChar_eq_iff _ (D.host.g_prime 0), resChar_eq_iff _ (D.host.g_prime 1), natCast_mem_plEquiv, natCast_mem_plEquiv]
  rfl

def EtaTie : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
    ((Formalism.L2.SG.LocVol.etaV (E := X.B.I.E) v : ℤ) : ℝ) = Formalism.L2.SG.DataInst.eta₃ (plEquiv X v)

/- English proof (translation)
Unfold `EtaTie`. Introduce `v`. Establish `hjk : ∀ a : X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E a) = algebraMap D.host.F D.host.E (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X a)` using `fun a => (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF_coe X a).symm`. Establish `h1` using `idemNT_iff (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) X.ιE hjk v`. Take `⟨e⟩` from `hL (plEquiv X v)`.

Establish `h2 : IdemNT ((mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) v).adicCompletion D.host.F ⊗[D.host.F] D.host.E) ↔ IdemNT (D.s.atP (plEquiv X v)).Ep` using `⟨idemNT_of e.eE.symm.toRingHom e.eE.toRingHom (fun x => e.eE.apply_symm_apply x), idemNT_of e.eE.toRingHom e.eE.symm.toRingHom (fun x => e.eE.symm_apply_apply x)⟩`. Establish `hiff` using `h1.trans h2`. Unfold `Formalism.L2.SG.LocVol.etaV Formalism.L2.SG.DataInst.eta₃`. Use `split_ifs with ha hb hb`. Simplify using the standard rewrite rules.

Conclude with `absurd (hiff.1 ha) hb`. Conclude with `absurd (hiff.2 hb) ha`. Simplify using the standard rewrite rules.
-/
theorem etaTie_of (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) : EtaTie X := by
  unfold EtaTie
  intro v
  have hjk : ∀ a : X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E a) =
      algebraMap D.host.F D.host.E (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X a) :=
    fun a => (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF_coe X a).symm
  have h1 := idemNT_iff (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) X.ιE hjk v
  obtain ⟨e⟩ := hL (plEquiv X v)
  have h2 : IdemNT ((mapPl (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) v).adicCompletion D.host.F ⊗[D.host.F] D.host.E) ↔
      IdemNT (D.s.atP (plEquiv X v)).Ep :=
    ⟨idemNT_of e.eE.symm.toRingHom e.eE.toRingHom (fun x => e.eE.apply_symm_apply x),
      idemNT_of e.eE.toRingHom e.eE.symm.toRingHom (fun x => e.eE.symm_apply_apply x)⟩
  have hiff := h1.trans h2
  unfold Formalism.L2.SG.LocVol.etaV Formalism.L2.SG.DataInst.eta₃
  split_ifs with ha hb hb
  · simp
  · exact absurd (hiff.1 ha) hb
  · exact absurd (hiff.2 hb) ha
  · simp

end Formalism.L2.SG.Pf.AlTie
