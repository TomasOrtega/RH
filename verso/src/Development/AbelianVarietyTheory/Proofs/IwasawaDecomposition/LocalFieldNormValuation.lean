import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionNorm

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

/- English proof (translation)
Establish `: (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`. Conclude with `isEquiv (valuation (w.adicCompletion E)) (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))`.
-/
theorem isEquiv_valued :
    (valuation (w.adicCompletion E)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))

/- English proof (translation)
Take `⟨π, hπ⟩` from `w.valuation_exists_uniformizer E`. Establish `h : Valued.v ((π : E) : w.adicCompletion E) = WithZero.exp (-1)`. Rewrite using `[w.valuedAdicCompletion_eq_valuation']`. Conclude with `hπ`. Establish `h0 : ((π : E) : w.adicCompletion E) ≠ 0`.

Introduce `h'`. Rewrite `h` using `[h', map_zero]`. Conclude with `WithZero.zero_ne_coe h`. Conclude with `⟨Units.mk0 _ h0, h⟩`.
-/
theorem exists_unit_valued_eq :
    ∃ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h : Valued.v ((π : E) : w.adicCompletion E) = WithZero.exp (-1) := by
    rw [w.valuedAdicCompletion_eq_valuation']; exact hπ
  have h0 : ((π : E) : w.adicCompletion E) ≠ 0 := by
    intro h'; rw [h', map_zero] at h; exact WithZero.zero_ne_coe h
  exact ⟨Units.mk0 _ h0, h⟩

/- English proof (translation)
Distinguish the cases in `h0 : a = 0`. Simplify using `[h0]`. Rewrite `ha` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[← WithZero.exp_log h0, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) : a ≤ WithZero.exp (-1) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

/- English proof (translation)
Establish `he` using `isEquiv_valued w`. Take `⟨ϖ, hϖ⟩` from `exists_unit_valued_eq w`. Establish `hϖ1 : Valued.v (ϖ : w.adicCompletion E) < 1`. Rewrite using `[hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.

Establish `hu : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_uniformizer_iff.2 (he.lt_one_iff_lt_one.2 hϖ1)`. Take `⟨y, hy⟩` from `valuation_surjective (uniformizer (w.adicCompletion E))`. Rewrite using `[← hy]`.

Establish `hy1 : Valued.v y < 1` using `he.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)`. Conclude with `(he y ϖ).2 (hϖ ▸ le_exp_neg_one_of_lt_one hy1)`. Establish `hord : ord (w.adicCompletion E) ϖ = 1` using `SmGL.ord_eq_one hu`. Set `o : (w.adicCompletion E)ˣ →* Multiplicative ℤ` to `MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]`. Use `set n := ord (w.adicCompletion E) x`.

Use `set u := x * ϖ ^ (-n)`. Establish `hou : o u = 1`. Rewrite using `[map_mul, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hord, ← ofAdd_zsmul, smul_eq_mul, mul_one]`. Use `show Multiplicative.ofAdd n * Multiplicative.ofAdd (-n) = 1`. Rewrite using `[← ofAdd_add, add_neg_cancel, ofAdd_zero]`.

Establish `hu1 : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1` using `SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 hou)`. Establish `hv1 : Valued.v (u : w.adicCompletion E) = 1` using `he.eq_one_iff_eq_one.1 hu1`. Establish `hx : x = u * ϖ ^ n` using `by simp [u]`. Rewrite using `[hx, Units.val_mul, map_mul, hv1, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]`.
-/
theorem valued_eq_exp (x : (w.adicCompletion E)ˣ) :
    Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x) := by
  have he := isEquiv_valued w
  obtain ⟨ϖ, hϖ⟩ := exists_unit_valued_eq w
  have hϖ1 : Valued.v (ϖ : w.adicCompletion E) < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hu : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E) := by
    apply le_antisymm
    · exact le_uniformizer_iff.2 (he.lt_one_iff_lt_one.2 hϖ1)
    · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer (w.adicCompletion E))
      rw [← hy]
      have hy1 : Valued.v y < 1 := he.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      exact (he y ϖ).2 (hϖ ▸ le_exp_neg_one_of_lt_one hy1)
  have hord : ord (w.adicCompletion E) ϖ = 1 := SmGL.ord_eq_one hu
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  set n := ord (w.adicCompletion E) x
  set u := x * ϖ ^ (-n)
  have hou : o u = 1 := by
    rw [map_mul, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hord, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    show Multiplicative.ofAdd n * Multiplicative.ofAdd (-n) = 1
    rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]
  have hu1 : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 :=
    SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 hou)
  have hv1 : Valued.v (u : w.adicCompletion E) = 1 := he.eq_one_iff_eq_one.1 hu1
  have hx : x = u * ϖ ^ n := by simp [u]
  rw [hx, Units.val_mul, map_mul, hv1, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul,
    smul_eq_mul, mul_neg_one]

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
theorem normV_eq_absNorm : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

/- English proof (translation)
Establish `key : ∀ (a : ℤ) (h : WithZero.exp a ≠ 0), (WithZero.unzero h).toAdd = a` using `fun a h => rfl`. Rewrite using `[FinitePlace.norm_def, valued_eq_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -ord (w.adicCompletion E) x)), key]`. Simplify using `[normV_eq_absNorm]`.
-/
theorem norm_eq_zpow (x : (w.adicCompletion E)ˣ) :
    ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) := by
  have key : ∀ (a : ℤ) (h : WithZero.exp a ≠ 0), (WithZero.unzero h).toAdd = a := fun a h => rfl
  rw [FinitePlace.norm_def, valued_eq_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -ord (w.adicCompletion E) x)), key]
  simp [normV_eq_absNorm]

/- English proof (translation)
Use `one_lt_resCard (w.adicCompletion E)` as an intermediate fact. Rewrite `this` using `[GlobalTheory.LocLanglands.resCard_eq_normV]`. Then use the resulting hypothesis.
-/
theorem one_lt_normV : 1 < normV w := by
  have := one_lt_resCard (w.adicCompletion E)
  rwa [GlobalTheory.LocLanglands.resCard_eq_normV] at this

/- English proof (translation)
Establish `h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal)`. Rewrite using `[← normV_eq_absNorm]`. Conclude with `one_lt_normV w` after adjusting the coercions. Rewrite using `[isEquiv_valued w x y, FinitePlace.norm_def, FinitePlace.norm_def, NNReal.coe_le_coe]`. Conclude with `(WithZeroMulInt.toNNReal_strictMono h1).le_iff_le.symm`.
-/
theorem valuation_le_iff_norm_le (x y : w.adicCompletion E) :
    valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖ := by
  have h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal) := by
    rw [← normV_eq_absNorm]; exact_mod_cast one_lt_normV w
  rw [isEquiv_valued w x y, FinitePlace.norm_def, FinitePlace.norm_def, NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono h1).le_iff_le.symm

/- English proof (translation)
Establish `he` using `isEquiv_valued w`. Establish `hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring`. Use extensionality with `y`. Rewrite using `[Valuation.mem_integer_iff, he.le_one_iff_le_one]`. Conclude with `Iff.rfl`.

Set `e` to `RingEquiv.subringCongr hO`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`. Use `⟨GeneralLinearGroup.map e.symm.toRingHom h, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Both sides reduce to the same expression. Introduce and unpack `⟨h, rfl⟩`. Use `⟨GeneralLinearGroup.map e.toRingHom h, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Both sides reduce to the same expression.
-/
theorem range_map_eq_KO (m : ℕ) :
    (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  have he := isEquiv_valued w
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  let e := RingEquiv.subringCongr hO
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.symm.toRingHom h, ?_⟩
    ext i j; rfl
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.toRingHom h, ?_⟩
    ext i j; rfl

end GlobalTheory.CompletionNorm

open GlobalTheory.CompletionNorm in

/- English proof (translation)
Introduce `E _ _ w`. Use `⟨fun x => ⟨?_, norm_eq_zpow w x, valued_eq_exp w x⟩, valuation_le_iff_norm_le w, range_map_eq_KO w⟩` and prove the remaining obligations. Rewrite using `[norm_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LocLanglands.resCard_eq_normV]`.
-/
theorem GlobalTheory.CompletionNorm.norm_nabs_valuation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (∀ x : (w.adicCompletion E)ˣ, ‖(x : w.adicCompletion E)‖ = nabs (w.adicCompletion E) x ∧ ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) ∧ Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x)) ∧ (∀ x y : w.adicCompletion E, valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖) ∧ ∀ m : ℕ, (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  intro E _ _ w
  refine ⟨fun x => ⟨?_, norm_eq_zpow w x, valued_eq_exp w x⟩, valuation_le_iff_norm_le w, range_map_eq_KO w⟩
  rw [norm_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LocLanglands.resCard_eq_normV]
