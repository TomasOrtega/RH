import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCard

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hx`. Establish `h0 : Valued.v (i x) ≠ 0` using `by simpa using hx0`. Establish `h1 : Valued.v (i x) ≤ 1` using `(GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi x).2 hx.le`. Establish `h2 : Valued.v (i x⁻¹) ≤ 1` using `(GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 (by rw [map_inv₀, hx, inv_one])`. Rewrite `h2` using `[map_inv₀, map_inv₀]`.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem v_map_eq_one {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {x : v.adicCompletion K}
    (hx : Valued.v x = 1) : Valued.v (i x) = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h0 : Valued.v (i x) ≠ 0 := by simpa using hx0
  have h1 : Valued.v (i x) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi x).2 hx.le
  have h2 : Valued.v (i x⁻¹) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 (by rw [map_inv₀, hx, inv_one])
  rw [map_inv₀, map_inv₀] at h2
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (i x) * (Valued.v (i x))⁻¹ := (mul_inv_cancel₀ h0).symm
    _ ≤ Valued.v (i x) * 1 := mul_le_mul' le_rfl h2
    _ = Valued.v (i x) := mul_one _

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `by rintro rfl; rw [map_zero] at hp; exact WithZero.exp_ne_zero hp.symm`. Establish `hlt : Valued.v (i p) < 1` using `(GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi p).2 (by`. Rewrite using `[hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use the proof step `omega)`. Establish `key : ∀ z : w.adicCompletion M, Valued.v z < 1 → Valued.v z ≤ Valued.v (i p)` using `fun z hz => by`.

Establish `hy : Valued.v (i.symm z) < 1` using `(GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi _).1 (by simpa using hz)`. Rewrite `hy` using `[GlobalTheory.SplitUnif.lt_one_iff, ← hp]`. Establish `h3 : Valued.v (i.symm z / p) ≤ 1`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ hy zero_le`.

Establish `h4` using `(GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 h3`. Rewrite `h4` using `[map_div₀, map_div₀, RingEquiv.apply_symm_apply]`. Establish `hip : 0 < Valued.v (i p)`. Rewrite using `[zero_lt_iff]`. Simplify using `using hp0`.

Conclude with `(div_le_one₀ hip).1 h4`. Take `⟨q, hq⟩` from `w.valuation_exists_uniformizer M`. Establish `hq' : Valued.v ((q : M) : w.adicCompletion M) = WithZero.exp (-1)`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]`. Use `le_antisymm ((GlobalTheory.SplitUnif.lt_one_iff _).1 hlt) ?_` and prove the remaining obligations.

Rewrite using `[← hq']`. Conclude with `key _ (by rw [hq', ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)`.
-/
theorem v_map_unif {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {p : v.adicCompletion K}
    (hp : Valued.v p = WithZero.exp (-1)) : Valued.v (i p) = WithZero.exp (-1) := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hlt : Valued.v (i p) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have key : ∀ z : w.adicCompletion M, Valued.v z < 1 → Valued.v z ≤ Valued.v (i p) := fun z hz => by
    have hy : Valued.v (i.symm z) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi _).1 (by simpa using hz)
    rw [GlobalTheory.SplitUnif.lt_one_iff, ← hp] at hy
    have h3 : Valued.v (i.symm z / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have h4 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 h3
    rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply] at h4
    have hip : 0 < Valued.v (i p) := by
      rw [zero_lt_iff]; simpa using hp0
    exact (div_le_one₀ hip).1 h4
  obtain ⟨q, hq⟩ := w.valuation_exists_uniformizer M
  have hq' : Valued.v ((q : M) : w.adicCompletion M) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]
  refine le_antisymm ((GlobalTheory.SplitUnif.lt_one_iff _).1 hlt) ?_
  rw [← hq']
  exact key _ (by rw [hq', ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Take `⟨p0, hp0⟩` from `v.valuation_exists_uniformizer K`. Use `set p : v.adicCompletion K := (p0 : v.adicCompletion K)`. Establish `hp : Valued.v p = WithZero.exp (-1)`.

Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hp0]`. Establish `hpne : p ≠ 0` using `by rintro h; rw [h, map_zero] at hp; exact WithZero.exp_ne_zero hp.symm`. Establish `hvx : Valued.v x ≠ 0` using `by simpa using hx`. Use `set k := WithZero.log (Valued.v x)`. Establish `hk : Valued.v x = WithZero.exp k` using `(WithZero.exp_log hvx).symm`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu, e⟩ : ∃ u, Valued.v u = 1 ∧ x = u * (p ^ k)⁻¹ := by`. Use `⟨x * p ^ k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_zpow₀, hp, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Simplify using `only [map_mul, map_inv₀, map_zpow₀]`. Rewrite using `[v_map_eq_one i hi hu, hu, v_map_unif i hi hp, hp]`.
-/
theorem v_map_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) (x : v.adicCompletion K) :
    Valued.v (i x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨p0, hp0⟩ := v.valuation_exists_uniformizer K
  set p : v.adicCompletion K := (p0 : v.adicCompletion K)
  have hp : Valued.v p = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hp0]
  have hpne : p ≠ 0 := by rintro h; rw [h, map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hvx : Valued.v x ≠ 0 := by simpa using hx
  set k := WithZero.log (Valued.v x)
  have hk : Valued.v x = WithZero.exp k := (WithZero.exp_log hvx).symm
  obtain ⟨u, hu, e⟩ : ∃ u, Valued.v u = 1 ∧ x = u * (p ^ k)⁻¹ := by
    refine ⟨x * p ^ k, ?_, ?_⟩
    · rw [map_mul, map_zpow₀, hp, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
      simp
    · field_simp
  rw [e]
  simp only [map_mul, map_inv₀, map_zpow₀]
  rw [v_map_eq_one i hi hu, hu, v_map_unif i hi hp, hp]

/- English proof (translation)
Establish `hF : ∀ s : 𝓞 K, Valued.v (algebraMap K (v.adicCompletion K) s) = v.intValuation s` using `fun s => (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)`. Conclude with `GlobalTheory.SplitUnif.card_residueField v (algebraMap K (v.adicCompletion K)) v (fun _ => rfl) fun s => by`. Rewrite using `[hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]`.
-/
theorem card_residue (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  have hF : ∀ s : 𝓞 K, Valued.v (algebraMap K (v.adicCompletion K) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap K (v.adicCompletion K)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]

/- English proof (translation)
Set `ψ : v.adicCompletionIntegers K ≃+* w.adicCompletionIntegers M` to `{ toFun := fun a => ⟨i a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((v_map_eq i hi a).le.trans ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2))⟩ invFun := fun b => ⟨i.symm b, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by`. Rewrite using `[← v_map_eq i hi, RingEquiv.apply_symm_apply]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩`. Use `left_inv := fun a => Subtype.ext (i.symm_apply_apply a)`. Use `right_inv := fun b => Subtype.ext (i.apply_symm_apply b)`.

Use the proof step `map_mul' := fun a b => Subtype.ext (map_mul i (a : v.adicCompletion K) (b : v.adicCompletion K))`. Use the proof step `map_add' := fun a b => Subtype.ext (map_add i (a : v.adicCompletion K) (b : v.adicCompletion K)) }`. Rewrite using `[← card_residue v, ← card_residue w]`. Conclude with `Nat.card_congr (IsLocalRing.ResidueField.mapEquiv ψ).toEquiv`.
-/
theorem absNorm_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
  let ψ : v.adicCompletionIntegers K ≃+* w.adicCompletionIntegers M :=
    { toFun := fun a => ⟨i a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        ((v_map_eq i hi a).le.trans ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2))⟩
      invFun := fun b => ⟨i.symm b, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by
        rw [← v_map_eq i hi, RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (i.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (i.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul i (a : v.adicCompletion K) (b : v.adicCompletion K))
      map_add' := fun a b => Subtype.ext (map_add i (a : v.adicCompletion K) (b : v.adicCompletion K)) }
  rw [← card_residue v, ← card_residue w]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv ψ).toEquiv

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
theorem absNorm_eq_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal = normV v := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

end GlobalTheory.LiftAbsPow
