import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramInvOHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRAlgebraMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormLeOfNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff

noncomputable section

namespace PI.OmLocU.NormOneUnitFixedPoints

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Introduce `hs`. Take `⟨-, htc, -, h4⟩` from `h`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom`. Establish `hr : ComplexEmbedding.IsReal τ`. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Use `h4 τ x` as an intermediate fact. Rewrite `this` using `[hs, AlgHom.id_apply]`. Rewrite using `[starRingEnd_apply]`.

Conclude with `this.symm`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ)) (InfinitePlace.isReal_mk_iff.2 hr)`.
-/
theorem gr_sig_ne (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hs
  obtain ⟨-, htc, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h4 τ x
    rw [hs, AlgHom.id_apply] at this
    rw [starRingEnd_apply]; exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 hr)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `li : LinearIndependent F ![(1 : E), y]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst`. Conclude with `⟨hst, rfl⟩`. It suffices to derive a contradiction.

Apply `hne (-(t⁻¹ * s))` to reduce the goal to its premises. Establish `hy' : y = t⁻¹ • (t • y)` using `by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]`. Rewrite using `[hy', eq_neg_of_add_eq_zero_right hst, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one, neg_smul]`. Establish `hsp` using `li.span_eq_top_of_card_eq_finrank' (by simpa using h.2.2.1.symm)`. Apply `gr_sig_ne σ h` to reduce the goal to its premises.

Establish `hl : σ.toLinearMap = LinearMap.id`. Use `LinearMap.ext_on_range hsp fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify using the standard rewrite rules. Simplify using `using hy`.

Conclude with `AlgHom.ext fun x => LinearMap.congr_fun hl x`.
-/
theorem gr_fix_range (h : IsCMExt F E σ) {y : E} (hy : σ y = y) : ∃ c : F, algebraMap F E c = y := by
  by_contra hne
  push Not at hne
  have li : LinearIndependent F ![(1 : E), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hne (-(t⁻¹ * s))
      have hy' : y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [hy', eq_neg_of_add_eq_zero_right hst, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one, neg_smul]
  have hsp := li.span_eq_top_of_card_eq_finrank' (by simpa using h.2.2.1.symm)
  apply gr_sig_ne σ h
  have hl : σ.toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range hsp fun i => ?_
    fin_cases i
    · simp
    · simpa using hy
  exact AlgHom.ext fun x => LinearMap.congr_fun hl x

/- English proof (translation)
Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨r, hr⟩` from `hu.exists_right_inv`. Establish `hq' : q * (r : Fv F v) = 1` using `congrArg Subtype.val hr`. Establish `hr1 : Valued.v (r : Fv F v) ≤ 1` using `r.2`.

Use `congrArg Valued.v hq'` as an intermediate fact. Rewrite `this` using `[map_mul, map_one]`. Establish `hle : Valued.v q * Valued.v (r : Fv F v) ≤ Valued.v q` using `mul_le_of_le_one_right' hr1`. Rewrite `hle` using `[this]`. Conclude with `absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)`.
-/
theorem span_le_jac {q : Fv F v} (hq : q ∈ v.adicCompletionIntegers F) (h1 : Valued.v q < 1) :
    Ideal.span {(⟨q, hq⟩ : v.adicCompletionIntegers F)} ≤ Ideal.jacobson ⊥ := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff,
    SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨r, hr⟩ := hu.exists_right_inv
  have hq' : q * (r : Fv F v) = 1 := congrArg Subtype.val hr
  have hr1 : Valued.v (r : Fv F v) ≤ 1 := r.2
  have := congrArg Valued.v hq'
  rw [map_mul, map_one] at this
  have hle : Valued.v q * Valued.v (r : Fv F v) ≤ Valued.v q := mul_le_of_le_one_right' hr1
  rw [this] at hle
  exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)

/- English proof (translation)
Introduce `hqc`. Establish `hle : oEvS (E` using `E) v ≤ Ideal.span {(⟨q, hq⟩ : v.adicCompletionIntegers F)} • oEvS (E := E) v := by`. Introduce `z hz`. Establish `e : z = (⟨q, hq⟩ : v.adicCompletionIntegers F) • (c * z)`. Establish `e1 : (⟨q, hq⟩ : v.adicCompletionIntegers F) • (c * z) = sc (E` using `E) v q * (c * z) := by`.

Rewrite using `[← smul_eq_sc]`. Both sides reduce to the same expression. Rewrite using `[e1, ← mul_assoc, hqc, one_mul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (oEv_mul v hc hz)`.

Establish `hbot` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (oEvS_fg (E := E) v) hle (span_le_jac v hq h1)`. Establish `h1m : (1 : Fv F v ⊗[F] E) ∈ oEvS (E` using `E) v := oEv_one (E := E) v`. Rewrite `h1m` using `[hbot, Submodule.mem_bot]`. Conclude with `one_ne_zero h1m`.
-/
theorem sc_mul_ne_one {q : Fv F v} (hq : q ∈ v.adicCompletionIntegers F) (h1 : Valued.v q < 1)
    {c : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v) : sc (E := E) v q * c ≠ 1 := by
  intro hqc
  have hle : oEvS (E := E) v ≤
      Ideal.span {(⟨q, hq⟩ : v.adicCompletionIntegers F)} • oEvS (E := E) v := by
    intro z hz
    have e : z = (⟨q, hq⟩ : v.adicCompletionIntegers F) • (c * z) := by
      have e1 : (⟨q, hq⟩ : v.adicCompletionIntegers F) • (c * z) = sc (E := E) v q * (c * z) := by
        rw [← smul_eq_sc]
        rfl
      rw [e1, ← mul_assoc, hqc, one_mul]
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (oEv_mul v hc hz)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (oEvS_fg (E := E) v) hle (span_le_jac v hq h1)
  have h1m : (1 : Fv F v ⊗[F] E) ∈ oEvS (E := E) v := oEv_one (E := E) v
  rw [hbot, Submodule.mem_bot] at h1m
  exact one_ne_zero h1m

/- English proof (translation)
Simplify using `only [sc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`.
-/
theorem sc_mul_sc (r s : Fv F v) : sc (E := E) v r * sc (E := E) v s = sc (E := E) v (r * s) := by
  simp only [sc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sc_one : sc (E := E) v 1 = 1 := rfl

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Assume the negation of the conclusion as `hr`. Use `push Not at hr`. Establish `hr0 : r ≠ 0`. Introduce `h0`.

Rewrite `hr` using `[h0, map_zero]`. Conclude with `absurd hr (not_lt.2 zero_le')`. Establish `hv : Valued.v r⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ hr`.

Apply `sc_mul_ne_one v (hv.le : r⁻¹ ∈ v.adicCompletionIntegers F) hv h` to reduce the goal to its premises. Rewrite using `[sc_mul_sc, inv_mul_cancel₀ hr0, sc_one]`.
-/
theorem int_of_sc {r : Fv F v} (h : sc (E := E) v r ∈ OEv (E := E) v) : r ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  by_contra hr
  push Not at hr
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hr
    exact absurd hr (not_lt.2 zero_le')
  have hv : Valued.v r⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hr
  apply sc_mul_ne_one v (hv.le : r⁻¹ ∈ v.adicCompletionIntegers F) hv h
  rw [sc_mul_sc, inv_mul_cancel₀ hr0, sc_one]

/- English proof (translation)
Establish `key : ∀ t : Fv F v ⊗[F] E, ∃ r : Fv F v, t + sigR (Fv F v) σ t = sc (E` using `E) v r := by`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp [sc]⟩`. Consider the case `tmul a e`.

Establish `hfix : σ (e + σ e) = e + σ e`. Rewrite using `[map_add, PI.OmLocU.Orb.sigma_invol σ hcm, add_comm]`. Take `⟨c, hc⟩` from `gr_fix_range σ hcm hfix`. Use `⟨c • a, ?_⟩` and prove the remaining obligations. Establish `hs1 : sigR (Fv F v) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e`.

Simplify using `[sigR, Algebra.TensorProduct.map_tmul]`. Rewrite using `[hs1, ← TensorProduct.tmul_add, ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Both sides reduce to the same expression. Consider the case `add x y hx hy`. Take `⟨rx, hx⟩` from `hx`.

Take `⟨ry, hy⟩` from `hy`. Use `⟨rx + ry, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, show x + y + (sigR (Fv F v) σ x + sigR (Fv F v) σ y) = (x + sigR (Fv F v) σ x) + (y + sigR (Fv F v) σ y) by abel, hx, hy]`. Simplify using `[sc, TensorProduct.add_tmul]`. Take `⟨r, hr⟩` from `key s`.

Establish `h2 : (2 : Fv F v) ≠ 0`. Introduce `h`. Apply `two_ne_zero (α := F)` to reduce the goal to its premises. Apply `(algebraMap F (Fv F v)).injective` to reduce the goal to its premises. Rewrite using `[map_ofNat, map_zero]`.

Conclude with `h`. Use `⟨(1 / 2 : Fv F v) * r, ?_⟩` and prove the remaining obligations. Establish `e : sc (E` using `E) v ((1 / 2 : Fv F v) * r) = (1 / 2 : Fv F v) • sc (E := E) v r := by`. Simplify using `only [sc]`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul]`.

Rewrite using `[e, ← hr, hs, ← two_smul (Fv F v) s, smul_smul, one_div, inv_mul_cancel₀ h2, one_smul]`.
-/
theorem fix_sc (hcm : IsCMExt F E σ) (s : Fv F v ⊗[F] E) (hs : sigR (Fv F v) σ s = s) :
    ∃ r : Fv F v, s = sc (E := E) v r := by
  have key : ∀ t : Fv F v ⊗[F] E, ∃ r : Fv F v, t + sigR (Fv F v) σ t = sc (E := E) v r := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [sc]⟩
    | tmul a e =>
      have hfix : σ (e + σ e) = e + σ e := by
        rw [map_add, PI.OmLocU.Orb.sigma_invol σ hcm, add_comm]
      obtain ⟨c, hc⟩ := gr_fix_range σ hcm hfix
      refine ⟨c • a, ?_⟩
      have hs1 : sigR (Fv F v) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by
        simp [sigR, Algebra.TensorProduct.map_tmul]
      rw [hs1, ← TensorProduct.tmul_add, ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
      rfl
    | add x y hx hy =>
      obtain ⟨rx, hx⟩ := hx
      obtain ⟨ry, hy⟩ := hy
      refine ⟨rx + ry, ?_⟩
      rw [map_add, show x + y + (sigR (Fv F v) σ x + sigR (Fv F v) σ y) =
        (x + sigR (Fv F v) σ x) + (y + sigR (Fv F v) σ y) by abel, hx, hy]
      simp [sc, TensorProduct.add_tmul]
  obtain ⟨r, hr⟩ := key s
  have h2 : (2 : Fv F v) ≠ 0 := by
    intro h
    apply two_ne_zero (α := F)
    apply (algebraMap F (Fv F v)).injective
    rw [map_ofNat, map_zero]
    exact h
  refine ⟨(1 / 2 : Fv F v) * r, ?_⟩
  have e : sc (E := E) v ((1 / 2 : Fv F v) * r) = (1 / 2 : Fv F v) • sc (E := E) v r := by
    simp only [sc]
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  rw [e, ← hr, hs, ← two_smul (Fv F v) s, smul_smul, one_div, inv_mul_cancel₀ h2, one_smul]

/- English proof (translation)
Take `⟨r, hr⟩` from `fix_sc σ v hcm s hs`. Conclude with `⟨r, int_of_sc v (hr ▸ hs0), hr⟩`.
-/
theorem fix_int_sc (hcm : IsCMExt F E σ) {s : Fv F v ⊗[F] E} (hs0 : s ∈ OEv (E := E) v)
    (hs : sigR (Fv F v) σ s = s) : ∃ r ∈ v.adicCompletionIntegers F, s = sc (E := E) v r := by
  obtain ⟨r, hr⟩ := fix_sc σ v hcm s hs
  exact ⟨r, int_of_sc v (hr ▸ hs0), hr⟩

def redR : v.adicCompletionIntegers F →+* 𝓞 F ⧸ v.asIdeal where
  toFun x := red v (x : Fv F v)
  map_one' := red_one v
  map_mul' x y := red_mul v x.2 y.2
  map_zero' := red_zero v
  map_add' x y := red_add v x.2 y.2

/- English proof (translation)
The claim follows from `red_eq_zero_iff v x.2`.
-/
theorem redR_eq_zero (x : v.adicCompletionIntegers F) : redR v x = 0 ↔ Valued.v (x : Fv F v) < 1 :=
  red_eq_zero_iff v x.2

/- English proof (translation)
Use `sc_mul_mem_oEv v hr (oEv_one (E := E) v)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem sc_mem {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) : sc (E := E) v r ∈ OEv (E := E) v := by
  have := sc_mul_mem_oEv v hr (oEv_one (E := E) v)
  rwa [mul_one] at this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sc_eq (r : Fv F v) :
    sc (E := E) v r = (Algebra.TensorProduct.includeLeftRingHom : Fv F v →+* Fv F v ⊗[F] E) r := rfl

/- English proof (translation)
Simplify using `[sigR, sc, Algebra.TensorProduct.map_tmul]`.
-/
theorem sigR_sc' (r : Fv F v) : sigR (Fv F v) σ (sc (E := E) v r) = sc (E := E) v r := by
  simp [sigR, sc, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
The claim follows from `Valued.toNormedField.norm_le_one_iff.2 hx`.
-/
theorem norm_le_one_of {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.2 hx

/- English proof (translation)
The claim follows from `le_antisymm (norm_le_one_of v hx) (not_lt.1 fun h' => h (Valued.toNormedField.norm_lt_one_iff.1 h'))`.
-/
theorem norm_eq_one_of {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (h : ¬ Valued.v x < 1) : ‖x‖ = 1 :=
  le_antisymm (norm_le_one_of v hx) (not_lt.1 fun h' => h (Valued.toNormedField.norm_lt_one_iff.1 h'))

/- English proof (translation)
Take `⟨k, _, _, -, hcase⟩` from `hRes hstd hun ϖ hϖ`. Break down `hcase with ⟨-, K, _, _, σ', π, -, -, hne, hsurj, hker, hsig⟩ | ⟨-, π, hsurj, hker, hsig⟩` into its components or cases. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, σ' z ≠ z := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hne (AlgEquiv.ext h)`. Take `⟨θ, rfl⟩` from `hsurj z`. Use `⟨θ, θ.2, fun hmem => ?_⟩` and prove the remaining obligations. Set `θs : PI.OmLocU.Red.OR (E` to `E) v := ⟨sigR (Fv F v) σ θ, PI.OmLocU.UnN.sigR_mem σ v θ.2⟩`. Establish `h1` using `hsig θ θs rfl`.

Establish `h2 : π ((θ - θs) * (θ - θs)) = 0` using `(hker _).2 hmem`. Rewrite `h2` using `[map_mul, map_sub, h1]`. Conclude with `hz (by simpa using (sub_eq_zero.1 (mul_self_eq_zero.1 h2)).symm)`. Take `⟨θ, hθ⟩` from `hsurj (1, 0)`. Use `⟨θ, θ.2, fun hmem => ?_⟩` and prove the remaining obligations.

Set `θs : PI.OmLocU.Red.OR (E` to `E) v := ⟨sigR (Fv F v) σ θ, PI.OmLocU.UnN.sigR_mem σ v θ.2⟩`. Establish `h1` using `hsig θ θs rfl`. Establish `h2 : π ((θ - θs) * (θ - θs)) = 0` using `(hker _).2 hmem`. Rewrite `h2` using `[map_mul, map_sub, h1, hθ]`. Simplify using `[Prod.ext_iff] at h2`.
-/
theorem exists_theta (hRes : PI.OmLocU.Red.ResAlg σ J ψ v) (hstd : StdHyp σ J ψ) (hun : UnramAt (E := E) v)
    {ϖ : Fv F v} (hϖ : IsUnif v ϖ) : ∃ θ ∈ OEv (E := E) v,
      (θ - sigR (Fv F v) σ θ) * (θ - sigR (Fv F v) σ θ) ∉ PO (E := E) v ϖ := by
  classical
  obtain ⟨k, _, _, -, hcase⟩ := hRes hstd hun ϖ hϖ
  rcases hcase with ⟨-, K, _, _, σ', π, -, -, hne, hsurj, hker, hsig⟩ | ⟨-, π, hsurj, hker, hsig⟩
  · obtain ⟨z, hz⟩ : ∃ z, σ' z ≠ z := by
      by_contra h
      push Not at h
      exact hne (AlgEquiv.ext h)
    obtain ⟨θ, rfl⟩ := hsurj z
    refine ⟨θ, θ.2, fun hmem => ?_⟩
    let θs : PI.OmLocU.Red.OR (E := E) v := ⟨sigR (Fv F v) σ θ, PI.OmLocU.UnN.sigR_mem σ v θ.2⟩
    have h1 := hsig θ θs rfl
    have h2 : π ((θ - θs) * (θ - θs)) = 0 := (hker _).2 hmem
    rw [map_mul, map_sub, h1] at h2
    exact hz (by simpa using (sub_eq_zero.1 (mul_self_eq_zero.1 h2)).symm)
  · obtain ⟨θ, hθ⟩ := hsurj (1, 0)
    refine ⟨θ, θ.2, fun hmem => ?_⟩
    let θs : PI.OmLocU.Red.OR (E := E) v := ⟨sigR (Fv F v) σ θ, PI.OmLocU.UnN.sigR_mem σ v θ.2⟩
    have h1 := hsig θ θs rfl
    have h2 : π ((θ - θs) * (θ - θs)) = 0 := (hker _).2 hmem
    rw [map_mul, map_sub, h1, hθ] at h2
    simp [Prod.ext_iff] at h2

/- English proof (translation)
Introduce `hstd hun u hu0 hus hinv`. Take `⟨u', hu'0, huu'⟩` from `hinv`. Establish `hcm : IsCMExt F E σ` using `hstd.1`. Take `⟨ϖ, hϖ⟩` from `unifEx_holds v`. Take `⟨θ, hθ0, hθd⟩` from `exists_theta σ J ψ v hRes hstd hun hϖ`.

Use `set θs := sigR (Fv F v) σ θ with hθs`. Establish `hθs0 : θs ∈ OEv (E` using `E) v := PI.OmLocU.UnN.sigR_mem σ v hθ0`. Establish `hθinv : sigR (Fv F v) σ θs = θ` using `PI.OmLocU.Orb.sigR_invol (v := v) σ hcm θ`. Take `⟨t, ht, hT⟩` from `fix_int_sc σ v hcm (oEv_add v hθ0 hθs0) (by rw [map_add, hθinv, add_comm])`. Take `⟨m, hm, hM⟩` from `fix_int_sc σ v hcm (oEv_mul v hθ0 hθs0) (by rw [map_mul, hθinv, mul_comm])`.

Take `⟨ε, hε, hU⟩` from `fix_int_sc σ v hcm hu0 hus`. Establish `hus' : sigR (Fv F v) σ u' = u'`. Establish `h1 : sigR (Fv F v) σ u' * u = 1`. Rewrite using `[← hus, ← map_mul, show u' * u = 1 by rw [mul_comm]; exact huu', map_one]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨ε', hε', hU'⟩` from `fix_int_sc σ v hcm hu'0 hus'`. Establish `hDsc : sc (E` using `E) v (t ^ 2 - 4 * m) = (θ - θs) * (θ - θs) := by`. Establish `e : (θ - θs) * (θ - θs) = (θ + θs) * (θ + θs) - 4 * (θ * θs)` using `by ring`. Rewrite using `[e, hT, hM, sc_eq, sc_eq, sc_eq]`. Simplify using `only [map_sub, map_mul, map_pow, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨tO, htO⟩ : ∃ tO : v.adicCompletionIntegers F, (tO : Fv F v) = t` from `⟨⟨t, ht⟩, rfl⟩`. Take `⟨mO, hmO⟩ : ∃ mO : v.adicCompletionIntegers F, (mO : Fv F v) = m` from `⟨⟨m, hm⟩, rfl⟩`. Take `⟨eO, heO⟩ : ∃ eO : v.adicCompletionIntegers F, (eO : Fv F v) = ε'` from `⟨⟨ε', hε'⟩, rfl⟩`. Establish `hDc : ((tO ^ 2 - 4 * mO : v.adicCompletionIntegers F) : Fv F v) = t ^ 2 - 4 * m`.

Use `push_cast`. Rewrite using `[htO, hmO]`. Both sides reduce to the same expression. Establish `hDint : t ^ 2 - 4 * m ∈ v.adicCompletionIntegers F` using `hDc ▸ (tO ^ 2 - 4 * mO).2`. Establish `hDv : ¬ Valued.v (t ^ 2 - 4 * m) < 1`.

Introduce `hlt`. Take `⟨d, hd⟩` from `(mem_unifO_iff v hϖ (⟨_, hDint⟩ : v.adicCompletionIntegers F)).2 hlt`. Apply `hθd` to reduce the goal to its premises. Use `⟨sc (E := E) v d, sc_mem v d.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hDsc, sc_mul_sc]`.

Conclude with `congrArg (sc (E := E) v) hd`. Establish `hε'1 : ¬ Valued.v ε' < 1`. Introduce `hlt`. Apply `sc_mul_ne_one v hε' hlt (hU ▸ hu0 : sc (E := E) v ε ∈ OEv (E := E) v)` to reduce the goal to its premises. Rewrite using `[← hU', ← hU, mul_comm]`.

Conclude with `huu'`. Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Use `letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal`. Use `letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)`. Establish `hDk : redR v tO ^ 2 - 4 * redR v mO ≠ 0`.

Introduce `h0`. Apply `hDv` to reduce the goal to its premises. Establish `h1 : redR v (tO ^ 2 - 4 * mO) = 0`. Rewrite using `[map_sub, map_mul, map_pow, map_ofNat]`. Conclude with `h0`.

Establish `h2` using `(redR_eq_zero v _).1 h1`. Rewrite `h2` using `[hDc]`. Then use the resulting hypothesis. Take `⟨xb, yb, hxy⟩` from `PI.OmLocU.Nrm.ff_binary (redR v tO) (redR v mO) (redR v eO) hDk`. Take `⟨x0, hx0, hx0r⟩` from `red_surj v xb`. Take `⟨y0, hy0, hy0r⟩` from `red_surj v yb`.

Take `⟨xO, hxO⟩ : ∃ xO : v.adicCompletionIntegers F, (xO : Fv F v) = x0` from `⟨⟨x0, hx0⟩, rfl⟩`. Take `⟨yO, hyO⟩ : ∃ yO : v.adicCompletionIntegers F, (yO : Fv F v) = y0` from `⟨⟨y0, hy0⟩, rfl⟩`. Establish `hres : redR v (xO ^ 2 + tO * xO * yO + mO * yO ^ 2 - eO) = 0`. Rewrite using `[map_sub, map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_pow]`. Establish `ex : redR v xO = xb` using `by show red v (xO : Fv F v) = xb`.

Rewrite using `[hxO]`. Conclude with `hx0r`. Establish `ey : redR v yO = yb` using `by show red v (yO : Fv F v) = yb`. Rewrite using `[hyO]`. Conclude with `hy0r`.

Rewrite using `[ex, ey, hxy, sub_self]`. Establish `hrc : ((xO ^ 2 + tO * xO * yO + mO * yO ^ 2 - eO : v.adicCompletionIntegers F) : Fv F v) = x0 ^ 2 + t * x0 * y0 + m * y0 ^ 2 - ε'`. Use `push_cast`. Rewrite using `[hxO, hyO, htO, hmO, heO]`. Establish `h0 : ‖x0 ^ 2 + t * x0 * y0 + m * y0 ^ 2 - ε'‖ < 1`.

Establish `h3` using `(redR_eq_zero v _).1 hres`. Rewrite `h3` using `[hrc]`. Conclude with `Valued.toNormedField.norm_lt_one_iff.2 h3`. Take `⟨x, y, hx, hy, hq⟩` from `PI.OmLocU.Nrm.solve_int t m ε' x0 y0 (norm_le_one_of v ht) (norm_le_one_of v hm) (norm_eq_one_of v hDint hDv) (norm_eq_one_of v hε' hε'1) (norm_le_one_of v hx0) (norm_le_one_of v hy0) h0`. Establish `hxi : x ∈ v.adicCompletionIntegers F` using `Valued.toNormedField.norm_le_one_iff.1 hx`.

Establish `hyi : y ∈ v.adicCompletionIntegers F` using `Valued.toNormedField.norm_le_one_iff.1 hy`. Use `⟨sc (E := E) v x + sc (E := E) v y * θ, oEv_add v (sc_mem v hxi) (oEv_mul v (sc_mem v hyi) hθ0), ?_⟩` and prove the remaining obligations. Establish `hl : sigR (Fv F v) σ (sc (E` using `E) v x + sc (E := E) v y * θ) = sc (E := E) v x + sc (E := E) v y * θs := by`. Rewrite using `[map_add, map_mul, sigR_sc', sigR_sc']`. Rewrite using `[hl]`.

Establish `e1 : (sc (E` using `E) v x + sc (E := E) v y * θs) * (sc (E := E) v x + sc (E := E) v y * θ) = sc (E := E) v x * sc (E := E) v x + sc (E := E) v x * sc (E := E) v y * (θ + θs) + sc (E := E) v y * sc (E := E) v y * (θ * θs) := by ring`. Establish `e2 : sc (E` using `E) v x * sc (E := E) v x + sc (E := E) v x * sc (E := E) v y * sc (E := E) v t + sc (E := E) v y * sc (E := E) v y * sc (E := E) v m = sc (E := E) v (x ^ 2 + t * x * y + m * y ^ 2) := by`. Simplify using `only [sc_eq, map_add, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, hT, hM, e2, hq, ← hU', mul_comm]`.

Conclude with `huu'`.
-/
theorem normOne_of (hRes : PI.OmLocU.Red.ResAlg σ J ψ v) : PI.OmLocU.Orb.NormOne σ J ψ v := by
  classical
  intro hstd hun u hu0 hus hinv
  obtain ⟨u', hu'0, huu'⟩ := hinv
  have hcm : IsCMExt F E σ := hstd.1
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨θ, hθ0, hθd⟩ := exists_theta σ J ψ v hRes hstd hun hϖ
  set θs := sigR (Fv F v) σ θ with hθs
  have hθs0 : θs ∈ OEv (E := E) v := PI.OmLocU.UnN.sigR_mem σ v hθ0
  have hθinv : sigR (Fv F v) σ θs = θ := PI.OmLocU.Orb.sigR_invol (v := v) σ hcm θ
  obtain ⟨t, ht, hT⟩ := fix_int_sc σ v hcm (oEv_add v hθ0 hθs0) (by rw [map_add, hθinv, add_comm])
  obtain ⟨m, hm, hM⟩ := fix_int_sc σ v hcm (oEv_mul v hθ0 hθs0) (by rw [map_mul, hθinv, mul_comm])
  obtain ⟨ε, hε, hU⟩ := fix_int_sc σ v hcm hu0 hus
  have hus' : sigR (Fv F v) σ u' = u' := by
    have h1 : sigR (Fv F v) σ u' * u = 1 := by
      rw [← hus, ← map_mul, show u' * u = 1 by rw [mul_comm]; exact huu', map_one]
    calc sigR (Fv F v) σ u' = sigR (Fv F v) σ u' * (u * u') := by rw [huu', mul_one]
      _ = (sigR (Fv F v) σ u' * u) * u' := by ring
      _ = u' := by rw [h1, one_mul]
  obtain ⟨ε', hε', hU'⟩ := fix_int_sc σ v hcm hu'0 hus'

  have hDsc : sc (E := E) v (t ^ 2 - 4 * m) = (θ - θs) * (θ - θs) := by
    have e : (θ - θs) * (θ - θs) = (θ + θs) * (θ + θs) - 4 * (θ * θs) := by ring
    rw [e, hT, hM, sc_eq, sc_eq, sc_eq]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  obtain ⟨tO, htO⟩ : ∃ tO : v.adicCompletionIntegers F, (tO : Fv F v) = t := ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨mO, hmO⟩ : ∃ mO : v.adicCompletionIntegers F, (mO : Fv F v) = m := ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨eO, heO⟩ : ∃ eO : v.adicCompletionIntegers F, (eO : Fv F v) = ε' := ⟨⟨ε', hε'⟩, rfl⟩
  have hDc : ((tO ^ 2 - 4 * mO : v.adicCompletionIntegers F) : Fv F v) = t ^ 2 - 4 * m := by
    push_cast
    rw [htO, hmO]
    rfl
  have hDint : t ^ 2 - 4 * m ∈ v.adicCompletionIntegers F := hDc ▸ (tO ^ 2 - 4 * mO).2
  have hDv : ¬ Valued.v (t ^ 2 - 4 * m) < 1 := by
    intro hlt
    obtain ⟨d, hd⟩ := (mem_unifO_iff v hϖ (⟨_, hDint⟩ : v.adicCompletionIntegers F)).2 hlt
    apply hθd
    refine ⟨sc (E := E) v d, sc_mem v d.2, ?_⟩
    rw [← hDsc, sc_mul_sc]
    exact congrArg (sc (E := E) v) hd
  have hε'1 : ¬ Valued.v ε' < 1 := by
    intro hlt
    apply sc_mul_ne_one v hε' hlt (hU ▸ hu0 : sc (E := E) v ε ∈ OEv (E := E) v)
    rw [← hU', ← hU, mul_comm]
    exact huu'

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  have hDk : redR v tO ^ 2 - 4 * redR v mO ≠ 0 := by
    intro h0
    apply hDv
    have h1 : redR v (tO ^ 2 - 4 * mO) = 0 := by
      rw [map_sub, map_mul, map_pow, map_ofNat]
      exact h0
    have h2 := (redR_eq_zero v _).1 h1
    rwa [hDc] at h2
  obtain ⟨xb, yb, hxy⟩ := PI.OmLocU.Nrm.ff_binary (redR v tO) (redR v mO) (redR v eO) hDk
  obtain ⟨x0, hx0, hx0r⟩ := red_surj v xb
  obtain ⟨y0, hy0, hy0r⟩ := red_surj v yb
  obtain ⟨xO, hxO⟩ : ∃ xO : v.adicCompletionIntegers F, (xO : Fv F v) = x0 := ⟨⟨x0, hx0⟩, rfl⟩
  obtain ⟨yO, hyO⟩ : ∃ yO : v.adicCompletionIntegers F, (yO : Fv F v) = y0 := ⟨⟨y0, hy0⟩, rfl⟩
  have hres : redR v (xO ^ 2 + tO * xO * yO + mO * yO ^ 2 - eO) = 0 := by
    rw [map_sub, map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_pow]
    have ex : redR v xO = xb := by
      show red v (xO : Fv F v) = xb
      rw [hxO]
      exact hx0r
    have ey : redR v yO = yb := by
      show red v (yO : Fv F v) = yb
      rw [hyO]
      exact hy0r
    rw [ex, ey, hxy, sub_self]
  have hrc : ((xO ^ 2 + tO * xO * yO + mO * yO ^ 2 - eO : v.adicCompletionIntegers F) : Fv F v) =
      x0 ^ 2 + t * x0 * y0 + m * y0 ^ 2 - ε' := by
    push_cast
    rw [hxO, hyO, htO, hmO, heO]
  have h0 : ‖x0 ^ 2 + t * x0 * y0 + m * y0 ^ 2 - ε'‖ < 1 := by
    have h3 := (redR_eq_zero v _).1 hres
    rw [hrc] at h3
    exact Valued.toNormedField.norm_lt_one_iff.2 h3
  obtain ⟨x, y, hx, hy, hq⟩ := PI.OmLocU.Nrm.solve_int t m ε' x0 y0 (norm_le_one_of v ht) (norm_le_one_of v hm)
    (norm_eq_one_of v hDint hDv) (norm_eq_one_of v hε' hε'1) (norm_le_one_of v hx0) (norm_le_one_of v hy0) h0
  have hxi : x ∈ v.adicCompletionIntegers F := Valued.toNormedField.norm_le_one_iff.1 hx
  have hyi : y ∈ v.adicCompletionIntegers F := Valued.toNormedField.norm_le_one_iff.1 hy
  refine ⟨sc (E := E) v x + sc (E := E) v y * θ, oEv_add v (sc_mem v hxi) (oEv_mul v (sc_mem v hyi) hθ0), ?_⟩
  have hl : sigR (Fv F v) σ (sc (E := E) v x + sc (E := E) v y * θ) = sc (E := E) v x + sc (E := E) v y * θs := by
    rw [map_add, map_mul, sigR_sc', sigR_sc']
  rw [hl]
  have e1 : (sc (E := E) v x + sc (E := E) v y * θs) * (sc (E := E) v x + sc (E := E) v y * θ) =
      sc (E := E) v x * sc (E := E) v x + sc (E := E) v x * sc (E := E) v y * (θ + θs) +
        sc (E := E) v y * sc (E := E) v y * (θ * θs) := by ring
  have e2 : sc (E := E) v x * sc (E := E) v x + sc (E := E) v x * sc (E := E) v y * sc (E := E) v t +
      sc (E := E) v y * sc (E := E) v y * sc (E := E) v m = sc (E := E) v (x ^ 2 + t * x * y + m * y ^ 2) := by
    simp only [sc_eq, map_add, map_mul, map_pow]
    ring
  rw [e1, hT, hM, e2, hq, ← hU', mul_comm]
  exact huu'

end PI.OmLocU.NormOneUnitFixedPoints
