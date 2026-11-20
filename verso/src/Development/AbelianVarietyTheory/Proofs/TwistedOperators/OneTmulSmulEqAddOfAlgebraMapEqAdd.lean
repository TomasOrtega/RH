import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.DetNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

open Formalism.BasicNotions.Examples₂

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Establish `: Finite (𝓞 H.F ⧸ v.asIdeal)` using `v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`. Use `adicInt_residue_finite (K := H.F) v` as an intermediate fact. Establish `hDu : IsUnit ((1 : v.adicCompletionIntegers H.F) ^ 2 - 4 * (N : v.adicCompletionIntegers H.F))`. Establish `e : ((1 : v.adicCompletionIntegers H.F) ^ 2 - 4 * (N : v.adicCompletionIntegers H.F)) = algebraMap (𝓞 H.F) _ (((1 : ℤ) ^ 2 - 4 * N : ℤ) : 𝓞 H.F)`. Rewrite using `[map_intCast]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `adicInt_isUnit_of_not_mem v _ hD`. Take `⟨s, t, h⟩` from `Formalism.HermitianLatticesTheory.unimodUnramUnique_quad 1 _ u hDu hu`.

Use `⟨s, t, ?_⟩` and prove the remaining obligations. Use `congrArg (fun z : v.adicCompletionIntegers H.F => (z : v.adicCompletion H.F)) h` as an intermediate fact. Simplify using `using this`.
-/
theorem local_quad (v : HeightOneSpectrum (𝓞 H.F)) (N : ℤ) (hD : (((1 : ℤ) ^ 2 - 4 * N : ℤ) : 𝓞 H.F) ∉ v.asIdeal)
    (u : v.adicCompletionIntegers H.F) (hu : IsUnit u) :
    ∃ s t : v.adicCompletionIntegers H.F, (s : v.adicCompletion H.F) ^ 2 + (s : v.adicCompletion H.F) * t +
      (N : v.adicCompletion H.F) * (t : v.adicCompletion H.F) ^ 2 = u := by
  have : Finite (𝓞 H.F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  have := adicInt_residue_finite (K := H.F) v
  have hDu : IsUnit ((1 : v.adicCompletionIntegers H.F) ^ 2 - 4 * (N : v.adicCompletionIntegers H.F)) := by
    have e : ((1 : v.adicCompletionIntegers H.F) ^ 2 - 4 * (N : v.adicCompletionIntegers H.F)) =
        algebraMap (𝓞 H.F) _ (((1 : ℤ) ^ 2 - 4 * N : ℤ) : 𝓞 H.F) := by
      rw [map_intCast]; push_cast; ring
    rw [e]; exact adicInt_isUnit_of_not_mem v _ hD
  obtain ⟨s, t, h⟩ := Formalism.HermitianLatticesTheory.unimodUnramUnique_quad 1 _ u hDu hu
  refine ⟨s, t, ?_⟩
  have := congrArg (fun z : v.adicCompletionIntegers H.F => (z : v.adicCompletion H.F)) h
  simpa using this

/- English proof (translation)
Distinguish the cases in `hd : ((H.d : ℤ) : 𝓞 H.F) ∈ v.asIdeal`. Establish `hq : ((H.q : ℤ) : 𝓞 H.F) ∉ v.asIdeal` using `fun hq => adel_not_both H v ⟨hd, hq⟩`. Establish `hdisc : (((1 : ℤ) ^ 2 - 4 * adelNq H : ℤ) : 𝓞 H.F) ∉ v.asIdeal`. Establish `e : ((1 : ℤ) ^ 2 - 4 * adelNq H : ℤ) = -(H.q : ℤ)`. Use `adelNq_spec H` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Int.cast_neg, v.asIdeal.neg_mem_iff]`. Conclude with `hq`. Take `⟨s, t, h3⟩` from `local_quad H v (adelNq H) hdisc u hu`. Use `set α := algebraMap H.F (v.adicCompletion H.F) (adelAlpha H)`.

Use `set β := algebraMap H.F (v.adicCompletion H.F) (adelBeta H)`. Use `⟨(s : v.adicCompletion H.F) + (t : v.adicCompletion H.F) * α, (t : v.adicCompletion H.F) * β, fun h => absurd hd h, ?_⟩` and prove the remaining obligations. Establish `h1 : 2 * α + β = 1`. Use `congrArg (algebraMap H.F (v.adicCompletion H.F)) (adelic_alpha_beta_linear H)` as an intermediate fact. Simplify `this` using `[α, β, map_add, map_mul, map_ofNat]`.

Establish `h2 : α ^ 2 + α * β + ((adelNd H : ℤ) : v.adicCompletion H.F) * β ^ 2 = ((adelNq H : ℤ) : v.adicCompletion H.F)`. Use `congrArg (algebraMap H.F (v.adicCompletion H.F)) (adelic_alpha_beta_norm H)` as an intermediate fact. Simplify `this` using `[α, β, map_add, map_mul, map_pow, map_intCast]`. Take the linear combination `h3 + ((s : v.adicCompletion H.F) * t) * h1 + (t : v.adicCompletion H.F) ^ 2 * h2`. Establish `hdisc : (((1 : ℤ) ^ 2 - 4 * adelNd H : ℤ) : 𝓞 H.F) ∉ v.asIdeal`.

Establish `e : ((1 : ℤ) ^ 2 - 4 * adelNd H : ℤ) = -(H.d : ℤ)`. Use `adelNd_spec H` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[e, Int.cast_neg, v.asIdeal.neg_mem_iff]`. Conclude with `hd`.

Take `⟨s, t, hst⟩` from `local_quad H v (adelNd H) hdisc u hu`. Use `⟨s, t, fun _ => ⟨s.2, t.2⟩, ?_⟩` and prove the remaining obligations. Take the linear combination `hst`.
-/
theorem local_norm (v : HeightOneSpectrum (𝓞 H.F)) (u : v.adicCompletionIntegers H.F) (hu : IsUnit u) :
    ∃ S T : v.adicCompletion H.F,
      (((H.d : ℤ) : 𝓞 H.F) ∉ v.asIdeal →
        S ∈ v.adicCompletionIntegers H.F ∧ T ∈ v.adicCompletionIntegers H.F) ∧
      S * S + S * T + ((adelNd H : ℤ) : v.adicCompletion H.F) * (T * T) = u := by
  by_cases hd : ((H.d : ℤ) : 𝓞 H.F) ∈ v.asIdeal
  · have hq : ((H.q : ℤ) : 𝓞 H.F) ∉ v.asIdeal := fun hq => adel_not_both H v ⟨hd, hq⟩
    have hdisc : (((1 : ℤ) ^ 2 - 4 * adelNq H : ℤ) : 𝓞 H.F) ∉ v.asIdeal := by
      have e : ((1 : ℤ) ^ 2 - 4 * adelNq H : ℤ) = -(H.q : ℤ) := by
        have := adelNq_spec H; omega
      rw [e, Int.cast_neg, v.asIdeal.neg_mem_iff]; exact hq
    obtain ⟨s, t, h3⟩ := local_quad H v (adelNq H) hdisc u hu
    set α := algebraMap H.F (v.adicCompletion H.F) (adelAlpha H)
    set β := algebraMap H.F (v.adicCompletion H.F) (adelBeta H)
    refine ⟨(s : v.adicCompletion H.F) + (t : v.adicCompletion H.F) * α,
      (t : v.adicCompletion H.F) * β, fun h => absurd hd h, ?_⟩
    have h1 : 2 * α + β = 1 := by
      have := congrArg (algebraMap H.F (v.adicCompletion H.F)) (adelic_alpha_beta_linear H)
      simpa [α, β, map_add, map_mul, map_ofNat] using this
    have h2 : α ^ 2 + α * β + ((adelNd H : ℤ) : v.adicCompletion H.F) * β ^ 2 =
        ((adelNq H : ℤ) : v.adicCompletion H.F) := by
      have := congrArg (algebraMap H.F (v.adicCompletion H.F)) (adelic_alpha_beta_norm H)
      simpa [α, β, map_add, map_mul, map_pow, map_intCast] using this
    linear_combination h3 + ((s : v.adicCompletion H.F) * t) * h1 + (t : v.adicCompletion H.F) ^ 2 * h2
  · have hdisc : (((1 : ℤ) ^ 2 - 4 * adelNd H : ℤ) : 𝓞 H.F) ∉ v.asIdeal := by
      have e : ((1 : ℤ) ^ 2 - 4 * adelNd H : ℤ) = -(H.d : ℤ) := by
        have := adelNd_spec H; omega
      rw [e, Int.cast_neg, v.asIdeal.neg_mem_iff]; exact hd
    obtain ⟨s, t, hst⟩ := local_quad H v (adelNd H) hdisc u hu
    refine ⟨s, t, fun _ => ⟨s.2, t.2⟩, ?_⟩
    linear_combination hst

/- English proof (translation)
Use `choose S T hST hq using fun v => local_norm H v ⟨u v, hu v⟩ (IsUnit.of_mul_eq_one ⟨u' v, hu' v⟩ (Subtype.ext (h v)))`. Use `⟨⟨S, Filter.eventually_cofinite.2 ((adel_finite_d H).subset (fun v hv => by` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hv (hST v h).1))⟩, ⟨T, Filter.eventually_cofinite.2 ((adel_finite_d H).subset (fun v hv => by`. Assume the negation of the conclusion as `h`.

Conclude with `hv (hST v h).2))⟩, ?_⟩`. Rewrite using `[← map_intCast (algebraMap H.F (FiniteAdeleRing (𝓞 H.F) H.F)) (adelNd H)]`. Use `FiniteAdeleRing.ext (R := 𝓞 H.F) H.F (fun v => ?_)` and prove the remaining obligations. Establish `h` using `hq v`. Rewrite `h` using `[← map_intCast (algebraMap H.F (v.adicCompletion H.F)) (adelNd H)]`.

Conclude with `h`.
-/
theorem adele_quad (u u' : FiniteAdeleRing (𝓞 H.F) H.F) (hu : ∀ v, u v ∈ v.adicCompletionIntegers H.F)
    (hu' : ∀ v, u' v ∈ v.adicCompletionIntegers H.F) (h : ∀ v, u v * u' v = 1) :
    ∃ S T : FiniteAdeleRing (𝓞 H.F) H.F,
      S * S + S * T + ((adelNd H : ℤ) : FiniteAdeleRing (𝓞 H.F) H.F) * (T * T) = u := by
  choose S T hST hq using fun v => local_norm H v ⟨u v, hu v⟩
    (IsUnit.of_mul_eq_one ⟨u' v, hu' v⟩ (Subtype.ext (h v)))
  refine ⟨⟨S, Filter.eventually_cofinite.2 ((adel_finite_d H).subset (fun v hv => by
    by_contra h
    exact hv (hST v h).1))⟩, ⟨T, Filter.eventually_cofinite.2 ((adel_finite_d H).subset (fun v hv => by
    by_contra h
    exact hv (hST v h).2))⟩, ?_⟩
  rw [← map_intCast (algebraMap H.F (FiniteAdeleRing (𝓞 H.F) H.F)) (adelNd H)]
  refine FiniteAdeleRing.ext (R := 𝓞 H.F) H.F (fun v => ?_)
  have h := hq v
  rw [← map_intCast (algebraMap H.F (v.adicCompletion H.F)) (adelNd H)] at h
  exact h

end Local

/- English proof (translation)
Rewrite `h`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Assume the negation of the conclusion as `ha`. Rewrite `ha` using `[not_le]`. Establish `a0 : a ≠ 0` using `by rintro rfl; simp at ha`. Establish `h1 : Valued.v a⁻¹ < 1`.

Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ ha`. Establish `h2` using `GlobalTheory.AdeleBaseChange.locMap_valued P 1 a⁻¹ (by simpa using (Formalism.BasicNotions.Examples₂.wz_lt_one_iff _).1 h1)`. Establish `h3 : Valued.v (GlobalTheory.AdeleBaseChange.locMap F P a⁻¹) < 1` using `(Formalism.BasicNotions.Examples₂.wz_lt_one_iff _).2 (by simpa using h2)`. Establish `h4` using `(mul_le_of_le_one_left' h).trans_lt h3`.

Rewrite `h4` using `[← map_mul, ← map_mul, mul_inv_cancel₀ a0, map_one, map_one]`. Conclude with `lt_irrefl _ h4`.
-/
theorem int_of_locMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F)
    (h : GlobalTheory.AdeleBaseChange.locMap F P a ∈ P.adicCompletionIntegers E) :
    a ∈ (P.under (𝓞 F)).adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h ⊢
  by_contra ha
  rw [not_le] at ha
  have a0 : a ≠ 0 := by rintro rfl; simp at ha
  have h1 : Valued.v a⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ ha
  have h2 := GlobalTheory.AdeleBaseChange.locMap_valued P 1 a⁻¹ (by simpa using (Formalism.BasicNotions.Examples₂.wz_lt_one_iff _).1 h1)
  have h3 : Valued.v (GlobalTheory.AdeleBaseChange.locMap F P a⁻¹) < 1 := (Formalism.BasicNotions.Examples₂.wz_lt_one_iff _).2 (by simpa using h2)
  have h4 := (mul_le_of_le_one_left' h).trans_lt h3
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ a0, map_one, map_one] at h4
  exact lt_irrefl _ h4

section Global

open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices Formalism.BasicNotions.Examples₂ Formalism.IndefR.Datum

variable {D : D7}

def iR (D : D7) : FiniteAdeleRing (𝓞 D.host.F) D.host.F →+* Ef D :=
  (Algebra.TensorProduct.includeRight :
    FiniteAdeleRing (𝓞 D.host.F) D.host.F →ₐ[D.host.F] D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `star (1 : D.host.E) ⊗ₜ[D.host.F] a = (1 : D.host.E) ⊗ₜ[D.host.F] a`. Rewrite using `[star_one]`.
-/
theorem sg_iR (a : FiniteAdeleRing (𝓞 D.host.F) D.host.F) : sg D (iR D a) = iR D a := by
  change star (1 : D.host.E) ⊗ₜ[D.host.F] a = (1 : D.host.E) ⊗ₜ[D.host.F] a
  rw [star_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sg_e (x : D.host.E) : sg D (eToEAf D x) = eToEAf D (star x) := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toAd D ((1 : D.host.E) ⊗ₜ[D.host.F] a) Q = _`. Rewrite using `[toAd_spec, map_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem cpt_iR (Q : HeightOneSpectrum (𝓞 D.host.E)) (a : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :
    cpt Q (iR D a) = GlobalTheory.AdeleBaseChange.locMap D.host.F Q (a (Q.under (𝓞 D.host.F))) := by
  change toAd D ((1 : D.host.E) ⊗ₜ[D.host.F] a) Q = _
  rw [toAd_spec, map_one, one_mul]
  rfl

/- English proof (translation)
Rewrite using `[← TensorProduct.add_tmul, ← h, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem one_tmul_smul_eq_add_of_algebraMap_eq_add {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] (c : F) (x y : E) (a : A)
    (h : algebraMap F E c = x + y) : (1 : E) ⊗ₜ[F] (c • a) = x ⊗ₜ[F] a + y ⊗ₜ[F] a := by
  rw [← TensorProduct.add_tmul, ← h, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, add_zero, zero_mem]`. Consider the case `tmul x a`. Take `⟨c, hc⟩` from `(D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])`. Conclude with `⟨_, one_tmul_smul_eq_add_of_algebraMap_eq_add c x (star x) a hc⟩`.

Consider the case `add a b ha hb`. Rewrite using `[RingHom.map_add, add_add_add_comm]`. Conclude with `add_mem ha hb`.
-/
theorem trace_mem (z : Ef D) : z + sg D z ∈ (iR D).range := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero, zero_mem]
  | tmul x a =>
    obtain ⟨c, hc⟩ := (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])
    exact ⟨_, one_tmul_smul_eq_add_of_algebraMap_eq_add c x (star x) a hc⟩
  | add a b ha hb =>
    rw [RingHom.map_add, add_add_add_comm]
    exact add_mem ha hb

/- English proof (translation)
Rewrite using `[sg_e, ← conj_eq_star, adelic_theta_conj, RingHom.map_sub, RingHom.map_one]`.
-/
theorem sg_theta : sg D (eToEAf D (adelTheta D.host)) = 1 - eToEAf D (adelTheta D.host) := by
  rw [sg_e, ← conj_eq_star, adelic_theta_conj, RingHom.map_sub, RingHom.map_one]

/- English proof (translation)
Use `trace_mem (eToEAf D (adelTheta D.host) * z)` as an intermediate fact. Rewrite `this` using `[RingHom.map_mul, sg_theta, h, ← add_mul, add_sub_cancel, one_mul]`. Then use the resulting hypothesis.
-/
theorem fixed_mem {z : Ef D} (h : sg D z = z) : z ∈ (iR D).range := by
  have := trace_mem (eToEAf D (adelTheta D.host) * z)
  rwa [RingHom.map_mul, sg_theta, h, ← add_mul, add_sub_cancel, one_mul] at this

/- English proof (translation)
Take `⟨Q, rfl⟩` from `(GlobalTheory.QNorm.places_over D.host.F D.host.E).2.1 v`. Conclude with `int_of_locMap Q _ (cpt_iR Q a ▸ (mem_OA_iff _).1 h Q)`.
-/
theorem int_of_iR {a : FiniteAdeleRing (𝓞 D.host.F) D.host.F} (h : iR D a ∈ OA D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    a v ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨Q, rfl⟩ := (GlobalTheory.QNorm.places_over D.host.F D.host.E).2.1 v
  exact int_of_locMap Q _ (cpt_iR Q a ▸ (mem_OA_iff _).1 h Q)

/- English proof (translation)
Establish `hs' : sg D d' = d'`. Use `congrArg (sg D) h` as an intermediate fact. Rewrite `this` using `[RingHom.map_mul, hs, RingHom.map_one]`. Take the linear combination `d' * this - sg D d' * h`. Take `⟨u, rfl⟩` from `fixed_mem hs`.

Take `⟨u', rfl⟩` from `fixed_mem hs'`. Take `⟨S, T, hST⟩` from `adele_quad D.host u u' (int_of_iR hd) (int_of_iR hd') fun v => by`. Take `⟨Q, rfl⟩` from `(GlobalTheory.QNorm.places_over D.host.F D.host.E).2.1 v`. Apply `(GlobalTheory.AdeleBaseChange.locMap D.host.F Q).injective` to reduce the goal to its premises. Rewrite using `[map_mul, ← cpt_iR, ← cpt_iR, ← map_mul, mul_comm, h, map_one, map_one]`.

Use `⟨iR D S + eToEAf D (adelTheta D.host) * iR D T, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (iR D) hST`. Establish `h2` using `congrArg (eToEAf D) (adelic_theta_mul_one_sub D.host)`. Simplify using `only [RingHom.map_add, RingHom.map_mul, map_intCast, RingHom.map_sub, RingHom.map_one] at h1 h2`. Rewrite using `[RingHom.map_add, RingHom.map_mul, sg_iR, sg_iR, sg_theta]`.

Take the linear combination `(iR D T * iR D T) * h2 + h1`.
-/
theorem unit_norm {d d' : Ef D} (hd : d ∈ OA D) (hd' : d' ∈ OA D) (h : d' * d = 1) (hs : sg D d = d) :
    ∃ y, sg D y * y = d := by
  have hs' : sg D d' = d' := by
    have := congrArg (sg D) h
    rw [RingHom.map_mul, hs, RingHom.map_one] at this
    linear_combination d' * this - sg D d' * h
  obtain ⟨u, rfl⟩ := fixed_mem hs
  obtain ⟨u', rfl⟩ := fixed_mem hs'
  obtain ⟨S, T, hST⟩ := adele_quad D.host u u' (int_of_iR hd) (int_of_iR hd') fun v => by
    obtain ⟨Q, rfl⟩ := (GlobalTheory.QNorm.places_over D.host.F D.host.E).2.1 v
    apply (GlobalTheory.AdeleBaseChange.locMap D.host.F Q).injective
    rw [map_mul, ← cpt_iR, ← cpt_iR, ← map_mul, mul_comm, h, map_one, map_one]
  refine ⟨iR D S + eToEAf D (adelTheta D.host) * iR D T, ?_⟩
  have h1 := congrArg (iR D) hST
  have h2 := congrArg (eToEAf D) (adelic_theta_mul_one_sub D.host)
  simp only [RingHom.map_add, RingHom.map_mul, map_intCast, RingHom.map_sub, RingHom.map_one] at h1 h2
  rw [RingHom.map_add, RingHom.map_mul, sg_iR, sg_iR, sg_theta]
  linear_combination (iR D T * iR D T) * h2 + h1

def IsN (D : D7) (x : D.host.E) : Prop := ∃ y : Ef D, sg D y * y = eToEAf D x

/- English proof (translation)
Take `⟨y, h⟩` from `h`. Take `⟨y', h'⟩` from `h'`. Conclude with `⟨y * y', by rw [RingHom.map_mul, RingHom.map_mul, ← h, ← h']; ring⟩`.
-/
theorem IsN.mul {x x' : D.host.E} (h : IsN D x) (h' : IsN D x') : IsN D (x * x') := by
  obtain ⟨y, h⟩ := h
  obtain ⟨y', h'⟩ := h'
  exact ⟨y * y', by rw [RingHom.map_mul, RingHom.map_mul, ← h, ← h']; ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨eToEAf D a, by rw [sg_e, RingHom.map_mul]⟩`.
-/
theorem isN_star (a : D.host.E) : IsN D (star a * a) := ⟨eToEAf D a, by rw [sg_e, RingHom.map_mul]⟩

/- English proof (translation)
Use `h.mul (isN_star x⁻¹)` as an intermediate fact. Break down `eq_or_ne x 0 with rfl | h0` into its components or cases. Simplify using `using h`. Rewrite `this` using `[star_inv₀, hx, mul_inv_cancel_left₀ h0]`. Then use the resulting hypothesis.
-/
theorem IsN.inv {x : D.host.E} (h : IsN D x) (hx : star x = x) : IsN D x⁻¹ := by
  have := h.mul (isN_star x⁻¹)
  rcases eq_or_ne x 0 with rfl | h0
  · simpa using h
  · rwa [star_inv₀, hx, mul_inv_cancel_left₀ h0] at this

/- English proof (translation)
Take `⟨y, hy⟩` from `unit_norm (D := D) (d := -1) (d' := -1) (neg_mem (one_mem _)) (neg_mem (one_mem _)) (by ring) (by rw [RingHom.map_neg, RingHom.map_one])`. Conclude with `⟨y, by rw [hy, RingHom.map_neg, RingHom.map_one]⟩`.
-/
theorem isN_neg_one : IsN D (-1) := by
  obtain ⟨y, hy⟩ := unit_norm (D := D) (d := -1) (d' := -1) (neg_mem (one_mem _)) (neg_mem (one_mem _)) (by ring)
    (by rw [RingHom.map_neg, RingHom.map_one])
  exact ⟨y, by rw [hy, RingHom.map_neg, RingHom.map_one]⟩

/- English proof (translation)
Unfold `Formalism.UG.cT`. Rewrite using `[Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_cT {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A) :
    (Formalism.UG.cT σ M).det = σ M.det := by
  unfold Formalism.UG.cT
  rw [Matrix.det_transpose, RingHom.map_det]
  rfl

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)`.
-/
theorem det_mem {A : Type} [CommRing A] (S : Subring A) {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

/- English proof (translation)
The claim follows from `(RingHom.map_det _ _).symm`.
-/
theorem det_ratM (V : HSp D) : (ratM V.gram).det = eToEAf D V.gram.det := (RingHom.map_det _ _).symm

/- English proof (translation)
Establish `: V.gramᴴ = V.gram` using `Matrix.ext fun i j => V.herm.eq _ _`. Rewrite using `[← Matrix.det_conjTranspose, this]`.
-/
theorem star_det (V : HSp D) : star V.gram.det = V.gram.det := by
  have : V.gramᴴ = V.gram := Matrix.ext fun i j => V.herm.eq _ _
  rw [← Matrix.det_conjTranspose, this]

/- English proof (translation)
Take `⟨hi, U, hU, h⟩` from `hU`. Establish `hd : (Formalism.UG.cT σ β.val * J * β.val).det = σ β.val.det * J.det * β.val.det`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, det_cT]`. Take `⟨y, hy⟩` from `hS _ _ (det_mem _ _ hi) (det_mem _ _ hU) (by rw [← Matrix.det_mul, h, Matrix.det_one]) (by`. Rewrite using `[hd, map_mul, map_mul, hσ, hJ]`.

Use the proof step `ring)`. Establish `hb : β.val.det * (β⁻¹).val.det = 1` using `by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]`. Establish `hb'` using `congrArg σ hb`. Rewrite `hb'` using `[map_mul, map_one]`. Use `⟨y * (β⁻¹).val.det, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Rewrite `hy` using `[hd]`. Take the linear combination `(σ (β⁻¹).val.det * (β⁻¹).val.det) * hy + (J.det * (β.val.det * (β⁻¹).val.det)) * hb' + J.det * hb`.
-/
theorem norm_of_gram {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (S : Subring A) {n : ℕ}
    (hS : ∀ d d' : A, d ∈ S → d' ∈ S → d' * d = 1 → σ d = d → ∃ y, σ y * y = d) (J : Matrix (Fin n) (Fin n) A)
    (hJ : σ J.det = J.det) (β : GL (Fin n) A) (hU : Unimod S (Formalism.UG.cT σ β.val * J * β.val)) :
    ∃ y, σ y * y = J.det := by
  obtain ⟨hi, U, hU, h⟩ := hU
  have hd : (Formalism.UG.cT σ β.val * J * β.val).det = σ β.val.det * J.det * β.val.det := by
    rw [Matrix.det_mul, Matrix.det_mul, det_cT]
  obtain ⟨y, hy⟩ := hS _ _ (det_mem _ _ hi) (det_mem _ _ hU) (by rw [← Matrix.det_mul, h, Matrix.det_one]) (by
    rw [hd, map_mul, map_mul, hσ, hJ]; ring)
  have hb : β.val.det * (β⁻¹).val.det = 1 := by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hb' := congrArg σ hb
  rw [map_mul, map_one] at hb'
  refine ⟨y * (β⁻¹).val.det, ?_⟩
  rw [map_mul]
  rw [hd] at hy
  linear_combination (σ (β⁻¹).val.det * (β⁻¹).val.det) * hy +
    (J.det * (β.val.det * (β⁻¹).val.det)) * hb' + J.det * hb

/- English proof (translation)
Take `⟨β, hβ⟩` from `exists_base V`. Use `norm_of_gram (sg D) sg_sg (OA D) (fun _ _ => unit_norm) (ratM V.gram) (by rw [det_ratM, sg_e, star_det]) β (unimod_of_isSD (isSD_one hβ))` as an intermediate fact. Rewrite `this` using `[det_ratM]`. Then use the resulting hypothesis.
-/
theorem isN_det (V : HSp D) : IsN D V.gram.det := by
  obtain ⟨β, hβ⟩ := exists_base V
  have := norm_of_gram (sg D) sg_sg (OA D) (fun _ _ => unit_norm) (ratM V.gram)
    (by rw [det_ratM, sg_e, star_det]) β (unimod_of_isSD (isSD_one hβ))
  rwa [det_ratM] at this

/- English proof (translation)
Set `e : Fin V.rank ≃ ι` to `(Fintype.equivFinOfCardEq hc).symm`. Set `P : Matrix (Fin V.rank) (Fin V.rank) E` to `Matrix.of fun a b => V.frame.repr (v (e b)) a`. Use `⟨P.det, ?_⟩` and prove the remaining obligations. Establish `: (Matrix.of fun i j => V.hT (v i) (v j)).submatrix e e = Pᴴ * V.gram * P`. Use extensionality with `a b`.

Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, P, HSpace.gram]`. Use `conv_lhs => rw [← V.frame.sum_repr (v (e a)), ← V.frame.sum_repr (v (e b))]`. Simplify using `only [map_sum, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← Matrix.det_submatrix_equiv_self e, this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_family {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) {ι : Type} [Fintype ι] [DecidableEq ι] (hc : Fintype.card ι = V.rank) (v : ι → V.V) :
    ∃ a : E, (Matrix.of fun i j => V.hT (v i) (v j)).det = star a * a * V.gram.det := by
  let e : Fin V.rank ≃ ι := (Fintype.equivFinOfCardEq hc).symm
  let P : Matrix (Fin V.rank) (Fin V.rank) E := Matrix.of fun a b => V.frame.repr (v (e b)) a
  refine ⟨P.det, ?_⟩
  have : (Matrix.of fun i j => V.hT (v i) (v j)).submatrix e e = Pᴴ * V.gram * P := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, P, HSpace.gram]
    conv_lhs => rw [← V.frame.sum_repr (v (e a)), ← V.frame.sum_repr (v (e b))]
    simp only [map_sum, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [← Matrix.det_submatrix_equiv_self e, this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  ring

/- English proof (translation)
Establish `hm : 0 < R.m` using `lt_of_lt_of_le two_pos R.two_le_m`. Establish `sym : ∀ x y, (S.Y 0).hT x y = 0 → (S.Y 0).hT y x = 0` using `fun x y h => by`. Rewrite using `[← (S.Y 0).herm.eq x y, h, map_zero]`. Establish `hfe : ∀ i l, (S.Y 0).hT (S.hypF i) (S.hypE l) = if i = l then 1 else 0`. Introduce `i l`.

Rewrite using `[← (S.Y 0).herm.eq, S.hyp_ef]`. Distinguish the cases in `h : i = l`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Set `v : Fin (S.X 0).rank ⊕ (Unit ⊕ (Fin R.rS ⊕ Fin R.rS)) → (S.Y 0).V` to `Sum.elim (fun i => S.iXY 0 ((S.X 0).frame i)) (Sum.elim (fun _ => S.zm) (Sum.elim S.hypE S.hypF))`.

Take `⟨a, ha⟩` from `det_family (S.Y 0) (by`. Establish `h1` using `S.X_rank 0 hm.le`. Establish `h2` using `S.Y_rank 0 hm.le`. Take `⟨c, hc⟩` from `R.m_even`. Simplify using `only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]`.

Simplify using `only [h1, h2, Ranks.N, Ranks.rankY, Ranks.r, Ranks.rS]`. Use the proof step `omega) v`. Set `Hy : Matrix (Fin R.rS ⊕ Fin R.rS) (Fin R.rS ⊕ Fin R.rS) E` to `Matrix.fromBlocks 0 1 1 0`. Establish `hG : (Matrix.of fun i j => (S.Y 0).hT (v i) (v j)) = Matrix.fromBlocks (S.X 0).gram 0 0 (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => -(S.T : E)) 0 0 Hy)`. Use extensionality with `i j`.

Apply the tactic sequence `rcases i with i | i | i | i <;> rcases j with j | j | j | j`. Conclude with `S.iXY_isom 0 hm _ _`. Conclude with `S.zm_orth _`. Conclude with `(S.hyp_orthX _ _).1`. Conclude with `(S.hyp_orthX _ _).2`.

Conclude with `sym _ _ (S.zm_orth _)`. Conclude with `S.zm_norm`. Conclude with `(S.hyp_orthz _).1`. Conclude with `(S.hyp_orthz _).2`. Conclude with `sym _ _ (S.hyp_orthX _ _).1`.

Conclude with `sym _ _ (S.hyp_orthz _).1`. Conclude with `S.hyp_ee _ _`. Conclude with `S.hyp_ef _ _`. Conclude with `sym _ _ (S.hyp_orthX _ _).2`. Conclude with `sym _ _ (S.hyp_orthz _).2`.

Conclude with `hfe _ _`. Conclude with `S.hyp_ff _ _`. Rewrite `ha` using `[hG, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply]`. Establish `hH : Hy.det * Hy.det = 1`. Rewrite using `[← Matrix.det_mul, Matrix.fromBlocks_multiply]`.

Simplify using the standard rewrite rules. Conclude with `⟨a, _, hH, ha⟩`.
-/
theorem det_Y_zero {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (S : Spaces R F E) :
    ∃ a ε : E, ε * ε = 1 ∧ (S.X 0).gram.det * (-(S.T : E) * ε) = star a * a * (S.Y 0).gram.det := by
  have hm : 0 < R.m := lt_of_lt_of_le two_pos R.two_le_m
  have sym : ∀ x y, (S.Y 0).hT x y = 0 → (S.Y 0).hT y x = 0 := fun x y h => by
    rw [← (S.Y 0).herm.eq x y, h, map_zero]
  have hfe : ∀ i l, (S.Y 0).hT (S.hypF i) (S.hypE l) = if i = l then 1 else 0 := by
    intro i l
    rw [← (S.Y 0).herm.eq, S.hyp_ef]
    by_cases h : i = l
    · simp [h]
    · simp [h, Ne.symm h]
  let v : Fin (S.X 0).rank ⊕ (Unit ⊕ (Fin R.rS ⊕ Fin R.rS)) → (S.Y 0).V :=
    Sum.elim (fun i => S.iXY 0 ((S.X 0).frame i)) (Sum.elim (fun _ => S.zm) (Sum.elim S.hypE S.hypF))
  obtain ⟨a, ha⟩ := det_family (S.Y 0) (by
    have h1 := S.X_rank 0 hm.le
    have h2 := S.Y_rank 0 hm.le
    obtain ⟨c, hc⟩ := R.m_even
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    simp only [h1, h2, Ranks.N, Ranks.rankY, Ranks.r, Ranks.rS]
    omega) v
  let Hy : Matrix (Fin R.rS ⊕ Fin R.rS) (Fin R.rS ⊕ Fin R.rS) E := Matrix.fromBlocks 0 1 1 0
  have hG : (Matrix.of fun i j => (S.Y 0).hT (v i) (v j)) = Matrix.fromBlocks (S.X 0).gram 0 0
      (Matrix.fromBlocks (Matrix.of fun _ _ : Unit => -(S.T : E)) 0 0 Hy) := by
    ext i j
    rcases i with i | i | i | i <;> rcases j with j | j | j | j
    · exact S.iXY_isom 0 hm _ _
    · exact S.zm_orth _
    · exact (S.hyp_orthX _ _).1
    · exact (S.hyp_orthX _ _).2
    · exact sym _ _ (S.zm_orth _)
    · exact S.zm_norm
    · exact (S.hyp_orthz _).1
    · exact (S.hyp_orthz _).2
    · exact sym _ _ (S.hyp_orthX _ _).1
    · exact sym _ _ (S.hyp_orthz _).1
    · exact S.hyp_ee _ _
    · exact S.hyp_ef _ _
    · exact sym _ _ (S.hyp_orthX _ _).2
    · exact sym _ _ (S.hyp_orthz _).2
    · exact hfe _ _
    · exact S.hyp_ff _ _
  rw [hG, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply] at ha
  have hH : Hy.det * Hy.det = 1 := by
    rw [← Matrix.det_mul, Matrix.fromBlocks_multiply]
    simp
  exact ⟨a, _, hH, ha⟩

/- English proof (translation)
Take `⟨a, ε, hH, ha⟩` from `det_Y_zero D.sp`. Establish `hN : IsN D ε`. Break down `mul_self_eq_one_iff.1 hH with h | h` into its components or cases. Rewrite using `[h]`. Simplify using `using isN_star (D := D) 1`.

Rewrite using `[h]`. Conclude with `isN_neg_one`. Establish `h0` using `(GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (D.sp.X 0)).ne_zero`. Use `((((isN_star a).mul (isN_det (D.sp.Y 0))).mul ((isN_det (D.sp.X 0)).inv (star_det _))).mul isN_neg_one).mul hN` as an intermediate fact. Rewrite `this` using `[← ha]`.

Establish `e : ∀ x t : D.host.E, x ≠ 0 → x * (-t * ε) * x⁻¹ * -1 * ε = t` using `fun x t hx => by`. Clear the denominators using the available nonvanishing facts. Take the linear combination `t * hH`. Rewrite `this` using `[e _ _ h0]`. Then use the resulting hypothesis.
-/
theorem isNormFromTensorFiniteAdele_levelNormT : IsN D (D.sp.T : D.host.E) := by
  obtain ⟨a, ε, hH, ha⟩ := det_Y_zero D.sp
  have hN : IsN D ε := by
    rcases mul_self_eq_one_iff.1 hH with h | h
    · rw [h]; simpa using isN_star (D := D) 1
    · rw [h]; exact isN_neg_one
  have h0 := (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (D.sp.X 0)).ne_zero
  have := ((((isN_star a).mul (isN_det (D.sp.Y 0))).mul ((isN_det (D.sp.X 0)).inv (star_det _))).mul isN_neg_one).mul hN
  rw [← ha] at this
  have e : ∀ x t : D.host.E, x ≠ 0 → x * (-t * ε) * x⁻¹ * -1 * ε = t := fun x t hx => by
    field_simp
    linear_combination t * hH
  rwa [e _ _ h0] at this

end Global

end GlobalTheory.DetNorm

end
