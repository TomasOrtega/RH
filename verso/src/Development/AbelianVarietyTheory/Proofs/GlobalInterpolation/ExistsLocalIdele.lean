import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Ker
open TensorProduct Formalism.UG Formalism.UG.P

noncomputable section

namespace GlobalTheory.UnifConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h1 : P.intValuation b ≤ WithZero.exp (-((1 : ℕ) : ℤ))`. Rewrite using `[P.intValuation_le_pow_iff_mem]`. Simplify using `using hb`. Establish `h2 : WithZero.exp (-((2 : ℕ) : ℤ)) < P.intValuation b`. Rewrite using `[← not_le, P.intValuation_le_pow_iff_mem]`.

Conclude with `hb2`. Establish `h0 : P.intValuation b ≠ 0` using `(lt_of_le_of_lt zero_le h2).ne'`. Establish `h3 : P.intValuation b = WithZero.exp (-1 : ℤ)`. Rewrite `h1`, `h2`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h1` using `[WithZero.exp_le_exp]`.

Rewrite `h2` using `[WithZero.exp_lt_exp]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `h4` using `GlobalTheory.SuppIdele.val_algebraMap P b`. Rewrite using `[← h3, ← h4]`.

Conclude with `Valuation.map_eq_of_sub_lt _ (by rw [h4]; exact lt_of_le_of_lt h h2)`.
-/
theorem val_of_cong (P : HeightOneSpectrum (𝓞 E)) (x : P.adicCompletion E) (b : 𝓞 E) (hb : b ∈ P.asIdeal)
    (hb2 : b ∉ P.asIdeal ^ 2) (h : Valued.v (x - algebraMap E _ (b : E)) ≤ WithZero.exp (-((2 : ℕ) : ℤ))) :
    Valued.v x = WithZero.exp (-1 : ℤ) := by
  have h1 : P.intValuation b ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [P.intValuation_le_pow_iff_mem]; simpa using hb
  have h2 : WithZero.exp (-((2 : ℕ) : ℤ)) < P.intValuation b := by
    rw [← not_le, P.intValuation_le_pow_iff_mem]; exact hb2
  have h0 : P.intValuation b ≠ 0 := (lt_of_le_of_lt zero_le h2).ne'
  have h3 : P.intValuation b = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log h0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1
    rw [WithZero.exp_lt_exp] at h2
    congr 1
    omega
  have h4 := GlobalTheory.SuppIdele.val_algebraMap P b
  rw [← h3, ← h4]
  exact Valuation.map_eq_of_sub_lt _ (by rw [h4]; exact lt_of_le_of_lt h h2)

section

variable (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (h1 : ∀ x : E, ι (x ⊗ₜ[F] 1) = algebraMap E _ x)
  (h2 : ∀ y, y ∈ RInt F E ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι y P) ≤ 1)
  (h3 : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ),
    y ∈ Formalism.L2.DIV.suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → ι (y : AfE F E) P = 1)

include h1 in
/- English proof (translation)
Rewrite using `[GlobalTheory.SuppIdele.coe_toRInt, h1]`. Both sides reduce to the same expression.
-/
theorem iota_toRInt (b : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) :
    ι (toRInt F E b : AfE F E) P = algebraMap E _ (b : E) := by
  rw [GlobalTheory.SuppIdele.coe_toRInt, h1]; rfl

include h1 h2 in
/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`. Rewrite using `[iota_toRInt ι h1, GlobalTheory.SuppIdele.val_algebraMap, P.intValuation_le_pow_iff_mem]`. Conclude with `hb`.

Consider the case `zero`. Rewrite using `[Subring.coe_zero, map_zero, afsplit_zero_apply, map_zero]`. Conclude with `zero_le`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Subring.coe_add, map_add, afsplit_add_apply]`.

Conclude with `Valuation.map_add_le _ hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[smul_eq_mul, Subring.coe_mul, map_mul, afsplit_mul_apply, map_mul]`. Conclude with `(mul_le_of_le_one_left' ((h2 _).1 a.2 P)).trans hx`.
-/
theorem val_le_of_mem (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z : RInt F E)
    (hz : z ∈ (P.asIdeal ^ n).map (toRInt F E)) : Valued.v (ι (z : AfE F E) P) ≤ WithZero.exp (-(n : ℤ)) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [iota_toRInt ι h1, GlobalTheory.SuppIdele.val_algebraMap, P.intValuation_le_pow_iff_mem]
    exact hb
  | zero =>
    rw [Subring.coe_zero, map_zero, afsplit_zero_apply, map_zero]; exact zero_le
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add, afsplit_add_apply]
    exact Valuation.map_add_le _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, afsplit_mul_apply, map_mul]
    exact (mul_le_of_le_one_left' ((h2 _).1 a.2 P)).trans hx

include h2 in
/- English proof (translation)
Establish `key : ∀ a b : (AfE F E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι (a : AfE F E) P) = Valued.v (ι (b : AfE F E) P)) → ((a * b⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E`. Introduce `a b hab`. Rewrite using `[h2]`. Introduce `P`. Rewrite using `[Units.val_mul, map_mul, afsplit_mul_apply, map_mul, hab, ← map_mul, ← afsplit_mul_apply, ← map_mul, Units.mul_inv, map_one, afsplit_one_apply, map_one]`.

Establish `hm : y * y'⁻¹ ∈ inertAt E v`. Establish `k2 : (((y * y'⁻¹)⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E`. Rewrite using `[mul_inv_rev, inv_inv]`. Conclude with `key y' y fun P => (h P).symm`. Conclude with `Subgroup.mem_inf.2 ⟨⟨key y y' h, k2⟩, mul_mem hy (inv_mem hy')⟩`.

Use `hξ hm` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]`. Then use the resulting hypothesis.
-/
theorem eq_of_val {K : Type} [Field K] (ξ : Chr F E K) (v : HeightOneSpectrum (𝓞 F)) (hξ : inertAt E v ≤ ξ.ker)
    (y y' : (AfE F E)ˣ) (hy : y ∈ Formalism.L2.DIV.suppAt E v) (hy' : y' ∈ Formalism.L2.DIV.suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι (y : AfE F E) P) = Valued.v (ι (y' : AfE F E) P)) :
    ξ y = ξ y' := by
  have key : ∀ a b : (AfE F E)ˣ,
      (∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι (a : AfE F E) P) = Valued.v (ι (b : AfE F E) P)) →
      ((a * b⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
    intro a b hab
    rw [h2]
    intro P
    rw [Units.val_mul, map_mul, afsplit_mul_apply, map_mul, hab, ← map_mul, ← afsplit_mul_apply, ← map_mul,
      Units.mul_inv, map_one, afsplit_one_apply, map_one]
  have hm : y * y'⁻¹ ∈ inertAt E v := by
    have k2 : (((y * y'⁻¹)⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
      rw [mul_inv_rev, inv_inv]
      exact key y' y fun P => (h P).symm
    exact Subgroup.mem_inf.2 ⟨⟨key y y' h, k2⟩, mul_mem hy (inv_mem hy')⟩
  have := hξ hm
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this

include h1 h2 in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `val_le_of_mem ι h1 h2 P 2 _ hc` as an intermediate fact. Rewrite `this` using `[AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, iota_toRInt ι h1]`. Conclude with `val_of_cong P _ b hb hb2 this`. Introduce `Q hQ`.

Use `val_le_of_mem ι h1 h2 Q 1 _ (by rw [pow_one]; exact hc' Q hQ)` as an intermediate fact. Rewrite `this` using `[AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, Subring.coe_one, map_one, afsplit_one_apply]`. Rewrite using `[← map_one (Valued.v : Valuation (Q.adicCompletion E) _)]`. Use `Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt this ?_)` and prove the remaining obligations. Rewrite using `[map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Evaluate the numerical expressions.
-/
theorem val_of_unif (P : HeightOneSpectrum (𝓞 E)) (y₀ : RInt F E) (b : 𝓞 E) (hb : b ∈ P.asIdeal)
    (hb2 : b ∉ P.asIdeal ^ 2) (hc : y₀ - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (hc' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E)) :
    Valued.v (ι (y₀ : AfE F E) P) = WithZero.exp (-1 : ℤ) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Valued.v (ι (y₀ : AfE F E) Q) = 1 := by
  constructor
  · have := val_le_of_mem ι h1 h2 P 2 _ hc
    rw [AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, iota_toRInt ι h1] at this
    exact val_of_cong P _ b hb hb2 this
  · intro Q hQ
    have := val_le_of_mem ι h1 h2 Q 1 _ (by rw [pow_one]; exact hc' Q hQ)
    rw [AddSubgroupClass.coe_sub, map_sub, afsplit_sub_apply, Subring.coe_one, map_one, afsplit_one_apply] at this
    rw [← map_one (Valued.v : Valuation (Q.adicCompletion E) _)]
    refine Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt this ?_)
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

include h1 h2 in

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by`. Use `Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1` as an intermediate fact. Simplify using `using this`. Take `⟨y, y₀, e1, e2, e3, e4⟩` from `GlobalTheory.SuppIdele.exists_supported_idele F E P v b hP`. Establish `hv` using `val_of_unif ι h1 h2 P y₀ b hb hb2 e3 e4`.

Rewrite `hv` using `[e1]`. Use `⟨y, e2, hv.1, hv.2, ?_⟩` and prove the remaining obligations. Establish `hex : ∃ k, IsUnifVal ξ P k`. Use `⟨ξ y, fun w hw z z₀ c f1 hc hc2 f2 f3 f4 => ?_⟩` and prove the remaining obligations. Take `rfl : w = v` from `HeightOneSpectrum.ext (hw.symm.trans hP)`.

Establish `hz` using `val_of_unif ι h1 h2 P z₀ c hc hc2 f3 f4`. Rewrite `hz` using `[f1]`. Use `eq_of_val ι h2 ξ w hξ z y f2 e2 fun Q => ?_` and prove the remaining obligations. Distinguish the cases in `hQ : Q = P`. Rewrite using `[hQ, hz.1, hv.1]`.

Rewrite using `[hz.2 Q hQ, hv.2 Q hQ]`. Unfold `unifVal`. Rewrite using `[dif_pos hex]`. Conclude with `(hex.choose_spec v hP y y₀ b e1 hb hb2 e2 e3 e4).symm`.
-/
theorem exists_unif {K : Type} [Field K] (ξ : Chr F E K) (v : HeightOneSpectrum (𝓞 F)) (hξ : inertAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ y ∈ Formalism.L2.DIV.suppAt E v, Valued.v (ι (y : AfE F E) P) = WithZero.exp (-1 : ℤ) ∧
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Valued.v (ι (y : AfE F E) Q) = 1) ∧ unifVal ξ P = ξ y := by
  obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
    have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
    simpa using this
  obtain ⟨y, y₀, e1, e2, e3, e4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P v b hP
  have hv := val_of_unif ι h1 h2 P y₀ b hb hb2 e3 e4
  rw [e1] at hv
  refine ⟨y, e2, hv.1, hv.2, ?_⟩
  have hex : ∃ k, IsUnifVal ξ P k := by
    refine ⟨ξ y, fun w hw z z₀ c f1 hc hc2 f2 f3 f4 => ?_⟩
    obtain rfl : w = v := HeightOneSpectrum.ext (hw.symm.trans hP)
    have hz := val_of_unif ι h1 h2 P z₀ c hc hc2 f3 f4
    rw [f1] at hz
    refine eq_of_val ι h2 ξ w hξ z y f2 e2 fun Q => ?_
    by_cases hQ : Q = P
    · rw [hQ, hz.1, hv.1]
    · rw [hz.2 Q hQ, hv.2 Q hQ]
  unfold unifVal
  rw [dif_pos hex]
  exact (hex.choose_spec v hP y y₀ b e1 hb hb2 e2 e3 e4).symm

end

/- English proof (translation)
Establish `hle : v.asIdeal ≤ P.asIdeal.under (𝓞 F)`. Rewrite using `[Ideal.under, ← Ideal.map_le_iff_le_comap, h]`. Conclude with `fun t ht => (Ideal.mul_le_inf ht).1`. Conclude with `(v.isMaximal.eq_of_le (P.under (𝓞 F)).isPrime.ne_top hle).symm`.
-/
theorem under_eq (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (J : Ideal (𝓞 E))
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * J) : P.asIdeal.under (𝓞 F) = v.asIdeal := by
  have hle : v.asIdeal ≤ P.asIdeal.under (𝓞 F) := by
    rw [Ideal.under, ← Ideal.map_le_iff_le_comap, h]; exact fun t ht => (Ideal.mul_le_inf ht).1
  exact (v.isMaximal.eq_of_le (P.under (𝓞 F)).isPrime.ne_top hle).symm

/- English proof (translation)
Establish `hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal` using `by rw [h]; exact fun t ht => (Ideal.mul_le_inf ht).1`. Use `⟨hle (Ideal.mem_map_of_mem _ ha), fun hm => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {a}` from `Ideal.dvd_span_singleton.2 ha`. Establish `hJv : ¬ J ≤ v.asIdeal` using `fun hh => ha2 (by`. Rewrite using `[← Ideal.span_singleton_le_iff_mem, hJ, pow_two]`.

Conclude with `Ideal.mul_mono_right hh)`. Establish `hE` using `congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hJ`. Rewrite `hE` using `[Ideal.map_span, Set.image_singleton, Ideal.map_mul, h]`. Rewrite `hm` using `[← Ideal.dvd_span_singleton, hE, pow_two, mul_assoc, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le]`. Break down `P.isPrime.mul_le.1 hm with h' | h'` into its components or cases.

Conclude with `hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h')).symm`. Apply `hJv` to reduce the goal to its premises. Rewrite using `[← under_eq v P _ h]`. Conclude with `Ideal.map_le_iff_le_comap.1 h'`.
-/
theorem unif_notMem (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P')
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (a : 𝓞 F) (ha : a ∈ v.asIdeal)
    (ha2 : a ∉ v.asIdeal ^ 2) :
    algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) a ∉ P.asIdeal ^ 2 := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by rw [h]; exact fun t ht => (Ideal.mul_le_inf ht).1
  refine ⟨hle (Ideal.mem_map_of_mem _ ha), fun hm => ?_⟩
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {a} := Ideal.dvd_span_singleton.2 ha
  have hJv : ¬ J ≤ v.asIdeal := fun hh => ha2 (by
    rw [← Ideal.span_singleton_le_iff_mem, hJ, pow_two]; exact Ideal.mul_mono_right hh)
  have hE := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 E))) hJ
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_mul, h] at hE
  rw [← Ideal.dvd_span_singleton, hE, pow_two, mul_assoc, mul_dvd_mul_iff_left P.ne_bot, Ideal.dvd_iff_le] at hm
  rcases P.isPrime.mul_le.1 hm with h' | h'
  · exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top h')).symm
  · apply hJv
    rw [← under_eq v P _ h]
    exact Ideal.map_le_iff_le_comap.1 h'

/- English proof (translation)
Establish `hs : ∀ c : F, (1 + afsplitI v (algebraMap F _ c - 1)) v = algebraMap F _ c` using `fun c => by`. Rewrite using `[afsplit_add_apply, afsplitI_self, afsplit_one_apply, add_sub_cancel]`. Establish `hn : ∀ (c : F) w, w ≠ v → (1 + afsplitI v (algebraMap F _ c - 1)) w = 1` using `fun c w hw => by`. Rewrite using `[afsplit_add_apply, afsplitI_ne v w hw, afsplit_one_apply, add_zero]`. Establish `hm : (1 + afsplitI v (algebraMap F _ a - 1)) * (1 + afsplitI v (algebraMap F _ a⁻¹ - 1)) = 1`.

Use `FiniteAdeleRing.ext _ fun w => ?_` and prove the remaining obligations. Rewrite using `[afsplit_mul_apply, afsplit_one_apply]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[hs, hs, ← map_mul, mul_inv_cancel₀ ha, map_one]`.

Rewrite using `[hn _ w hw, hn _ w hw, one_mul]`. Conclude with `⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, hs a, hn a⟩`.
-/
theorem exists_local_idele (v : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0) :
    ∃ x : (FiniteAdeleRing (𝓞 F) F)ˣ, (x : FiniteAdeleRing (𝓞 F) F) v = algebraMap F _ a ∧
      ∀ w, w ≠ v → (x : FiniteAdeleRing (𝓞 F) F) w = 1 := by
  have hs : ∀ c : F, (1 + afsplitI v (algebraMap F _ c - 1)) v = algebraMap F _ c := fun c => by
    rw [afsplit_add_apply, afsplitI_self, afsplit_one_apply, add_sub_cancel]
  have hn : ∀ (c : F) w, w ≠ v → (1 + afsplitI v (algebraMap F _ c - 1)) w = 1 := fun c w hw => by
    rw [afsplit_add_apply, afsplitI_ne v w hw, afsplit_one_apply, add_zero]
  have hm : (1 + afsplitI v (algebraMap F _ a - 1)) * (1 + afsplitI v (algebraMap F _ a⁻¹ - 1)) = 1 := by
    refine FiniteAdeleRing.ext _ fun w => ?_
    rw [afsplit_mul_apply, afsplit_one_apply]
    by_cases hw : w = v
    · subst hw
      rw [hs, hs, ← map_mul, mul_inv_cancel₀ ha, map_one]
    · rw [hn _ w hw, hn _ w hw, one_mul]
  exact ⟨⟨_, _, hm, by rw [mul_comm, hm]⟩, hs a, hn a⟩

/- English proof (translation)
Take `⟨ι, h1, h2, h3, h4⟩` from `GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E`. Establish `h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P'.asIdeal * P.asIdeal` using `by rw [h, mul_comm]`. Establish `hP` using `under_eq v P _ h`. Establish `hP'` using `under_eq v P' _ h'`. Take `⟨y, y1, y2, y3, y4⟩` from `exists_unif ι h1 h2 ξ v hξ P hP`.

Take `⟨z, z1, z2, z3, z4⟩` from `exists_unif ι h1 h2 ξ v hξ P' hP'`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, ha2⟩ : ∃ b ∈ v.asIdeal, b ∉ v.asIdeal ^ 2 := by`. Use `Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1` as an intermediate fact. Simplify using `using this`. Establish `ha0 : (a : F) ≠ 0`.

Establish `: a ≠ 0` using `by rintro rfl; exact ha2 (zero_mem _)`. Simplify using `using this`. Take `⟨x, x1, x2⟩` from `exists_local_idele v (a : F) ha0`. Establish `hxs : idF F E x ∈ Formalism.L2.DIV.suppAt E v`. Simplify using `only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]`.

Introduce `w hw`. Apply `Units.ext` to reduce the goal to its premises. Use `show prV (E := E) w ((1 : E) ⊗ₜ[F] (x : FiniteAdeleRing (𝓞 F) F)) = 1`. Rewrite using `[afsplit_prV_tmul, x2 w hw]`. Both sides reduce to the same expression.

Establish `hxv : ∀ Q Q' : HeightOneSpectrum (𝓞 E), Q ≠ Q' → Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal → Valued.v (ι (idF F E x : AfE F E) Q) = WithZero.exp (-1 : ℤ)`. Introduce `Q Q' hQ hm`. Take `⟨m1, m2⟩` from `unif_notMem v Q Q' hQ hm a ha ha2`. Establish `hu : Q.under (𝓞 F) = v` using `HeightOneSpectrum.ext (under_eq v Q _ hm)`. Use `val_of_cong Q _ _ m1 m2 (h4 x (a : F) Q 2 ?_)` and prove the remaining obligations.

Substitute `hu` using the available equality. Rewrite using `[x1, sub_self, map_zero]`. Conclude with `zero_le`. Establish `hyz : ξ (y * z) = ξ (idF F E x)`. Use `eq_of_val ι h2 ξ v hξ _ _ (mul_mem y1 z1) hxs fun Q => ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, map_mul, afsplit_mul_apply, map_mul]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[y2, z3 Q hne, mul_one, hxv Q P' hne h]`. Distinguish the cases in `hQ' : Q = P'`.

Substitute `hQ'` using the available equality. Rewrite using `[z2, y3 Q hQ, one_mul, hxv Q P hQ h']`. Rewrite using `[y3 Q hQ, z3 Q hQ', one_mul, (h3 v _).1 hxs Q, map_one]`. Introduce `hu`. Establish `hle : P.asIdeal * P'.asIdeal ≤ Q.asIdeal`.

Rewrite using `[← h, ← hu]`. Conclude with `Ideal.map_comap_le`. Break down `Q.isPrime.mul_le.1 hle with k | k` into its components or cases. Conclude with `hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top k)).symm`. Conclude with `hQ' (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top k)).symm`.

Establish `hx1 : ξ (idF F E x) = 1` using `hF ⟨x, rfl⟩`. Rewrite `hyz` using `[hx1, map_mul]`. Rewrite using `[y4, z4]`. Conclude with `eq_inv_of_mul_eq_one_right hyz`.
-/
theorem unifVal_conj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K]
    (ξ : Chr F E K) (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E))
    (hF : (idF F E).range ≤ ξ.ker) (hξ : inertAt E v ≤ ξ.ker) (hne : P ≠ P')
    (h : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    unifVal ξ P' = (unifVal ξ P)⁻¹ := by
  obtain ⟨ι, h1, h2, h3, h4⟩ := GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P'.asIdeal * P.asIdeal := by rw [h, mul_comm]
  have hP := under_eq v P _ h
  have hP' := under_eq v P' _ h'
  obtain ⟨y, y1, y2, y3, y4⟩ := exists_unif ι h1 h2 ξ v hξ P hP
  obtain ⟨z, z1, z2, z3, z4⟩ := exists_unif ι h1 h2 ξ v hξ P' hP'
  obtain ⟨a, ha, ha2⟩ : ∃ b ∈ v.asIdeal, b ∉ v.asIdeal ^ 2 := by
    have := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
    simpa using this
  have ha0 : (a : F) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
    simpa using this
  obtain ⟨x, x1, x2⟩ := exists_local_idele v (a : F) ha0
  have hxs : idF F E x ∈ Formalism.L2.DIV.suppAt E v := by
    simp only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w hw
    apply Units.ext
    show prV (E := E) w ((1 : E) ⊗ₜ[F] (x : FiniteAdeleRing (𝓞 F) F)) = 1
    rw [afsplit_prV_tmul, x2 w hw]; rfl
  have hxv : ∀ Q Q' : HeightOneSpectrum (𝓞 E), Q ≠ Q' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal →
      Valued.v (ι (idF F E x : AfE F E) Q) = WithZero.exp (-1 : ℤ) := by
    intro Q Q' hQ hm
    obtain ⟨m1, m2⟩ := unif_notMem v Q Q' hQ hm a ha ha2
    have hu : Q.under (𝓞 F) = v := HeightOneSpectrum.ext (under_eq v Q _ hm)
    refine val_of_cong Q _ _ m1 m2 (h4 x (a : F) Q 2 ?_)
    subst hu
    rw [x1, sub_self, map_zero]; exact zero_le
  have hyz : ξ (y * z) = ξ (idF F E x) := by
    refine eq_of_val ι h2 ξ v hξ _ _ (mul_mem y1 z1) hxs fun Q => ?_
    rw [Units.val_mul, map_mul, afsplit_mul_apply, map_mul]
    by_cases hQ : Q = P
    · subst hQ
      rw [y2, z3 Q hne, mul_one, hxv Q P' hne h]
    by_cases hQ' : Q = P'
    · subst hQ'
      rw [z2, y3 Q hQ, one_mul, hxv Q P hQ h']
    rw [y3 Q hQ, z3 Q hQ', one_mul, (h3 v _).1 hxs Q, map_one]
    intro hu
    have hle : P.asIdeal * P'.asIdeal ≤ Q.asIdeal := by
      rw [← h, ← hu]; exact Ideal.map_comap_le
    rcases Q.isPrime.mul_le.1 hle with k | k
    · exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top k)).symm
    · exact hQ' (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le Q.isPrime.ne_top k)).symm
  have hx1 : ξ (idF F E x) = 1 := hF ⟨x, rfl⟩
  rw [hx1, map_mul] at hyz
  rw [y4, z4]
  exact eq_inv_of_mul_eq_one_right hyz

end GlobalTheory.UnifConj
