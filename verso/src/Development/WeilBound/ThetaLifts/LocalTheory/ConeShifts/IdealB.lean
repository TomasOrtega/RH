import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.IdealA

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Id

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes WithZero
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Idele
open Formalism.L2.Host (IsUnitAt IsUnifAt atFin unif unif_spec)
open FractionalIdeal (count)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.StdDual (codiff codiff_ne_zero)

/- English proof (translation)
Establish `hc` using `h.2.1`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩`. Set `s : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (by ext y; simp [PositivityTheory.ThK.Vac.sigma_sigma h]) (by ext y; simp [PositivityTheory.ThK.Vac.sigma_sigma h])`. Establish `hs : (1 : E ≃ₐ[F] E) ≠ s`. Introduce `h1`.

Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `IsTotallyComplex.complexEmbedding_not_isReal τ ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `y`. Establish `h2 : σ y = y` using `(DFunLike.congr_fun h1 y).symm`.

Use `h.2.2.2 τ y` as an intermediate fact. Rewrite `this` using `[h2]`. Simplify using `using this.symm`. Establish `hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s}`. Use `symm`.

Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1]`. Rewrite using `[trace_eq_sum_automorphisms, hu, Finset.sum_pair hs]`. Both sides reduce to the same expression.
-/
theorem add_sigma (h : IsCMExt F E σ) (x : E) : x + σ x = algebraMap F E (Algebra.trace F E x) := by
  classical
  have hc := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (by ext y; simp [PositivityTheory.ThK.Vac.sigma_sigma h]) (by ext y; simp [PositivityTheory.ThK.Vac.sigma_sigma h])
  have hs : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h1
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have h2 : σ y = y := (DFunLike.congr_fun h1 y).symm
    have := h.2.2.2 τ y
    rw [h2] at this
    simpa using this.symm
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1]
  rw [trace_eq_sum_automorphisms, hu, Finset.sum_pair hs]
  rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Conclude with `⟨a + b, by rw [map_add, map_add, ← ha, ← hb]; ring⟩`. Consider the case `tmul a e`. Use `⟨Algebra.trace F E e • a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] e + a ⊗ₜ[F] σ e = (Algebra.trace F E e • a) ⊗ₜ[F] (1 : E)`. Rewrite using `[← TensorProduct.tmul_add, add_sigma h, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem add_cA (h : IsCMExt F E σ) (z : AE F E) : ∃ a : AF F, z + cA σ z = algebraMap (AF F) (AE F E) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ← ha, ← hb]; ring⟩
  | tmul a e =>
    refine ⟨Algebra.trace F E e • a, ?_⟩
    change a ⊗ₜ[F] e + a ⊗ₜ[F] σ e = (Algebra.trace F E e • a) ⊗ₜ[F] (1 : E)
    rw [← TensorProduct.tmul_add, add_sigma h, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Take `⟨a, ha⟩` from `add_cA h z`. Use `⟨⅟(2 : AF F) * a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← ha, hz, ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one, one_mul]`.
-/
theorem fixed_cA (h : IsCMExt F E σ) {z : AE F E} (hz : cA σ z = z) : ∃ a : AF F, z = algebraMap (AF F) (AE F E) a := by
  obtain ⟨a, ha⟩ := add_cA h z
  refine ⟨⅟(2 : AF F) * a, ?_⟩
  rw [map_mul, ← ha, hz, ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self,
    map_one, one_mul]

/- English proof (translation)
Establish `hσ` using `PositivityTheory.ThK.Vac.cA_cA (F := F) (PositivityTheory.ThK.Vac.sigma_sigma h)`. Use `set y := z * Units.map (cA σ : AE F E →* AE F E) z with hy`. Establish `f : ∀ u : (AE F E)ˣ, cA σ ((u * Units.map (cA σ : AE F E →* AE F E) u : (AE F E)ˣ) : AE F E) = (u * Units.map (cA σ : AE F E →* AE F E) u : (AE F E)ˣ)` using `fun u => by`. Express the relevant statement in the definitionally equal form `cA σ (u * cA σ u) = u * cA σ u`. Rewrite using `[map_mul, hσ, mul_comm]`.

Take `⟨a, ha⟩` from `fixed_cA h (f z)`. Take `⟨b, hb⟩` from `fixed_cA h (f z⁻¹)`. Establish `hab : a * b = 1`. Apply `Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E) (algebraMap F E).injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (AF F) (AE F E) (a * b) = algebraMap (AF F) (AE F E) 1`.

Rewrite using `[map_mul, ← ha, ← hb, map_one, ← Units.val_mul, map_inv, ← mul_inv, mul_inv_cancel, Units.val_one]`. Establish `: y = ideleMap F E ⟨a, b, hab, (mul_comm b a).trans hab⟩` using `Units.ext ha`. Establish `h2` using `hν ⟨a, b, hab, (mul_comm b a).trans hab⟩`. Rewrite `h2` using `[← this, hy, map_mul]`. Conclude with `eq_inv_of_mul_eq_one_right h2`.
-/
theorem nu_conj (h : IsCMExt F E σ) {ν : Chr F E} (hν : ∀ a : (AF F)ˣ, ν (ideleMap F E a) = 1) (z : (AE F E)ˣ) :
    ν (Units.map (cA σ : AE F E →* AE F E) z) = (ν z)⁻¹ := by
  have hσ := PositivityTheory.ThK.Vac.cA_cA (F := F) (PositivityTheory.ThK.Vac.sigma_sigma h)
  set y := z * Units.map (cA σ : AE F E →* AE F E) z with hy
  have f : ∀ u : (AE F E)ˣ, cA σ ((u * Units.map (cA σ : AE F E →* AE F E) u : (AE F E)ˣ) : AE F E) =
      (u * Units.map (cA σ : AE F E →* AE F E) u : (AE F E)ˣ) := fun u => by
    change cA σ (u * cA σ u) = u * cA σ u
    rw [map_mul, hσ, mul_comm]
  obtain ⟨a, ha⟩ := fixed_cA h (f z)
  obtain ⟨b, hb⟩ := fixed_cA h (f z⁻¹)
  have hab : a * b = 1 := by
    apply Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E) (algebraMap F E).injective
    change algebraMap (AF F) (AE F E) (a * b) = algebraMap (AF F) (AE F E) 1
    rw [map_mul, ← ha, ← hb, map_one, ← Units.val_mul, map_inv, ← mul_inv, mul_inv_cancel, Units.val_one]
  have : y = ideleMap F E ⟨a, b, hab, (mul_comm b a).trans hab⟩ := Units.ext ha
  have h2 := hν ⟨a, b, hab, (mul_comm b a).trans hab⟩
  rw [← this, hy, map_mul] at h2
  exact eq_inv_of_mul_eq_one_right h2

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero (α := FI E))]`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Take `⟨q, hq⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (h o)`.

Use `⟨q, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, Algebra.traceForm_apply, mul_comm]`. Introduce `h o`. Take `⟨q, hq⟩` from `h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)`. Rewrite `hq` using `[Algebra.traceForm_apply]`.

Rewrite using `[mul_comm]`. Establish `: Algebra.trace ℚ E (z * (o : E)) = algebraMap ℤ ℚ q` using `by rw [hq]`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.
-/
theorem inD_iff (z : E) : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * z))) ↔ z ∈ codiff E := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FI E))]
  constructor
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨q, hq⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 (h o)
    refine ⟨q, ?_⟩
    rw [hq, Algebra.traceForm_apply, mul_comm]
  · intro h o
    obtain ⟨q, hq⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply] at hq
    rw [mul_comm]
    have : Algebra.trace ℚ E (z * (o : E)) = algebraMap ℤ ℚ q := by rw [hq]
    rw [this]; exact isIntegral_algebraMap

/- English proof (translation)
Take `⟨s, hs, es⟩` from `exists_mem_valuation_eq hI v`. Take `⟨t, ht, et⟩` from `exists_mem_valuation_eq (inv_ne_zero hI) v`. Establish `a1` using `(mem_iff_valuation_le hJ _).1 (h1 s hs) w`. Establish `a2` using `(mem_iff_valuation_le (inv_ne_zero hJ) _).1 (h2 t ht) w`. Rewrite `a2`, `et` using `[FractionalIdeal.count_inv, neg_neg]`.

Establish `a3 : w.valuation L (f s) * w.valuation L (f t) = 1`. Rewrite using `[← map_mul, ← map_mul, hm (s * t) 1 (by rw [map_mul, es, et, ← exp_add, map_one]; simp), map_one, map_one]`. Rewrite using `[hm x s (hx.trans es.symm)]`. Use `le_antisymm a1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_count_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] {I : FI K} {J : FI L} (hI : I ≠ 0) (hJ : J ≠ 0)
    (f : K →+* L) (h1 : ∀ t ∈ I, f t ∈ J) (h2 : ∀ t ∈ I⁻¹, f t ∈ J⁻¹) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hm : ∀ s t, v.valuation K s = v.valuation K t → w.valuation L (f s) = w.valuation L (f t)) {x : K}
    (hx : v.valuation K x = exp (-count K v I)) : w.valuation L (f x) = exp (-count L w J) := by
  obtain ⟨s, hs, es⟩ := exists_mem_valuation_eq hI v
  obtain ⟨t, ht, et⟩ := exists_mem_valuation_eq (inv_ne_zero hI) v
  have a1 := (mem_iff_valuation_le hJ _).1 (h1 s hs) w
  have a2 := (mem_iff_valuation_le (inv_ne_zero hJ) _).1 (h2 t ht) w
  rw [FractionalIdeal.count_inv, neg_neg] at a2 et
  have a3 : w.valuation L (f s) * w.valuation L (f t) = 1 := by
    rw [← map_mul, ← map_mul, hm (s * t) 1 (by rw [map_mul, es, et, ← exp_add, map_one]; simp), map_one, map_one]
  rw [hm x s (hx.trans es.symm)]
  refine le_antisymm a1 ?_
  calc exp (-count L w J) = exp (-count L w J) * (w.valuation L (f s) * w.valuation L (f t)) := by rw [a3, mul_one]
    _ ≤ exp (-count L w J) * (w.valuation L (f s) * exp (count L w J)) := by gcongr
    _ = _ := by rw [mul_left_comm, ← exp_add]; simp

/- English proof (translation)
Use `exp_count_eq codiff_ne_zero codiff_ne_zero (algebraMap F E) (fun t ht => ?_) (fun t ht => ?_) (fun s t e => by rw [valuation_up rfl, valuation_up rfl, e]) hx` and prove the remaining obligations. Use `(inD_iff _).1 fun o => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.trace_trace (S := F), mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`. Conclude with `(inD_iff t).2 ht ⟨Algebra.trace F E o, Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)⟩`. Establish `: Module.Finite (𝓞 F) (𝓞 E)` using `Module.Finite.of_restrictScalars_finite ℤ _ _`.

Establish `htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤`. Assume the negation of the conclusion as `hn`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hn`. Conclude with `(not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)`. Establish `e` using `differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)`.

Rewrite `e` using `[htop, Ideal.top_mul]`. Rewrite `ht` using `[← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]`. Rewrite using `[← coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), e]`. Take `⟨c, hc, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 ht`. Conclude with `(FractionalIdeal.mem_coeIdeal _).2 ⟨algebraMap _ _ c, Ideal.mem_map_of_mem _ hc, rfl⟩`.
-/
theorem codiff_up (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {w : HeightOneSpectrum (𝓞 E)} {x : F}
    (hx : (w.under (𝓞 F)).valuation F x = exp (-count F (w.under (𝓞 F)) (codiff F))) :
    w.valuation E (algebraMap F E x) = exp (-count E w (codiff E)) := by
  refine exp_count_eq codiff_ne_zero codiff_ne_zero (algebraMap F E) (fun t ht => ?_) (fun t ht => ?_)
    (fun s t e => by rw [valuation_up rfl, valuation_up rfl, e]) hx
  · refine (inD_iff _).1 fun o => ?_
    rw [← Algebra.trace_trace (S := F), mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    exact (inD_iff t).2 ht ⟨Algebra.trace F E o, Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)⟩
  · have : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
    have htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
      by_contra hn
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
      exact (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)
    have e := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)
    rw [htop, Ideal.top_mul] at e
    rw [← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)] at ht
    rw [← coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), e]
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ht
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨algebraMap _ _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

/- English proof (translation)
Take `⟨t, ht, et⟩` from `exists_mem_valuation_eq (codiff_ne_zero (F := F)) v`. Establish `h1 : algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F` using `(h _).1 fun y hy => by`. Establish `hm : singleFin v (algebraMap F (Fv F v) t * y) ∈ adelicIdeal (codiff F)` using `fun u => by`. Distinguish the cases in `hu : u = v`. Substitute `hu` using the available equality.

Rewrite using `[show (singleFin u (algebraMap F (Fv F u) t * y)) u = _ from evalV_singleFin_self u _, mul_comm]`. Conclude with `(localIdeal u (codiff F)).smul_mem ⟨y, hy⟩ (Submodule.subset_span ⟨t, ht, rfl⟩)`. Rewrite using `[show (singleFin v (algebraMap F (Fv F v) t * y)) u = _ from evalV_singleFin_ne hu _]`. Conclude with `zero_mem _`. Use `(GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ) _).1 hm 1 fun u => one_mem _` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Conclude with `this`. Rewrite `h1` using `[HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, et, ← exp_zero, exp_le_exp]`. Establish `h2` using `(mem_iff_valuation_le (codiff_ne_zero (F := F)) 1).1 (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)) v`. Rewrite `h2` using `[map_one, ← exp_zero, exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem count_codiff_F {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (h : PsiUnr ψ v) : count F v (codiff F) = 0 := by
  obtain ⟨t, ht, et⟩ := exists_mem_valuation_eq (codiff_ne_zero (F := F)) v
  have h1 : algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F := (h _).1 fun y hy => by
    have hm : singleFin v (algebraMap F (Fv F v) t * y) ∈ adelicIdeal (codiff F) := fun u => by
      by_cases hu : u = v
      · subst hu
        rw [show (singleFin u (algebraMap F (Fv F u) t * y)) u = _ from evalV_singleFin_self u _, mul_comm]
        exact (localIdeal u (codiff F)).smul_mem ⟨y, hy⟩ (Submodule.subset_span ⟨t, ht, rfl⟩)
      · rw [show (singleFin v (algebraMap F (Fv F v) t * y)) u = _ from evalV_singleFin_ne hu _]
        exact zero_mem _
    have := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ) _).1 hm 1 fun u => one_mem _
    rw [one_mul] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, et, ← exp_zero, exp_le_exp] at h1
  have h2 := (mem_iff_valuation_le (codiff_ne_zero (F := F)) 1).1
    (FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)) v
  rw [map_one, ← exp_zero, exp_le_exp] at h2
  omega

/- English proof (translation)
Introduce `w hw` and use `by have := codiff_up hB.unram (w := w) (x := 1) (by rw [count_codiff_F hB.std (hB.psiP _ hw)]; simp) rw [map_one, map_one, ← exp_zero, exp_inj] at this omega`.
-/
theorem pr_codiff {B : Base F E} (hB : B.IsGood σ) : Pr B.P (codiff E) := fun w hw => by
  have := codiff_up hB.unram (w := w) (x := 1) (by rw [count_codiff_F hB.std (hB.psiP _ hw)]; simp)
  rw [map_one, map_one, ← exp_zero, exp_inj] at this
  omega

/- English proof (translation)
Establish `hf : {v : Pl F | count F v (codiff F) ≠ 0}.Finite` using `FractionalIdeal.finite_factors _`. Set `a : Pl F → Fˣ` to `fun v => unif v ^ count F v (codiff F)`. Establish `ha : ∀ v, v.valuation F (a v : F) = exp (-count F v (codiff F))` using `fun v => by`. Use `unif_spec v` as an intermediate fact. Unfold `IsUnifAt at this`.

Establish `e : v.valuation F (unif v : F) = exp (-1 : ℤ)` using `(valued_algebraMap v _).symm.trans this`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, e, ← exp_zsmul, smul_eq_mul, mul_neg, mul_one]`. Set `l : (AE F E)ˣ` to `∏ v ∈ hf.toFinset, ideleMap F E (Neutral.B1.localIdele F v (atFin v (a v)))`. Establish `hc : ∀ w : HeightOneSpectrum (𝓞 E), cp F w (l : AE F E) = if w.under (𝓞 F) ∈ hf.toFinset then algebraMap E _ (algebraMap F E (a (w.under (𝓞 F)))) else 1` using `fun w => by`. Rewrite using `[Units.coe_prod, map_prod]`.

Simplify using `only [ideleMap_localIdele, cp_prod, mem_aboveF]`. Rewrite using `[Finset.prod_ite_eq]`. Both sides reduce to the same expression. Establish `G : Gen B.P (codiff E) hf.toFinset l`. Use `⟨fun v hv hP => hf.mem_toFinset.1 hv (count_codiff_F hB.std (hB.psiP _ hP)), ?_, fun v hv => ext_cp (by rw [inf_idem, inf_idem]) fun w => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.coe_prod, map_prod]`. Conclude with `Finset.prod_eq_one fun v _ => by rw [ideleMap_localIdele, inf_prod]`. Distinguish the cases in `hw : w.under (𝓞 F) = v`. Rewrite using `[cp_idem hw, cp_idem hw, hc, if_neg (hw ▸ hv), map_one]`. Rewrite using `[cp_idem_ne hw, cp_idem_ne hw]`.

Rewrite using `[hc] split_ifs with hw`. Rewrite using `[valued_algebraMap]`. Conclude with `codiff_up hB.unram (ha _)`. Establish `h0 : count F (w.under (𝓞 F)) (codiff F) = 0` using `by by_contra hn; exact hw (hf.mem_toFinset.2 hn)`. Use `codiff_up hB.unram (w := w) (x := 1) (by rw [h0]; simp)` as an intermediate fact.

Rewrite `this` using `[map_one, map_one]`. Rewrite using `[map_one, this]`. Rewrite using `[← G.eq hu, map_prod, Finset.prod_eq_one fun v _ => hν _, map_one]`.
-/
theorem idealVal_codiff {B : Base F E} (hB : B.IsGood σ) {ν : Chr F E} (hν : ∀ a : (AF F)ˣ, ν (ideleMap F E a) = 1)
    (hu : UnrOff ν (B.P : Set (Pl F))) : idealVal ν (codiff E) = 1 := by
  classical
  have hf : {v : Pl F | count F v (codiff F) ≠ 0}.Finite := FractionalIdeal.finite_factors _
  let a : Pl F → Fˣ := fun v => unif v ^ count F v (codiff F)
  have ha : ∀ v, v.valuation F (a v : F) = exp (-count F v (codiff F)) := fun v => by
    have := unif_spec v
    unfold IsUnifAt at this
    have e : v.valuation F (unif v : F) = exp (-1 : ℤ) := (valued_algebraMap v _).symm.trans this
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, e, ← exp_zsmul, smul_eq_mul, mul_neg, mul_one]
  let l : (AE F E)ˣ := ∏ v ∈ hf.toFinset, ideleMap F E (Neutral.B1.localIdele F v (atFin v (a v)))
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), cp F w (l : AE F E) = if w.under (𝓞 F) ∈ hf.toFinset then algebraMap E _ (algebraMap F E (a (w.under (𝓞 F)))) else 1 := fun w => by
    rw [Units.coe_prod, map_prod]
    simp only [ideleMap_localIdele, cp_prod, mem_aboveF]
    rw [Finset.prod_ite_eq]
    rfl
  have G : Gen B.P (codiff E) hf.toFinset l := by
    refine ⟨fun v hv hP => hf.mem_toFinset.1 hv (count_codiff_F hB.std (hB.psiP _ hP)), ?_,
      fun v hv => ext_cp (by rw [inf_idem, inf_idem]) fun w => ?_, fun w => ?_⟩
    · rw [Units.coe_prod, map_prod]
      exact Finset.prod_eq_one fun v _ => by rw [ideleMap_localIdele, inf_prod]
    · by_cases hw : w.under (𝓞 F) = v
      · rw [cp_idem hw, cp_idem hw, hc, if_neg (hw ▸ hv), map_one]
      · rw [cp_idem_ne hw, cp_idem_ne hw]
    · rw [hc]
      split_ifs with hw
      · rw [valued_algebraMap]; exact codiff_up hB.unram (ha _)
      · have h0 : count F (w.under (𝓞 F)) (codiff F) = 0 := by by_contra hn; exact hw (hf.mem_toFinset.2 hn)
        have := codiff_up hB.unram (w := w) (x := 1) (by rw [h0]; simp)
        rw [map_one, map_one] at this
        rw [map_one, this]
  rw [← G.eq hu, map_prod, Finset.prod_eq_one fun v _ => hν _, map_one]

variable (hσ : ∀ x, σ (σ x) = x)

/- English proof (translation)
Take `⟨s, -, es⟩` from `exists_mem_valuation_eq h0 (splitPrime (τ.comp σ))`. Establish `e : ∀ s, (splitPrime τ).valuation E ((σ : E →+* E) s) = (splitPrime (τ.comp σ)).valuation E s` using `fun s => by`. Rewrite using `[← valued_apply_eq_valuation, ← valued_apply_eq_valuation]`. Both sides reduce to the same expression. Use `exp_count_eq h0 (cj_ne hσ h0) (σ : E →+* E) (fun t ht => (mem_cj hσ).2 (by rwa [RingHom.coe_coe, hσ])) (fun t ht => by rw [← cj_inv hσ h0]; exact (mem_cj hσ).2 (by rwa [RingHom.coe_coe, hσ])) (w := splitPrime τ) (fun s t h => by rw [e, e, h]) es` as an intermediate fact.

Rewrite `this` using `[e, es, exp_inj]`. Use linear arithmetic over natural numbers and integers.
-/
theorem count_bar {v : Pl F} (τ : E →ₐ[F] Fv F v) {𝔞 : FI E} (h0 : 𝔞 ≠ 0) :
    count E (splitPrime (τ.comp σ)) 𝔞 = count E (splitPrime τ) (cj hσ 𝔞) := by
  obtain ⟨s, -, es⟩ := exists_mem_valuation_eq h0 (splitPrime (τ.comp σ))
  have e : ∀ s, (splitPrime τ).valuation E ((σ : E →+* E) s) = (splitPrime (τ.comp σ)).valuation E s := fun s => by
    rw [← valued_apply_eq_valuation, ← valued_apply_eq_valuation]; rfl
  have := exp_count_eq h0 (cj_ne hσ h0) (σ : E →+* E) (fun t ht => (mem_cj hσ).2 (by rwa [RingHom.coe_coe, hσ]))
    (fun t ht => by rw [← cj_inv hσ h0]; exact (mem_cj hσ).2 (by rwa [RingHom.coe_coe, hσ]))
    (w := splitPrime τ) (fun s t h => by rw [e, e, h]) es
  rw [e, es, exp_inj] at this
  omega

/- English proof (translation)
Introduce `w hw` and use `by have : w.asIdeal ∈ (w.under (𝓞 F)).asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩ rw [primesOver_eq_split h (B.τ ⟨_, hw⟩)] at this rcases this with e | e · rw [HeightOneSpectrum.ext e]; exact (H ⟨_, hw⟩).1 · rw [HeightOneSpectrum.ext e]; exact (H ⟨_, hw⟩).2`.
-/
theorem pr_of {B : Base F E} (h : IsCMExt F E σ) {𝔞 : FI E}
    (H : ∀ v : B.P, count E (splitPrime (B.τ v)) 𝔞 = 0 ∧ count E (splitPrime ((B.τ v).comp σ)) 𝔞 = 0) : Pr B.P 𝔞 := fun w hw => by
  have : w.asIdeal ∈ (w.under (𝓞 F)).asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [primesOver_eq_split h (B.τ ⟨_, hw⟩)] at this
  rcases this with e | e
  · rw [HeightOneSpectrum.ext e]; exact (H ⟨_, hw⟩).1
  · rw [HeightOneSpectrum.ext e]; exact (H ⟨_, hw⟩).2

/- English proof (translation)
The claim follows from `pr_of h fun v => ⟨by rw [← count_bar hσ _ h0]; exact H _ (by rw [splitPrime_under]; exact v.2), by rw [count_bar hσ _ (cj_ne hσ h0), cj_cj]; exact H _ (by rw [splitPrime_under]; exact v.2)⟩`.
-/
theorem Pr.cj {B : Base F E} (h : IsCMExt F E σ) {𝔞 : FI E} (h0 : 𝔞 ≠ 0) (H : Pr B.P 𝔞) : Pr B.P (cj hσ 𝔞) :=
  pr_of h fun v => ⟨by rw [← count_bar hσ _ h0]; exact H _ (by rw [splitPrime_under]; exact v.2),
    by rw [count_bar hσ _ (cj_ne hσ h0), cj_cj]; exact H _ (by rw [splitPrime_under]; exact v.2)⟩

/- English proof (translation)
Introduce `w hw` and use `by rw [FractionalIdeal.count_mul _ _ ha hb, h w hw, h' w hw, add_zero]`.
-/
theorem Pr.mul {P : Finset (Pl F)} {𝔞 𝔟 : FI E} (ha : 𝔞 ≠ 0) (hb : 𝔟 ≠ 0) (h : Pr P 𝔞) (h' : Pr P 𝔟) : Pr P (𝔞 * 𝔟) :=
  fun w hw => by rw [FractionalIdeal.count_mul _ _ ha hb, h w hw, h' w hw, add_zero]

/- English proof (translation)
Introduce `w hw` and use `by rw [FractionalIdeal.count_inv, h w hw, neg_zero]`.
-/
theorem Pr.inv {P : Finset (Pl F)} {𝔞 : FI E} (h : Pr P 𝔞) : Pr P 𝔞⁻¹ :=
  fun w hw => by rw [FractionalIdeal.count_inv, h w hw, neg_zero]

structure Line {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E) (𝔭 : FI E) : Prop where
  ne : 𝔭 ≠ 0
  mem : ∀ s ∈ 𝔭, s • x ∈ L
  ex : ∃ p : Fin n → E, x ⬝ᵥ p = 1 ∧ ∀ z ∈ L, z ⬝ᵥ p ∈ 𝔭

/- English proof (translation)
Take `⟨p, hp, hL⟩` from `h.ex`. Establish `col : ∀ c : Fv F v, β.1 *ᵥ Pi.single i c = fun r => c * τ (x r)` using `fun c => by`. Use extensionality with `r`. Rewrite using `[Matrix.mulVec_single]`. Simplify using `[hi, mul_comm]`.

Establish `a1 : ∀ u ∈ splitLat τ L, Valued.v (u ⬝ᵥ fun r => τ (p r)) ≤ exp (-count E (splitPrime τ) 𝔭)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `latLoc_induction (p := fun y => Valued.v (splitVec τ y ⬝ᵥ fun r => τ (p r)) ≤ exp (-count E (splitPrime τ) 𝔭)) (fun a ha z hz => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy` and prove the remaining obligations. Establish `: (splitVec τ (fun i => a ⊗ₜ[F] z i) ⬝ᵥ fun r => τ (p r)) = a * τ (z ⬝ᵥ p)`. Simplify using `[splitVec, dotProduct, Finset.mul_sum, mul_assoc]`.

Rewrite using `[this, map_mul, valued_apply_eq_valuation]`. Conclude with `(mul_le_of_le_one_left' ha).trans ((mem_iff_valuation_le h.ne _).1 (hL z hz) _)`. Simplify using `[splitVec, dotProduct]`. Rewrite using `[splitVec_add, add_dotProduct]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le hy hz)`.

Establish `: splitVec τ (-y) = -splitVec τ y` using `funext fun r => map_neg _ _`. Rewrite using `[this, neg_dotProduct, Valuation.map_neg]` and apply the resulting hypothesis. Establish `a2` using `a1 _ ((hβ (Pi.single i 1)).1 fun j => by`. Distinguish the cases in `e : j = i`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[e])`. Establish `e2 : ((fun r => 1 * τ (x r)) ⬝ᵥ fun r => τ (p r)) = 1`. Use `congrArg τ hp` as an intermediate fact. Simplify `this` using `[dotProduct]`.

Rewrite `a2` using `[col, e2, map_one, ← exp_zero, exp_le_exp]`. Take `⟨s, hs, es⟩` from `exists_mem_valuation_eq h.ne (splitPrime τ)`. Establish `a3` using `(hβ (Pi.single i (τ s))).2 (by`. Rewrite using `[col]`. Conclude with `⟨_, tmul_mem_latLoc (one_mem _) (h.mem s hs), funext fun r => by simp [splitVec]⟩) i`.

Rewrite `a3` using `[Pi.single_eq_same, HeightOneSpectrum.mem_adicCompletionIntegers, valued_apply_eq_valuation, es, ← exp_zero, exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Line.count_eq {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} {𝔭 : FI E} (h : Line L x 𝔭) {v : Pl F}
    {τ : E →ₐ[F] Fv F v} {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) (i : Fin n) (hi : ∀ r, β.1 r i = τ (x r)) :
    count E (splitPrime τ) 𝔭 = 0 := by
  classical
  obtain ⟨p, hp, hL⟩ := h.ex
  have col : ∀ c : Fv F v, β.1 *ᵥ Pi.single i c = fun r => c * τ (x r) := fun c => by
    ext r; rw [Matrix.mulVec_single]; simp [hi, mul_comm]
  have a1 : ∀ u ∈ splitLat τ L, Valued.v (u ⬝ᵥ fun r => τ (p r)) ≤ exp (-count E (splitPrime τ) 𝔭) := by
    rintro _ ⟨y, hy, rfl⟩
    refine latLoc_induction (p := fun y => Valued.v (splitVec τ y ⬝ᵥ fun r => τ (p r)) ≤ exp (-count E (splitPrime τ) 𝔭))
      (fun a ha z hz => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · have : (splitVec τ (fun i => a ⊗ₜ[F] z i) ⬝ᵥ fun r => τ (p r)) = a * τ (z ⬝ᵥ p) := by
        simp [splitVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [this, map_mul, valued_apply_eq_valuation]
      exact (mul_le_of_le_one_left' ha).trans ((mem_iff_valuation_le h.ne _).1 (hL z hz) _)
    · simp [splitVec, dotProduct]
    · rw [splitVec_add, add_dotProduct]; exact (Valuation.map_add _ _ _).trans (max_le hy hz)
    · have : splitVec τ (-y) = -splitVec τ y := funext fun r => map_neg _ _
      rwa [this, neg_dotProduct, Valuation.map_neg]
  have a2 := a1 _ ((hβ (Pi.single i 1)).1 fun j => by
    by_cases e : j = i
    · subst e; simp
    · simp [e])
  have e2 : ((fun r => 1 * τ (x r)) ⬝ᵥ fun r => τ (p r)) = 1 := by
    have := congrArg τ hp
    simpa [dotProduct] using this
  rw [col, e2, map_one, ← exp_zero, exp_le_exp] at a2
  obtain ⟨s, hs, es⟩ := exists_mem_valuation_eq h.ne (splitPrime τ)
  have a3 := (hβ (Pi.single i (τ s))).2 (by
    rw [col]
    exact ⟨_, tmul_mem_latLoc (one_mem _) (h.mem s hs), funext fun r => by simp [splitVec]⟩) i
  rw [Pi.single_eq_same, HeightOneSpectrum.mem_adicCompletionIntegers, valued_apply_eq_valuation, es, ← exp_zero,
    exp_le_exp] at a3
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨p, hp, hL⟩` from `hx.ex`. Take `⟨q, hq, hM⟩` from `hy.ex`. Establish `inc : ∀ {m : ℕ} (a b : Fin m → E), incV F a ⬝ᵥ incV F b = inclR (F` using `F) (AF F) (a ⬝ᵥ b) := fun a b => by`.

Simplify using `[incV, dotProduct]`. Establish `key : ∀ (x' : Fin n → E) (y' : Fin d → E), incV F p ⬝ᵥ Matrix.vecMulVec (incV F x') (incV F y') *ᵥ incV F q = inclR (F` using `F) (AF F) (x' ⬝ᵥ p * y' ⬝ᵥ q) := fun x' y' => by`. Rewrite using `[Matrix.vecMulVec_mulVec, dotProduct_smul, inc, inc, map_mul, dotProduct_comm p]`. Simplify using `[mul_comm]`. Establish `: ∀ Z ∈ latAtV X W v, incV F p ⬝ᵥ Z *ᵥ incV F q ∈ Lat (𝔭 * 𝔮) v` using `fun Z hZ => by`.

Proceed by induction on `hZ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, h1, h2, x', hx', y', hy', rfl⟩` from `hz`. Establish `e : incM F (Matrix.vecMulVec x' y') = Matrix.vecMulVec (incV F x') (incV F y')`. Use extensionality with `i j`.

Conclude with `map_mul (inclR (F := F) (AF F)) _ _`. Rewrite using `[e, Matrix.smul_mulVec, dotProduct_smul, key]`. Use `AddSubgroup.subset_closure ⟨a, h1, h2, _, FractionalIdeal.mul_mem_mul (hL _ hx') (hM _ hy'), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a • ((1 : AF F) ⊗ₜ[F] _) = _`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Consider the case `zero => rw [Matrix.zero_mulVec, dotProduct_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [Matrix.add_mulVec, dotProduct_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [Matrix.neg_mulVec, dotProduct_neg]`.

Conclude with `neg_mem ha`. Use `this _ h` as an intermediate fact. Rewrite `this` using `[Matrix.smul_mulVec, dotProduct_smul, key, hp, hq, mul_one, map_one, smul_eq_mul, mul_one]`. Then use the resulting hypothesis. Introduce `h`. Proceed by induction on `h using AddSubgroup.closure_induction with`.

Consider the case `mem z hz`. Take `⟨a, h1, h2, s, hs, rfl⟩` from `hz`. Use `FractionalIdeal.mul_induction_on (C := fun s => (a ⊗ₜ[F] s : AE F E) • Matrix.vecMulVec (incV F x) (incV F y) ∈ latAtV X W v) hs ?_ ?_` and prove the remaining obligations. Introduce `s hs t ht`. Use `AddSubgroup.subset_closure ⟨a, h1, h2, _, hx.mem s hs, _, hy.mem t ht, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(a ⊗ₜ[F] (s * t)) * (((1 : AF F) ⊗ₜ[F] x i) * ((1 : AF F) ⊗ₜ[F] y j)) = a • ((1 : AF F) ⊗ₜ[F] (s * x i * (t * y j)))`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]`. Apply the tactic sequence `congr 1 <;> ring`. Introduce `s t hs ht`.

Rewrite using `[TensorProduct.tmul_add, add_smul]`. Conclude with `add_mem hs ht`. Consider the case `zero => rw [zero_smul]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [add_smul]`.

Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [neg_smul]`. Conclude with `neg_mem ha`.
-/
theorem line_lat {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {x : Fin n → E} {y : Fin d → E} {𝔭 𝔮 : FI E} (hx : Line X.L x 𝔭)
    (hy : Line W.L y 𝔮) (v : Pl F) (c : AE F E) :
    c • Matrix.vecMulVec (incV F x) (incV F y) ∈ latAtV X W v ↔ c ∈ Lat (𝔭 * 𝔮) v := by
  constructor
  · intro h
    obtain ⟨p, hp, hL⟩ := hx.ex
    obtain ⟨q, hq, hM⟩ := hy.ex
    have inc : ∀ {m : ℕ} (a b : Fin m → E), incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) := fun a b => by
      simp [incV, dotProduct]
    have key : ∀ (x' : Fin n → E) (y' : Fin d → E), incV F p ⬝ᵥ Matrix.vecMulVec (incV F x') (incV F y') *ᵥ incV F q =
        inclR (F := F) (AF F) (x' ⬝ᵥ p * y' ⬝ᵥ q) := fun x' y' => by
      rw [Matrix.vecMulVec_mulVec, dotProduct_smul, inc, inc, map_mul, dotProduct_comm p]
      simp [mul_comm]
    have : ∀ Z ∈ latAtV X W v, incV F p ⬝ᵥ Z *ᵥ incV F q ∈ Lat (𝔭 * 𝔮) v := fun Z hZ => by
      induction hZ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, h1, h2, x', hx', y', hy', rfl⟩ := hz
        have e : incM F (Matrix.vecMulVec x' y') = Matrix.vecMulVec (incV F x') (incV F y') := by
          ext i j; exact map_mul (inclR (F := F) (AF F)) _ _
        rw [e, Matrix.smul_mulVec, dotProduct_smul, key]
        refine AddSubgroup.subset_closure ⟨a, h1, h2, _, FractionalIdeal.mul_mem_mul (hL _ hx') (hM _ hy'), ?_⟩
        change a • ((1 : AF F) ⊗ₜ[F] _) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | zero => rw [Matrix.zero_mulVec, dotProduct_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [Matrix.add_mulVec, dotProduct_add]; exact add_mem ha hb
      | neg a _ ha => rw [Matrix.neg_mulVec, dotProduct_neg]; exact neg_mem ha
    have := this _ h
    rwa [Matrix.smul_mulVec, dotProduct_smul, key, hp, hq, mul_one, map_one, smul_eq_mul, mul_one] at this
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, h1, h2, s, hs, rfl⟩ := hz
      refine FractionalIdeal.mul_induction_on
        (C := fun s => (a ⊗ₜ[F] s : AE F E) • Matrix.vecMulVec (incV F x) (incV F y) ∈ latAtV X W v) hs ?_ ?_
      · intro s hs t ht
        refine AddSubgroup.subset_closure ⟨a, h1, h2, _, hx.mem s hs, _, hy.mem t ht, ?_⟩
        ext i j
        change (a ⊗ₜ[F] (s * t)) * (((1 : AF F) ⊗ₜ[F] x i) * ((1 : AF F) ⊗ₜ[F] y j)) = a • ((1 : AF F) ⊗ₜ[F] (s * x i * (t * y j)))
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
        congr 1 <;> ring
      · intro s t hs ht
        rw [TensorProduct.tmul_add, add_smul]; exact add_mem hs ht
    | zero => rw [zero_smul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
    | neg a _ ha => rw [neg_smul]; exact neg_mem ha

/- English proof (translation)
Establish `sym : ∀ u w, form σ Y.J w u = ε * σ (form σ Y.J u w)` using `fun u w => by`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, hJ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Take the linear combination `(-(w b * Y.J b a * σ (u a))) * hε`.

Establish `fl : ∀ (s t : E) u w, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) w = s * form σ Y.J H.x w + form σ Y.J (H.ι *ᵥ u) w + t * form σ Y.J H.y w` using `fun s t u w => by`. Simplify using `only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]`. Establish `yx : form σ Y.J H.y H.x = ε` using `by rw [sym, h.xy, map_one, mul_one]`. Establish `f1 : ∀ (s t : E) u, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) H.y = s` using `fun s t u => by`. Rewrite using `[fl, h.xy, (h.orth u).2, h.yy]`.

Expand and normalize the polynomial expressions, which then agree. Establish `f2 : ∀ (s t : E) u, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) H.x = t * ε` using `fun s t u => by`. Rewrite using `[fl, h.xx, (h.orth u).1, yx]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ∀ z ∈ Y.L, form σ Y.J z H.y ∈ H.𝔟` using `fun z hz => by`.

Take `⟨s, t, u, hs, -, -, rfl⟩` from `h.split z hz`. Rewrite using `[f1]`. Conclude with `(h.ideal s).2 hs`. Establish `b0 : H.𝔟 ≠ 0` using `fun e => by`. Establish `: ∀ z ∈ Submodule.span E (Y.L : Set (Fin n → E)), form σ Y.J z H.y = 0` using `fun z hz => by`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => have := hb z hz`. Rewrite `this` using `[e, FractionalIdeal.mem_zero_iff]`. Then use the resulting hypothesis. Consider the case `zero => simp [form]`. Consider the case `add a b _ _ ha hb => simp only [form, add_dotProduct] at *`.

Rewrite using `[ha, hb, add_zero]`. Consider the case `smul a b _ hb => simp only [form, smul_dotProduct] at *`. Rewrite using `[hb, smul_zero]`. Use `this H.x (hl.span_eq_top ▸ Submodule.mem_top)` as an intermediate fact. Rewrite `this` using `[h.xy]`.

Conclude with `one_ne_zero this`. Establish `εD : ∀ t, t * ε ∈ D ↔ t ∈ D`. Establish `: ε = 1 ∨ ε = -1` using `mul_self_eq_one_iff.1 hε`. Break down `this with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules.

Introduce `t`. Rewrite using `[mul_neg, mul_one]`. Conclude with `D.val.neg_mem_iff`. Establish `my : ∀ t, t ∈ D * (cj hσ H.𝔟)⁻¹ ↔ t • H.y ∈ Y.L` using `fun t => by`. Rewrite using `[← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (cj_ne hσ b0), hd]`.

Establish `g : ∀ z, form σ Y.J (t • H.y) z = t * σ (form σ Y.J z H.y) * ε` using `fun z => by`. Use `sym z H.y` as an intermediate fact. Simplify using `only [form, smul_dotProduct, smul_eq_mul] at *`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Prove the components needed by the constructor for the conclusion. Introduce `H1 z hz`. Rewrite using `[g, εD]`. Conclude with `H1 _ ((mem_cj hσ).2 (by rw [hσ]; exact hb z hz))`. Introduce `H1 s hs`.

Use `H1 _ ((h.ideal _).1 hs)` as an intermediate fact. Rewrite `this` using `[g, εD]`. Establish `e : form σ Y.J (σ s • H.x) H.y = σ s`. Establish `e0` using `h.xy`. Simplify using `only [form, smul_dotProduct, smul_eq_mul] at e0 ⊢`.

Rewrite using `[e0, mul_one]`. Rewrite `this` using `[e, hσ]`. Then use the resulting hypothesis. Use `⟨⟨b0, fun s hs => (h.ideal s).1 hs, _, h.xy, hb⟩, ⟨mul_ne_zero hD (inv_ne_zero (cj_ne hσ b0)), fun t ht => (my t).1 ht, ε • Y.J *ᵥ fun i => σ (H.x i), ?_, fun z hz => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[dotProduct_smul]`. Express the relevant statement in the definitionally equal form `ε * form σ Y.J H.y H.x = 1`.

Rewrite using `[yx, hε]`. Rewrite using `[dotProduct_smul]`. Express the relevant statement in the definitionally equal form `ε * form σ Y.J z H.x ∈ _`. Take `⟨s, t, u, -, ht, -, rfl⟩` from `h.split z hz`. Rewrite using `[f2, mul_left_comm, hε, mul_one]`.

Conclude with `(my t).2 ht`.
-/
theorem plane_lines {B : Base F E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i j : ℕ} {ε : E} {D : FI E}
    (hε : ε * ε = 1) (hJ : ∀ i j, σ (Y.J j i) = ε * Y.J i j) (hl : Y.L.IsLattice E)
    (hd : ∀ y, y ∈ Y.L ↔ ∀ x ∈ Y.L, form σ Y.J y x ∈ D) (hD : D ≠ 0) (h : H.IsAdapted σ B Y Y₁ i j) :
    Line Y.L H.x H.𝔟 ∧ Line Y.L H.y (D * (cj hσ H.𝔟)⁻¹) := by
  have sym : ∀ u w, form σ Y.J w u = ε * σ (form σ Y.J u w) := fun u w => by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, hJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    linear_combination (-(w b * Y.J b a * σ (u a))) * hε
  have fl : ∀ (s t : E) u w, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) w =
      s * form σ Y.J H.x w + form σ Y.J (H.ι *ᵥ u) w + t * form σ Y.J H.y w := fun s t u w => by
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have yx : form σ Y.J H.y H.x = ε := by rw [sym, h.xy, map_one, mul_one]
  have f1 : ∀ (s t : E) u, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) H.y = s := fun s t u => by
    rw [fl, h.xy, (h.orth u).2, h.yy]; ring
  have f2 : ∀ (s t : E) u, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) H.x = t * ε := fun s t u => by
    rw [fl, h.xx, (h.orth u).1, yx]; ring
  have hb : ∀ z ∈ Y.L, form σ Y.J z H.y ∈ H.𝔟 := fun z hz => by
    obtain ⟨s, t, u, hs, -, -, rfl⟩ := h.split z hz
    rw [f1]; exact (h.ideal s).2 hs
  have b0 : H.𝔟 ≠ 0 := fun e => by
    have : ∀ z ∈ Submodule.span E (Y.L : Set (Fin n → E)), form σ Y.J z H.y = 0 := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz => have := hb z hz; rwa [e, FractionalIdeal.mem_zero_iff] at this
      | zero => simp [form]
      | add a b _ _ ha hb => simp only [form, add_dotProduct] at *; rw [ha, hb, add_zero]
      | smul a b _ hb => simp only [form, smul_dotProduct] at *; rw [hb, smul_zero]
    have := this H.x (hl.span_eq_top ▸ Submodule.mem_top)
    rw [h.xy] at this
    exact one_ne_zero this
  have εD : ∀ t, t * ε ∈ D ↔ t ∈ D := by
    have : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.1 hε
    rcases this with rfl | rfl
    · simp
    · intro t; rw [mul_neg, mul_one]; exact D.val.neg_mem_iff
  have my : ∀ t, t ∈ D * (cj hσ H.𝔟)⁻¹ ↔ t • H.y ∈ Y.L := fun t => by
    rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero (cj_ne hσ b0), hd]
    have g : ∀ z, form σ Y.J (t • H.y) z = t * σ (form σ Y.J z H.y) * ε := fun z => by
      have := sym z H.y
      simp only [form, smul_dotProduct, smul_eq_mul] at *
      rw [this]; ring
    constructor
    · intro H1 z hz
      rw [g, εD]
      exact H1 _ ((mem_cj hσ).2 (by rw [hσ]; exact hb z hz))
    · intro H1 s hs
      have := H1 _ ((h.ideal _).1 hs)
      rw [g, εD] at this
      have e : form σ Y.J (σ s • H.x) H.y = σ s := by
        have e0 := h.xy
        simp only [form, smul_dotProduct, smul_eq_mul] at e0 ⊢
        rw [e0, mul_one]
      rwa [e, hσ] at this
  refine ⟨⟨b0, fun s hs => (h.ideal s).1 hs, _, h.xy, hb⟩,
    ⟨mul_ne_zero hD (inv_ne_zero (cj_ne hσ b0)), fun t ht => (my t).1 ht, ε • Y.J *ᵥ fun i => σ (H.x i), ?_, fun z hz => ?_⟩⟩
  · rw [dotProduct_smul]; change ε * form σ Y.J H.y H.x = 1; rw [yx, hε]
  · rw [dotProduct_smul]; change ε * form σ Y.J z H.x ∈ _
    obtain ⟨s, t, u, -, ht, -, rfl⟩ := h.split z hz
    rw [f2, mul_left_comm, hε, mul_one]; exact (my t).2 ht

/- English proof (translation)
The claim follows from `pr_of hc fun v => by refine ⟨l.1.count_eq (hb v) ⟨i, hi⟩ ((h.bas v _).1 rfl), ?_⟩ have := l.2.count_eq (hb v) ⟨j, hj⟩ ((h.bas v _).2.1 rfl) rw [FractionalIdeal.count_mul _ _ hD (inv_ne_zero (cj_ne hσ l.1.ne)), FractionalIdeal.count_inv, pD _ (by rw [splitPrime_under]; exact v.2), …`.
-/
theorem plane_pr {B : Base F E} (hc : IsCMExt F E σ) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i j : ℕ} {D : FI E}
    (hD : D ≠ 0) (pD : Pr B.P D) (hb : ∀ v : B.P, IsSplitBasis (B.τ v) Y.L (Y.bas v)) (h : H.IsAdapted σ B Y Y₁ i j) (hi : i < n) (hj : j < n)
    (l : Line Y.L H.x H.𝔟 ∧ Line Y.L H.y (D * (cj hσ H.𝔟)⁻¹)) : Pr B.P H.𝔟 :=
  pr_of hc fun v => by
    refine ⟨l.1.count_eq (hb v) ⟨i, hi⟩ ((h.bas v _).1 rfl), ?_⟩
    have := l.2.count_eq (hb v) ⟨j, hj⟩ ((h.bas v _).2.1 rfl)
    rw [FractionalIdeal.count_mul _ _ hD (inv_ne_zero (cj_ne hσ l.1.ne)), FractionalIdeal.count_inv,
      pD _ (by rw [splitPrime_under]; exact v.2), ← count_bar hσ _ l.1.ne] at this
    omega

end PositivityTheory.ThKG.Loc.Cone.Id

end
