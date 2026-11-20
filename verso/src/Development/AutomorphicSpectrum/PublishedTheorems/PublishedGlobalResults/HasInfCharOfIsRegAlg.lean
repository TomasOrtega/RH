import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsCohomologicalRankOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits

noncomputable section

open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace GlobalTheory.CompanionTheory.Published.Rd.PurityModel

def finUnit {E : Type} [Field E] [NumberField E] : (𝓞 E)ˣ →* (Af E)ˣ :=
  Units.map ((algebraMap E (Af E)).comp (algebraMap (𝓞 E) E)).toMonoidHom

/- English proof (translation)
Establish `hV : {u | ψ u = 1} ∈ 𝓝 (1 : (Af E)ˣ)` using `(isOpen_ker_finIdele E ψ hψ).mem_nhds (map_one ψ)`. Rewrite `hV` using `[Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap]`. Take `⟨T, hT, hTV⟩` from `hV`. Take `⟨T1, hT1, T2, hT2, hTT⟩` from `mem_nhds_prod_iff.1 hT`. Establish `hf : Continuous fun b : Af E => 1 + b` using `continuous_const.add continuous_id`.

Establish `h1 : (fun b : Af E => 1 + b) ⁻¹' T1 ∈ 𝓝 0` using `hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)`. Establish `h2 : (fun b : Af E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0` using `(MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds (by rw [Function.comp_apply, add_zero]; exact hT2)`. Take `⟨N, hN, hNW⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)`. Establish `: Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})` using `Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')`. Set `q : (𝓞 E)ˣ →* (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ` to `Units.map (Ideal.Quotient.mk _).toMonoidHom`.

Establish `key : ∀ η : (𝓞 E)ˣ, q η = 1 → ∃ a : Af E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧ ((finUnit η : (Af E)ˣ) : Af E) = 1 + N • a`. Introduce `η hη`. Establish `h3 : Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)}) (η : 𝓞 E) = Ideal.Quotient.mk _ 1` using `congrArg Units.val hη`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h3)`. Use `⟨algebraMap E (Af E) (algebraMap (𝓞 E) E b), fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v b, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap E (Af E) (algebraMap (𝓞 E) E (η : 𝓞 E)) = _`. Rewrite using `[eq_add_of_sub_eq' hb]`. Simplify using the standard rewrite rules. Use `⟨Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ, Nat.card_pos, ?_⟩` and prove the remaining obligations. Use `set k := Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ`.

Establish `hk : q (θ ^ k) = 1` using `by rw [map_pow]; exact pow_card_eq_one'`. Take `⟨a, ha, e⟩` from `key _ hk`. Take `⟨b, hb, e'⟩` from `key (θ ^ k)⁻¹ (by rw [map_inv, hk, inv_one])`. Rewrite using `[← map_pow, ← map_pow]`. Use `hTV (a := finUnit (θ ^ k)) (hTT ⟨?_, ?_⟩)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((finUnit (θ ^ k) : (Af E)ˣ) : Af E) ∈ T1`. Rewrite using `[e]`. Conclude with `(hNW a ha).1`. Express the relevant statement in the definitionally equal form `MulOpposite.op (((finUnit (θ ^ k))⁻¹ : (Af E)ˣ) : Af E) ∈ T2`. Rewrite using `[← map_inv, e']`.

Conclude with `(hNW b hb).2`.
-/
theorem exists_pow_eq_one {E : Type} [Field E] [NumberField E] (ψ : (Af E)ˣ →* ℂˣ) (hψ : Continuous ψ) (θ : (𝓞 E)ˣ) :
    ∃ k : ℕ, 0 < k ∧ ψ (finUnit θ) ^ k = 1 := by
  have hV : {u | ψ u = 1} ∈ 𝓝 (1 : (Af E)ˣ) := (isOpen_ker_finIdele E ψ hψ).mem_nhds (map_one ψ)
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : Af E => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : Af E => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : Af E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  let q : (𝓞 E)ˣ →* (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ := Units.map (Ideal.Quotient.mk _).toMonoidHom
  have key : ∀ η : (𝓞 E)ˣ, q η = 1 → ∃ a : Af E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧
      ((finUnit η : (Af E)ˣ) : Af E) = 1 + N • a := by
    intro η hη
    have h3 : Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E)}) (η : 𝓞 E) = Ideal.Quotient.mk _ 1 := congrArg Units.val hη
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h3)
    refine ⟨algebraMap E (Af E) (algebraMap (𝓞 E) E b), fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v b, ?_⟩
    change algebraMap E (Af E) (algebraMap (𝓞 E) E (η : 𝓞 E)) = _
    rw [eq_add_of_sub_eq' hb]
    simp
  refine ⟨Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ, Nat.card_pos, ?_⟩
  set k := Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ
  have hk : q (θ ^ k) = 1 := by rw [map_pow]; exact pow_card_eq_one'
  obtain ⟨a, ha, e⟩ := key _ hk
  obtain ⟨b, hb, e'⟩ := key (θ ^ k)⁻¹ (by rw [map_inv, hk, inv_one])
  rw [← map_pow, ← map_pow]
  refine hTV (a := finUnit (θ ^ k)) (hTT ⟨?_, ?_⟩)
  · change ((finUnit (θ ^ k) : (Af E)ˣ) : Af E) ∈ T1
    rw [e]; exact (hNW a ha).1
  · change MulOpposite.op (((finUnit (θ ^ k))⁻¹ : (Af E)ˣ) : Af E) ∈ T2
    rw [← map_inv, e']; exact (hNW b hb).2

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def infUnit : (𝓞 E)ˣ →* (Cinf E)ˣ :=
  Units.map ((pInf E).comp ((algebraMap E (Ad E)).comp (algebraMap (𝓞 E) E))).toMonoidHom

/- English proof (translation)
Establish `hi : ∀ x, pInf E (sInf E x) = x` using `fun x => (infEq E).symm_apply_apply x`. Establish `hf : ∀ x, pInf E (sFin E x) = 0` using `fun x => map_zero (infEq E).symm`. Establish `hi' : ∀ x, pFin E (sInf E x) = 0` using `fun x => rfl`. Establish `hf' : ∀ x, pFin E (sFin E x) = x` using `fun x => rfl`. Establish `e : infId E (infUnit θ) * finId E (finUnit θ) = diagUnits E (Units.map (algebraMap (𝓞 E) E).toMonoidHom θ)`.

Use `Units.ext (ad_ext ?_ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pInf E ((1 - sInf E 1 + sInf E _) * (1 - sFin E 1 + sFin E _)) = _`. Simplify using `only [map_mul, map_add, map_sub, map_one, hi, hf, sub_self, zero_add, sub_zero, add_zero, mul_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `pFin E ((1 - sInf E 1 + sInf E _) * (1 - sFin E 1 + sFin E _)) = _`.

Simplify using `only [map_mul, map_add, map_sub, map_one, hi', hf', sub_self, zero_add, sub_zero, add_zero, one_mul]`. Both sides reduce to the same expression. Establish `h1` using `χ.2.2 (Units.map (algebraMap (𝓞 E) E).toMonoidHom θ)`. Rewrite `h1` using `[← e, map_mul]`. Take `⟨k, hk, h2⟩` from `exists_pow_eq_one (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E)) θ`.

Establish `h3 : chiInf χ (infUnit θ) ^ k = 1`. Use `congrArg (· ^ k) h1` as an intermediate fact. Simplify using `only [mul_pow, one_pow] at this`. Rewrite `this` using `[show χ.1 (finId E (finUnit θ)) ^ k = 1 from h2, mul_one]`. Conclude with `this`.

Establish `h4 : ‖((chiInf χ (infUnit θ) : ℂˣ) : ℂ)‖ ^ k = 1`. Rewrite using `[← norm_pow, ← Units.val_pow_eq_pow_val, h3]`. Simplify using the standard rewrite rules. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h4`.
-/
theorem norm_chiInf_unit (χ : HChar E) (θ : (𝓞 E)ˣ) : ‖((chiInf χ (infUnit θ) : ℂˣ) : ℂ)‖ = 1 := by
  have hi : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  have hf : ∀ x, pInf E (sFin E x) = 0 := fun x => map_zero (infEq E).symm
  have hi' : ∀ x, pFin E (sInf E x) = 0 := fun x => rfl
  have hf' : ∀ x, pFin E (sFin E x) = x := fun x => rfl
  have e : infId E (infUnit θ) * finId E (finUnit θ) =
      diagUnits E (Units.map (algebraMap (𝓞 E) E).toMonoidHom θ) := by
    refine Units.ext (ad_ext ?_ ?_)
    · change pInf E ((1 - sInf E 1 + sInf E _) * (1 - sFin E 1 + sFin E _)) = _
      simp only [map_mul, map_add, map_sub, map_one, hi, hf, sub_self, zero_add, sub_zero, add_zero, mul_one]
      rfl
    · change pFin E ((1 - sInf E 1 + sInf E _) * (1 - sFin E 1 + sFin E _)) = _
      simp only [map_mul, map_add, map_sub, map_one, hi', hf', sub_self, zero_add, sub_zero, add_zero, one_mul]
      rfl
  have h1 := χ.2.2 (Units.map (algebraMap (𝓞 E) E).toMonoidHom θ)
  rw [← e, map_mul] at h1
  obtain ⟨k, hk, h2⟩ := exists_pow_eq_one (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E)) θ
  have h3 : chiInf χ (infUnit θ) ^ k = 1 := by
    have := congrArg (· ^ k) h1
    simp only [mul_pow, one_pow] at this
    rw [show χ.1 (finId E (finUnit θ)) ^ k = 1 from h2, mul_one] at this
    exact this
  have h4 : ‖((chiInf χ (infUnit θ) : ℂˣ) : ℂ)‖ ^ k = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h3]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h4

/- English proof (translation)
Take `⟨c, hc⟩` from `GlobalTheory.CompanionTheory.Ar.Flat.exists_eq_mul_mult_of_units E (fun w => ((n w.embedding + n (ComplexEmbedding.conjugate w.embedding) : ℤ) : ℝ)) (fun θ => by`. Establish `h1` using `norm_chiInf_unit χ θ`. Rewrite `h1` using `[GlobalTheory.RegAlgPurityModel.chiInf_eq_prod χ n h, norm_prod]`. Establish `hc : ∀ τ : E →+* ℂ, coord τ (infUnit θ : (Cinf E)ˣ) = τ ((θ : 𝓞 E) : E)` using `fun τ => coord_algebraMap τ _`. Establish `hp : ∀ w : InfinitePlace E, 0 < w ((θ : 𝓞 E) : E)` using `fun w => Units.pos_at_place θ w`.

Establish `h2 : ∀ w : InfinitePlace E, ‖coord w.embedding (infUnit θ : (Cinf E)ˣ) ^ n w.embedding * coord (ComplexEmbedding.conjugate w.embedding) (infUnit θ : (Cinf E)ˣ) ^ n (ComplexEmbedding.conjugate w.embedding)‖ = w ((θ : 𝓞 E) : E) ^ (n w.embedding + n (ComplexEmbedding.conjugate w.emb …` using `fun w => by`. Rewrite using `[hc, hc, norm_mul, norm_zpow, norm_zpow, zpow_add₀ (hp w).ne', ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, InfinitePlace.norm_embedding_eq]`. Simplify using `only [h2] at h1`. Establish `h3` using `congrArg Real.log h1`. Rewrite `h3` using `[Real.log_prod (fun w _ => (zpow_pos (hp w) _).ne'), Real.log_one]`.

Rewrite using `[← h3]`. Conclude with `Finset.sum_congr rfl fun w _ => by rw [Real.log_zpow, mul_comm])`. Establish `hm : ∀ w : InfinitePlace E, ((n w.embedding + n (ComplexEmbedding.conjugate w.embedding) : ℤ) : ℝ) = c * 2` using `fun w => by rw [hc w, (IsTotallyComplex.isComplex w).mult_eq_two]; norm_num`. Take `⟨w₀⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Use `⟨n w₀.embedding + n (ComplexEmbedding.conjugate w₀.embedding), fun τ => ?_⟩` and prove the remaining obligations.

Establish `h5 : n (InfinitePlace.mk τ).embedding + n (ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding) = n w₀.embedding + n (ComplexEmbedding.conjugate w₀.embedding)`. Conclude with `(hm _).trans (hm w₀).symm` after adjusting the coercions. Break down `InfinitePlace.embedding_mk_eq τ with e | e` into its components or cases. Rewrite `h5` using `[e]`. Then use the resulting hypothesis. Rewrite `h5` using `[e, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ, add_comm]`.

Conclude with `h5`.
-/
theorem hecke_pure (χ : HChar E) (n : (E →+* ℂ) → ℤ) (h : ∀ τ, expo χ τ = n τ) :
    ∃ w₀ : ℤ, ∀ τ : E →+* ℂ, n τ + n (ComplexEmbedding.conjugate τ) = w₀ := by
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.Flat.exists_eq_mul_mult_of_units E
    (fun w => ((n w.embedding + n (ComplexEmbedding.conjugate w.embedding) : ℤ) : ℝ)) (fun θ => by
      have h1 := norm_chiInf_unit χ θ
      rw [GlobalTheory.RegAlgPurityModel.chiInf_eq_prod χ n h, norm_prod] at h1
      have hc : ∀ τ : E →+* ℂ, coord τ (infUnit θ : (Cinf E)ˣ) = τ ((θ : 𝓞 E) : E) := fun τ => coord_algebraMap τ _
      have hp : ∀ w : InfinitePlace E, 0 < w ((θ : 𝓞 E) : E) := fun w => Units.pos_at_place θ w
      have h2 : ∀ w : InfinitePlace E, ‖coord w.embedding (infUnit θ : (Cinf E)ˣ) ^ n w.embedding *
          coord (ComplexEmbedding.conjugate w.embedding) (infUnit θ : (Cinf E)ˣ) ^
            n (ComplexEmbedding.conjugate w.embedding)‖ =
          w ((θ : 𝓞 E) : E) ^ (n w.embedding + n (ComplexEmbedding.conjugate w.embedding)) := fun w => by
        rw [hc, hc, norm_mul, norm_zpow, norm_zpow, zpow_add₀ (hp w).ne', ComplexEmbedding.conjugate_coe_eq,
          Complex.norm_conj, InfinitePlace.norm_embedding_eq]
      simp only [h2] at h1
      have h3 := congrArg Real.log h1
      rw [Real.log_prod (fun w _ => (zpow_pos (hp w) _).ne'), Real.log_one] at h3
      rw [← h3]
      exact Finset.sum_congr rfl fun w _ => by rw [Real.log_zpow, mul_comm])
  have hm : ∀ w : InfinitePlace E, ((n w.embedding + n (ComplexEmbedding.conjugate w.embedding) : ℤ) : ℝ) = c * 2 :=
    fun w => by rw [hc w, (IsTotallyComplex.isComplex w).mult_eq_two]; norm_num
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  refine ⟨n w₀.embedding + n (ComplexEmbedding.conjugate w₀.embedding), fun τ => ?_⟩
  have h5 : n (InfinitePlace.mk τ).embedding + n (ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding) =
      n w₀.embedding + n (ComplexEmbedding.conjugate w₀.embedding) := by
    exact_mod_cast (hm _).trans (hm w₀).symm
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rwa [e] at h5
  · rw [e, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ, add_comm] at h5
    exact h5

/- English proof (translation)
Use `⟨?_, GlobalTheory.RegAlgPurityModel.isCohomological_rank_one π hr⟩` and prove the remaining obligations. Take `⟨χ, rfl⟩` from `RankOne.exists_eq_twist π`. Use `choose n hn using (CG.isRegAlg_ofChar χ).1 hr`. Take `⟨w₀, hw⟩` from `hecke_pure χ n hn`. Use `⟨w₀, fun τ => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(CG.ofChar χ).infChar (ComplexEmbedding.conjugate τ) = ((CG.ofChar χ).infChar τ).map _`. Rewrite using `[CG.infChar_ofChar, CG.infChar_ofChar, Multiset.map_singleton, hn, hn, ← hw τ]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rank_one (π : CuspSub E 1) (hr : (CG.mk π).IsRegAlg) :
    (∃ w₀ : ℤ, ∀ τ : E →+* ℂ,
      (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z) ∧
    IsCohomological π := by
  refine ⟨?_, GlobalTheory.RegAlgPurityModel.isCohomological_rank_one π hr⟩
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  choose n hn using (CG.isRegAlg_ofChar χ).1 hr
  obtain ⟨w₀, hw⟩ := hecke_pure χ n hn
  refine ⟨w₀, fun τ => ?_⟩
  change (CG.ofChar χ).infChar (ComplexEmbedding.conjugate τ) = ((CG.ofChar χ).infChar τ).map _
  rw [CG.infChar_ofChar, CG.infChar_ofChar, Multiset.map_singleton, hn, hn, ← hw τ]
  congr 1; push_cast; ring

/- English proof (translation)
Use `⟨fun H L _ _ _ a ha π hr => H L a (by omega) π hr, fun H L _ _ _ a ha π hr => ?_⟩` and prove the remaining obligations. Break down `ha.eq_or_lt with rfl | h` into its components or cases. Conclude with `rank_one π hr`. Conclude with `H L a h π hr`.
-/
theorem iff_two_le : GlobalTheory.CompanionTheory.Published.Rd.RegularAlgebraicPurity ↔
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ), 2 ≤ a → ∀ π : CuspSub L a, (CG.mk π).IsRegAlg →
      (∃ w₀ : ℤ, ∀ τ : L →+* ℂ,
        (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z) ∧
      IsCohomological π := by
  refine ⟨fun H L _ _ _ a ha π hr => H L a (by omega) π hr, fun H L _ _ _ a ha π hr => ?_⟩
  rcases ha.eq_or_lt with rfl | h
  · exact rank_one π hr
  · exact H L a h π hr

/- English proof (translation)
Distinguish the cases in `hm : ∃ m, π.HasInfChar τ m`. Take `⟨m, hm⟩` from `hm`. Rewrite using `[hm.infChar_eq]` and apply the resulting hypothesis. Establish `h1` using `(h τ).1`. Rewrite `h1` using `[CG.infChar, dif_neg hm]`.

Take `⟨b, rfl⟩ : ∃ b, a = b + 2` from `⟨a - 2, by omega⟩`. Simplify using `[Multiset.replicate_succ] at h1`.
-/
theorem hasInfChar_of_isRegAlg {a : ℕ} (ha : 2 ≤ a) {π : CG E a} (h : π.IsRegAlg) (τ : E →+* ℂ) :
    π.HasInfChar τ (π.infChar τ) := by
  by_cases hm : ∃ m, π.HasInfChar τ m
  · obtain ⟨m, hm⟩ := hm
    rwa [hm.infChar_eq]
  · have h1 := (h τ).1
    rw [CG.infChar, dif_neg hm] at h1
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    simp [Multiset.replicate_succ] at h1

end GlobalTheory.CompanionTheory.Published.Rd.PurityModel

end
