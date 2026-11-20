import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignatureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUniqueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioRankFactorStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.VolRatio

section Congr

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.fDeg`. Use `Fintype.card_congr { toFun := fun w => w.comap (e.symm : L →+* K) invFun := fun w => w.comap (e : K →+* L) left_inv := fun w => ?_ right_inv := fun w => ?_ }` and prove the remaining obligations. Use extensionality with `x`. Simplify using the standard rewrite rules. Use extensionality with `x`.

Simplify using the standard rewrite rules.
-/
theorem fDeg_congr (e : K ≃+* L) : Formalism.HermitianLatticesTheory.fDeg K = Formalism.HermitianLatticesTheory.fDeg L := by
  unfold Formalism.HermitianLatticesTheory.fDeg
  refine Fintype.card_congr
    { toFun := fun w => w.comap (e.symm : L →+* K)
      invFun := fun w => w.comap (e : K →+* L)
      left_inv := fun w => ?_
      right_inv := fun w => ?_ }
  · ext x
    simp
  · ext x
    simp

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.vInv`. Rewrite using `[fDeg_congr e, NumberField.discr_eq_discr_of_ringEquiv K e]`.
-/
theorem vInv_congr (e : K ≃+* L) : Formalism.HermitianLatticesTheory.vInv K = Formalism.HermitianLatticesTheory.vInv L := by
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [fDeg_congr e, NumberField.discr_eq_discr_of_ringEquiv K e]

variable [StarRing K] [StarRing L]

/- English proof (translation)
Use `set g := RingOfIntegers.mapRingEquiv e with hg`. Establish `hge : ∀ x : 𝓞 K, algebraMap (𝓞 L) L (g x) = e (algebraMap (𝓞 K) K x)` using `fun x => rfl`. Unfold `Formalism.HermitianLatticesTheory.conjIdeal`. Use `conv_rhs => rw [← Ideal.map_symm, Ideal.map_span]`. Use `congr 1`.

Use extensionality with `r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hr⟩`. Conclude with `⟨g r, ⟨g s, hs, by rw [hge, hge, hr, he]⟩, g.symm_apply_apply r⟩`. Introduce and unpack `⟨t, ⟨s, hs, ht⟩, rfl⟩`.

Use `⟨g.symm s, by simpa only [Ideal.mem_comap, RingEquiv.apply_symm_apply] using hs, e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[he, ← hge, ← hge, g.apply_symm_apply, g.apply_symm_apply, ht]`.
-/
theorem conjIdeal_comap (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (P : Ideal (𝓞 L)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (P.comap (RingOfIntegers.mapRingEquiv e)) =
      (Formalism.HermitianLatticesTheory.conjIdeal (K := L) P).comap (RingOfIntegers.mapRingEquiv e) := by
  set g := RingOfIntegers.mapRingEquiv e with hg
  have hge : ∀ x : 𝓞 K, algebraMap (𝓞 L) L (g x) = e (algebraMap (𝓞 K) K x) := fun x => rfl
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  conv_rhs => rw [← Ideal.map_symm, Ideal.map_span]
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, hr⟩
    exact ⟨g r, ⟨g s, hs, by rw [hge, hge, hr, he]⟩, g.symm_apply_apply r⟩
  · rintro ⟨t, ⟨s, hs, ht⟩, rfl⟩
    refine ⟨g.symm s, by simpa only [Ideal.mem_comap, RingEquiv.apply_symm_apply] using hs, e.injective ?_⟩
    rw [he, ← hge, ← hge, g.apply_symm_apply, g.apply_symm_apply, ht]

/- English proof (translation)
Establish `hN : Ideal.absNorm (P.comap (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm P`. Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `Nat.card_congr (Ideal.quotientEquiv _ P (RingOfIntegers.mapRingEquiv e) (Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective P).symm).toEquiv`. Establish `hc : Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) (P.comap (RingOfIntegers.mapRingEquiv e)) = P.comap (RingOfIntegers.mapRingEquiv e) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P := by`. Rewrite using `[conjIdeal_comap e he]`.

Conclude with `(Ideal.comap_injective_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective).eq_iff`. Unfold `Formalism.HermitianLatticesTheory.eulerFac`. Rewrite using `[hN]`. Distinguish the cases in `h : Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P`. Rewrite using `[if_pos h, if_pos (hc.2 h)]`.

Rewrite using `[if_neg h, if_neg (fun h' => h (hc.1 h'))]`.
-/
theorem eulerFac_comap (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) (P : Ideal (𝓞 L)) :
    Formalism.HermitianLatticesTheory.eulerFac K M (P.comap (RingOfIntegers.mapRingEquiv e)) = Formalism.HermitianLatticesTheory.eulerFac L M P := by
  have hN : Ideal.absNorm (P.comap (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv _ P (RingOfIntegers.mapRingEquiv e)
      (Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective P).symm).toEquiv
  have hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (P.comap (RingOfIntegers.mapRingEquiv e)) =
      P.comap (RingOfIntegers.mapRingEquiv e) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P := by
    rw [conjIdeal_comap e he]
    exact (Ideal.comap_injective_of_surjective _ (RingOfIntegers.mapRingEquiv e).surjective).eq_iff
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [hN]
  by_cases h : Formalism.HermitianLatticesTheory.conjIdeal (K := L) P = P
  · rw [if_pos h, if_pos (hc.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.1 h'))]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.lValEta`. Set `g` to `RingOfIntegers.mapRingEquiv e`. Set `φ : {P : Ideal (𝓞 L) // P.IsMaximal} ≃ {P : Ideal (𝓞 K) // P.IsMaximal}` to `{ toFun := fun P => ⟨P.1.comap g, by haveI := P.2`. Conclude with `Ideal.comap_isMaximal_of_surjective g g.surjective⟩`. Use `invFun := fun P => ⟨P.1.comap g.symm, by haveI := P.2`.

Conclude with `Ideal.comap_isMaximal_of_surjective g.symm g.symm.surjective⟩`. Use `left_inv := fun P => by`. Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, RingEquiv.apply_symm_apply]`. Use `right_inv := fun P => by`.

Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, RingEquiv.symm_apply_apply] }`. Rewrite using `[← φ.tprod_eq]`. Conclude with `tprod_congr fun P => eulerFac_comap e he M P.1`.
-/
theorem lValEta_congr (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) :
    Formalism.HermitianLatticesTheory.lValEta K M = Formalism.HermitianLatticesTheory.lValEta L M := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  let g := RingOfIntegers.mapRingEquiv e
  let φ : {P : Ideal (𝓞 L) // P.IsMaximal} ≃ {P : Ideal (𝓞 K) // P.IsMaximal} :=
    { toFun := fun P => ⟨P.1.comap g, by
        haveI := P.2
        exact Ideal.comap_isMaximal_of_surjective g g.surjective⟩
      invFun := fun P => ⟨P.1.comap g.symm, by
        haveI := P.2
        exact Ideal.comap_isMaximal_of_surjective g.symm g.symm.surjective⟩
      left_inv := fun P => by
        ext x
        simp only [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      right_inv := fun P => by
        ext x
        simp only [Ideal.mem_comap, RingEquiv.symm_apply_apply] }
  rw [← φ.tprod_eq]
  exact tprod_congr fun P => eulerFac_comap e he M P.1

/- English proof (translation)
Unfold `rankFac`. Rewrite using `[fDeg_congr e, vInv_congr e, lValEta_congr e he]`.
-/
theorem rankFac_congr (e : K ≃+* L) (he : ∀ x, e (star x) = star (e x)) (M : ℕ) :
    rankFac K M = rankFac L M := by
  unfold rankFac
  rw [fDeg_congr e, vInv_congr e, lValEta_congr e he]

/- English proof (translation)
Establish `h0 : Ideal.absNorm P ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)`. Establish `h1 : (1 : ℝ) ≤ (Ideal.absNorm P : ℝ)` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0`. Unfold `Formalism.HermitianLatticesTheory.eulerFac`.

Use `split_ifs`. Establish `h2 : (1 : ℝ) ≤ Real.sqrt (Ideal.absNorm P : ℝ)` using `Real.one_le_sqrt.2 h1`. Establish `h3 : Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1` using `zpow_le_one_of_nonpos₀ h2 (by omega)`. Establish `h4 : 0 ≤ Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))` using `by positivity`. Use `inv_nonneg.2 ?_` and prove the remaining obligations.

Apply the tactic sequence `rcases neg_one_pow_eq_or ℝ M with h | h <;> rw [h] <;> linarith`. Establish `h3 : (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1` using `zpow_le_one_of_nonpos₀ h1 (by omega)`. Conclude with `Real.rpow_nonneg (by linarith) _`.
-/
theorem eulerFac_nonneg (M : ℕ) (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    0 ≤ Formalism.HermitianLatticesTheory.eulerFac K M P := by
  have h0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs
  · have h2 : (1 : ℝ) ≤ Real.sqrt (Ideal.absNorm P : ℝ) := Real.one_le_sqrt.2 h1
    have h3 : Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ h2 (by omega)
    have h4 : 0 ≤ Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by positivity
    refine inv_nonneg.2 ?_
    rcases neg_one_pow_eq_or ℝ M with h | h <;> rw [h] <;> linarith
  · have h3 : (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ h1 (by omega)
    exact Real.rpow_nonneg (by linarith) _

/- English proof (translation)
Establish `h : 0 ≤ Formalism.HermitianLatticesTheory.lValEta K M` using `tprod_nonneg fun P => eulerFac_nonneg M P.1 P.2`. Establish `hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K`. Unfold `Formalism.HermitianLatticesTheory.vInv`. Check the signs of the components of the expression. Unfold `rankFac`.

Check the signs of the components of the expression.
-/
theorem rankFac_nonneg (M : ℕ) : 0 ≤ rankFac K M := by
  have h : 0 ≤ Formalism.HermitianLatticesTheory.lValEta K M := tprod_nonneg fun P => eulerFac_nonneg M P.1 P.2
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  unfold rankFac
  positivity

end Congr

/- English proof (translation)
Establish `: 0 < sphV i`. Unfold `sphV`. Conclude with `Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity`. Unfold `volU`. Check the signs of the components of the expression.
-/
theorem volU_pos (i : ℕ) : 0 < volU i := by
  have : 0 < sphV i := by
    unfold sphV
    exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity
  unfold volU
  positivity

/- English proof (translation)
Establish `e2 : ρ = b * (r / a)` using `by field_simp; linarith`. Rewrite `h` using `[e2, ENNReal.ofReal_mul hb.le, ← mul_assoc, ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top, ENNReal.ofReal_div_of_pos ha, ← mul_div_assoc]`. Establish `h0` using `(ENNReal.ofReal_pos.2 ha).ne'`. Rewrite using `[← ENNReal.div_mul_cancel (a := ENNReal.ofReal a) (b := X) h0 ENNReal.ofReal_ne_top, h, ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top]`.
-/
theorem ennreal_volume_ratio_step_cancel (X Y : ENNReal) (r a b ρ : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hρ : ρ * a = r * b)
    (h : X / ENNReal.ofReal a = Y / ENNReal.ofReal b * ENNReal.ofReal ρ) :
    X = Y * ENNReal.ofReal r := by
  have e2 : ρ = b * (r / a) := by field_simp; linarith
  rw [e2, ENNReal.ofReal_mul hb.le, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_div_of_pos ha, ← mul_div_assoc] at h
  have h0 := (ENNReal.ofReal_pos.2 ha).ne'
  rw [← ENNReal.div_mul_cancel (a := ENNReal.ofReal a) (b := X) h0 ENNReal.ofReal_ne_top, h,
    ENNReal.div_mul_cancel h0 ENNReal.ofReal_ne_top]

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Take `⟨e', he'⟩` from `h'`. Conclude with `⟨e'.trans e, fun x => by simp [he, he']⟩`.
-/
theorem sameField_trans {I I' I'' : AutInst} (h : SameField I I') (h' : SameField I' I'') :
    SameField I I'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e'.trans e, fun x => by simp [he, he']⟩

/- English proof (translation)
Take `⟨e, he⟩` from `h`. Use `⟨e.symm, fun x => e.injective ?_⟩` and prove the remaining obligations. Simplify using `[he]`.
-/
theorem sameField_symm {I I' : AutInst} (h : SameField I I') : SameField I' I := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun x => e.injective ?_⟩
  simp [he]

/- English proof (translation)
Take `⟨hf, -, -, -, -, hpq⟩` from `GlobalTheory.T.autInst_degree_rootDiscriminant_rank I`. Establish `hn` using `hpq P Q h`. Take `⟨I', e, x, A, he, hn', -, -, -, hsig, hv⟩` from `hstep I P Q h (by omega) s hs`. Use `⟨I', ⟨e, he⟩, hsig, ?_⟩` and prove the remaining obligations. Introduce `c μf _ _ c' μf' _ _ hc hc'`.

Establish `hR` using `GlobalTheory.T.mass_ratio_rank_factor I.E I.n (by omega)`. Rewrite `hR` using `[hf, show I.n - 1 = I'.n by omega]`. Rewrite using `[hn]`. Conclude with `ennreal_volume_ratio_step_cancel _ _ _ _ _ _ (rankFac_nonneg _) (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hR (hv c μf c' μf' hc hc')`.
-/
theorem step (hstep : VolumeStep) (I : AutInst) (P Q : ℕ) (h : HasSig I P Q) (h3 : 3 ≤ P + Q) (s : Bool)
    (hs : if s then 1 ≤ P else 1 ≤ Q) :
    ∃ I' : AutInst, SameField I I' ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) ∧
      ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
        (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
        IsGaugeAll I c → IsGaugeAll I' c' →
        gaugeVol I c μf = gaugeVol I' c' μf' * ENNReal.ofReal (rankFac I.E (P + Q)) := by
  obtain ⟨hf, -, -, -, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hn := hpq P Q h
  obtain ⟨I', e, x, A, he, hn', -, -, -, hsig, hv⟩ := hstep I P Q h (by omega) s hs
  refine ⟨I', ⟨e, he⟩, hsig, ?_⟩
  intro c μf _ _ c' μf' _ _ hc hc'
  have hR := GlobalTheory.T.mass_ratio_rank_factor I.E I.n (by omega)
  rw [hf, show I.n - 1 = I'.n by omega] at hR
  rw [hn]
  exact ennreal_volume_ratio_step_cancel _ _ _ _ _ _ (rankFac_nonneg _) (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hR
    (hv c μf c' μf' hc hc')

/- English proof (translation)
Introduce `hstep I p q p₀ q₀ hsig hp hq h2`. Use the proof step `induction' hd : (p - p₀) + (q - q₀) with d ih generalizing I p q`. Take `rfl : p₀ = p` from `by omega`. Take `rfl : q₀ = q` from `by omega`. Use `⟨⟨I, ⟨RingEquiv.refl _, fun _ => rfl⟩, hsig⟩, ?_⟩` and prove the remaining obligations.

Introduce `I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀`. Rewrite using `[Finset.Ioc_self, Finset.prod_empty, ENNReal.ofReal_one, mul_one]`. Conclude with `GlobalTheory.T.hermitian_volume_depends_only_on_field_signature I I₀ _ _ hI hsig hsig₀ c μf c₀ μ₀ hc hc₀`. Choose the witnesses or unpack the hypotheses as in `⟨I', p', q', hI', hsig', hp', hq', hsum, hv⟩ : ∃ (I' : AutInst) (p' q' : ℕ), SameField I I' ∧ HasSig I' p' q' ∧ p₀ ≤ p' ∧ q₀ ≤ q' ∧ p' + q' + 1 = p + q ∧ ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μf' : Mea …`. Distinguish the cases in `hpp : p₀ < p`.

Take `⟨I', h1, h2, h3⟩` from `step hstep I p q hsig (by omega) true (by simp; omega)`. Conclude with `⟨I', p - 1, q, h1, h2, by omega, hq, by omega, h3⟩`. Take `⟨I', h1, h2, h3⟩` from `step hstep I p q hsig (by omega) false (by simp; omega)`. Conclude with `⟨I', p, q - 1, h1, h2, hp, by omega, by omega, h3⟩`. Take `⟨⟨I₁, hI₁, hsig₁⟩, hrat⟩` from `ih I' p' q' hsig' hp' hq' (by omega)`.

Use `⟨⟨I₁, sameField_trans hI' hI₁, hsig₁⟩, ?_⟩` and prove the remaining obligations. Introduce `I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀`. Take `⟨μ', hH, hS⟩` from `GlobalTheory.CongTop.exists_haar_sigmaFinite I'`. Use `choose c' _ hc' _ using fun v : InfinitePlace I'.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I'.n (I'.ε v)`. Establish `hg' : IsGaugeAll I' c'` using `hc'`.

Rewrite using `[hv c μf c' μ' hc hg', hrat I₀ (sameField_trans (sameField_symm hI') hI) hsig₀ c' μ' c₀ μ₀ hg' hc₀, ← hsum, Finset.prod_Ioc_succ_top (by omega), ENNReal.ofReal_mul (Finset.prod_nonneg fun M _ => rankFac_nonneg M), mul_assoc]`. Take `⟨e, he⟩` from `hI'`. Simplify using `only [rankFac_congr e he]`.
-/
theorem volumeRatio_of_volumeStep : VolumeStep → VolumeRatio := by
  intro hstep I p q p₀ q₀ hsig hp hq h2
  induction' hd : (p - p₀) + (q - q₀) with d ih generalizing I p q
  · obtain rfl : p₀ = p := by omega
    obtain rfl : q₀ = q := by omega
    refine ⟨⟨I, ⟨RingEquiv.refl _, fun _ => rfl⟩, hsig⟩, ?_⟩
    intro I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀
    rw [Finset.Ioc_self, Finset.prod_empty, ENNReal.ofReal_one, mul_one]
    exact GlobalTheory.T.hermitian_volume_depends_only_on_field_signature I I₀ _ _ hI hsig hsig₀ c μf c₀ μ₀ hc hc₀
  · obtain ⟨I', p', q', hI', hsig', hp', hq', hsum, hv⟩ : ∃ (I' : AutInst) (p' q' : ℕ), SameField I I' ∧
        HasSig I' p' q' ∧ p₀ ≤ p' ∧ q₀ ≤ q' ∧ p' + q' + 1 = p + q ∧
        ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
          (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure],
          IsGaugeAll I c → IsGaugeAll I' c' →
          gaugeVol I c μf = gaugeVol I' c' μf' * ENNReal.ofReal (rankFac I.E (p + q)) := by
      by_cases hpp : p₀ < p
      · obtain ⟨I', h1, h2, h3⟩ := step hstep I p q hsig (by omega) true (by simp; omega)
        exact ⟨I', p - 1, q, h1, h2, by omega, hq, by omega, h3⟩
      · obtain ⟨I', h1, h2, h3⟩ := step hstep I p q hsig (by omega) false (by simp; omega)
        exact ⟨I', p, q - 1, h1, h2, hp, by omega, by omega, h3⟩
    obtain ⟨⟨I₁, hI₁, hsig₁⟩, hrat⟩ := ih I' p' q' hsig' hp' hq' (by omega)
    refine ⟨⟨I₁, sameField_trans hI' hI₁, hsig₁⟩, ?_⟩
    intro I₀ hI hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀
    obtain ⟨μ', hH, hS⟩ := GlobalTheory.CongTop.exists_haar_sigmaFinite I'
    choose c' _ hc' _ using fun v : InfinitePlace I'.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I'.n (I'.ε v)
    have hg' : IsGaugeAll I' c' := hc'
    rw [hv c μf c' μ' hc hg', hrat I₀ (sameField_trans (sameField_symm hI') hI) hsig₀ c' μ' c₀ μ₀ hg' hc₀,
      ← hsum, Finset.prod_Ioc_succ_top (by omega),
      ENNReal.ofReal_mul (Finset.prod_nonneg fun M _ => rankFac_nonneg M), mul_assoc]
    obtain ⟨e, he⟩ := hI'
    simp only [rankFac_congr e he]

end GlobalTheory.FlagMeas.VolRatio
