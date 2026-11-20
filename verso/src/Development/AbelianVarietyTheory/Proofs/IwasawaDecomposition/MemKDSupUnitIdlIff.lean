import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Chr.IdlFact

namespace GlobalTheory.Mem.Chr.KDVal

variable {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]

open Classical in

/- English proof (translation)
Unfold `locF`. Rewrite using `[map_prod]`. Establish `hm : ∀ Q : HeightOneSpectrum (𝓞 L), Q ∈ aboveF (L` using `L) F v ↔ Q.under (𝓞 F) = v := fun Q => by`. Simplify using `[aboveF]`. Use `split_ifs with hw`.

Rewrite using `[Finset.prod_eq_single_of_mem w ((hm w).2 hw) (fun Q _ hQ => valAt_localIdele_ne hQ.symm _), valAt_localIdele_self]`. Establish `h0 : w.valuation L ((upF F k : Lˣ) : L) ≠ 0` using `by simp`. Unfold `ordF`. Rewrite using `[neg_neg, WithZero.exp_log h0]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _`.

Conclude with `Finset.prod_eq_one fun Q hQ => valAt_localIdele_ne (fun e : w = Q => hw (by rw [e]; exact (hm Q).1 hQ)) _`.
-/
theorem valAt_locF (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    valAt w (locF (L := L) F v k) =
      if w.under (𝓞 F) = v then WithZero.exp (-ordF w (upF F k)) else 1 := by
  unfold locF
  rw [map_prod]
  have hm : ∀ Q : HeightOneSpectrum (𝓞 L), Q ∈ aboveF (L := L) F v ↔ Q.under (𝓞 F) = v := fun Q => by
    simp [aboveF]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w ((hm w).2 hw) (fun Q _ hQ => valAt_localIdele_ne hQ.symm _),
      valAt_localIdele_self]
    have h0 : w.valuation L ((upF F k : Lˣ) : L) ≠ 0 := by simp
    unfold ordF
    rw [neg_neg, WithZero.exp_log h0]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  · exact Finset.prod_eq_one fun Q hQ => valAt_localIdele_ne (fun e : w = Q => hw (by rw [e]; exact (hm Q).1 hQ)) _

def balanced : Subgroup (Ideles L) where
  carrier := {a | ∀ w w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) → valAt w a = valAt w' a}
  one_mem' := fun w w' _ => by rw [map_one, map_one]
  mul_mem' := fun {a b} ha hb w w' h => by rw [map_mul, map_mul, ha w w' h, hb w w' h]
  inv_mem' := fun {a} ha w w' h => by rw [map_inv, map_inv, ha w w' h]

/- English proof (translation)
Introduce `a ha w w' _` and use `(ha w).trans (ha w').symm`.
-/
theorem unitIdl_le_balanced : unitIdl L ≤ balanced (L := L) F := fun a ha w w' _ =>
  (ha w).trans (ha w').symm

variable {F}

/- English proof (translation)
Introduce `w w' h` and use `by rw [valAt_locF, valAt_locF, hu, hu, h]`.
-/
theorem locF_mem_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : locF (L := L) F v k ∈ balanced (L := L) F := fun w w' h => by
  rw [valAt_locF, valAt_locF, hu, hu, h]

/- English proof (translation)
Set `T : Finset (HeightOneSpectrum (𝓞 F))` to `(finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 F)`. Set `m : HeightOneSpectrum (𝓞 F) → ℤ` to `fun v => if h : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v then -WithZero.log (valAt h.choose a) else 0`. Set `b : Ideles L` to `∏ v ∈ T, locF (L := L) F v (unif v) ^ m v`. Establish `hb : b ∈ G` using `prod_mem fun v _ => zpow_mem (hG _ _) _`. Establish `hval : ∀ w, valAt w b = valAt w a` using `fun w => by`.

Establish `h1 : ∀ v, v ≠ w.under (𝓞 F) → valAt w (locF (L` using `L) F v (unif v) ^ m v) = 1 := fun v hv => by`. Rewrite using `[map_zpow, valAt_locF, if_neg hv.symm, one_zpow]`. Simplify using `only [b]`. Rewrite using `[map_prod]`. Distinguish the cases in `hw : w.under (𝓞 F) ∈ T`.

Rewrite using `[Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu, ordF_unif_self, ← WithZero.exp_zsmul]`. Establish `hex : ∃ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F)` using `⟨w, rfl⟩`. Establish `hm : m (w.under (𝓞 F)) = -WithZero.log (valAt w a)`. Simplify using `only [m]`. Rewrite using `[dif_pos hex, ha w hex.choose hex.choose_spec]`.

Rewrite using `[hm]`. Simplify using `only [smul_eq_mul, mul_neg, neg_neg, mul_one]`. Conclude with `WithZero.exp_log (valAt_ne_zero w a)`. Rewrite using `[Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]`. Assume the negation of the conclusion as `hne`.

Conclude with `hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))`. Establish `hu' : b⁻¹ * a ∈ unitIdl L` using `fun w => by`. Rewrite using `[← valAt_apply, map_mul, map_inv, hval]`. Conclude with `inv_mul_cancel₀ (valAt_ne_zero w a)`. Rewrite using `[← mul_inv_cancel_left b a]`.

Conclude with `Subgroup.mul_mem_sup hb hu'`.
-/
theorem mem_sup_of_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (G : Subgroup (Ideles L)) (hG : ∀ v k, locF (L := L) F v k ∈ G) (a : Ideles L)
    (ha : a ∈ balanced (L := L) F) : a ∈ G ⊔ unitIdl L := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 F)
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles L := ∏ v ∈ T, locF (L := L) F v (unif v) ^ m v
  have hb : b ∈ G := prod_mem fun v _ => zpow_mem (hG _ _) _
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 F) → valAt w (locF (L := L) F v (unif v) ^ m v) = 1 := fun v hv => by
      rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul]
      have hex : ∃ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) := ⟨w, rfl⟩
      have hm : m (w.under (𝓞 F)) = -WithZero.log (valAt w a) := by
        simp only [m]
        rw [dif_pos hex, ha w hex.choose hex.choose_spec]
      rw [hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl L := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)
  rw [← mul_inv_cancel_left b a]
  exact Subgroup.mul_mem_sup hb hu'

end GlobalTheory.Mem.Chr.KDVal

open GlobalTheory.Mem.Chr.KDVal in
open Classical in

/- English proof (translation)
Introduce `R H a`. Take `⟨c, hc, hcm, hu, -⟩` from `GlobalTheory.Mem.HostCM.host_cm R H`. Establish `hiff : ∀ w w' : HeightOneSpectrum (𝓞 H.E), w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ (w' = w ∨ IsConjPl H w w')` using `fun w w' => by`. Rewrite using `[under_eq_iff_conjPl c hcm.rank hcm.ne, conjPl_main.2.1 R H w w']`. Establish `: c.toRingEquiv = H.conj.toRingEquiv` using `RingEquiv.ext hc`.

Rewrite using `[this]`. Prove the components needed by the constructor for the conclusion. Introduce `ha w w' h`. Establish `hle : KD H ⊔ unitIdl H.E ≤ balanced (L` using `H.E) H.F := by`. Use `sup_le ((Subgroup.closure_le _).2 ?_) (unitIdl_le_balanced _)` and prove the remaining obligations.

Introduce and unpack `x (hx | ⟨v, k, rfl⟩)`. Conclude with `unitIdl_le_balanced _ hx.1`. Conclude with `locF_mem_balanced hu v k`. Conclude with `hle ha w w' ((hiff w w').2 (Or.inr h))`. Introduce `h`.

Use `mem_sup_of_balanced hu _ (locF_mem_KD H) a fun w w' hw => ?_` and prove the remaining obligations. Break down `(hiff w w').1 hw with rfl | h'` into its components or cases. Both sides reduce to the same expression. Conclude with `h w w' h'`.
-/
theorem GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : Ideles H.E), a ∈ KD H ⊔ unitIdl H.E ↔ ∀ w w', IsConjPl H w w' → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w) = Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w') := by
  intro R H a
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hiff : ∀ w w' : HeightOneSpectrum (𝓞 H.E),
      w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ (w' = w ∨ IsConjPl H w w') := fun w w' => by
    rw [under_eq_iff_conjPl c hcm.rank hcm.ne, conjPl_main.2.1 R H w w']
    have : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
    rw [this]
  constructor
  · intro ha w w' h
    have hle : KD H ⊔ unitIdl H.E ≤ balanced (L := H.E) H.F := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) (unitIdl_le_balanced _)
      rintro x (hx | ⟨v, k, rfl⟩)
      · exact unitIdl_le_balanced _ hx.1
      · exact locF_mem_balanced hu v k
    exact hle ha w w' ((hiff w w').2 (Or.inr h))
  · intro h
    refine mem_sup_of_balanced hu _ (locF_mem_KD H) a fun w w' hw => ?_
    rcases (hiff w w').1 hw with rfl | h'
    · rfl
    · exact h w w' h'
