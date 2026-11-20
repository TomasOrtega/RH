import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.NuCharNorm

open Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.LocTriv
open GlobalTheory.Mem.Chr (finPartI unitIdl locF)
open GlobalTheory.NormSum.UnramHecke GlobalTheory.Mem.Col2.SplitChar

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

/- English proof (translation)
Rewrite using `[HChar.inf, MonoidHom.comp_apply, infDiag, MonoidHom.finsetProd_apply, map_prod, ← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L => w.comap (algebraMap F L)]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[HChar.resInf_apply]`. Conclude with `Finset.prod_congr (by ext; simp [aboveInf]) fun _ _ => rfl`.
-/
theorem inf_upF (χ : HChar L) (k : Fˣ) : χ.inf (upF F k) = ∏ w : InfinitePlace F, χ.resInf w k := by
  classical
  rw [HChar.inf, MonoidHom.comp_apply, infDiag, MonoidHom.finsetProd_apply, map_prod,
    ← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L => w.comap (algebraMap F L)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [HChar.resInf_apply]
  exact Finset.prod_congr (by ext; simp [aboveInf]) fun _ _ => rfl

end General

/- English proof (translation)
Establish `hfin : ∀ k : (D.host.F)ˣ, χ.1 (finIdl D (incU D (upF D.host.F k))) = 1` using `fun k => by`. Establish `h1` using `χ.2.2 (upF D.host.F k)`. Rewrite `h1` using `[← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU]`. Establish `h2 : χ.inf (upF D.host.F k) = 1`. Rewrite using `[inf_upF]`.

Conclude with `Finset.prod_eq_one fun w _ => ht.2 w k`. Rewrite `h2` using `[HChar.inf, MonoidHom.comp_apply]`. Rewrite `h1` using `[h2, one_mul]`. Conclude with `h1`. Take `⟨n, hn, hx⟩` from `GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)`.

Take `⟨a, r, hr, e⟩` from `exists_approx (x : AE D) (Nat.mul_pos (Nat.mul_pos prod_g_pos hM) hn)`. Establish `hs : -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) ∈ OhE D` using `neg_mem (mul_mem hr hx)`. Establish `h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 = ((∏ i, D.host.g i : ℕ) : AE D) * ((M : AE D) * -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))))`. Rewrite `e` using `[Nat.cast_mul, Nat.cast_mul]`. Take the linear combination `x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e`.

Generalize the expression as in `-(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) = s at hs h1`. Generalize the expression as in `hG : ((∏ i, D.host.g i : ℕ) : AE D) = G at h1`. Establish `hGm : G ∈ OhE D` using `hG ▸ natCast_mem _ _`. Establish `hGs : sgA D G = G` using `hG ▸ map_natCast _ _`. Establish `hMs : sgA D (M : AE D) = M` using `map_natCast _ _`.

Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Take `⟨v, hv⟩` from `GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (D.host.g_prime 0)`. Use `vl_cong (mul_mem (natCast_mem _ M) hs) 0 v hv` as an intermediate fact. Rewrite `this` using `[hG, ← h1, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one]`.

Conclude with `lt_irrefl _ this`. Set `z : (AE D)ˣ` to `incU D (Units.mk0 a ha) * x⁻¹`. Establish `hz : (z : AE D) = 1 + G * ((M : AE D) * s)` using `eq_add_of_sub_eq' h1`. Set `w : (AE D)ˣ` to `z * sgU D z`. Establish `hw : (w : AE D) - 1 = (M : AE D) * (G * (s + sgA D s + G * M * s * sgA D s))`.

Establish `e1 : (w : AE D) = (z : AE D) * sgA D z` using `rfl`. Rewrite using `[e1, hz, map_add, map_one, map_mul, map_mul, hGs, hMs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwM : ∀ P, vl D P ((w : AE D) - 1) ≤ vl D P (M : AE D)` using `fun P => by`. Rewrite using `[hw, map_mul]`.

Conclude with `mul_le_of_le_one_right' (vl_le (mul_mem hGm (add_mem (add_mem hs (sgA_mem D hs)) (mul_mem (mul_mem (mul_mem hGm (natCast_mem _ _)) hs) (sgA_mem D hs)))) P)`. Establish `hvM : ∀ P, vl D P (M : AE D) = Valued.v (((M : D.host.E) : P.adicCompletion D.host.E))` using `fun P => by`. Rewrite using `[vl_nat]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm`. Take `⟨c, -, -, hu, -⟩` from `GlobalTheory.Mem.HostCM.host_cm D.R D.host`.

Take `⟨b, hb, hun, hc⟩` from `exists_of_balanced hu ((χ.1.comp (finPartI D.host.E)).ker) (fun v k => (MonoidHom.mem_ker).2 (GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k)) (finIdl D w) (norm_balanced z)`. Establish `hb' : χ.1 (finPartI D.host.E b) = 1` using `(MonoidHom.mem_ker).1 hb`. Establish `hc1 : χ.1 (finPartI D.host.E (b⁻¹ * finIdl D w)) = 1`. Use `hker _ hun (fun _ => rfl) fun P => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ _`.

Rewrite using `[← hvM]`. Distinguish the cases in `hP : vl D P ((w : AE D) - 1) < 1`. Establish `h2 : valAt P (finIdl D w) = 1`. Rewrite using `[valAt_apply, ← sub_add_cancel ((finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P) 1, add_comm]`. Conclude with `Valuation.map_one_add_of_lt _ (by rw [vl_sub_one]; exact hP)`.

Establish `h3 : Units.map (ev P) (b⁻¹ * finIdl D w) = Units.map (ev P) (finIdl D w)`. Rewrite using `[map_mul, map_inv, hc P h2, inv_one, one_mul]`. Establish `h4 : ((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P = (finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P` using `congrArg Units.val h3`. Rewrite using `[h4, vl_sub_one]`. Conclude with `hwM P`.

Establish `hM1 : vl D P (M : AE D) = 1` using `le_antisymm (vl_le (natCast_mem _ _) P) ((not_lt.1 hP).trans (hwM P))`. Rewrite using `[hM1]`. Use `(Valuation.map_sub _ _ _).trans ?_` and prove the remaining obligations. Establish `hP1 : Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P) = 1` using `hun P`. Rewrite using `[hP1, map_one, max_self]`.

Establish `e2 : finPartI D.host.E (b⁻¹ * finIdl D w) = (finPartI D.host.E b)⁻¹ * finIdl D w`. Rewrite using `[map_mul, map_inv, finPartI_finIdl]`. Rewrite `hc1` using `[e2, map_mul, map_inv, hb', inv_one, one_mul]`. Take `⟨k, hk⟩` from `exists_real_norm (Units.mk0 a ha)`. Establish `h5 : χ.1 (finIdl D (incU D (Units.mk0 a ha) * sgU D (incU D (Units.mk0 a ha)))) = 1`.

Rewrite using `[hk]`. Conclude with `hfin k`. Establish `h6 : χ.1 (finIdl D ((incU D (Units.mk0 a ha) * x⁻¹) * sgU D (incU D (Units.mk0 a ha) * x⁻¹))) = 1` using `hc1`. Rewrite `h6` using `[map_mul (sgU D), mul_mul_mul_comm, map_inv, ← mul_inv, map_mul, map_mul, h5, one_mul, map_inv, map_inv, inv_eq_one]`. Conclude with `h6`.
-/
theorem norm_killed (D : D7) (χ : HChar D.host.E) (ht : χ.TrivOn D.host.F) (M : ℕ) (hM : 0 < M)
    (hker : ∀ a : Ideles D.host.E, a ∈ unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) →
      (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤
        Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1)
    (x : (AE D)ˣ) : χ.1 (finIdl D (x * sgU D x)) = 1 := by
  have hfin : ∀ k : (D.host.F)ˣ, χ.1 (finIdl D (incU D (upF D.host.F k))) = 1 := fun k => by
    have h1 := χ.2.2 (upF D.host.F k)
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
    have h2 : χ.inf (upF D.host.F k) = 1 := by
      rw [inf_upF]
      exact Finset.prod_eq_one fun w _ => ht.2 w k
    rw [HChar.inf, MonoidHom.comp_apply] at h2
    rw [h2, one_mul] at h1
    exact h1
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos (Nat.mul_pos prod_g_pos hM) hn)
  have hs : -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) ∈ OhE D := neg_mem (mul_mem hr hx)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 =
      ((∏ i, D.host.g i : ℕ) : AE D) * ((M : AE D) * -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul, Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  generalize -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) = s at hs h1
  generalize hG : ((∏ i, D.host.g i : ℕ) : AE D) = G at h1
  have hGm : G ∈ OhE D := hG ▸ natCast_mem _ _
  have hGs : sgA D G = G := hG ▸ map_natCast _ _
  have hMs : sgA D (M : AE D) = M := map_natCast _ _
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (D.host.g_prime 0)
    have := vl_cong (mul_mem (natCast_mem _ M) hs) 0 v hv
    rw [hG, ← h1, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
    exact lt_irrefl _ this
  let z : (AE D)ˣ := incU D (Units.mk0 a ha) * x⁻¹
  have hz : (z : AE D) = 1 + G * ((M : AE D) * s) := eq_add_of_sub_eq' h1
  let w : (AE D)ˣ := z * sgU D z
  have hw : (w : AE D) - 1 = (M : AE D) * (G * (s + sgA D s + G * M * s * sgA D s)) := by
    have e1 : (w : AE D) = (z : AE D) * sgA D z := rfl
    rw [e1, hz, map_add, map_one, map_mul, map_mul, hGs, hMs]
    ring
  have hwM : ∀ P, vl D P ((w : AE D) - 1) ≤ vl D P (M : AE D) := fun P => by
    rw [hw, map_mul]
    exact mul_le_of_le_one_right' (vl_le (mul_mem hGm (add_mem (add_mem hs (sgA_mem D hs))
      (mul_mem (mul_mem (mul_mem hGm (natCast_mem _ _)) hs) (sgA_mem D hs)))) P)
  have hvM : ∀ P, vl D P (M : AE D) = Valued.v (((M : D.host.E) : P.adicCompletion D.host.E)) := fun P => by
    rw [vl_nat]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu ((χ.1.comp (finPartI D.host.E)).ker)
    (fun v k => (MonoidHom.mem_ker).2 (GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k)) (finIdl D w) (norm_balanced z)
  have hb' : χ.1 (finPartI D.host.E b) = 1 := (MonoidHom.mem_ker).1 hb
  have hc1 : χ.1 (finPartI D.host.E (b⁻¹ * finIdl D w)) = 1 := by
    refine hker _ hun (fun _ => rfl) fun P => ?_
    change Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ _
    rw [← hvM]
    by_cases hP : vl D P ((w : AE D) - 1) < 1
    · have h2 : valAt P (finIdl D w) = 1 := by
        rw [valAt_apply, ← sub_add_cancel ((finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P) 1, add_comm]
        exact Valuation.map_one_add_of_lt _ (by rw [vl_sub_one]; exact hP)
      have h3 : Units.map (ev P) (b⁻¹ * finIdl D w) = Units.map (ev P) (finIdl D w) := by
        rw [map_mul, map_inv, hc P h2, inv_one, one_mul]
      have h4 : ((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P =
          (finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P := congrArg Units.val h3
      rw [h4, vl_sub_one]
      exact hwM P
    · have hM1 : vl D P (M : AE D) = 1 := le_antisymm (vl_le (natCast_mem _ _) P) ((not_lt.1 hP).trans (hwM P))
      rw [hM1]
      refine (Valuation.map_sub _ _ _).trans ?_
      have hP1 : Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P) = 1 := hun P
      rw [hP1, map_one, max_self]
  have e2 : finPartI D.host.E (b⁻¹ * finIdl D w) = (finPartI D.host.E b)⁻¹ * finIdl D w := by
    rw [map_mul, map_inv, finPartI_finIdl]
  rw [e2, map_mul, map_inv, hb', inv_one, one_mul] at hc1
  obtain ⟨k, hk⟩ := exists_real_norm (Units.mk0 a ha)
  have h5 : χ.1 (finIdl D (incU D (Units.mk0 a ha) * sgU D (incU D (Units.mk0 a ha)))) = 1 := by
    rw [hk]
    exact hfin k
  have h6 : χ.1 (finIdl D ((incU D (Units.mk0 a ha) * x⁻¹) * sgU D (incU D (Units.mk0 a ha) * x⁻¹))) = 1 := hc1
  rw [map_mul (sgU D), mul_mul_mul_comm, map_inv, ← mul_inv, map_mul, map_mul, h5, one_mul, map_inv, map_inv,
    inv_eq_one] at h6
  exact h6

end GlobalTheory.NuCharNorm

/- English proof (translation)
Introduce `D χ ht ⟨M, hM, h⟩ x` and use `GlobalTheory.NuCharNorm.norm_killed D χ ht M hM h x`.
-/
theorem GlobalTheory.NuCharNorm.chi_norm_one : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.TrivOn D.host.F → (∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles D.host.E, a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1) → ∀ x : (AE D)ˣ, χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D (x * sgU D x)) = 1 :=
  fun D χ ht ⟨M, hM, h⟩ x => GlobalTheory.NuCharNorm.norm_killed D χ ht M hM h x
