import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] rlt_top rlt_topRing adeles_t2Space

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))}

/- English proof (translation)
Establish `hd : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det = 1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s`. Rewrite using `[Matrix.det_fin_one, hx]`. Establish `hdd` using `DetLift.det_mul_conj_det _ _ x.2`. Use `set d := ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det with hdef`. Establish `hci : ∀ w : HeightOneSpectrum (𝓞 H.E), adAt H.F w (iA H.F H.E (algebraMap (𝓞 H.E) H.E c)) = algebraMap H.E _ (algebraMap (𝓞 H.E) H.E c)` using `fun w => adAt_inclE H.F w _`.

Establish `hsv : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w s) ≤ 1` using `(mem_rInt_iff H.F H.E s).1 hs`. Establish `hle : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) ≤ 1` using `fun w => by`. Rewrite using `[hd, map_add, map_one, map_mul, hci]`. Use `Valuation.map_add_le _ (by rw [map_one]) ?_` and prove the remaining obligations. Rewrite using `[map_mul, valued_algebraMap]`.

Conclude with `mul_le_one' (HeightOneSpectrum.valuation_le_one _ _) (hsv w)`. Establish `hv1 : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) = 1` using `fun w => by`. Establish `e` using `congrArg (fun z => Valued.v (adAt H.F w z)) hdd`. Simplify using `only [map_mul, map_one] at e`. Use `le_antisymm (hle w) ?_` and prove the remaining obligations.

Establish `e' : Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) = 1`. Rewrite using `[← valued_sigR (host_cmData R H) w d]`. Conclude with `e`. Combine the equalities or inequalities in the displayed calculation. Establish `hcomp` using `fun w => DetSpec.compAt_eq hb w`.

Use `mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_` and prove the remaining obligations. Rewrite using `[hcomp w, map_mul, hv1 w, one_mul, valued_sigR, adAt_finAf]`. Establish `h0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0`. Rewrite using `[← (Valued.v : Valuation (P.adicCompletion H.E) _).ne_zero_iff, valued_sigR, adAt_finAf]`. Conclude with `DetSpec.val_compAt_ne _ _`.

Rewrite using `[hcomp P, mul_div_cancel_right₀ _ h0]`. Use `show Valued.v (adAt H.F P d - 1) < 1`. Rewrite using `[hd, map_add, map_one, add_sub_cancel_left, map_mul, hci, map_mul, valued_algebraMap]`. Establish `hlt : P.valuation H.E (algebraMap (𝓞 H.E) H.E c) < 1` using `(HeightOneSpectrum.valuation_lt_one_iff_mem P c).2 (hc P hP)`. Conclude with `(mul_le_of_le_one_right' (hsv P)).trans_lt hlt`.
-/
theorem lift_mem_KDq (hl : LevOk H SG SQ) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (b : GlobalTheory.Mem.Chr.Ideles H.E)
    (hb : IsDetLift (host_cmData R H) x.1 b) (c : 𝓞 H.E) (hc : ∀ P ∈ uSG SG SQ, c ∈ P.asIdeal) (s : AfE H.F H.E)
    (hs : s ∈ RInt H.F H.E)
    (hx : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s) : b ∈ KDq H SQ := by
  have hd : ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det =
      1 + iA H.F H.E (algebraMap (𝓞 H.E) H.E c) * s := by
    rw [Matrix.det_fin_one, hx]
  have hdd := DetLift.det_mul_conj_det _ _ x.2
  set d := ((x.1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)).det with hdef
  have hci : ∀ w : HeightOneSpectrum (𝓞 H.E), adAt H.F w (iA H.F H.E (algebraMap (𝓞 H.E) H.E c)) =
      algebraMap H.E _ (algebraMap (𝓞 H.E) H.E c) := fun w => adAt_inclE H.F w _
  have hsv : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w s) ≤ 1 := (mem_rInt_iff H.F H.E s).1 hs
  have hle : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) ≤ 1 := fun w => by
    rw [hd, map_add, map_one, map_mul, hci]
    refine Valuation.map_add_le _ (by rw [map_one]) ?_
    rw [map_mul, valued_algebraMap]
    exact mul_le_one' (HeightOneSpectrum.valuation_le_one _ _) (hsv w)
  have hv1 : ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (adAt H.F w d) = 1 := fun w => by
    have e := congrArg (fun z => Valued.v (adAt H.F w z)) hdd
    simp only [map_mul, map_one] at e
    refine le_antisymm (hle w) ?_
    have e' : Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) = 1 := by
      rw [← valued_sigR (host_cmData R H) w d]
      exact e
    calc (1 : _) = Valued.v (adAt H.F w d) * Valued.v (adAt H.F (conjPrime₂ w) d) := e'.symm
      _ ≤ _ := mul_le_of_le_one_right' (hle _)
  have hcomp := fun w => DetSpec.compAt_eq hb w
  refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
  · rw [hcomp w, map_mul, hv1 w, one_mul, valued_sigR, adAt_finAf]
  · have h0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 := by
      rw [← (Valued.v : Valuation (P.adicCompletion H.E) _).ne_zero_iff, valued_sigR, adAt_finAf]
      exact DetSpec.val_compAt_ne _ _
    rw [hcomp P, mul_div_cancel_right₀ _ h0]
    show Valued.v (adAt H.F P d - 1) < 1
    rw [hd, map_add, map_one, add_sub_cancel_left, map_mul, hci, map_mul,
      valued_algebraMap]
    have hlt : P.valuation H.E (algebraMap (𝓞 H.E) H.E c) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem P c).2 (hc P hP)
    exact (mul_le_of_le_one_right' (hsv P)).trans_lt hlt

/- English proof (translation)
Introduce `R H SG SQ hl`. Take `⟨a, ha0, ha⟩` from `rlt_exists_a (uSG SG SQ)`. Use `set c : AfE H.F H.E := iA H.F H.E (algebraMap (𝓞 H.E) H.E a)⁻¹ with hc'`. Establish `hca : iA H.F H.E (algebraMap (𝓞 H.E) H.E a) * c = 1`. Rewrite using `[hc', ← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]`.

Set `W : Set (GL (Fin 1) (AfE H.F H.E))` to `{u | c * ((u : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E}`. Establish `hWo : IsOpen W`. Use `rlt_isOpen_intAf.preimage ?_` and prove the remaining obligations. Conclude with `continuous_const.mul ((Units.continuous_val.matrix_elem 0 0).sub continuous_const)`. Establish `hW1 : (1 : GL (Fin 1) (AfE H.F H.E)) ∈ W` using `by show c * (((1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E`.

Simplify using the standard rewrite rules. Establish `hsub : ∀ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), x.1 ∈ W → x ∈ (u1Dt H SQ).ker`. Introduce `x hx`. Take `⟨b, hb⟩` from `exists_lift H x`. Rewrite using `[MonoidHom.mem_ker, normOneFiniteAdeleDetClass_of_isDetLift H SQ x b hb]`.

Use `(QuotientGroup.eq_one_iff b).2 (lift_mem_KDq hl x b hb a ha _ hx ?_)` and prove the remaining obligations. Rewrite using `[← mul_assoc, hca, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnh : (((u1Dt H SQ).ker : Subgroup _) : Set (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))) ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))` using `Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hW1) fun x hx => hsub x hx`. Conclude with `Subgroup.isOpen_of_mem_nhds _ hnh`.
-/
theorem isOpen_ker_u1Dt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  intro R H SG SQ hl
  classical
  obtain ⟨a, ha0, ha⟩ := rlt_exists_a (uSG SG SQ)
  set c : AfE H.F H.E := iA H.F H.E (algebraMap (𝓞 H.E) H.E a)⁻¹ with hc'
  have hca : iA H.F H.E (algebraMap (𝓞 H.E) H.E a) * c = 1 := by
    rw [hc', ← map_mul, mul_inv_cancel₀ (by simpa using ha0), map_one]
  let W : Set (GL (Fin 1) (AfE H.F H.E)) :=
    {u | c * ((u : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E}
  have hWo : IsOpen W := by
    refine rlt_isOpen_intAf.preimage ?_
    exact continuous_const.mul ((Units.continuous_val.matrix_elem 0 0).sub continuous_const)
  have hW1 : (1 : GL (Fin 1) (AfE H.F H.E)) ∈ W := by
    show c * (((1 : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 - 1) ∈ Formalism.L2.Herm.intAf H.F H.E
    simp
  have hsub : ∀ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), x.1 ∈ W → x ∈ (u1Dt H SQ).ker := by
    intro x hx
    obtain ⟨b, hb⟩ := exists_lift H x
    rw [MonoidHom.mem_ker, normOneFiniteAdeleDetClass_of_isDetLift H SQ x b hb]
    refine (QuotientGroup.eq_one_iff b).2 (lift_mem_KDq hl x b hb a ha _ hx ?_)
    rw [← mul_assoc, hca, one_mul]
    ring
  have hnh : (((u1Dt H SQ).ker : Subgroup _) : Set (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H))) ∈ 𝓝 (1 : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) :=
    Filter.mem_of_superset ((hWo.preimage continuous_subtype_val).mem_nhds hW1) fun x hx => hsub x hx
  exact Subgroup.isOpen_of_mem_nhds _ hnh

end GlobalTheory.Mem.Col2.FullDt

end
