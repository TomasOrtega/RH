import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 400000

namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDyIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop :=
  IsSplitIdem D e ∧ finPart D e ∈ intAE D ∧
    ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def DyadIdem (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → ∃ e : AE D, IsDyIdem v e

open Classical in

def eDy (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  if (2 : 𝓞 D.host.F) ∈ v.asIdeal then Classical.epsilon (IsDyIdem (D := D) v) else 0

/- English proof (translation)
Unfold `eDy`. Rewrite using `[if_pos h2]`. Conclude with `Classical.epsilon_spec (hdy v h2)`.
-/
theorem eDy_spec (hdy : DyadIdem D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) :
    IsDyIdem v (eDy (D := D) v) := by
  unfold eDy
  rw [if_pos h2]
  exact Classical.epsilon_spec (hdy v h2)

/- English proof (translation)
Unfold `eDy`. Rewrite using `[if_neg h2]`.
-/
theorem eDy_of_not (v : HeightOneSpectrum (𝓞 D.host.F)) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) : eDy (D := D) v = 0 := by
  unfold eDy; rw [if_neg h2]

/- English proof (translation)
Establish `h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `two_ne_zero`. Use `(Ideal.finite_factors h0).subset ?_` and prove the remaining obligations. Introduce `v hv`.

Simplify using `only [Set.mem_setOf_eq] at hv ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hv`.
-/
theorem dyad_finite (D : D7) : {v : HeightOneSpectrum (𝓞 D.host.F) | (2 : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

def e2 (D : D7) : AE D := ∑ v ∈ (dyad_finite D).toFinset, eDy v

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fstA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : fstA D.host.F (pairA D.host.F x y) = x := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sndA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : sndA D.host.F (pairA D.host.F x y) = y := rfl

open Classical in
/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Take `⟨α', rfl, h1', h0'⟩` from `h'`. Use `split_ifs with hvv`. Substitute `hvv` using the available equality. Use `Fock.DRho.AF_ext D ?_ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, fstA_pairA, zero_mul]`. Rewrite using `[map_mul, sndA_pairA, sndA_pairA]`. Use `Formalism.IndefR.Fin.af_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[h1', mul_one]`. Rewrite using `[h0 w hw, zero_mul]`. Use `Fock.DRho.AF_ext D ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, fstA_pairA, zero_mul, map_zero]`.

Rewrite using `[map_mul, sndA_pairA, sndA_pairA, map_zero]`. Use `Formalism.IndefR.Fin.af_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_zero]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[h0' w hvv, mul_zero]`. Rewrite using `[h0 w hw, zero_mul]`.
-/
theorem placeIdem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v' ε') : ε * ε' = if v = v' then ε else 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, h1', h0'⟩ := h'
  split_ifs with hvv
  · subst hvv
    refine Fock.DRho.AF_ext D ?_ ?_
    · rw [map_mul, fstA_pairA, zero_mul]
    · rw [map_mul, sndA_pairA, sndA_pairA]
      refine Formalism.IndefR.Fin.af_ext fun w => ?_
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1', mul_one]
      · rw [h0 w hw, zero_mul]
  · refine Fock.DRho.AF_ext D ?_ ?_
    · rw [map_mul, fstA_pairA, zero_mul, map_zero]
    · rw [map_mul, sndA_pairA, sndA_pairA, map_zero]
      refine Formalism.IndefR.Fin.af_ext fun w => ?_
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [h0' w hvv, mul_zero]
      · rw [h0 w hw, zero_mul]

/- English proof (translation)
Take `⟨α, rfl, -, -⟩` from `h`. Use `show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0`. Rewrite using `[Fock.DRho.infPart_tmul, fstA_pairA, TensorProduct.zero_tmul]`.
-/
theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := h
  show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Fock.DRho.infPart_tmul, fstA_pairA, TensorProduct.zero_tmul]

/- English proof (translation)
Rewrite using `[← hs, mul_add, he, hc, add_zero]`.
-/
theorem idem_mul_eps {e : AE D} {ε : AF D.host.F} (he : e * e = e) (hc : e * cA D e = 0)
    (hs : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : e * algebraMap (AF D.host.F) (AE D) ε = e := by
  rw [← hs, mul_add, he, hc, add_zero]

/- English proof (translation)
Rewrite using `[← idem_mul_eps he hc hs, map_mul, infPart_placeIdem hε, mul_zero]`.
-/
theorem infPart_idem {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (he : e * e = e)
    (hc : e * cA D e = 0) (hε : IsPlaceIdem D v ε) (hs : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    infPart D e = 0 := by
  rw [← idem_mul_eps he hc hs, map_mul, infPart_placeIdem hε, mul_zero]

open Classical in
/- English proof (translation)
Distinguish the cases in `h2 : (2 : 𝓞 D.host.F) ∈ v'.asIdeal`. Take `⟨⟨he, hc, -⟩, -, ε', hε', hs⟩` from `eDy_spec hdy v' h2 conv_lhs => rw [← idem_mul_eps he hc hs]`. Rewrite using `[mul_assoc, ← map_mul, placeIdem_mul hε' hε]`. Use `split_ifs`. Conclude with `idem_mul_eps he hc hs`.

Rewrite using `[map_zero, mul_zero]`. Apply the tactic sequence `rw [eDy_of_not v' h2, zero_mul]; split_ifs <;> rfl`.
-/
theorem eDy_mul_eps (hdy : DyadIdem D) (v' : HeightOneSpectrum (𝓞 D.host.F)) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    eDy (D := D) v' * algebraMap (AF D.host.F) (AE D) ε = if v' = v then eDy v' else 0 := by
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v'.asIdeal
  · obtain ⟨⟨he, hc, -⟩, -, ε', hε', hs⟩ := eDy_spec hdy v' h2
    conv_lhs => rw [← idem_mul_eps he hc hs]
    rw [mul_assoc, ← map_mul, placeIdem_mul hε' hε]
    split_ifs
    · exact idem_mul_eps he hc hs
    · rw [map_zero, mul_zero]
  · rw [eDy_of_not v' h2, zero_mul]; split_ifs <;> rfl

/- English proof (translation)
Unfold `e2`. Rewrite using `[Finset.sum_mul]`. Distinguish the cases in `h : (2 : 𝓞 D.host.F) ∈ v.asIdeal`. Rewrite using `[Finset.sum_eq_single v]`. Rewrite using `[eDy_mul_eps hdy v hε, if_pos rfl]`.

Introduce `b _ hb`. Rewrite using `[eDy_mul_eps hdy b hε, if_neg hb]`. Introduce `hv`. Conclude with `absurd ((Set.Finite.mem_toFinset (dyad_finite D)).2 h) hv`. Rewrite using `[eDy_of_not v h]`.

Use `Finset.sum_eq_zero fun b hb => ?_` and prove the remaining obligations. Rewrite using `[eDy_mul_eps hdy b hε, if_neg]`. Introduce and unpack `rfl`. Conclude with `h ((Set.Finite.mem_toFinset (dyad_finite D)).1 hb)`.
-/
theorem dyadic_idempotent_mul_place_idempotent (hdy : DyadIdem D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) : e2 D * algebraMap (AF D.host.F) (AE D) ε = eDy v := by
  unfold e2
  rw [Finset.sum_mul]
  by_cases h : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · rw [Finset.sum_eq_single v]
    · rw [eDy_mul_eps hdy v hε, if_pos rfl]
    · intro b _ hb; rw [eDy_mul_eps hdy b hε, if_neg hb]
    · intro hv; exact absurd ((Set.Finite.mem_toFinset (dyad_finite D)).2 h) hv
  · rw [eDy_of_not v h]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [eDy_mul_eps hdy b hε, if_neg]
    rintro rfl
    exact h ((Set.Finite.mem_toFinset (dyad_finite D)).1 hb)

/- English proof (translation)
Distinguish the cases in `h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal`. Take `⟨⟨he, hc, -⟩, -, ε, hε, hs⟩` from `eDy_spec hdy v h2`. Conclude with `infPart_idem he hc hε hs`. Rewrite using `[eDy_of_not v h2, map_zero]`.
-/
theorem infPart_eDy (hdy : DyadIdem D) (v : HeightOneSpectrum (𝓞 D.host.F)) : infPart D (eDy (D := D) v) = 0 := by
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · obtain ⟨⟨he, hc, -⟩, -, ε, hε, hs⟩ := eDy_spec hdy v h2
    exact infPart_idem he hc hε hs
  · rw [eDy_of_not v h2, map_zero]

/- English proof (translation)
Unfold `e2`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun v _ => infPart_eDy hdy v`.
-/
theorem infinite_part_dyadic_idempotent (hdy : DyadIdem D) : infPart D (e2 D) = 0 := by
  unfold e2; rw [map_sum]; exact Finset.sum_eq_zero fun v _ => infPart_eDy hdy v

/- English proof (translation)
Unfold `e2`. Rewrite using `[map_sum]`. Use `AddSubgroup.sum_mem _ fun v hv => ?_` and prove the remaining obligations. Establish `h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal` using `(Set.Finite.mem_toFinset (dyad_finite D)).1 hv`. Conclude with `(eDy_spec hdy v h2).2.1`.
-/
theorem dyadic_idempotent_integral (hdy : DyadIdem D) : finPart D (e2 D) ∈ intAE D := by
  unfold e2; rw [map_sum]
  refine AddSubgroup.sum_mem _ fun v hv => ?_
  have h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal := (Set.Finite.mem_toFinset (dyad_finite D)).1 hv
  exact (eDy_spec hdy v h2).2.1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPart_algebraMap (r : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) r) = sndA D.host.F r ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `hε`. Use `AddSubgroup.subset_closure ⟨sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * pairA D.host.F 0 α), ?_, 1, ?_⟩` and prove the remaining obligations. Introduce `w`. Rewrite using `[map_mul, sndA_pairA, map_mul]`. Establish `e : evalV D.host.F w (sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2))) = algebraMap D.host.F (w.adicCompletion D.host.F) (1 / 2)`.

Rewrite using `[AlgHom.commutes, AlgHom.commutes]`. Rewrite using `[e]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[h1, mul_one]`.

Establish `hv2 : Valued.v (((2 : 𝓞 D.host.F) : D.host.F) : w.adicCompletion D.host.F) = 1`. Use `le_antisymm (Formalism.IndefR.Fin.val_coe_le_one w 2) ?_` and prove the remaining obligations. Conclude with `not_lt.1 fun h => h2 ((Formalism.IndefR.Fin.val_coe_lt_one_iff w 2).1 h)`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hprod : algebraMap D.host.F (w.adicCompletion D.host.F) (1 / 2) * (((2 : 𝓞 D.host.F) : D.host.F) : w.adicCompletion D.host.F) = 1`.

Establish `hc2 : (((2 : 𝓞 D.host.F) : D.host.F)) = 2` using `by norm_cast`. Rewrite using `[← Formalism.IndefR.Fin.algebraMap_adic_eq (D := D) w, hc2, ← map_mul]`. Evaluate the numerical expressions. Establish `hv` using `congrArg Valued.v hprod`. Rewrite `hv` using `[map_mul, hv2, mul_one, map_one]`.

Rewrite using `[hv]`. Rewrite using `[h0 w hw, mul_zero]`. Conclude with `zero_mem _`. Rewrite using `[finPart_algebraMap]`. Both sides reduce to the same expression.
-/
theorem half_mem_int {v : HeightOneSpectrum (𝓞 D.host.F)} (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) :
    finPart D (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * ε)) ∈ intAE D := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  refine AddSubgroup.subset_closure ⟨sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * pairA D.host.F 0 α), ?_,
    1, ?_⟩
  · intro w
    rw [map_mul, sndA_pairA, map_mul]
    have e : evalV D.host.F w (sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2))) =
        algebraMap D.host.F (w.adicCompletion D.host.F) (1 / 2) := by
      rw [AlgHom.commutes, AlgHom.commutes]
    rw [e]
    by_cases hw : w = v
    · subst hw
      rw [h1, mul_one]
      have hv2 : Valued.v (((2 : 𝓞 D.host.F) : D.host.F) : w.adicCompletion D.host.F) = 1 := by
        refine le_antisymm (Formalism.IndefR.Fin.val_coe_le_one w 2) ?_
        exact not_lt.1 fun h => h2 ((Formalism.IndefR.Fin.val_coe_lt_one_iff w 2).1 h)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have hprod : algebraMap D.host.F (w.adicCompletion D.host.F) (1 / 2) *
          (((2 : 𝓞 D.host.F) : D.host.F) : w.adicCompletion D.host.F) = 1 := by
        have hc2 : (((2 : 𝓞 D.host.F) : D.host.F)) = 2 := by norm_cast
        rw [← Formalism.IndefR.Fin.algebraMap_adic_eq (D := D) w, hc2, ← map_mul]; norm_num
      have hv := congrArg Valued.v hprod
      rw [map_mul, hv2, mul_one, map_one] at hv
      rw [hv]
    · rw [h0 w hw, mul_zero]
      exact zero_mem _
  · rw [finPart_algebraMap]; rfl

section Sym

variable (S T : HSp D)

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul a w => show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (a ⊗ₜ[D.host.F] w)) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]`. Use `show a ⊗ₜ[D.host.F] star (star w) = _`.

Rewrite using `[star_star]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA' (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a w =>
    show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (a ⊗ₜ[D.host.F] w)) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    show a ⊗ₜ[D.host.F] star (star w) = _
    rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Unfold `hO`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hO_smul_left (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/- English proof (translation)
Unfold `hO`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

/- English proof (translation)
Unfold `symplO`. Rewrite using `[hO_smul_left, hO_smul_right, cA_cA']`.
-/
theorem symplO_smul_adj (a : AE D) (x y : WO S T) : symplO S T (a • x) y = symplO S T x (cA D a • y) := by
  unfold symplO
  rw [hO_smul_left, hO_smul_right, cA_cA']

/- English proof (translation)
Unfold `symplO`. Rewrite using `[hO_smul_left, mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`.
-/
theorem symplO_alg_left (r : AF D.host.F) (x y : WO S T) :
    symplO S T (algebraMap (AF D.host.F) (AE D) r • x) y = r * symplO S T x y := by
  unfold symplO
  rw [hO_smul_left, mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, Formalism.IndefR.Fin.symplO_add_left, Formalism.IndefR.Fin.symplO_neg_left, ← sub_eq_add_neg]`.
-/
theorem symplO_sub_left (x x' y : WO S T) : symplO S T (x - x') y = symplO S T x y - symplO S T x' y := by
  rw [sub_eq_add_neg, Formalism.IndefR.Fin.symplO_add_left, Formalism.IndefR.Fin.symplO_neg_left, ← sub_eq_add_neg]

def halfE (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2))

/- English proof (translation)
Unfold `symplOH halfE`. Rewrite using `[symplO_alg_left]`.
-/
theorem symplOH_eq (x y : WO S T) : symplOH S T x y = symplO S T (halfE D • x) y := by
  unfold symplOH halfE; rw [symplO_alg_left]

/- English proof (translation)
Rewrite using `[← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]`. Evaluate the numerical expressions.
-/
theorem two_halfE : (2 : AF D.host.F) * algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num

/- English proof (translation)
The claim follows from `Formalism.IndefR.Fin.symplOH_two S T x y`.
-/
theorem symplOH_add_self (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y :=
  Formalism.IndefR.Fin.symplOH_two S T x y

/- English proof (translation)
Take `⟨h1, h2⟩` from `Fock.DRho.symplOH_real_fin S T r z hr hz`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← symplOH_add_self, h1, add_zero]`. Rewrite using `[← symplOH_add_self, h2, add_zero]`.
-/
theorem symplO_re_fi (r z : WO S T) (hr : ∀ i j, finPart D (r i j) = 0) (hz : ∀ i j, infPart D (z i j) = 0) :
    symplO S T r z = 0 ∧ symplO S T z r = 0 := by
  obtain ⟨h1, h2⟩ := Fock.DRho.symplOH_real_fin S T r z hr hz
  constructor
  · rw [← symplOH_add_self, h1, add_zero]
  · rw [← symplOH_add_self, h2, add_zero]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Use `Fock.DRho.eq_zero_of_parts D _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, ha, zero_mul]`. Rewrite using `[map_mul, hr i j, mul_zero]`.
-/
theorem smul_re_eq_zero (a : AE D) (ha : infPart D a = 0) (r : WO S T) (hr : ∀ i j, finPart D (r i j) = 0) :
    a • r = 0 := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  refine Fock.DRho.eq_zero_of_parts D _ ?_ ?_
  · rw [map_mul, ha, zero_mul]
  · rw [map_mul, hr i j, mul_zero]

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul, ha, zero_mul]`.
-/
theorem isFi_smul (a : AE D) (ha : infPart D a = 0) (z : WO S T) : ∀ i j, infPart D ((a • z) i j) = 0 := by
  intro i j; rw [Matrix.smul_apply, smul_eq_mul, map_mul, ha, zero_mul]

end Sym

section Phi

variable (S T : HSp D)

def U0 (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', fun i j => ?_⟩
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add, ha, hb, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, fun i j => by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, fun i j => ?_⟩
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, ha, neg_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_U0 {Λ : AddSubgroup (WO S T)} {w : WO S T} :
    w ∈ U0 S T Λ ↔ ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0 := Iff.rfl

/- English proof (translation)
Introduce `u hu` and use `⟨u, hu, fun i j => by simp⟩`.
-/
theorem le_open_neighbourhood {Λ : AddSubgroup (WO S T)} : Λ ≤ U0 S T Λ := fun u hu => ⟨u, hu, fun i j => by simp⟩

/- English proof (translation)
Use extensionality with `w`. Simplify using `only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]`. Use `exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `h i j`.

Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify using `using this`.
-/
theorem open_neighbourhood_set_eq (Λ : AddSubgroup (WO S T)) :
    (U0 S T Λ : Set (WO S T)) = {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0} := by
  ext w
  simp only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]
  refine exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩
  · ext i j; exact h i j
  · have := congrFun (congrFun h i) j; simpa using this

open Classical in

def phiV (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (g : WO S T → ℂ) (y : WO S T) : ℂ :=
  if y ∈ U0 S T Λ then ψ (symplOH S T (e2 D • y) y) * g y else 0

def thS (ψ : AddChar (AF D.host.F) ℂ) (Φ : WO S T → ℂ) (w : WO S T) : ℂ :=
  ∑' γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ψ (symplOH S T (ratW T S γ) w) * Φ (ratW T S γ + w)

/- English proof (translation)
Take `⟨q, hq⟩` from `Formalism.IndefR.Fin.symplO_rat S T a b`. Conclude with `⟨1 / 2 * q, by unfold symplOH; rw [hq, map_mul]⟩`.
-/
theorem symplOH_rat (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ q : D.host.F, symplOH S T (ratW T S a) (ratW T S b) = algebraMap D.host.F (AF D.host.F) q := by
  obtain ⟨q, hq⟩ := Formalism.IndefR.Fin.symplO_rat S T a b
  exact ⟨1 / 2 * q, by unfold symplOH; rw [hq, map_mul]⟩

/- English proof (translation)
Unfold `thS`. Rewrite using `[← tsum_mul_left, ← (Equiv.subRight γ₀).tsum_eq]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.subRight_apply]`. Establish `hsub : ratW T S (γ - γ₀) = ratW T S γ - ratW T S γ₀`.

Rewrite using `[sub_eq_add_neg, Formalism.IndefR.Fin.ratW_add, Formalism.IndefR.Fin.ratW_neg, ← sub_eq_add_neg]`. Rewrite using `[hsub, show ratW T S γ - ratW T S γ₀ + (ratW T S γ₀ + w) = ratW T S γ + w by abel]`. Take `⟨q, hq⟩` from `symplOH_rat S T γ γ₀`. Take `⟨q', hq'⟩` from `symplOH_rat S T γ₀ γ₀`. Establish `e : symplOH S T (ratW T S γ - ratW T S γ₀) (ratW T S γ₀ + w) = algebraMap D.host.F (AF D.host.F) (q - q') + (-(symplOH S T (ratW T S γ₀) w) + symplOH S T (ratW T S γ) w)`.

Rewrite using `[sub_eq_add_neg, Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_right, map_sub, ← hq, ← hq']`. Establish `hn : ∀ x y, symplOH S T (-x) y = -symplOH S T x y`. Introduce `x y`. Unfold `symplOH`. Rewrite using `[Formalism.IndefR.Fin.symplO_neg_left, mul_neg]`.

Rewrite using `[hn, hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, AddChar.map_add_eq_mul, hψF, one_mul, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thS_quasi (ψ : AddChar (AF D.host.F) ℂ) (hψF : ∀ a : D.host.F, ψ (algebraMap D.host.F (AF D.host.F) a) = 1)
    (Φ : WO S T → ℂ) (γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    thS S T ψ Φ (ratW T S γ₀ + w) = ψ (-(symplOH S T (ratW T S γ₀) w)) * thS S T ψ Φ w := by
  unfold thS
  rw [← tsum_mul_left, ← (Equiv.subRight γ₀).tsum_eq]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.subRight_apply]
  have hsub : ratW T S (γ - γ₀) = ratW T S γ - ratW T S γ₀ := by
    rw [sub_eq_add_neg, Formalism.IndefR.Fin.ratW_add, Formalism.IndefR.Fin.ratW_neg, ← sub_eq_add_neg]
  rw [hsub, show ratW T S γ - ratW T S γ₀ + (ratW T S γ₀ + w) = ratW T S γ + w by abel]
  obtain ⟨q, hq⟩ := symplOH_rat S T γ γ₀
  obtain ⟨q', hq'⟩ := symplOH_rat S T γ₀ γ₀
  have e : symplOH S T (ratW T S γ - ratW T S γ₀) (ratW T S γ₀ + w) =
      algebraMap D.host.F (AF D.host.F) (q - q') + (-(symplOH S T (ratW T S γ₀) w) + symplOH S T (ratW T S γ) w) := by
    rw [sub_eq_add_neg, Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_right,
      Formalism.IndefR.Fin.symplOH_add_right, map_sub, ← hq, ← hq']
    have hn : ∀ x y, symplOH S T (-x) y = -symplOH S T x y := by
      intro x y; unfold symplOH; rw [Formalism.IndefR.Fin.symplO_neg_left, mul_neg]
    rw [hn, hn]
    ring
  rw [e, AddChar.map_add_eq_mul, hψF, one_mul, AddChar.map_add_eq_mul]
  ring

/- English proof (translation)
Unfold `heisO thS`. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← add_assoc, Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_left, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thS_heis (ψ : AddChar (AF D.host.F) ℂ) (Φ : WO S T → ℂ) (u w : WO S T) :
    heisO ψ S T u (thS S T ψ Φ) w = thS S T ψ (heisO ψ S T u Φ) w := by
  unfold heisO thS
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  dsimp only
  rw [← add_assoc, Formalism.IndefR.Fin.symplOH_add_right, Formalism.IndefR.Fin.symplOH_add_left,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

end Phi

section Lat

variable (S T : HSp D)

structure LatHyp (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) : Prop where
  fi : ∀ x ∈ Λ, ∀ i j, infPart D (x i j) = 0
  int : ∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ
  pair : ∀ x ∈ Λ, ∀ u ∈ Λ, ψ (symplO S T x u) = 1

variable {S T}

/- English proof (translation)
Establish `he : e2 D • r = 0` using `smul_re_eq_zero S T (e2 D) (infinite_part_dyadic_idempotent hdy) r hr`. Establish `h1 : symplOH S T r z = 0` using `(Fock.DRho.symplOH_real_fin S T r z hr hz).1`. Establish `hz2 : ∀ i j, infPart D ((e2 D • z) i j) = 0` using `isFi_smul S T (e2 D) (infinite_part_dyadic_idempotent hdy) z`. Establish `h2 : symplOH S T (e2 D • z) r = 0` using `(Fock.DRho.symplOH_real_fin S T r _ hr hz2).2`. Simplify using `only [smul_add, he, zero_add, Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_right, h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem phase_expand (hdy : DyadIdem D) (x r z : WO S T) (hr : ∀ i j, finPart D (r i j) = 0)
    (hx : ∀ i j, infPart D (x i j) = 0) (hz : ∀ i j, infPart D (z i j) = 0) :
    symplOH S T (r + x) z + symplOH S T (e2 D • (r + x + z)) (r + x + z) =
      symplOH S T (e2 D • (r + x)) (r + x) +
        (symplOH S T x z + symplOH S T (e2 D • x) z + symplOH S T (e2 D • z) x + symplOH S T (e2 D • z) z) := by
  have he : e2 D • r = 0 := smul_re_eq_zero S T (e2 D) (infinite_part_dyadic_idempotent hdy) r hr
  have h1 : symplOH S T r z = 0 := (Fock.DRho.symplOH_real_fin S T r z hr hz).1
  have hz2 : ∀ i j, infPart D ((e2 D • z) i j) = 0 := isFi_smul S T (e2 D) (infinite_part_dyadic_idempotent hdy) z
  have h2 : symplOH S T (e2 D • z) r = 0 := (Fock.DRho.symplOH_real_fin S T r _ hr hz2).2
  simp only [smul_add, he, zero_add, Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_right, h1, h2]
  ring

/- English proof (translation)
The claim follows from `hL.pair a ha b hb`.
-/
theorem psi_one_of_mem (ψ : AddChar (AF D.host.F) ℂ) {Λ : AddSubgroup (WO S T)} (hL : LatHyp S T ψ Λ) {a b : WO S T}
    (ha : a ∈ Λ) (hb : b ∈ Λ) : ψ (symplO S T a b) = 1 := hL.pair a ha b hb

/- English proof (translation)
Rewrite using `[symplO_smul_adj, cA_cA']`.
-/
theorem symplO_smul_right_adj (c : AE D) (a b : WO S T) : symplO S T a (c • b) = symplO S T (cA D c • a) b := by
  rw [symplO_smul_adj, cA_cA']

/- English proof (translation)
Rewrite using `[symplOH_eq, symplOH_eq, symplO_smul_right_adj, smul_comm]`.
-/
theorem symplOH_smul_right_adj (c : AE D) (a b : WO S T) :
    symplOH S T a (c • b) = symplOH S T (cA D c • a) b := by
  rw [symplOH_eq, symplOH_eq, symplO_smul_right_adj, smul_comm]

/- English proof (translation)
Unfold `symplOH`. Rewrite using `[symplO_sub_left, mul_sub]`.
-/
theorem symplOH_sub_left (a b c : WO S T) : symplOH S T (a - b) c = symplOH S T a c - symplOH S T b c := by
  unfold symplOH; rw [symplO_sub_left, mul_sub]

/- English proof (translation)
Establish `hce : cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε` using `PHeisTh.cA_algebraMap ε`. Establish `h1 : algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)) = algebraMap (AF D.host.F) (AE D) ε + eDy v - cA D (eDy v)`. Rewrite using `[← dyadic_idempotent_mul_place_idempotent hdy hε, map_mul, hce]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`.

Distinguish the cases in `h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal`. Take `⟨⟨hee, hec, -⟩, hint, ε', hε', hs⟩` from `eDy_spec hdy v h2`. Establish `hεε : ε' = ε`. Establish `a` using `placeIdem_mul hε' hε`. Establish `b` using `placeIdem_mul hε hε'`.

Rewrite `a`, `b` using `[if_pos rfl]`. Rewrite using `[← a, mul_comm, b]`. Substitute `hεε` using the available equality. Rewrite using `[← hs]`. Establish `: halfE D * (eDy v + cA D (eDy v) + eDy v - cA D (eDy v)) = eDy (D` using `D) v := by`.

Establish `h2' : halfE D * 2 = 1`. Unfold `halfE`. Rewrite using `[← map_ofNat (algebraMap (AF D.host.F) (AE D)) 2, ← map_mul, mul_comm, two_halfE, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`.

Conclude with `hint`. Rewrite using `[eDy_of_not v h2, add_zero, map_zero, sub_zero]`. Unfold `halfE`. Rewrite using `[← map_mul]`. Conclude with `half_mem_int h2 hε`.
-/
theorem beta_int (hdy : DyadIdem D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    finPart D (halfE D * (algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)))) ∈ intAE D := by
  have hce : cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := PHeisTh.cA_algebraMap ε
  have h1 : algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)) =
      algebraMap (AF D.host.F) (AE D) ε + eDy v - cA D (eDy v) := by
    rw [← dyadic_idempotent_mul_place_idempotent hdy hε, map_mul, hce]; ring
  rw [h1]
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · obtain ⟨⟨hee, hec, -⟩, hint, ε', hε', hs⟩ := eDy_spec hdy v h2
    have hεε : ε' = ε := by
      have a := placeIdem_mul hε' hε
      have b := placeIdem_mul hε hε'
      rw [if_pos rfl] at a b
      rw [← a, mul_comm, b]
    subst hεε
    rw [← hs]
    have : halfE D * (eDy v + cA D (eDy v) + eDy v - cA D (eDy v)) = eDy (D := D) v := by
      have h2' : halfE D * 2 = 1 := by
        unfold halfE
        rw [← map_ofNat (algebraMap (AF D.host.F) (AE D)) 2, ← map_mul, mul_comm, two_halfE, map_one]
      calc halfE D * (eDy v + cA D (eDy v) + eDy v - cA D (eDy v)) = (halfE D * 2) * eDy v := by ring
        _ = eDy v := by rw [h2', one_mul]
    rw [this]; exact hint
  · rw [eDy_of_not v h2, add_zero, map_zero, sub_zero]
    unfold halfE
    rw [← map_mul]
    exact half_mem_int h2 hε

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `heisO phiV`. Establish `h2u : 2 • u ∈ U0 S T Λ` using `(U0 S T Λ).nsmul_mem (le_open_neighbourhood S T hu) 2`. Establish `hfi2 : ∀ i j, infPart D ((2 • u) i j) = 0`. Introduce `i j`.

Rewrite using `[two_nsmul, Matrix.add_apply, map_add, hL.fi u hu i j, add_zero]`. Distinguish the cases in `hy : y ∈ U0 S T Λ`. Rewrite using `[if_pos ((U0 S T Λ).add_mem hy h2u), if_pos hy, hg y _ hfi2]`. Take `⟨x, hx, hr⟩` from `hy`. Establish `hyx : y = (y - x) + x` using `by abel`.

Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul, hyx, phase_expand hdy x (y - x) (2 • u) hr (hL.fi x hx) hfi2, AddChar.map_add_eq_mul, ← hyx]`. Establish `hex : e2 D • x ∈ Λ` using `hL.int _ (dyadic_idempotent_integral hdy) x hx`. Establish `heu : e2 D • u ∈ Λ` using `hL.int _ (dyadic_idempotent_integral hdy) u hu`. Establish `key : symplOH S T x (2 • u) + symplOH S T (e2 D • x) (2 • u) + symplOH S T (e2 D • (2 • u)) x + symplOH S T (e2 D • (2 • u)) (2 • u) = symplO S T x u + symplO S T (e2 D • x) u + symplO S T (e2 D • u) x + (symplO S T (e2 D • u) u + symplO S T (e2 D • u) u)`. Simplify using `only [two_nsmul, smul_add, Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_right, ← symplOH_add_self]`.

Apply the tactic sequence `try ring`. Rewrite using `[key, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hL.pair _ hx _ hu, hL.pair _ hex _ hu, hL.pair _ heu _ hx, hL.pair _ heu _ hu]`. Apply the tactic sequence `try ring`. Establish `: y + 2 • u ∉ U0 S T Λ` using `fun h => hy (by simpa using (U0 S T Λ).sub_mem h h2u)`. Rewrite using `[if_neg this, if_neg hy, mul_zero]`.
-/
theorem phi_heis_two (hdy : DyadIdem D) (ψ : AddChar (AF D.host.F) ℂ) {Λ : AddSubgroup (WO S T)}
    (hL : LatHyp S T ψ Λ) (g : WO S T → ℂ) (hg : ∀ y u : WO S T, (∀ i j, infPart D (u i j) = 0) → g (y + u) = g y)
    (u : WO S T) (hu : u ∈ Λ) : heisO ψ S T (2 • u) (phiV S T ψ Λ g) = phiV S T ψ Λ g := by
  funext y
  unfold heisO phiV
  have h2u : 2 • u ∈ U0 S T Λ := (U0 S T Λ).nsmul_mem (le_open_neighbourhood S T hu) 2
  have hfi2 : ∀ i j, infPart D ((2 • u) i j) = 0 := by
    intro i j; rw [two_nsmul, Matrix.add_apply, map_add, hL.fi u hu i j, add_zero]
  by_cases hy : y ∈ U0 S T Λ
  · rw [if_pos ((U0 S T Λ).add_mem hy h2u), if_pos hy, hg y _ hfi2]
    obtain ⟨x, hx, hr⟩ := hy
    have hyx : y = (y - x) + x := by abel
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, hyx, phase_expand hdy x (y - x) (2 • u) hr (hL.fi x hx) hfi2,
      AddChar.map_add_eq_mul, ← hyx]
    have hex : e2 D • x ∈ Λ := hL.int _ (dyadic_idempotent_integral hdy) x hx
    have heu : e2 D • u ∈ Λ := hL.int _ (dyadic_idempotent_integral hdy) u hu
    have key : symplOH S T x (2 • u) + symplOH S T (e2 D • x) (2 • u) + symplOH S T (e2 D • (2 • u)) x +
        symplOH S T (e2 D • (2 • u)) (2 • u) =
        symplO S T x u + symplO S T (e2 D • x) u + symplO S T (e2 D • u) x +
          (symplO S T (e2 D • u) u + symplO S T (e2 D • u) u) := by
      simp only [two_nsmul, smul_add, Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_right,
        ← symplOH_add_self]
      try ring
    rw [key, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      hL.pair _ hx _ hu, hL.pair _ hex _ hu, hL.pair _ heu _ hx, hL.pair _ heu _ hu]
    try ring
  · have : y + 2 • u ∉ U0 S T Λ := fun h => hy (by simpa using (U0 S T Λ).sub_mem h h2u)
    rw [if_neg this, if_neg hy, mul_zero]

/- English proof (translation)
Take `⟨hee, hec, v, ε, hε, hs⟩` from `he`. Establish `hue : e • u = u` using `by ext i j; exact hh i j`. Establish `heps : algebraMap (AF D.host.F) (AE D) ε • u = u` using `by conv_lhs => rw [← hue, smul_smul, mul_comm, idem_mul_eps hee hec hs, hue]`. Use function extensionality and compare the values at `y`. Unfold `heisO phiV`.

Establish `hfi : ∀ i j, infPart D (u i j) = 0` using `hL.fi u hu`. Distinguish the cases in `hy : y ∈ U0 S T Λ`. Rewrite using `[if_pos ((U0 S T Λ).add_mem hy (le_open_neighbourhood S T hu)), if_pos hy, hg y _ hfi]`. Take `⟨x, hx, hr⟩` from `hy`. Establish `hyx : y = (y - x) + x` using `by abel`.

Rewrite using `[← mul_assoc, ← AddChar.map_add_eq_mul, hyx, phase_expand hdy x (y - x) u hr (hL.fi x hx) hfi, AddChar.map_add_eq_mul, ← hyx]`. Establish `hiso : symplOH S T (e2 D • u) u = 0`. Establish `h1 : e2 D • u = e • (e2 D • u)` using `by rw [smul_comm, hue]`. Establish `h2 : symplOH S T (e • (e2 D • u)) (e • u) = 0`. Rewrite using `[symplOH_eq, smul_comm (halfE D) e, symplO_smul_adj, smul_smul (cA D e) e u, show cA D e * e = 0 by rw [mul_comm]; exact hec, zero_smul]`.

Unfold `symplO hO`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Establish `hβ` using `beta_int hdy hε`. Establish `hβx : (halfE D * (algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)))) • x ∈ Λ` using `hL.int _ hβ x hx`.

Establish `key : symplOH S T x u + symplOH S T (e2 D • x) u + symplOH S T (e2 D • u) x = symplO S T ((halfE D * (algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)))) • x) u`. Rewrite using `[Formalism.IndefR.Fin.symplOH_swap S T x (e2 D • u), symplOH_smul_right_adj]`. Establish `h1 : symplOH S T x u + symplOH S T (e2 D • x) u + -symplOH S T (cA D (e2 D) • x) u = symplOH S T ((1 + e2 D - cA D (e2 D)) • x) u`. Rewrite using `[sub_smul, add_smul, one_smul, symplOH_sub_left, Formalism.IndefR.Fin.symplOH_add_left]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Use `conv_lhs => rw [← heps, symplOH_smul_right_adj, PHeisTh.cA_algebraMap, smul_smul, symplOH_eq, smul_smul]`. Rewrite using `[hiso, add_zero, key, hL.pair _ hβx _ hu]`. Expand and normalize the polynomial expressions, which then agree. Establish `: y + u ∉ U0 S T Λ` using `fun h => hy (by simpa using (U0 S T Λ).sub_mem h (le_open_neighbourhood S T hu))`.

Rewrite using `[if_neg this, if_neg hy, mul_zero]`.
-/
theorem phi_heis_half (hdy : DyadIdem D) (ψ : AddChar (AF D.host.F) ℂ) {Λ : AddSubgroup (WO S T)}
    (hL : LatHyp S T ψ Λ) (g : WO S T → ℂ) (hg : ∀ y u : WO S T, (∀ i j, infPart D (u i j) = 0) → g (y + u) = g y)
    (e : AE D) (he : IsSplitIdem D e) (u : WO S T) (hu : u ∈ Λ) (hh : IsHalf e u) :
    heisO ψ S T u (phiV S T ψ Λ g) = phiV S T ψ Λ g := by
  obtain ⟨hee, hec, v, ε, hε, hs⟩ := he
  have hue : e • u = u := by ext i j; exact hh i j
  have heps : algebraMap (AF D.host.F) (AE D) ε • u = u := by
    conv_lhs => rw [← hue, smul_smul, mul_comm, idem_mul_eps hee hec hs, hue]
  funext y
  unfold heisO phiV
  have hfi : ∀ i j, infPart D (u i j) = 0 := hL.fi u hu
  by_cases hy : y ∈ U0 S T Λ
  · rw [if_pos ((U0 S T Λ).add_mem hy (le_open_neighbourhood S T hu)), if_pos hy, hg y _ hfi]
    obtain ⟨x, hx, hr⟩ := hy
    have hyx : y = (y - x) + x := by abel
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, hyx, phase_expand hdy x (y - x) u hr (hL.fi x hx) hfi,
      AddChar.map_add_eq_mul, ← hyx]

    have hiso : symplOH S T (e2 D • u) u = 0 := by
      have h1 : e2 D • u = e • (e2 D • u) := by rw [smul_comm, hue]
      have h2 : symplOH S T (e • (e2 D • u)) (e • u) = 0 := by
        rw [symplOH_eq, smul_comm (halfE D) e, symplO_smul_adj, smul_smul (cA D e) e u,
          show cA D e * e = 0 by rw [mul_comm]; exact hec, zero_smul]
        unfold symplO hO; simp
      calc symplOH S T (e2 D • u) u = symplOH S T (e • (e2 D • u)) (e • u) := by rw [← h1, hue]
        _ = 0 := h2
    have hβ := beta_int hdy hε
    have hβx : (halfE D * (algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)))) • x ∈ Λ :=
      hL.int _ hβ x hx
    have key : symplOH S T x u + symplOH S T (e2 D • x) u + symplOH S T (e2 D • u) x =
        symplO S T ((halfE D * (algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)))) • x) u := by
      rw [Formalism.IndefR.Fin.symplOH_swap S T x (e2 D • u), symplOH_smul_right_adj]
      have h1 : symplOH S T x u + symplOH S T (e2 D • x) u + -symplOH S T (cA D (e2 D) • x) u =
          symplOH S T ((1 + e2 D - cA D (e2 D)) • x) u := by
        rw [sub_smul, add_smul, one_smul, symplOH_sub_left, Formalism.IndefR.Fin.symplOH_add_left]; ring
      rw [h1]
      conv_lhs => rw [← heps, symplOH_smul_right_adj, PHeisTh.cA_algebraMap, smul_smul, symplOH_eq, smul_smul]
    rw [hiso, add_zero, key, hL.pair _ hβx _ hu]
    ring
  · have : y + u ∉ U0 S T Λ := fun h => hy (by simpa using (U0 S T Λ).sub_mem h (le_open_neighbourhood S T hu))
    rw [if_neg this, if_neg hy, mul_zero]

end Lat

end Formalism.IndefR.Fin.VacEx
