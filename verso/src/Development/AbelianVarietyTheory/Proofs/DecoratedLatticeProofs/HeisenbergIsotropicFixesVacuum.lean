import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHEqZeroOfHO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.FlatFix

variable {D : D7}

/- English proof (translation)
Rewrite using `[← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]`. Conclude with `(map_ne_zero_iff _ (algebraMap D.host.F (Fv D.host.F w)).injective).2 two_ne_zero`.
-/
theorem two_ne_zero_at (w : Pl D) : (2 : Fv D.host.F w) ≠ 0 := by
  rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]
  exact (map_ne_zero_iff _ (algebraMap D.host.F (Fv D.host.F w)).injective).2 two_ne_zero

/- English proof (translation)
Establish `h3 : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1`. Use `HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (2 : 𝓞 D.host.F)` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.intValuation_eq_one_iff.2 hw]`. Rewrite using `[← this]`. Use `congr 1`.

Establish `h2 : ((2 : D.host.F) : Fv D.host.F w) = 2`. Rewrite using `[← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]`. Both sides reduce to the same expression. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← h2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h3, inv_one]`.
-/
theorem two_inv_int (w : Pl D) (hw : (2 : 𝓞 D.host.F) ∉ w.asIdeal) :
    (2⁻¹ : Fv D.host.F w) ∈ w.adicCompletionIntegers D.host.F := by
  have h3 : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (2 : 𝓞 D.host.F)
    rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hw] at this
    rw [← this]
    congr 1
  have h2 : ((2 : D.host.F) : Fv D.host.F w) = 2 := by
    rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]; rfl
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← h2,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h3, inv_one]

/- English proof (translation)
Establish `h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `two_ne_zero`. Use `(Ideal.finite_factors h0).subset fun v hv => ?_` and prove the remaining obligations. Conclude with `(Ideal.dvd_span_singleton).2 hv.2`.
-/
theorem finite_two (P : Pl D → Prop) : {v : Pl D | P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact (Ideal.dvd_span_singleton).2 hv.2

open Classical in

def halfOff (P : Pl D → Prop) : Af D.host.F :=
  RestrictedProduct.mk (fun w => if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0)
    (Filter.Eventually.of_forall fun w => by
      split_ifs with h
      · exact two_inv_int w h.2
      · exact zero_mem _)

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_halfOff (P : Pl D → Prop) (w : Pl D) :
    evalV D.host.F w (halfOff P) = if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0 := rfl

/- English proof (translation)
Introduce `w`. Rewrite using `[evalV_halfOff]`. Use `split_ifs with h`. Conclude with `two_inv_int w h.2`. Conclude with `zero_mem _`.
-/
theorem halfOff_int (P : Pl D → Prop) : halfOff P ∈ intAf D.host.F := by
  classical
  intro w
  rw [evalV_halfOff]
  split_ifs with h
  · exact two_inv_int w h.2
  · exact zero_mem _

/- English proof (translation)
The claim follows from `Prod.ext (add_zero (0 : Ainf D.host.F)).symm rfl`.
-/
theorem pair_add (a b : Af D.host.F) : pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
  Prod.ext (add_zero (0 : Ainf D.host.F)).symm rfl

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact Prod.ext rfl rfl`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, pair_add]`.
-/
theorem sum_pair {ι : Type} (s : Finset ι) (α : ι → Af D.host.F) :
    ∑ i ∈ s, pairA D.host.F 0 (α i) = pairA D.host.F 0 (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Prod.ext rfl rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, pair_add]

/- English proof (translation)
Use `choose! α hα h1 h0 using hε`. Rewrite using `[Finset.sum_congr rfl hα, sum_pair, ← pair_add]`. Unfold `GlobalTheory.SelfDualAt.cP`. Use `congr 1`. Use `FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) = evalV D.host.F w (halfOff P + halfOff P + ∑ i ∈ Qs, α i)`. Rewrite using `[map_add, map_add, map_sum, GlobalTheory.SelfDualAt.evalV_indP, evalV_halfOff]`. Distinguish the cases in `hw : w ∈ Qs`. Take `⟨hP, h2⟩` from `(hQ w).1 hw`. Rewrite using `[Finset.sum_eq_single_of_mem w hw (fun v hv hvw => h0 v hv w (Ne.symm hvw)), h1 w hw, if_pos hP, if_neg (fun h => h.2 h2), zero_add, zero_add]`.

Rewrite using `[Finset.sum_eq_zero (fun v hv => h0 v hv w (fun h => hw (h ▸ hv))), add_zero]`. Distinguish the cases in `hP : P w`. Establish `h2 : (2 : 𝓞 D.host.F) ∉ w.asIdeal` using `fun h2 => hw ((hQ w).2 ⟨hP, h2⟩)`. Rewrite using `[if_pos hP, if_pos ⟨hP, h2⟩, ← two_mul, mul_inv_cancel₀ (two_ne_zero_at w)]`. Rewrite using `[if_neg hP, if_neg (fun h => hP h.1), add_zero]`.
-/
theorem indicatorIdempotent_eq_add_sum (P : Pl D → Prop) (Qs : Finset (Pl D)) (hQ : ∀ v, v ∈ Qs ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Pl D → AF D.host.F) (hε : ∀ v ∈ Qs, IsPlaceIdem D v (ε v)) :
    GlobalTheory.SelfDualAt.cP P = pairA D.host.F 0 (halfOff P + halfOff P) + ∑ v ∈ Qs, ε v := by
  classical
  choose! α hα h1 h0 using hε
  rw [Finset.sum_congr rfl hα, sum_pair, ← pair_add]
  unfold GlobalTheory.SelfDualAt.cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  change evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) = evalV D.host.F w (halfOff P + halfOff P + ∑ i ∈ Qs, α i)
  rw [map_add, map_add, map_sum, GlobalTheory.SelfDualAt.evalV_indP, evalV_halfOff]
  by_cases hw : w ∈ Qs
  · obtain ⟨hP, h2⟩ := (hQ w).1 hw
    rw [Finset.sum_eq_single_of_mem w hw (fun v hv hvw => h0 v hv w (Ne.symm hvw)), h1 w hw, if_pos hP,
      if_neg (fun h => h.2 h2), zero_add, zero_add]
  · rw [Finset.sum_eq_zero (fun v hv => h0 v hv w (fun h => hw (h ▸ hv))), add_zero]
    by_cases hP : P w
    · have h2 : (2 : 𝓞 D.host.F) ∉ w.asIdeal := fun h2 => hw ((hQ w).2 ⟨hP, h2⟩)
      rw [if_pos hP, if_pos ⟨hP, h2⟩, ← two_mul, mul_inv_cancel₀ (two_ne_zero_at w)]
    · rw [if_neg hP, if_neg (fun h => hP h.1), add_zero]

/- English proof (translation)
Establish `e : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) = pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`. Establish `e2 : finPart D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) = β ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)` using `by show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Rewrite using `[e, e2]`.

Conclude with `AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩`.
-/
theorem int_alg_pair {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) ∈ intAE D := by
  have e : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) = pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) =
      β ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
    show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]; rfl
  rw [e, e2]
  exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩

/- English proof (translation)
Establish `key` using `GlobalTheory.LatVac.heisO_heisO ψ (a • z) (b • z) f`. Rewrite `key` using `[hb, ha, hiso a b, ψ.map_zero_eq_one, one_smul, ← add_smul]`. Conclude with `key.symm`.
-/
theorem fix_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} {z : WO S T}
    (hiso : ∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) {a b : AE D}
    (ha : heisO ψ S T (a • z) f = f) (hb : heisO ψ S T (b • z) f = f) : heisO ψ S T ((a + b) • z) f = f := by
  have key := GlobalTheory.LatVac.heisO_heisO ψ (a • z) (b • z) f
  rw [hb, ha, hiso a b, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
  exact key.symm

end GlobalTheory.FinPl.FlatFix

open GlobalTheory.FinPl.FlatFix in

/- English proof (translation)
Introduce `D ψ S T LS LT P _ _ hT f hf z hz hiso`. Establish `hfix_split : ∀ e, IsSplitIdem D e → heisO ψ S T (e • z) f = f` using `fun e he => hf.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P e (GlobalTheory.SplitHomLattice.idem_int he) z hz) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])`. Establish `hQ` using `finite_two (D := D) P`. Establish `hmemQ : ∀ v, v ∈ hQ.toFinset ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal` using `fun v => hQ.mem_toFinset`. Establish `hch : ∀ v, v ∈ hQ.toFinset → ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε`.

Introduce `v hv`. Take `⟨hPv, h2⟩` from `(hmemQ v).1 hv`. Break down `(hT v hPv).2 with h | h` into its components or cases. Conclude with `absurd h2 h`. Conclude with `h`.

Use `choose! e ε he hε hsum using hch`. Establish `hdec` using `indicatorIdempotent_eq_add_sum P hQ.toFinset hmemQ ε hε`. Establish `hzc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP P) • z = z`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Conclude with `GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul P _ (LatMem.latO_mxAt hz i j)`. Rewrite using `[← hzc, hdec, map_add, map_sum]`. Use `fix_add hiso ?_ ?_` and prove the remaining obligations. Establish `hm` using `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P _ (int_alg_pair (halfOff_int P)) z hz`. Establish `e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P + halfOff P)) • z = 2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P)) • z)`.

Rewrite using `[pair_add, map_add, add_smul, two_nsmul]`. Rewrite using `[e2]`. Conclude with `hf.1 _ hm`. Use `Finset.sum_induction _ (fun c => heisO ψ S T (c • z) f = f) (fun a b ha hb => fix_add hiso ha hb) ?_ ?_` and prove the remaining obligations. Rewrite using `[zero_smul]`.

Conclude with `GlobalTheory.LatVac.heisO_zero ψ f`. Introduce `v hv`. Rewrite using `[← hsum v hv]`. Conclude with `fix_add hiso (hfix_split _ (he v hv)) (hfix_split _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (he v hv)))`.
-/
theorem GlobalTheory.FinPl.FlatFix.fix_of_isotropic : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), IsSelfDualC S LS → IsSelfDualC T LT → (∀ v, P v → Tame D v) → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f → ∀ z ∈ latO S T (LS : Set _) (LT : Set _) P, (∀ c c' : AE D, symplOH S T (c • z) (c' • z) = 0) → heisO ψ S T z f = f := by
  intro D ψ S T LS LT P _ _ hT f hf z hz hiso
  classical
  have hfix_split : ∀ e, IsSplitIdem D e → heisO ψ S T (e • z) f = f := fun e he =>
    hf.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P e (GlobalTheory.SplitHomLattice.idem_int he) z hz)
      (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
  have hQ := finite_two (D := D) P
  have hmemQ : ∀ v, v ∈ hQ.toFinset ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal := fun v => hQ.mem_toFinset
  have hch : ∀ v, v ∈ hQ.toFinset → ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
    intro v hv
    obtain ⟨hPv, h2⟩ := (hmemQ v).1 hv
    rcases (hT v hPv).2 with h | h
    · exact absurd h2 h
    · exact h
  choose! e ε he hε hsum using hch
  have hdec := indicatorIdempotent_eq_add_sum P hQ.toFinset hmemQ ε hε
  have hzc : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP P) • z = z := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul P _ (LatMem.latO_mxAt hz i j)
  rw [← hzc, hdec, map_add, map_sum]
  refine fix_add hiso ?_ ?_
  · have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ P _ (int_alg_pair (halfOff_int P)) z hz
    have e2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P + halfOff P)) • z =
        2 • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (halfOff P)) • z) := by
      rw [pair_add, map_add, add_smul, two_nsmul]
    rw [e2]
    exact hf.1 _ hm
  · refine Finset.sum_induction _ (fun c => heisO ψ S T (c • z) f = f) (fun a b ha hb => fix_add hiso ha hb) ?_ ?_
    · rw [zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
    · intro v hv
      rw [← hsum v hv]
      exact fix_add hiso (hfix_split _ (he v hv)) (hfix_split _ (GlobalTheory.IdemSumVac.isSplitIdem_cA (he v hv)))

end
