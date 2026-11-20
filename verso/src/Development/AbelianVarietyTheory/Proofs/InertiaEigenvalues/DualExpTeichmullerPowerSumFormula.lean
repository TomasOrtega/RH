import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSolutionExpansionModFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpStarOfLowTermsRemovedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamElementOfCocycleRecursionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfCocycleSolutionTeichmullerEpsilonRootPowStatement

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

/- English proof (translation)
Establish `hn : (-(l : ℤ_[l]) ^ s) ∈ nonunits ℤ_[l]`. Rewrite using `[PadicInt.mem_nonunits, norm_neg, norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)`. Establish `hunit` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn`. Take `⟨V, hV⟩` from `hunit.exists_left_inv`.

Use `⟨V ^ e, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (V : ℚ_[l]) * (u : ℚ_[l]) = 1`. Use `congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hV` as an intermediate fact. Rewrite using `[hu]`. Move the coercions through the operations in `at this ⊢`.

Take the linear combination `this`. Establish `h2 : (V : ℚ_[l]) = (u : ℚ_[l])⁻¹` using `eq_inv_of_mul_eq_one_left h1`. Simplify using `[h2]`. Establish `h1 : (l : ℤ_[l]) ^ s ∣ V - 1` using `⟨-V, by linear_combination hV⟩`. Establish `h2` using `sub_dvd_pow_sub_pow V 1 e`.

Rewrite `h2` using `[one_pow]`. Conclude with `h1.trans h2`.
-/
theorem exists_inv_pow_one_add {l : ℕ} [Fact l.Prime] {s : ℕ} (hs : 1 ≤ s) (e : ℕ) (u : ℚ_[l]ˣ)
    (hu : (u : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l])) :
    ∃ U : ℤ_[l], (U : ℚ_[l]) = ((u ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) ∧ (l : ℤ_[l]) ^ s ∣ U - 1 := by
  have hn : (-(l : ℤ_[l]) ^ s) ∈ nonunits ℤ_[l] := by
    rw [PadicInt.mem_nonunits, norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn
  obtain ⟨V, hV⟩ := hunit.exists_left_inv
  refine ⟨V ^ e, ?_, ?_⟩
  · have h1 : (V : ℚ_[l]) * (u : ℚ_[l]) = 1 := by
      have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hV
      rw [hu]
      push_cast at this ⊢
      linear_combination this
    have h2 : (V : ℚ_[l]) = (u : ℚ_[l])⁻¹ := eq_inv_of_mul_eq_one_left h1
    simp [h2]
  · have h1 : (l : ℤ_[l]) ^ s ∣ V - 1 := ⟨-V, by linear_combination hV⟩
    have h2 := sub_dvd_pow_sub_pow V 1 e
    rw [one_pow] at h2
    exact h1.trans h2

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simpa using P.ζQ_zero`. Consider the case `succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]`.
-/
theorem zetaQ_pow_level {l : ℕ} [Fact l.Prime] (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simpa using P.ζQ_zero
  | succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

/- English proof (translation)
Establish `h0 : ∀ x : ↥(K0 K), (x : Om l) ∈ Ks K s` using `fun x => (le_sup_left : K0 K ≤ Ks K s) x.2`. Establish `hζ : P.ζQ s ∈ Ks K s`. Use `(le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ ?_)` and prove the remaining obligations. Conclude with `zetaQ_pow_level P s`. Unfold `levSum`.

Use `add_mem (sum_mem fun i _ => mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun a _ => mul_mem (mul_mem (h0 _) (pow_mem (natCast_mem _ _) _)) (pow_mem hζ _))) (mul_mem (pow_mem (natCast_mem _ _) _) (h0 _))` and prove the remaining obligations.
-/
theorem levSum_mem_Ks {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s j : ℕ) {ι : Type}
    (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ↥(K0 K)) :
    levSum P K s j T c m d ∈ Ks K s := by
  have h0 : ∀ x : ↥(K0 K), (x : Om l) ∈ Ks K s := fun x => (le_sup_left : K0 K ≤ Ks K s) x.2
  have hζ : P.ζQ s ∈ Ks K s := by
    refine (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ ?_)
    exact zetaQ_pow_level P s
  unfold levSum
  refine add_mem (sum_mem fun i _ => mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun a _ =>
    mul_mem (mul_mem (h0 _) (pow_mem (natCast_mem _ _) _)) (pow_mem hζ _)))
    (mul_mem (pow_mem (natCast_mem _ _) _) (h0 _))

/- English proof (translation)
Introduce `LT l _ AI hT K s hs e g hg hχ ι T c m d hc hd`. Take `⟨U, hU, hU1⟩` from `exists_inv_pow_one_add hs.1 e ((LT l).χQ g) hχ`. Establish `hgen : IsGen (LT l).χQ K s g`. Use `⟨hg, ?_⟩` and prove the remaining obligations. Rewrite using `[hχ]`.

Use `push_cast`. Rewrite using `[add_sub_cancel_left, Padic.norm_p_pow]`. Establish `hw : ∀ i, ∃ w : Ainf l, i ∈ T → Lifts AI K w (c i)`. Introduce `i`. Distinguish the cases in `hi : i ∈ T`.

Take `⟨w, hw⟩` from `GlobalTheory.T.exists_lifts_of_norm_le_one_alt l (LT l) AI hT K (c i) (hc i hi).1`. Conclude with `⟨w, fun _ => hw⟩`. Conclude with `⟨0, fun h => absurd h hi⟩`. Use `choose w hw using hw`. Take `⟨y, hy, hexp⟩` from `GlobalTheory.T.frobeniusSolution_expansion_mod_filtration l (LT l) AI hT K s ι T w c m (e + 1) d (by omega) hw (fun j hj => hd j (by omega))`.

Establish `hsolv : Solv AI K s g U (y - WittVector.frobenius y)`. Rewrite using `[hy]`. Use `Solv.sum T _ fun i hi => ?_` and prove the remaining obligations. Conclude with `(GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow l (LT l) AI K s hs g hχ U hU1 (m i) (hc i hi).2).mul ((hw i hi).act (Gj_le_fix s hg)) (fun h hh => (hw i hi).act (Hinf_le_fix hh))`. Take `⟨b, hb0, hbH, z₀, hz₀⟩` from `GlobalTheory.T.exists_deRham_element_of_cocycleRecursion l (LT l) AI hT K s hs g U (e + 1) (by omega) y hsolv`.

Take `⟨z, hz, hE⟩` from `GlobalTheory.T.expStar_of_low_terms_removed LT l AI hT K s hs e g hgen (fun j => algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum (LT l) K s j T c m (d j)) (fun j => mul_mem (IntermediateField.algebraMap_mem _ _) (levSum_mem_Ks _ _ _ _ _ _ _ _)) …`. Use `add_mem hz₀ hexp` as an intermediate fact. Rewrite `this` using `[hU]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring⟩`.

Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Rewrite `hE` using `[hχ, ← mul_assoc, ← map_mul, ← mul_inv]`. Conclude with `hE`.
-/
theorem expStar_levSum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  intro LT l _ AI hT K s hs e g hg hχ ι T c m d hc hd
  classical
  obtain ⟨U, hU, hU1⟩ := exists_inv_pow_one_add hs.1 e ((LT l).χQ g) hχ
  have hgen : IsGen (LT l).χQ K s g := by
    refine ⟨hg, ?_⟩
    rw [hχ]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hw : ∀ i, ∃ w : Ainf l, i ∈ T → Lifts AI K w (c i) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l (LT l) AI hT K (c i) (hc i hi).1
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hw
  obtain ⟨y, hy, hexp⟩ := GlobalTheory.T.frobeniusSolution_expansion_mod_filtration l (LT l) AI hT K s ι T w c m (e + 1) d (by omega) hw
    (fun j hj => hd j (by omega))
  have hsolv : Solv AI K s g U (y - WittVector.frobenius y) := by
    rw [hy]
    refine Solv.sum T _ fun i hi => ?_
    exact (GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow l (LT l) AI K s hs g hχ U hU1 (m i) (hc i hi).2).mul
      ((hw i hi).act (Gj_le_fix s hg)) (fun h hh => (hw i hi).act (Hinf_le_fix hh))
  obtain ⟨b, hb0, hbH, z₀, hz₀⟩ := GlobalTheory.T.exists_deRham_element_of_cocycleRecursion l (LT l) AI hT K s hs g U (e + 1) (by omega) y hsolv
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.expStar_of_low_terms_removed LT l AI hT K s hs e g hgen
    (fun j => algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
      levSum (LT l) K s j T c m (d j))
    (fun j => mul_mem (IntermediateField.algebraMap_mem _ _) (levSum_mem_Ks _ _ _ _ _ _ _ _))
    b hb0 hbH ⟨z₀, by
      have := add_mem hz₀ hexp
      rw [hU] at this
      convert this using 1
      ring⟩
  refine ⟨z, hz, ?_⟩
  rw [hχ, ← mul_assoc, ← map_mul, ← mul_inv] at hE
  exact hE

end GlobalTheory.ExpImage
