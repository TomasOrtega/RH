import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRootsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBounds
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

/- English proof (translation)
Establish `hf0 : 0 < f` using `by linarith`. Establish `hL0 : 0 < L` using `by linarith`. Establish `hfE0 : 0 ≤ f * lE` using `mul_nonneg hf0.le hE0`. Establish `hfE : f * lE ≤ f * (2 * L)` using `mul_le_mul_of_nonneg_left hE hf0.le`. Establish `hfL : 32 ≤ f * L` using `by nlinarith`.

Establish `h1 : Real.log (1 + f * lE) ≤ Real.log (f * (3 * L))` using `Real.log_le_log (by linarith) (by nlinarith)`. Establish `h2 : Real.log (f * (3 * L)) = Real.log f + Real.log (3 * L)` using `Real.log_mul hf0.ne' (by positivity)`. Establish `h3 : Real.log (3 * L) ≤ 3 * L - 1` using `Real.log_le_sub_one_of_pos (by positivity)`. Establish `h4 : Real.log (1 + f * lE) ≤ 4 * L` using `by linarith`. Establish `h5 : 2 * f * Real.log (1 + f * lE) ≤ 2 * f * (4 * L)` using `mul_le_mul_of_nonneg_left h4 (by positivity)`.

Establish `h6 : lh ≤ 10 * (f * L)` using `by nlinarith`. Establish `h7 : 2 * f * lN ≤ 2 * f * (20 * L + 2)` using `mul_le_mul_of_nonneg_left hN (by positivity)`. Establish `h8 : 4 * f ≤ f * L` using `by nlinarith`. Establish `h9 : lhs ≤ 51 * (f * L)` using `by nlinarith`. Establish `h10 : (rk + 2) * lhs ≤ (2 * f + 2) * (51 * (f * L))` using `mul_le_mul_of_nonneg_right (by linarith) hs0 |>.trans (mul_le_mul_of_nonneg_left h9 (by linarith))`.

Establish `h11 : f * r ^ 2 * 2 ≤ f * r ^ 2 * L` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Establish `h12 : 8 * (f * L) ≤ f * (f * L)` using `mul_le_mul_of_nonneg_right hf (by positivity)`. Establish `h13 : f * (f * L) = f ^ 2 * L` using `by ring`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem om_sizes_le_poR (f r L lE lh lN lhs lG lr ld rk ldeg : ℝ) (hf : 8 ≤ f) (hr : 62 ≤ r) (hL : 4 ≤ L)
    (hlf : Real.log f ≤ L) (hE0 : 0 ≤ lE) (hE : lE ≤ 2 * L)
    (hh : lh ≤ f * lE + 2 * f * Real.log (1 + f * lE)) (hN : lN ≤ 20 * L + 2) (hs0 : 0 ≤ lhs)
    (hs : lhs ≤ lh + 2 * f * lN) (hG : lG ≤ f * r ^ 2 * (18 * L + 2)) (hr' : lr ≤ lG + 24)
    (hd : ld ≤ 4 * L) (hk : rk ≤ 2 * f) (hdeg : ldeg ≤ 1 + L) :
    (ld + 20) + (ldeg + lhs) + lr + (ldeg + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L ∧
    (3 * ld + 20) + (lE + lN + lhs) + lr + (lE + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : Real.log (1 + f * lE) ≤ Real.log (f * (3 * L)) := Real.log_le_log (by linarith) (by nlinarith)
  have h2 : Real.log (f * (3 * L)) = Real.log f + Real.log (3 * L) := Real.log_mul hf0.ne' (by positivity)
  have h3 : Real.log (3 * L) ≤ 3 * L - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * Real.log (1 + f * lE) ≤ 2 * f * (4 * L) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : 2 * f * lN ≤ 2 * f * (20 * L + 2) := mul_le_mul_of_nonneg_left hN (by positivity)
  have h8 : 4 * f ≤ f * L := by nlinarith
  have h9 : lhs ≤ 51 * (f * L) := by nlinarith
  have h10 : (rk + 2) * lhs ≤ (2 * f + 2) * (51 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) hs0 |>.trans (mul_le_mul_of_nonneg_left h9 (by linarith))
  have h11 : f * r ^ 2 * 2 ≤ f * r ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h12 : 8 * (f * L) ≤ f * (f * L) := mul_le_mul_of_nonneg_right hf (by positivity)
  have h13 : f * (f * L) = f ^ 2 * L := by ring
  constructor <;> nlinarith

/- English proof (translation)
Introduce `hR P δ L hL`. Establish `hcm : IsCMField P.host.E` using `P.host.isCMField_hostE`. Take `⟨K, _, _, hK2, hKd, -, hKE, -, hdeg⟩` from `exists_hostK P.R P.host`. Establish `hE` using `sz_fieldRange_embedding P.host.E P.host.φ₀`. Use `set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE`.

Establish `hlE0 : 0 ≤ lE`. Use `div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)` and prove the remaining obligations. Conclude with `Int.one_le_abs (discr_ne_zero P.host.E)` after adjusting the coercions. Establish `hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f)` using `by rw [hlE, hdeg]; push_cast; rfl`. Establish `hrd : lE ≤ 2 * L` using `hlE' ▸ hL.rd`.

Establish `hd : Real.log (P.host.d : ℝ) ≤ 4 * L`. Take `⟨_, -, h⟩` from `sz_mono_and_of_le.2 _ _ _ _ hKE hE`. Establish `h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE` using `h`. Rewrite `h'` using `[hK2, hKd]`. Move the coercions through the operations in `at h'`.

Rewrite `h'` using `[abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM'` using `GlobalTheory.T.field_datum_size_log_discriminant hR P δ`. Take `⟨hdeg_le, hray⟩` from `GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound P.host.E P.host.φ₀ (modulus P) δ.ray δ.isRay (modulus_ne_zero P)`. Establish `hcyc : Sz (cycField (rootOrder P)) (Real.log (rootOrder P)) (Real.log (rootOrder P))` using `sz_adjoin_rootOfUnity _ (Nat.pos_of_ne_zero (rootOrder_ne_zero P))`.

Establish `hV : Sz δ.V _ _` using `GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots P.host.E P.host.φ₀ δ.hstar δ.hstar_pos`. Establish `hall` using `sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ hM' hray) hcyc) hV`. Express the relevant statement in the definitionally equal form `Sz (δ.M' ⊔ δ.ray ⊔ cycField (rootOrder P) ⊔ δ.V) _ _`. Take `⟨hG, -, hf8, -⟩` from `roots_sizes P L hL`. Establish `hf0 : (0 : ℝ) < P.R.f` using `by have : 8 ≤ P.R.f := hf8; exact_mod_cast (by omega : 0 < P.R.f)`.

Establish `hcl` using `GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg`. Rewrite `hcl` using `[← hlE']`. Establish `hh0 : 0 < classNumber P.host.E` using `classNumber_pos _`. Establish `hg0` using `(P.host.g_prime 0).pos`. Establish `hg1` using `(P.host.g_prime 1).pos`.

Establish `hp` using `P.host.pde_prime.pos`. Establish `hp'` using `P.host.pde'_prime.pos`. Establish `hN : Real.log (modulus P : ℝ) ≤ 20 * L + 2`. Establish `e : Real.log (modulus P : ℝ) = Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log P.host.pde + Real.log P.host.pde'`. Simplify using `only [modulus]`.

Use `push_cast`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]`. Use `hL.g 0` as an intermediate fact. Use `hL.g 1` as an intermediate fact. Use `hL.p` as an intermediate fact.

Rewrite using `[e]`. Combine the linear relations using `[this.1, this.2]`. Establish `hs0 : 0 ≤ Real.log (δ.hstar : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hs : Real.log (δ.hstar : ℝ) ≤ Real.log (classNumber P.host.E) + 2 * P.R.f * Real.log (modulus P : ℝ)`. Establish `h1 : (δ.hstar : ℝ) ≤ (classNumber P.host.E : ℝ) * (modulus P : ℝ) ^ Module.finrank ℚ P.host.E`.

Conclude with `hdeg_le` after adjusting the coercions. Establish `h2` using `Real.log_le_log (by exact_mod_cast δ.hstar_pos) h1`. Rewrite `h2` using `[Real.log_mul (by positivity) (pow_ne_zero _ (by exact_mod_cast modulus_ne_zero P)), Real.log_pow, hdeg]`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hr : Real.log (rootOrder P : ℝ) ≤ Real.log P.restRowsFiniteGroupCard + 24`. Establish `hc` using `P.restRowsFiniteGroupCard_pos`. Establish `h1 : (rootOrder P : ℝ) ≤ (P.restRowsFiniteGroupCard : ℝ) * ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ)`. Conclude with `Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)` after adjusting the coercions. Establish `h2` using `Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (rootOrder_ne_zero P)) h1`.

Rewrite `h2` using `[Real.log_mul (by positivity) (by positivity)]`. Establish `e : Real.log ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = 4 * Real.log 3 + 4 * Real.log 5`. Rewrite using `[show ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = (3 : ℝ) ^ 4 * (5 : ℝ) ^ 4 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)` as an intermediate fact. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk : (NumberField.Units.rank P.host.E : ℝ) ≤ 2 * P.R.f`. Establish `: NumberField.Units.rank P.host.E ≤ Module.finrank ℚ P.host.E`. Rewrite using `[NumberField.Units.rank, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]`. Use linear arithmetic over natural numbers and integers.

Rewrite `this` using `[hdeg]`. Conclude with `this` after adjusting the coercions. Establish `d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L`. Rewrite using `[hdeg]`. Use `push_cast`.

Rewrite using `[Real.log_mul (by norm_num) (by positivity)]`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)` as an intermediate fact. Use `hL.deg` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnum` using `om_sizes_le_poR P.R.f P.R.r L lE (Real.log (classNumber P.host.E)) (Real.log (modulus P : ℝ)) (Real.log (δ.hstar : ℝ)) (Real.log P.restRowsFiniteGroupCard) (Real.log (rootOrder P : ℝ)) (Real.log (P.host.d : ℝ)) (NumberField.Units.rank P.host.E) (Real.log (Module.finrank ℚ P.host. …`.

Use `sz_mono_and_of_le.1 _ _ _ _ _ hall ?_ ?_` and prove the remaining obligations. Unfold `poR`. Conclude with `hnum.1`. Unfold `poR`. Conclude with `hnum.2`.
-/
theorem sz_Om_poR : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  intro hR P δ L hL
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  obtain ⟨K, _, _, hK2, hKd, -, hKE, -, hdeg⟩ := exists_hostK P.R P.host
  have hE := sz_fieldRange_embedding P.host.E P.host.φ₀
  set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE
  have hlE0 : 0 ≤ lE := by
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    exact_mod_cast Int.one_le_abs (discr_ne_zero P.host.E)
  have hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f) := by rw [hlE, hdeg]; push_cast; rfl
  have hrd : lE ≤ 2 * L := hlE' ▸ hL.rd

  have hd : Real.log (P.host.d : ℝ) ≤ 4 * L := by
    obtain ⟨_, -, h⟩ := sz_mono_and_of_le.2 _ _ _ _ hKE hE
    have h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE := h
    rw [hK2, hKd] at h'
    push_cast at h'
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at h'
    linarith

  have hM' := GlobalTheory.T.field_datum_size_log_discriminant hR P δ
  obtain ⟨hdeg_le, hray⟩ := GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound P.host.E P.host.φ₀ (modulus P) δ.ray δ.isRay (modulus_ne_zero P)
  have hcyc : Sz (cycField (rootOrder P)) (Real.log (rootOrder P)) (Real.log (rootOrder P)) :=
    sz_adjoin_rootOfUnity _ (Nat.pos_of_ne_zero (rootOrder_ne_zero P))
  have hV : Sz δ.V _ _ := GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots P.host.E P.host.φ₀ δ.hstar δ.hstar_pos
  have hall := sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ hM' hray) hcyc) hV
  change Sz (δ.M' ⊔ δ.ray ⊔ cycField (rootOrder P) ⊔ δ.V) _ _

  obtain ⟨hG, -, hf8, -⟩ := roots_sizes P L hL
  have hf0 : (0 : ℝ) < P.R.f := by have : 8 ≤ P.R.f := hf8; exact_mod_cast (by omega : 0 < P.R.f)
  have hcl := GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg
  rw [← hlE'] at hcl
  have hh0 : 0 < classNumber P.host.E := classNumber_pos _

  have hg0 := (P.host.g_prime 0).pos
  have hg1 := (P.host.g_prime 1).pos
  have hp := P.host.pde_prime.pos
  have hp' := P.host.pde'_prime.pos
  have hN : Real.log (modulus P : ℝ) ≤ 20 * L + 2 := by
    have e : Real.log (modulus P : ℝ) = Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log P.host.pde +
        Real.log P.host.pde' := by
      simp only [modulus]; push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    have := hL.g 0
    have := hL.g 1
    have := hL.p
    rw [e]; linarith [this.1, this.2]

  have hs0 : 0 ≤ Real.log (δ.hstar : ℝ) := Real.log_natCast_nonneg _
  have hs : Real.log (δ.hstar : ℝ) ≤ Real.log (classNumber P.host.E) + 2 * P.R.f * Real.log (modulus P : ℝ) := by
    have h1 : (δ.hstar : ℝ) ≤ (classNumber P.host.E : ℝ) * (modulus P : ℝ) ^ Module.finrank ℚ P.host.E := by
      exact_mod_cast hdeg_le
    have h2 := Real.log_le_log (by exact_mod_cast δ.hstar_pos) h1
    rw [Real.log_mul (by positivity) (pow_ne_zero _ (by exact_mod_cast modulus_ne_zero P)), Real.log_pow, hdeg] at h2
    push_cast at h2
    linarith

  have hr : Real.log (rootOrder P : ℝ) ≤ Real.log P.restRowsFiniteGroupCard + 24 := by
    have hc := P.restRowsFiniteGroupCard_pos
    have h1 : (rootOrder P : ℝ) ≤ (P.restRowsFiniteGroupCard : ℝ) * ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)
    have h2 := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (rootOrder_ne_zero P)) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    have e : Real.log ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = 4 * Real.log 3 + 4 * Real.log 5 := by
      rw [show ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = (3 : ℝ) ^ 4 * (5 : ℝ) ^ 4 by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith

  have hk : (NumberField.Units.rank P.host.E : ℝ) ≤ 2 * P.R.f := by
    have : NumberField.Units.rank P.host.E ≤ Module.finrank ℚ P.host.E := by
      rw [NumberField.Units.rank, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
    rw [hdeg] at this
    exact_mod_cast this
  have d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L := by
    rw [hdeg]; push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have := hL.deg
    linarith
  have hnum := om_sizes_le_poR P.R.f P.R.r L lE (Real.log (classNumber P.host.E)) (Real.log (modulus P : ℝ))
    (Real.log (δ.hstar : ℝ)) (Real.log P.restRowsFiniteGroupCard) (Real.log (rootOrder P : ℝ)) (Real.log (P.host.d : ℝ))
    (NumberField.Units.rank P.host.E) (Real.log (Module.finrank ℚ P.host.E)) (by exact_mod_cast hf8)
    (by exact_mod_cast hL.rank) hL.len hL.deg hlE0 hrd hcl hN hs0 hs hG hr hd hk d1
  refine sz_mono_and_of_le.1 _ _ _ _ _ hall ?_ ?_
  · unfold poR; exact hnum.1
  · unfold poR; exact hnum.2

end GlobalTheory.FieldSize

end
