import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodConstantEqOfCardCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHeckeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoissonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfIsIntegralAlgebraicNumbers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllIsAlgebraicHfunTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulMatSmulOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCmStatement
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOneIffIsIntegral

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.RoadELatAlg

/- English proof (translation)
Use `⟨Polynomial.X ^ 2 - Polynomial.C q, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.X_pow_sub_C_ne_zero (by norm_num) q`. Simplify using `[h]`.
-/
theorem isAlgebraic_of_sq_eq_ratCast {x : ℂ} (q : ℚ) (h : x ^ 2 = (q : ℂ)) : IsAlgebraic ℚ x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C q, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) q
  · simp [h]

/- English proof (translation)
Establish `hmem : ∀ z : ℂ, z ∈ Λ.lattice → ∃ a : K, ι a = z`. Introduce `z hz`. Establish `: z ∈ (Λ.lattice : Set ℂ)` using `hz`. Rewrite `this` using `[hΛ]`. Take `⟨a, -, ha⟩` from `this`.

Conclude with `⟨a, ha⟩`. Take `⟨a, ha⟩` from `hmem c ((hτ.2 c).2 ⟨0, 1, by simp⟩)`. Take `⟨b, hb⟩` from `hmem (c * τ) ((hτ.2 _).2 ⟨1, 0, by simp⟩)`. Establish `hc : c ≠ 0` using `hτ.1`. Use `⟨b / a, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, ha, hb]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[← ha]`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic a).algHom ι.toRatAlgHom`.
-/
theorem exists_theta {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ) (Λ : PeriodPair)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ) (c : ℂ) (τ : ℍ) (hτ : IsTauOf Λ c τ) :
    ∃ θ : K, ι θ = (τ : ℂ) ∧ IsAlgebraic ℚ c := by
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice → ∃ a : K, ι a = z := by
    intro z hz
    have : z ∈ (Λ.lattice : Set ℂ) := hz
    rw [hΛ] at this
    obtain ⟨a, -, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hmem c ((hτ.2 c).2 ⟨0, 1, by simp⟩)
  obtain ⟨b, hb⟩ := hmem (c * τ) ((hτ.2 _).2 ⟨1, 0, by simp⟩)
  have hc : c ≠ 0 := hτ.1
  refine ⟨b / a, ?_, ?_⟩
  · rw [map_div₀, ha, hb]; field_simp
  · rw [← ha]; exact (Algebra.IsAlgebraic.isAlgebraic a).algHom ι.toRatAlgHom

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[pow_add, pow_mul, div_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem term_div_eq (r Y H ω : ℂ) (a w W : ℕ) (h : W = 2 * a + w) :
    r * Y ^ a * H / ω ^ W = r * ((Y / ω ^ 2) ^ a * (H / ω ^ w)) := by
  subst h
  rw [pow_add, pow_mul, div_pow]
  ring

/- English proof (translation)
Establish `h2 : (2 * im / r) ^ K * (pi / im) ^ K = (2 * pi / r) ^ K`. Rewrite using `[← mul_pow]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `h3 : c ^ W / p ^ W / (Ω * c / p) ^ W = 1 / Ω ^ W`.

Rewrite using `[div_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel₀ hsg, h2, h3, hc0]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [hD]; ring`.
-/
theorem coord_id (c0 S0 D Ω c cW P pi im r p sg : ℂ) (W K : ℕ) (hsg : sg ≠ 0) (hD : D = cW * (sg * P) * S0)
    (hc0 : c0 = cW * P * (2 * pi / r) ^ K) (hΩ : Ω ≠ 0) (hc : c ≠ 0) (hp : p ≠ 0) (him : im ≠ 0) (hr : r ≠ 0) :
    c0 * S0 / Ω ^ W = sg⁻¹ * (2 * im / r) ^ K * c ^ W * (D * (pi / im) ^ K / p ^ W / (Ω * c / p) ^ W) := by
  have h2 : (2 * im / r) ^ K * (pi / im) ^ K = (2 * pi / r) ^ K := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : c ^ W / p ^ W / (Ω * c / p) ^ W = 1 / Ω ^ W := by
    rw [div_pow, mul_pow]; field_simp
  calc c0 * S0 / Ω ^ W = (sg⁻¹ * sg) * (cW * P * S0) * ((2 * im / r) ^ K * (pi / im) ^ K) *
        (c ^ W / p ^ W / (Ω * c / p) ^ W) := by
          rw [inv_mul_cancel₀ hsg, h2, h3, hc0]; ring
    _ = _ := by rw [hD]; ring

/- English proof (translation)
Introduce `hSKDR hPZ _ _`. Introduce `K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS`. Take `⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩` from `hDat`. Establish `hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E)` using `GlobalTheory.LatAlgebraic.two_le_finrank hUn`. Establish `hc0 : condQ 𝔣 Q ≠ ⊥` using `by show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0`.

Conclude with `mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)`. Establish `hΩ0 : Ω₀ ≠ 0`. Introduce and unpack `rfl`. Conclude with `latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)`. Establish `hW2` using `GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ`.

Establish `hSt` using `GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2`. Establish `hEis` using `GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson hW2 hPZ`. Take `⟨⟨z, hz⟩, -⟩` from `GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSKDR E s hs`. Take `⟨⟨g, hg⟩, hD⟩` from `(((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1`. Take `⟨u, hu⟩` from `GlobalTheory.LatAlgebraic.exists_list_count κ`.

Establish `hDg` using `((hD g hg).2 κ u hu).1 S hS`. Take `⟨c, τ, hτ⟩` from `latTau Λ₀`. Take `⟨θ, hθτ, hcalg⟩` from `exists_theta ι Λ₀ hΛ c τ hτ`. Establish `hc : c ≠ 0` using `hτ.1`. Establish `hφθ : ∀ i, φ i (algebraMap K E θ) = (τ : ℂ)`.

Introduce `i`. Rewrite using `[← RingHom.comp_apply, hφι i, hθτ]`. Take `⟨e, he⟩` from `GlobalTheory.CMTypeEmb.exists_equiv E I φ hCM`. Establish `hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)` using `GlobalTheory.LatAlgebraic.card_eq_finrank hCM`. Establish `hI : Nonempty I` using `Fintype.card_pos_iff.1 (by omega)`.

Take `⟨i₀⟩` from `hI`. Establish `hθF : algebraMap K E θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E))`. Introduce and unpack `⟨x, hx⟩`. Establish `h1` using `he i₀ x`. Express the relevant statement in the definitionally equal form `(x : E) = _ at hx`.

Rewrite `h1` using `[hx, hφθ i₀]`. Establish `h2` using `congrArg Complex.im h1`. Simplify using `only [Complex.ofReal_im] at h2`. Conclude with `τ.im_pos.ne' h2`. Take `⟨n, N, L, hn, hN, hN2, hL, hLΛ⟩` from `GlobalTheory.RoadE.exists_level E (algebraMap K E θ) (condQ 𝔣 Q) y 2 hc0 hθF (by norm_num)`.

Establish `hN2' : 2 ≤ N` using `Nat.le_of_dvd hN hN2`. Use `haveI : NeZero N := ⟨by omega⟩`. Use `haveI : Fact (1 < N) := ⟨by omega⟩`. Set `y₁ : Fin 2 → ZMod N` to `![1, 0]`. Establish `hy₁ : y₁ ≠ 0`.

Introduce `h`. Use `congrFun h 0` as an intermediate fact. Simplify using `[y₁] at this`. Establish `hval` using `GlobalTheory.HilbFam.eValue_derivs hEis E I φ e (algebraMap K E θ) τ (lattice (condQ 𝔣 Q) y) L n s N g κ u (wB N y₁) hf2 hs hN hL he hφθ hn hLΛ hg hu`. Take `⟨hωDD, hj, hG2, hwp⟩` from `GlobalTheory.AlgTau.main K d δ ι 1 Λ₀ c Ω₀ τ hd hδ hΛ hτ hΩ`.

Use `set ω : ℂ := Ω₀ * c / (2 * Real.pi * Complex.I) with hω`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[hpi, Complex.I_ne_zero]`. Establish `hω0 : ω ≠ 0` using `div_ne_zero (mul_ne_zero hΩ0 hc) h2piI`.

Establish `hH : ∀ μ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ, IsAlgebraic ℚ (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ)`. Introduce `μ`. Establish `h` using `GlobalTheory.QFam.fam_value_isAlgebraic (GL (Fin 2) (ZMod N)) (GlobalTheory.WpFam.gact N 1) (GlobalTheory.HilbFam.wt (2 * s) μ) N (fun α ↦ GlobalTheory.HilbFam.hfun (2 * s) (GlobalTheory.HilbFam.twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) μ (wB N (Glo …`. Simplify `h` using `only [Units.val_one, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L hL, (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.1]`. Establish `hX : IsAlgebraic ℚ ((((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y₁ τ) / ω ^ 2)`.

Rewrite using `[GlobalTheory.wB_nonhol_correction, neg_div, add_div]`. Conclude with `((hG2.add (hwp N y₁))).neg`. Use `set f := Module.finrank ℚ (maximalRealSubfield E) with hf`. Use `set k := ∑ i, κ i with hk`. Use `set P : ℂ := 2 * Real.pi * Complex.I with hP`.

Use `set Y : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) / P ^ 2 - wB N y₁ τ with hY`. Use `set κ' : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ := fun j ↦ κ (e.symm j) with hκ'`. Establish `hsum' : ∑ j, κ' j = k` using `Equiv.sum_comp e.symm κ`. Establish `hA : ∀ x : ℂ, IsAlgebraic ℚ x → x ∈ algebraicClosure ℚ ℂ` using `fun x h ↦ mem_algebraicClosure_iff.2 h`. Establish `hRalg : IsAlgebraic ℚ (((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ', ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) * GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k))`.

Establish `key : ((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ', ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) * GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k) = (n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ', ((∏ j, Global …`. Rewrite using `[mul_div_assoc, Finset.sum_div]`. Use `congrArg _ (Finset.sum_congr rfl fun μ hμ ↦ ?_)` and prove the remaining obligations. Establish `hle : μ ≤ κ'` using `Finset.mem_Iic.1 hμ`. Establish `hexp : 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + GlobalTheory.HilbFam.wt (2 * s) μ`.

Establish `h1 : ∑ j, (κ' j - μ j) + ∑ j, μ j = ∑ j, κ' j`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hle j)`. Express the relevant statement in the definitionally equal form `2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + (2 * s * f + 2 * ∑ j, μ j)`. Use linear arithmetic over natural numbers and integers.

Conclude with `term_div_eq _ _ _ _ _ _ _ hexp`. Rewrite using `[key, ← mem_algebraicClosure_iff]`. Use `mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _) (mul_mem (pow_mem (hA _ hX) _) (hA _ (hH μ))))` and prove the remaining obligations. Establish `hRalg' : IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ k / P ^ (2 * s * f + 2 * k) / ω ^ (2 * s * f + 2 * k))`. Rewrite using `[hval]`.

Conclude with `hRalg`. Rewrite `hRalg'` using `[Complex.ofReal_div]`. Establish `hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd)`. Conclude with `this.ne'` after adjusting the coercions.

Establish `him : ((τ.im : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast τ.im_pos.ne'`. Establish `hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s)`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt`. Establish `h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)|` using `abs_pos.2 (by exact_mod_cast discr_ne_zero _)`.

Conclude with `mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)`. Conclude with `this.ne'` after adjusting the coercions. Establish `hP' : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)` using `Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hsgn : ((-1 : ℂ) ^ k) ≠ 0` using `pow_ne_zero _ (by norm_num)`. Establish `hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) * (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k`. Rewrite using `[GlobalTheory.LatAlgebraic.cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hDg` using `[GlobalTheory.LatAlgebraic.risingFactor_eq]`. Establish `key2 : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) = ((-1 : ℂ) ^ k)⁻¹ * (2 * ((τ.im : ℝ) : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k * c ^ (2 * s * f + 2 * k) * (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi : ℂ) / ((τ.im : ℝ) : ℂ)) ^ k / P …`. Rewrite using `[GlobalTheory.ToricTransport.coordIn, hcard]`. Conclude with `coord_id _ (S 0) (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) Ω₀ c _ _ (Real.pi : ℂ) ((τ.im : ℝ) : ℂ) ((Real.sqrt d : ℝ) : ℂ) P ((-1 : ℂ) ^ k) (2 * s * f + 2 * k) k hsgn hDg hC0 hΩ0 hc h2piI him hsd`. Establish `hτalg : IsAlgebraic ℚ (τ : ℂ)`.

Rewrite using `[← hθτ]`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic θ).algHom ι.toRatAlgHom`. Establish `hτc : IsAlgebraic ℚ (starRingEnd ℂ (τ : ℂ))`. Rewrite using `[← hθτ]`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic θ).algHom ((starRingEnd ℂ).comp ι).toRatAlgHom`.

Establish `hIalg : IsAlgebraic ℚ Complex.I` using `isAlgebraic_of_sq_eq_ratCast (-1) (by simp [Complex.I_sq])`. Establish `himalg : IsAlgebraic ℚ ((τ.im : ℝ) : ℂ)`. Rewrite using `[← UpperHalfPlane.coe_im, Complex.im_eq_sub_conj, ← mem_algebraicClosure_iff]`. Conclude with `div_mem (sub_mem (hA _ hτalg) (hA _ hτc)) (mul_mem (ofNat_mem _ 2) (hA _ hIalg))`. Establish `hsdalg : IsAlgebraic ℚ ((Real.sqrt d : ℝ) : ℂ)`.

Use `isAlgebraic_of_sq_eq_ratCast (d : ℚ) ?_` and prove the remaining obligations. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Rewrite using `[key2, ← mem_algebraicClosure_iff]`. Conclude with `mul_mem (mul_mem (mul_mem (inv_mem (pow_mem (neg_mem (one_mem _)) _)) (pow_mem (div_mem (mul_mem (ofNat_mem _ 2) (hA _ himalg)) (hA _ hsdalg)) _)) (pow_mem (hA _ hcalg) _)) (hA _ hRalg')`.
-/
theorem latAlg_of_siegelKlingen : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation →
    GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  intro hSKDR hPZ _ _
  intro K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS
  classical
  obtain ⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩ := hDat
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hΩ0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)
  have hW2 := GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ
  have hSt := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2
  have hEis := GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson hW2 hPZ
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSKDR E s hs
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := GlobalTheory.LatAlgebraic.exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  obtain ⟨c, τ, hτ⟩ := latTau Λ₀
  obtain ⟨θ, hθτ, hcalg⟩ := exists_theta ι Λ₀ hΛ c τ hτ
  have hc : c ≠ 0 := hτ.1
  have hφθ : ∀ i, φ i (algebraMap K E θ) = (τ : ℂ) := by
    intro i; rw [← RingHom.comp_apply, hφι i, hθτ]
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeEmb.exists_equiv E I φ hCM
  have hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.card_eq_finrank hCM
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hI
  have hθF : algebraMap K E θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) := by
    rintro ⟨x, hx⟩
    have h1 := he i₀ x
    change (x : E) = _ at hx
    rw [hx, hφθ i₀] at h1
    have h2 := congrArg Complex.im h1
    simp only [Complex.ofReal_im] at h2
    exact τ.im_pos.ne' h2
  obtain ⟨n, N, L, hn, hN, hN2, hL, hLΛ⟩ := GlobalTheory.RoadE.exists_level E (algebraMap K E θ) (condQ 𝔣 Q) y 2 hc0 hθF (by norm_num)
  have hN2' : 2 ≤ N := Nat.le_of_dvd hN hN2
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨by omega⟩
  let y₁ : Fin 2 → ZMod N := ![1, 0]
  have hy₁ : y₁ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [y₁] at this
  have hval := GlobalTheory.HilbFam.eValue_derivs hEis E I φ e (algebraMap K E θ) τ (lattice (condQ 𝔣 Q) y) L n s N g κ u
    (wB N y₁) hf2 hs hN hL he hφθ hn hLΛ hg hu
  obtain ⟨hωDD, hj, hG2, hwp⟩ := GlobalTheory.AlgTau.main K d δ ι 1 Λ₀ c Ω₀ τ hd hδ hΛ hτ hΩ

  set ω : ℂ := Ω₀ * c / (2 * Real.pi * Complex.I) with hω
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have hω0 : ω ≠ 0 := div_ne_zero (mul_ne_zero hΩ0 hc) h2piI
  have hH : ∀ μ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ,
      IsAlgebraic ℚ (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ) := by
    intro μ
    have h := GlobalTheory.QFam.fam_value_isAlgebraic (GL (Fin 2) (ZMod N)) (GlobalTheory.WpFam.gact N 1) (GlobalTheory.HilbFam.wt (2 * s) μ) N
      (fun α ↦ GlobalTheory.HilbFam.hfun (2 * s) (GlobalTheory.HilbFam.twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) μ (wB N (GlobalTheory.WpFam.vmul y₁ α)))
      τ ω (by omega) (((GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.1 1).actBij)
      (GlobalTheory.HilbFam.isFam_hfun_GL hEis (maximalRealSubfield E) hf2 s N L hs hL y₁ μ)
      (fun α ↦ GlobalTheory.HilbFam.qAll_isAlgebraic_hfun_twist hEis (maximalRealSubfield E) hf2 s N L hs hL z hz μ y₁ hy₁ α)
      hj hωDD 1
    simpa only [Units.val_one, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L hL, (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.1] using h
  have hX : IsAlgebraic ℚ ((((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y₁ τ) / ω ^ 2) := by
    rw [GlobalTheory.wB_nonhol_correction, neg_div, add_div]
    exact ((hG2.add (hwp N y₁))).neg
  set f := Module.finrank ℚ (maximalRealSubfield E) with hf
  set k := ∑ i, κ i with hk
  set P : ℂ := 2 * Real.pi * Complex.I with hP
  set Y : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) / P ^ 2 - wB N y₁ τ with hY
  set κ' : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ := fun j ↦ κ (e.symm j) with hκ'
  have hsum' : ∑ j, κ' j = k := Equiv.sum_comp e.symm κ
  have hA : ∀ x : ℂ, IsAlgebraic ℚ x → x ∈ algebraicClosure ℚ ℂ := fun x h ↦ mem_algebraicClosure_iff.2 h

  have hRalg : IsAlgebraic ℚ (((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
      ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
        GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k)) := by
    have key : ((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
        ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
          GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k) =
        (n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ', ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) *
          ((Y / ω ^ 2) ^ (∑ j, (κ' j - μ j)) * (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ)) := by
      rw [mul_div_assoc, Finset.sum_div]
      refine congrArg _ (Finset.sum_congr rfl fun μ hμ ↦ ?_)
      have hle : μ ≤ κ' := Finset.mem_Iic.1 hμ
      have hexp : 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + GlobalTheory.HilbFam.wt (2 * s) μ := by
        have h1 : ∑ j, (κ' j - μ j) + ∑ j, μ j = ∑ j, κ' j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hle j)
        change 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + (2 * s * f + 2 * ∑ j, μ j)
        omega
      exact term_div_eq _ _ _ _ _ _ _ hexp
    rw [key, ← mem_algebraicClosure_iff]
    refine mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _)
      (mul_mem (pow_mem (hA _ hX) _) (hA _ (hH μ))))
  have hRalg' : IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ k / P ^ (2 * s * f + 2 * k) /
      ω ^ (2 * s * f + 2 * k)) := by
    rw [hval]; exact hRalg
  rw [Complex.ofReal_div] at hRalg'
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have him : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt
      have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
      exact mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)
    exact_mod_cast this.ne'
  have hP' : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity
    exact_mod_cast this.ne'
  have hsgn : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) *
      (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k := by
    rw [GlobalTheory.LatAlgebraic.cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]; push_cast; ring
  rw [GlobalTheory.LatAlgebraic.risingFactor_eq] at hDg
  have key2 : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) = ((-1 : ℂ) ^ k)⁻¹ *
      (2 * ((τ.im : ℝ) : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k * c ^ (2 * s * f + 2 * k) *
      (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi : ℂ) / ((τ.im : ℝ) : ℂ)) ^ k / P ^ (2 * s * f + 2 * k) /
        ω ^ (2 * s * f + 2 * k)) := by
    rw [GlobalTheory.ToricTransport.coordIn, hcard]
    exact coord_id _ (S 0) (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) Ω₀ c _ _ (Real.pi : ℂ) ((τ.im : ℝ) : ℂ)
      ((Real.sqrt d : ℝ) : ℂ) P ((-1 : ℂ) ^ k) (2 * s * f + 2 * k) k hsgn hDg hC0 hΩ0 hc h2piI him hsd
  have hτalg : IsAlgebraic ℚ (τ : ℂ) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ι.toRatAlgHom
  have hτc : IsAlgebraic ℚ (starRingEnd ℂ (τ : ℂ)) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ((starRingEnd ℂ).comp ι).toRatAlgHom
  have hIalg : IsAlgebraic ℚ Complex.I := isAlgebraic_of_sq_eq_ratCast (-1) (by simp [Complex.I_sq])
  have himalg : IsAlgebraic ℚ ((τ.im : ℝ) : ℂ) := by
    rw [← UpperHalfPlane.coe_im, Complex.im_eq_sub_conj, ← mem_algebraicClosure_iff]
    exact div_mem (sub_mem (hA _ hτalg) (hA _ hτc)) (mul_mem (ofNat_mem _ 2) (hA _ hIalg))
  have hsdalg : IsAlgebraic ℚ ((Real.sqrt d : ℝ) : ℂ) := by
    refine isAlgebraic_of_sq_eq_ratCast (d : ℚ) ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rw [key2, ← mem_algebraicClosure_iff]
  exact mul_mem (mul_mem (mul_mem (inv_mem (pow_mem (neg_mem (one_mem _)) _))
    (pow_mem (div_mem (mul_mem (ofNat_mem _ 2) (hA _ himalg)) (hA _ hsdalg)) _)) (pow_mem (hA _ hcalg) _)) (hA _ hRalg')

end GlobalTheory.RoadELatAlg
