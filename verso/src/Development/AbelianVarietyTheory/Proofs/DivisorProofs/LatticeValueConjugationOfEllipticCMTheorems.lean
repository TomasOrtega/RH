import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordInEqOfJet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHeckeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoissonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportModularFamilyGL2ZModWeierstrassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassTorsionConjTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitZetaAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulMatSmulOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOneIffIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveRat

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UpperHalfPlane GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory.LatJet (EisExp FR)
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD cWt risingFactor DerivFormula lamInf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsLatOf IsInvIdealOf nrm)
open GlobalTheory.ToricTransport (coordIn)
open ReciprocityTheory.ChartRestriction.L1 (IsTauOf)
open scoped Classical nonZeroDivisors MatrixGroups

namespace GlobalTheory.LatConjEll

/- English proof (translation)
Establish `h1` using `congrArg ι hab`. Simplify using `only [map_add, map_mul, map_intCast, h, map_zero] at h1`. Establish `h2` using `congrArg Complex.im h1`. Establish `ha : a = 0`. Establish `: (a : ℝ) * τ.im = 0` using `by simpa using h2`.

Conclude with `(mul_eq_zero.1 this).resolve_right τ.im_pos.ne'` after adjusting the coercions. Substitute `ha` using the available equality. Conclude with `⟨rfl, by simpa using h1⟩`.
-/
theorem indep {K : Type} [Field K] (ι : K →+* ℂ) (θ : K) (τ : ℍ) (h : ι θ = τ) (a b : ℤ) (hab : (a : K) * θ + b = 0) :
    a = 0 ∧ b = 0 := by
  have h1 := congrArg ι hab
  simp only [map_add, map_mul, map_intCast, h, map_zero] at h1
  have h2 := congrArg Complex.im h1
  have ha : a = 0 := by
    have : (a : ℝ) * τ.im = 0 := by simpa using h2
    exact_mod_cast (mul_eq_zero.1 this).resolve_right τ.im_pos.ne'
  subst ha
  exact ⟨rfl, by simpa using h1⟩

/- English proof (translation)
Take `⟨θ, hθ⟩` from `(FractionalIdeal.mem_one_iff _).1 ((hO θ₀).2 ⟨1, 0, by simp⟩)`. Establish `hcK : (c : K) ≠ 0` using `by exact_mod_cast hc.ne'`. Set `b : Module.Basis (Fin 2) ℤ (𝓞 K)` to `Module.Basis.mk (v := ![θ, 1]) (by`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Apply `indep ι θ₀ τ₀ h0` to reduce the goal to its premises. Use `congrArg (algebraMap (𝓞 K) K) hst` as an intermediate fact. Simplify `this)` using `[hθ]`. Use the proof step `(by`. Introduce `x _`.

Take `⟨u, v, huv⟩` from `(hO (algebraMap (𝓞 K) K x)).1 ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)`. Rewrite using `[Matrix.range_cons_cons_empty, Submodule.mem_span_pair]`. Use `⟨u, v, FaithfulSMul.algebraMap_injective (𝓞 K) K ?_⟩` and prove the remaining obligations. Simplify using `[huv, hθ])`. Set `bI : Module.Basis (Fin 2) ℤ 𝔞` to `Module.Basis.mk (v := ![⟨c * θ₁, (ha _).2 ⟨1, 0, by simp⟩⟩, ⟨c, (ha _).2 ⟨0, 1, by simp⟩⟩]) (by`.

Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Apply `indep ι θ₁ τ₁ h1` to reduce the goal to its premises. Use `congrArg Subtype.val hst` as an intermediate fact. Apply `mul_left_cancel₀ hcK` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, Submodule.coe_zero] at this`. Take the linear combination `this)`. Use the proof step `(by`. Introduce `x _`. Take `⟨u, v, huv⟩` from `(ha x).1 x.2`.

Rewrite using `[Matrix.range_cons_cons_empty, Submodule.mem_span_pair]`. Use `⟨u, v, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul]`. Rewrite using `[huv]`. Use the proof step `ring)`.

Establish `key` using `FractionalIdeal.abs_det_basis_change b 𝔞 bI`. Use `set B := b.localizationLocalization ℚ ℤ⁰ K with hB`. Establish `hB0 : B 0 = θ₀` using `by simp [hB, b, hθ]`. Establish `hB1 : B 1 = 1` using `by simp [hB, b]`. Establish `e0 : (bI 0 : K) = c * θ₁` using `by simp [bI]`.

Establish `e1 : (bI 1 : K) = c • B 1` using `by simp [bI, hB1, Rat.smul_def]`. Establish `hs` using `B.sum_repr (c * θ₁)`. Rewrite `hs` using `[Fin.sum_univ_two, hB0, hB1]`. Rewrite `key` using `[Module.Basis.det_apply, Matrix.det_fin_two]`. Simplify using `only [Module.Basis.toMatrix_apply, Function.comp_apply, e0, e1, map_smul, Module.Basis.repr_self] at key`.

Simplify using `at key`. Establish `h2` using `congrArg (fun z => (ι z).im) hs`. Simplify using `[Rat.smul_def, h0, h1] at h2`. Establish `hcR : (0 : ℝ) < c` using `by exact_mod_cast hc`. Establish `hp : (0 : ℝ) < ((B.repr (c * θ₁) 0 : ℚ) : ℝ)`.

Use `mul_pos hcR τ₁.im_pos` as an intermediate fact. Rewrite `this` using `[← h2]`. Conclude with `(pos_iff_pos_of_mul_pos this).2 τ₀.im_pos`. Establish `hp' : 0 < B.repr (c * θ₁) 0` using `by exact_mod_cast hp`. Rewrite using `[nrm, ← key, abs_of_pos hp', abs_of_pos hc]`.

Use `push_cast`. Take the linear combination `(-(c : ℝ)) * h2`.
-/
theorem covol {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (θ₀ θ₁ : K) (c : ℚ) (τ₀ τ₁ : ℍ)
    (hc : 0 < c) (h0 : ι θ₀ = τ₀) (h1 : ι θ₁ = τ₁)
    (hO : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ ∃ a b : ℤ, x = (a : K) * θ₀ + b)
    (ha : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ₁ + (b : K))) :
    (c : ℝ) ^ 2 * τ₁.im = nrm 𝔞 * τ₀.im := by
  obtain ⟨θ, hθ⟩ := (FractionalIdeal.mem_one_iff _).1 ((hO θ₀).2 ⟨1, 0, by simp⟩)
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc.ne'
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.Basis.mk (v := ![θ, 1])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply indep ι θ₀ τ₀ h0
      have := congrArg (algebraMap (𝓞 K) K) hst
      simpa [hθ] using this)
    (by
      intro x _
      obtain ⟨u, v, huv⟩ := (hO (algebraMap (𝓞 K) K x)).1 ((FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩)
      rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
      refine ⟨u, v, FaithfulSMul.algebraMap_injective (𝓞 K) K ?_⟩
      simp [huv, hθ])
  let bI : Module.Basis (Fin 2) ℤ 𝔞 := Module.Basis.mk
    (v := ![⟨c * θ₁, (ha _).2 ⟨1, 0, by simp⟩⟩, ⟨c, (ha _).2 ⟨0, 1, by simp⟩⟩])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply indep ι θ₁ τ₁ h1
      have := congrArg Subtype.val hst
      apply mul_left_cancel₀ hcK
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, Submodule.coe_zero] at this
      linear_combination this)
    (by
      intro x _
      obtain ⟨u, v, huv⟩ := (ha x).1 x.2
      rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
      refine ⟨u, v, Subtype.ext ?_⟩
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul]
      rw [huv]; ring)
  have key := FractionalIdeal.abs_det_basis_change b 𝔞 bI
  set B := b.localizationLocalization ℚ ℤ⁰ K with hB
  have hB0 : B 0 = θ₀ := by simp [hB, b, hθ]
  have hB1 : B 1 = 1 := by simp [hB, b]
  have e0 : (bI 0 : K) = c * θ₁ := by simp [bI]
  have e1 : (bI 1 : K) = c • B 1 := by simp [bI, hB1, Rat.smul_def]
  have hs := B.sum_repr (c * θ₁)
  rw [Fin.sum_univ_two, hB0, hB1] at hs
  rw [Module.Basis.det_apply, Matrix.det_fin_two] at key
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply, e0, e1, map_smul, Module.Basis.repr_self] at key
  simp at key
  have h2 := congrArg (fun z => (ι z).im) hs
  simp [Rat.smul_def, h0, h1] at h2
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hp : (0 : ℝ) < ((B.repr (c * θ₁) 0 : ℚ) : ℝ) := by
    have := mul_pos hcR τ₁.im_pos
    rw [← h2] at this
    exact (pos_iff_pos_of_mul_pos this).2 τ₀.im_pos
  have hp' : 0 < B.repr (c * θ₁) 0 := by exact_mod_cast hp
  rw [nrm, ← key, abs_of_pos hp', abs_of_pos hc]
  push_cast
  linear_combination (-(c : ℝ)) * h2

/- English proof (translation)
Establish `h2 : (ι δ) ^ 2 = -(d : ℂ)` using `by rw [← map_pow, hδ]; simp`. Establish `hre` using `congrArg Complex.re h2`. Establish `him` using `congrArg Complex.im h2`. Simplify using `[pow_two] at hre him`. Establish `hdR : (0 : ℝ) < d` using `by exact_mod_cast hd`.

Establish `h3 : (ι δ).im = a * τ.im` using `by rw [hab]; simp [h]`. Establish `h4 : (ι δ).re = 0`. Assume the negation of the conclusion as `hne`. Establish `: (ι δ).im = 0`. Establish `: 2 * (ι δ).re * (ι δ).im = 0` using `by linarith`.

Simplify `this` using `[hne]`. Rewrite `hre` using `[this]`. Use polynomial arithmetic with `[mul_self_nonneg (ι δ).re]`. Establish `h5 : (d : ℝ) = (a * τ.im) ^ 2` using `by rw [← h3]; rw [h4] at hre; linarith`. Establish `ha : (a : ℝ) ≠ 0`.

Introduce `h0`. Rewrite `h5` using `[h0]`. Simplify using `at h5`. Use linear arithmetic over natural numbers and integers. Use `⟨2 / |(a : ℚ)|, ?_⟩` and prove the remaining obligations.

Rewrite using `[h5, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos τ.im_pos]`. Use `τ.im_pos` as an intermediate fact. Use `abs_pos.2 ha` as an intermediate fact. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem ratio_rat {K : Type} [Field K] (ι : K →+* ℂ) (d : ℕ) (hd : 0 < d) (δ θ : K) (τ : ℍ) (hδ : δ ^ 2 = -(d : K)) (h : ι θ = τ)
    (a b : ℤ) (hab : δ = a * θ + b) : ∃ q : ℚ, 2 * τ.im / Real.sqrt d = q := by
  have h2 : (ι δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp [pow_two] at hre him
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : (ι δ).im = a * τ.im := by rw [hab]; simp [h]
  have h4 : (ι δ).re = 0 := by
    by_contra hne
    have : (ι δ).im = 0 := by
      have : 2 * (ι δ).re * (ι δ).im = 0 := by linarith
      simpa [hne] using this
    rw [this] at hre
    nlinarith [mul_self_nonneg (ι δ).re]
  have h5 : (d : ℝ) = (a * τ.im) ^ 2 := by rw [← h3]; rw [h4] at hre; linarith
  have ha : (a : ℝ) ≠ 0 := by
    intro h0; rw [h0] at h5; simp at h5; omega
  refine ⟨2 / |(a : ℚ)|, ?_⟩
  rw [h5, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos τ.im_pos]
  have := τ.im_pos
  have := abs_pos.2 ha
  push_cast
  field_simp

/- English proof (translation)
Rewrite using `[Finset.sum_div, Finset.sum_div, map_sum]`. Establish `hκ' : ∀ j, κ' j = κ (σ.symm j)` using `fun j => by rw [← hκ]; simp`. Use `Finset.sum_equiv (σ.arrowCongr (Equiv.refl ℕ)) (fun μ => ?_) (fun μ hμ => ?_)` and prove the remaining obligations. Simplify using `only [Finset.mem_Iic, Pi.le_def, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id, hκ']`. Conclude with `⟨fun h j => h _, fun h j => by simpa using h (σ j)⟩`.

Establish `hle : ∀ j, μ j ≤ κ j` using `Finset.mem_Iic.1 hμ`. Establish `hsum : ∑ j, κ j = ∑ j, (κ j - μ j) + ∑ j, μ j`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => (Nat.sub_add_cancel (hle j)).symm`. Establish `hsp : ∀ (r x H ω : ℂ), r * x ^ (∑ j, (κ j - μ j)) * H / ω ^ (a + 2 * ∑ j, κ j) = r * (x / ω ^ 2) ^ (∑ j, (κ j - μ j)) * (H / ω ^ (a + 2 * ∑ j, μ j))` using `fun r x H ω => by`.

Rewrite using `[show a + 2 * ∑ j, κ j = 2 * ∑ j, (κ j - μ j) + (a + 2 * ∑ j, μ j) by rw [hsum]; ring, pow_add, pow_mul, div_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hf : (σ.arrowCongr (Equiv.refl ℕ)) μ = fun j => μ (σ.symm j)` using `rfl`. Establish `e1 : ∏ j, rco k (κ' j) (μ (σ.symm j)) = ∏ j, rco k (κ j) (μ j)` using `(Fintype.prod_equiv σ _ _ fun j => by simp [hκ]).symm`. Establish `e2 : ∑ j, (κ' j - μ (σ.symm j)) = ∑ j, (κ j - μ j)` using `(Fintype.sum_equiv σ _ _ fun j => by simp [hκ]).symm`.

Rewrite using `[hf]`. Simplify using `only [e1, e2]`. Rewrite using `[hsp, hsp, map_mul, map_mul, map_pow, hx, hH, map_intCast]`.
-/
theorem sum_transport {J : Type} [Fintype J] [DecidableEq J] (g : ℂ ≃+* ℂ) (σ : J ≃ J) (k a : ℕ) (κ κ' : J → ℕ)
    (hκ : ∀ j, κ' (σ j) = κ j) (x₀ x₁ ω₀ ω₁ : ℂ) (H₀ H₁ : (J → ℕ) → ℂ) (hx : g (x₀ / ω₀ ^ 2) = x₁ / ω₁ ^ 2)
    (hH : ∀ μ : J → ℕ, g (H₀ μ / ω₀ ^ (a + 2 * ∑ j, μ j)) = H₁ (fun j => μ (σ.symm j)) / ω₁ ^ (a + 2 * ∑ j, μ j)) :
    g ((∑ μ ∈ Finset.Iic κ, ((∏ j, rco k (κ j) (μ j) : ℤ) : ℂ) * x₀ ^ (∑ j, (κ j - μ j)) * H₀ μ) / ω₀ ^ (a + 2 * ∑ j, κ j)) =
      (∑ μ ∈ Finset.Iic κ', ((∏ j, rco k (κ' j) (μ j) : ℤ) : ℂ) * x₁ ^ (∑ j, (κ' j - μ j)) * H₁ μ) / ω₁ ^ (a + 2 * ∑ j, κ j) := by
  rw [Finset.sum_div, Finset.sum_div, map_sum]
  have hκ' : ∀ j, κ' j = κ (σ.symm j) := fun j => by rw [← hκ]; simp
  refine Finset.sum_equiv (σ.arrowCongr (Equiv.refl ℕ)) (fun μ => ?_) (fun μ hμ => ?_)
  · simp only [Finset.mem_Iic, Pi.le_def, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id, hκ']
    exact ⟨fun h j => h _, fun h j => by simpa using h (σ j)⟩
  · have hle : ∀ j, μ j ≤ κ j := Finset.mem_Iic.1 hμ
    have hsum : ∑ j, κ j = ∑ j, (κ j - μ j) + ∑ j, μ j := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => (Nat.sub_add_cancel (hle j)).symm
    have hsp : ∀ (r x H ω : ℂ), r * x ^ (∑ j, (κ j - μ j)) * H / ω ^ (a + 2 * ∑ j, κ j) =
        r * (x / ω ^ 2) ^ (∑ j, (κ j - μ j)) * (H / ω ^ (a + 2 * ∑ j, μ j)) := fun r x H ω => by
      rw [show a + 2 * ∑ j, κ j = 2 * ∑ j, (κ j - μ j) + (a + 2 * ∑ j, μ j) by rw [hsum]; ring, pow_add, pow_mul, div_pow]
      ring
    have hf : (σ.arrowCongr (Equiv.refl ℕ)) μ = fun j => μ (σ.symm j) := rfl
    have e1 : ∏ j, rco k (κ' j) (μ (σ.symm j)) = ∏ j, rco k (κ j) (μ j) :=
      (Fintype.prod_equiv σ _ _ fun j => by simp [hκ]).symm
    have e2 : ∑ j, (κ' j - μ (σ.symm j)) = ∑ j, (κ j - μ j) :=
      (Fintype.sum_equiv σ _ _ fun j => by simp [hκ]).symm
    rw [hf]
    simp only [e1, e2]
    rw [hsp, hsp, map_mul, map_mul, map_pow, hx, hH, map_intCast]

/- English proof (translation)
Take `⟨⟨g, hg⟩, hD⟩` from `hD`. Take `⟨u, hu⟩` from `GlobalTheory.LatConjOne.exists_list_count κ`. Establish `e1` using `((hD g hg).2 κ u (fun i => by convert hu i)).1 S hS`. Establish `e2` using `GlobalTheory.T.hilbertEisenstein_value_derivatives_via_jets hE E I φ e θ τ Λ L n s N g κ u Ch hf hs hN hL he hθ hn hmem hg hu`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Establish `him : ((τ.im : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast τ.im_pos.ne'`. Establish `hn0 : (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hn.ne')`. Establish `hq : ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) = ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) * ((Real.pi / τ.im : ℝ) : ℂ)` using `by push_cast; field_simp`. Establish `h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero`. Rewrite using `[coordIn, GlobalTheory.LatConjOne.cmPeriodConstant_eq_of_card_cmType E d (by omega) hcard κ, hcard, hq, mul_pow, hω, div_pow, mul_pow Ω c]`.

Rewrite `e2` using `[e1]`. Generalize the expression as in `(∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), (_ : ℂ)) = T at e2 ⊢`. Establish `hcM` using `pow_ne_zero (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) hc`. Establish `hpM` using `pow_ne_zero (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) h2pi`. Rewrite `e2` using `[div_eq_iff hpM]`.

Generalize the expression as in `c ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = cM at *`. Generalize the expression as in `(2 * Real.pi * Complex.I : ℂ) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = pM at *`. Generalize the expression as in `Ω ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = W`. Establish `h3 : T / (W * cM / pM) = T * pM * W⁻¹ * cM⁻¹` using `by rw [div_div_eq_mul_div, div_eq_mul_inv, mul_inv]; ring`. Establish `h4 : cM * cM⁻¹ = 1` using `mul_inv_cancel₀ hcM`.

Rewrite using `[h3]`. Take the linear combination `((-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) * W⁻¹) * e2 - ((-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) * W⁻¹ * (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * T * pM) * h4`.
-/
theorem value_eq (hE : EisExp) (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n s N d : ℕ) (κ : I → ℕ) (Ch : ℍ → ℂ) (S : ℂ → ℂ)
    (Ω c ω : ℂ) (hf : 2 ≤ Module.finrank ℚ (FR E)) (hs : 1 ≤ s) (hN : 0 < N) (hL : HasLevel N L)
    (he : ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) (hθ : ∀ i, φ i θ = (τ : ℂ)) (hn : 0 < n)
    (hmem : ∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E))
    (hcard : Fintype.card I = Module.finrank ℚ (FR E)) (hD : DerivFormula φ (2 * s) Λ) (hS : IsLatSum φ (2 * s) κ Λ S)
    (hc : c ≠ 0) (hω : ω = Ω * c / (2 * Real.pi * Complex.I)) :
    coordIn E d s κ Ω (S 0) = (-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) *
      (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * c ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) *
      ((∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) *
        (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) *
          hfun (2 * s) L μ Ch τ) / ω ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i)) := by
  obtain ⟨⟨g, hg⟩, hD⟩ := hD
  obtain ⟨u, hu⟩ := GlobalTheory.LatConjOne.exists_list_count κ
  have e1 := ((hD g hg).2 κ u (fun i => by convert hu i)).1 S hS
  have e2 := GlobalTheory.T.hilbertEisenstein_value_derivatives_via_jets hE E I φ e θ τ Λ L n s N g κ u Ch hf hs hN hL he hθ hn hmem hg hu
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have him : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hn0 : (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  have hq : ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) = ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) * ((Real.pi / τ.im : ℝ) : ℂ) := by
    push_cast; field_simp
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  rw [coordIn, GlobalTheory.LatConjOne.cmPeriodConstant_eq_of_card_cmType E d (by omega) hcard κ, hcard, hq, mul_pow, hω, div_pow, mul_pow Ω c]
  rw [e1] at e2
  generalize (∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), (_ : ℂ)) = T at e2 ⊢
  have hcM := pow_ne_zero (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) hc
  have hpM := pow_ne_zero (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) h2pi
  rw [div_eq_iff hpM] at e2
  generalize c ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = cM at *
  generalize (2 * Real.pi * Complex.I : ℂ) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = pM at *
  generalize Ω ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = W
  have h3 : T / (W * cM / pM) = T * pM * W⁻¹ * cM⁻¹ := by rw [div_div_eq_mul_div, div_eq_mul_inv, mul_inv]; ring
  have h4 : cM * cM⁻¹ = 1 := mul_inv_cancel₀ hcM
  rw [h3]
  linear_combination ((-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) * W⁻¹) * e2 -
    ((-1) ^ (∑ i, κ i) * ((2 * τ.im / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) * W⁻¹ *
      (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * T * pM) * h4

/- English proof (translation)
Introduce `hSK hPZ _ _`. Establish `hW2` using `GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ`. Establish `hS` using `GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2`. Establish `hZ` using `GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSK`. Establish `hE` using `GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson hW2 hPZ`.

Introduce `K _ _ d δ ι hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ _ hTT E _ _ _ _ I _ φ s 𝔣 Q hD κ κ' hκ y S S' hSS hSS'`. Take `⟨hU, hφ, hφK, hs, hb, hQ⟩` from `hD`. Establish `hf : 2 ≤ Module.finrank ℚ (FR E)` using `GlobalTheory.LatConjOne.two_le_finrank_of_unramFin E hU`. Establish `hc : condQ 𝔣 Q ≠ ⊥`. Unfold `condQ`.

Use `mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)` and prove the remaining obligations. Take `⟨z, hz⟩` from `(hZ E s hs).1`. Take `⟨-, -, hg, hL0, ⟨𝔞, hinv, hL1⟩, -⟩` from `id hTT`. Establish `hmod : nrm 𝔞 = modF t` using `GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf t 𝔞 hinv`. Establish `h𝔞 : 𝔞 ≠ 0`.

Introduce and unpack `rfl`. Establish `h1 : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ)` using `Λ₁.ω₁_mem_lattice`. Rewrite `h1` using `[hL1]`. Take `⟨x, hx, hx'⟩` from `h1`. Establish `hx0 : x = 0` using `(FractionalIdeal.mem_zero_iff _).1 hx`.

Use `Λ₁.indep.ne_zero 0` as an intermediate fact. Simplify using `[← hx', hx0] at this`. Take `⟨c₀, θ₀, τ₀, hc₀, hθ₀, hT₀, hO⟩` from `GlobalTheory.IdealTheta.main K d δ ι 1 Λ₀ hK2 hd hδ one_ne_zero hL0`. Take `⟨c₁, θ₁, τ₁, hc₁, hθ₁, hT₁, ha⟩` from `GlobalTheory.IdealTheta.main K d δ ι 𝔞 Λ₁ hK2 hd hδ h𝔞 hL1`. Establish `hc1 : c₀ = 1`.

Take `⟨a, b, hab⟩` from `(hO 1).1 (FractionalIdeal.one_mem_one _)`. Take `⟨w, hw⟩` from `(FractionalIdeal.mem_one_iff _).1 ((hO c₀).2 ⟨0, 1, by simp⟩)`. Establish `hint : IsIntegral ℤ c₀`. Establish `h1 : IsIntegral ℤ (algebraMap ℚ K c₀)`. Use `w.isIntegral_coe` as an intermediate fact.

Rewrite `this` using `[hw]`. Simplify using `using this`. Conclude with `(isIntegral_algebraMap_iff (algebraMap ℚ K).injective).1 h1`. Take `⟨m, hm⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Establish `hm' : (m : ℚ) = c₀` using `by simpa using hm`.

Establish `h2` using `indep ι θ₀ τ₀ hθ₀ (m * a) (m * b - 1) (by`. Rewrite `hab` using `[← hm']`. Move the coercions through the operations in `at hab ⊢`. Take the linear combination `-hab)`. Establish `h3 : m = 1` using `Int.eq_one_of_mul_eq_one_right (by rw [← hm'] at hc₀; exact_mod_cast hc₀.le) (by linarith [h2.2])`.

Rewrite using `[← hm', h3]`. Simplify using the standard rewrite rules. Substitute `hc1` using the available equality. Simplify using `only [Rat.cast_one, one_mul] at hT₀ hO`. Establish `hcov` using `covol ι 𝔞 θ₀ θ₁ c₁ τ₀ τ₁ hc₁ hθ₀ hθ₁ hO ha`.

Establish `hδO : δ ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)`. Establish `hint : IsIntegral ℤ δ`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[hδ]`. Conclude with `(isIntegral_natCast d).neg`.

Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨⟨δ, hint⟩, rfl⟩`. Take `⟨a₀, b₀, hab⟩` from `(hO δ).1 hδO`. Take `⟨q, hq⟩` from `ratio_rat ι d hd δ θ₀ τ₀ hδ hθ₀ a₀ b₀ hab`. Establish `hφι : ∀ i x, φ i (algebraMap K E x) = ι x` using `fun i x => by rw [← RingHom.comp_apply, hφK]`. Take `⟨e, he⟩` from `GlobalTheory.CMTypeEmb.exists_equiv E I φ hφ`.

Establish `hcard : Fintype.card I = Module.finrank ℚ (FR E)`. Rewrite using `[Fintype.card_congr e, ← NumberField.Embeddings.card (FR E) ℂ]`. Use `Fintype.card_congr (Equiv.ofBijective (fun f => Complex.ofRealHom.comp f) ⟨fun f f' h => ?_, fun f => ?_⟩)` and prove the remaining obligations. Use extensionality with `x`. Use `congrArg (fun u : FR E →+* ℂ => u x) h` as an intermediate fact.

Simplify using `using this`. Conclude with `⟨(IsTotallyReal.complexEmbedding_isReal f).embedding, by ext x; simp⟩`. Establish `hI : Nonempty I` using `Fintype.card_pos_iff.1 (by omega)`. Establish `hθF : algebraMap K E θ₀ ∉ Set.range (fun x : maximalRealSubfield E => (x : E))`. Introduce and unpack `⟨x, hx⟩`.

Take `⟨i⟩` from `hI`. Establish `h1` using `he i x`. Simplify using `only at hx`. Rewrite `h1` using `[hx, hφι, hθ₀]`. Use `congrArg Complex.im h1` as an intermediate fact.

Simplify using `at this`. Conclude with `τ₀.im_pos.ne' this`. Take `⟨n, N, L₀, hn, hN, h2N, hLev, hmem⟩` from `GlobalTheory.RoadE.exists_level E (algebraMap K E θ₀) (condQ 𝔣 Q) y 2 hc hθF two_pos`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : Fact (1 < N) := ⟨Nat.le_of_dvd hN h2N⟩`.

Take `⟨hω₀, hω₁, h4, h6, hG, hA⟩` from `GlobalTheory.T.eisenstein_weierstrass_torsion_conj_transport K d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hTT 1 c₁ τ₀ τ₁ hT₀ hT₁ _ _ rfl rfl`. Take `⟨A, hAt, hAw⟩` from `hA N`. Establish `hmem₁` using `GlobalTheory.RoadE.ConjLat.twist_lattice K ι E (condQ 𝔣 Q) y t 𝔞 θ₀ (c₁ * θ₁) c₁ Λ₀ Λ₁ c₁ τ₀ τ₁ N A n L₀ hK2 hc hL0 hT₀ hθ₀ hinv hL1 hT₁ (by simp [hθ₁]) (by simp) (by simpa using hAt) hn hLev hmem`. Establish `hc₁E : (c₁ : E) ≠ 0` using `by exact_mod_cast hc₁.ne'`. Establish `hc₁C : (c₁ : ℂ) ≠ 0` using `by exact_mod_cast hc₁.ne'`.

Set `α : Eˣ` to `(Units.mk0 (c₁ : E) hc₁E)⁻¹`. Establish `hα : (α : E) = (c₁ : E)⁻¹` using `by simp [α]`. Establish `hSt` using `(hS E I φ hf hφ).1 s hs`. Use `set y₁ := y * (upIdele K E t)⁻¹ with hy₁`. Establish `hlat : (fun x => (α : E) * x) '' lattice (condQ 𝔣 Q) y₁ = lattice (condQ 𝔣 Q) (Units.map (algebraMap E (Af E)).toMonoidHom α * y₁)`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mul_mem_lattice_princ _ _ α x).2 hx`. Introduce `hx`.

Apply the tactic sequence `refine ⟨(α⁻¹ : Eˣ) * x, (mul_mem_lattice_princ _ _ α _).1 ?_, ?_⟩ <;> simpa using hx`. Establish `hH` using `((hSt.1 (condQ 𝔣 Q) y₁ hc).2 κ' α S' hSS').1`. Establish `hmem₂ : ∀ x : Fin 2 → FR E, x ∈ HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N)) ↔ ∃ y' ∈ (fun x => (α : E) * x) '' lattice (condQ 𝔣 Q) y₁, (n : E) * y' = (x 0 : E) * algebraMap K E θ₁ + (x 1 : E)`. Introduce `x`. Rewrite using `[hmem₁]`.

Simplify using `only [map_mul, map_ratCast, Set.mem_image, exists_exists_and_eq_and, hα]`. Use `exists_congr fun w => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`. Clear denominators, using `at h` for the nonvanishing conditions.

Take the linear combination `h`. Establish `hr0 : ∃ x : K, starRingEnd ℂ (ι x) ≠ ι x` using `⟨θ₀, fun h => by`. Rewrite `h` using `[hθ₀, Complex.conj_eq_iff_im]`. Conclude with `τ₀.im_pos.ne' h⟩`. Take `⟨π, hπ⟩` from `GlobalTheory.LatConjOne.exists_perm ι φ g hφ hφK hg hr0`.

Establish `hπ' : ∀ i x, g (φ i x) = φ (π i) x` using `fun i x => by`. Use `congrArg (fun h : E →+* ℂ => h x) (hπ i)` as an intermediate fact. Simplify using `using this`. Establish `hκπ : ∀ i, κ' (π i) = κ i` using `fun i => hκ i (π i) (hπ' i)`. Establish `hsum : ∑ i, κ' i = ∑ i, κ i` using `(Fintype.sum_equiv π _ _ fun i => (hκπ i).symm).symm`.

Set `σ : Emb (FR E) ≃ Emb (FR E)` to `e.symm.trans (π.trans e)`. Establish `hσ : ∀ (j : Emb (FR E)) (x : FR E), g ((j x : ℝ) : ℂ) = ((σ j x : ℝ) : ℂ)` using `fun j x => by`. Establish `h1` using `he (e.symm j) x`. Rewrite `h1` using `[e.apply_symm_apply]`. Rewrite using `[← h1, hπ', he]`.

Both sides reduce to the same expression. Set `v : Fin 2 → ZMod N` to `![1, 0]`. Establish `hv : v ≠ 0` using `fun h => by`. Use `congrFun h 0` as an intermediate fact. Simplify using `[v] at this`.

Establish `V0` using `value_eq hE E I φ e (algebraMap K E θ₀) τ₀ _ L₀ n s N d κ (wB N v) S Ω₀ 1 _ hf hs hN hLev he (fun i => by rw [hφι, hθ₀]) hn hmem hcard (hSt.1 _ y hc).1 hSS one_ne_zero rfl`. Establish `V1` using `value_eq hE E I φ e (algebraMap K E θ₁) τ₁ _ (HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N))) n s N d κ' (wB N (vmul v A)) _ Ω₁ c₁ _ hf hs hN (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel _ N L₀ _ hLev) he (fun i => by rw [hφι, hθ₁]) hn hmem₂ hcard (by rw [hlat]; exa …`. Take `⟨a, haz⟩` from `GlobalTheory.WpFam.exists_unit_zetaAct N g`. Establish `T` using `sum_transport g σ (2 * s) (2 * s * Module.finrank ℚ (FR E)) (fun j => κ (e.symm j)) (fun j => κ' (e.symm j)) (fun j => by simp [σ, hκπ]) (((Real.pi / τ₀.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N v τ₀) (((Real.pi / τ₁.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N ( …`. Establish `h` using `GlobalTheory.T.transport_modularFamily_GL2ZMod_weierstrass g N N (wt (2 * s) μ) a A _ (fun β => hfun (2 * s) (HilbFam.twist N L₀ ((β : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) (fun j => μ (σ.symm j)) (wB N (vmul v β))) τ₀ τ₁ _ _ hN dvd_rfl haz (GlobalTheory.T.hilb …`.

Establish `: j = σ i`. Use extensionality with `x`. Use `(hij x).symm.trans (hσ i x)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Simplify using `[this]) hv β) hω₀ h4 h6 hAw 1`.

Establish `hv1 : vmul v 1 = v` using `by simp [vmul]`. Simplify using `only [Units.val_one, one_mul, hv1, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L₀ hLev] at h`. Conclude with `h)`. Establish `hse : ∑ j, κ (e.symm j) = ∑ i, κ i` using `Equiv.sum_comp e.symm κ`. Rewrite `T` using `[hse]`.

Rewrite `V1` using `[hsum]`. Establish `hlam : (lamInf φ (2 * s) κ' α)⁻¹ = (c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E))`. Establish `: ∀ i, (φ i α) ^ (2 * s + κ' i) * (starRingEnd ℂ (φ i α))⁻¹ ^ κ' i = ((c₁ : ℂ) ^ (2 * s))⁻¹` using `fun i => by`. Rewrite using `[hα, map_inv₀, map_ratCast, map_inv₀, map_ratCast, inv_inv, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hc₁C, one_pow, mul_one, inv_pow]`. Rewrite using `[lamInf, Finset.prod_congr rfl fun i _ => this i, Finset.prod_const, Finset.card_univ, hcard, inv_pow, inv_inv, ← pow_mul]`.

Establish `hC0 : C0 E d (2 * s) κ = C0 E d (2 * s) κ'`. Rewrite using `[cmValueConst_eq, cmValueConst_eq, hsum]`. Use `congr 2`. Conclude with `Fintype.prod_equiv π _ _ fun i => by rw [hκπ]`. Simplify using `only [neg_zero, Complex.cpow_zero, mul_one, hlam] at V1`.

Establish `hmpos : (0 : ℝ) < modF t`. Rewrite using `[← hmod]`. Establish `h1 : 0 < nrm 𝔞 * τ₀.im`. Rewrite using `[← hcov]`. Establish `: (0 : ℝ) < c₁` using `by exact_mod_cast hc₁`.

Use `τ₁.im_pos` as an intermediate fact. Check the signs of the components of the expression. Conclude with `(pos_iff_pos_of_mul_pos h1).2 τ₀.im_pos`. Establish `hm0 : ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hmpos.ne')`. Establish `hr : ((2 * τ₁.im / Real.sqrt d : ℝ) : ℂ) * (c₁ : ℂ) ^ 2 = ((modF t : ℝ) : ℂ) * q`.

Establish `: (2 * τ₁.im / Real.sqrt d : ℝ) * (c₁ : ℝ) ^ 2 = modF t * q`. Rewrite using `[← hq, ← hmod]`. Take the linear combination `(2 / Real.sqrt d) * hcov`. Conclude with `this` after adjusting the coercions. Establish `hr'` using `congrArg (fun x : ℂ => x ^ (∑ i, κ i)) hr`.

Simplify using `only [mul_pow] at hr'`. Rewrite using `[V0, hq]`. Simplify using `only [map_mul, map_pow, map_neg, map_one, one_pow, Complex.ofReal_ratCast, map_ratCast, map_natCast]`. Rewrite `T` using `[mul_one Ω₀]`. Simplify using `only [mul_one]`.

Rewrite using `[T]`. Unfold `coordIn at V1 ⊢`. Rewrite using `[hC0]`. Rewrite `V1` using `[hsum]`. Apply `mul_left_cancel₀ (mul_ne_zero hm0 (pow_ne_zero (2 * s * Module.finrank ℚ (FR E)) hc₁C))` to reduce the goal to its premises.

Generalize the expression as in `(∑ μ ∈ Finset.Iic (fun j ↦ κ' (e.symm j)), (_ : ℂ)) / _ = X at V1 ⊢`. Rewrite `V1` using `[pow_add (c₁ : ℂ), pow_mul (c₁ : ℂ) 2 (∑ i, κ i)]`. Establish `hmi` using `mul_inv_cancel₀ hm0`. Take the linear combination `-V1 - ((-1) ^ (∑ i, κ i) * (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * (c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * X) * hr' - ((c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * (C0 E d (2 * s) κ' : ℂ) * S' 0 / Ω₁ ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)) * hmi`.
-/
theorem latConj : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ →
    GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatConj := by
  intro hSK hPZ _ _
  have hW2 := GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ
  have hS := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2
  have hZ := GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSK
  have hE := GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson hW2 hPZ
  intro K _ _ d δ ι hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ _ hTT E _ _ _ _ I _ φ s 𝔣 Q hD κ κ' hκ y S S' hSS hSS'
  obtain ⟨hU, hφ, hφK, hs, hb, hQ⟩ := hD
  have hf : 2 ≤ Module.finrank ℚ (FR E) := GlobalTheory.LatConjOne.two_le_finrank_of_unramFin E hU
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  obtain ⟨-, -, hg, hL0, ⟨𝔞, hinv, hL1⟩, -⟩ := id hTT
  have hmod : nrm 𝔞 = modF t := GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf t 𝔞 hinv
  have h𝔞 : 𝔞 ≠ 0 := by
    rintro rfl
    have h1 : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ) := Λ₁.ω₁_mem_lattice
    rw [hL1] at h1
    obtain ⟨x, hx, hx'⟩ := h1
    have hx0 : x = 0 := (FractionalIdeal.mem_zero_iff _).1 hx
    have := Λ₁.indep.ne_zero 0
    simp [← hx', hx0] at this
  obtain ⟨c₀, θ₀, τ₀, hc₀, hθ₀, hT₀, hO⟩ := GlobalTheory.IdealTheta.main K d δ ι 1 Λ₀ hK2 hd hδ one_ne_zero hL0
  obtain ⟨c₁, θ₁, τ₁, hc₁, hθ₁, hT₁, ha⟩ := GlobalTheory.IdealTheta.main K d δ ι 𝔞 Λ₁ hK2 hd hδ h𝔞 hL1
  have hc1 : c₀ = 1 := by
    obtain ⟨a, b, hab⟩ := (hO 1).1 (FractionalIdeal.one_mem_one _)
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 ((hO c₀).2 ⟨0, 1, by simp⟩)
    have hint : IsIntegral ℤ c₀ := by
      have h1 : IsIntegral ℤ (algebraMap ℚ K c₀) := by
        have := w.isIntegral_coe
        rw [hw] at this
        simpa using this
      exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).1 h1
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hm' : (m : ℚ) = c₀ := by simpa using hm
    have h2 := indep ι θ₀ τ₀ hθ₀ (m * a) (m * b - 1) (by
      rw [← hm'] at hab; push_cast at hab ⊢; linear_combination -hab)
    have h3 : m = 1 := Int.eq_one_of_mul_eq_one_right (by rw [← hm'] at hc₀; exact_mod_cast hc₀.le) (by linarith [h2.2])
    rw [← hm', h3]; simp
  subst hc1
  simp only [Rat.cast_one, one_mul] at hT₀ hO
  have hcov := covol ι 𝔞 θ₀ θ₁ c₁ τ₀ τ₁ hc₁ hθ₀ hθ₁ hO ha
  have hδO : δ ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have hint : IsIntegral ℤ δ := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hδ]
      exact (isIntegral_natCast d).neg
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨δ, hint⟩, rfl⟩
  obtain ⟨a₀, b₀, hab⟩ := (hO δ).1 hδO
  obtain ⟨q, hq⟩ := ratio_rat ι d hd δ θ₀ τ₀ hδ hθ₀ a₀ b₀ hab
  have hφι : ∀ i x, φ i (algebraMap K E x) = ι x := fun i x => by rw [← RingHom.comp_apply, hφK]
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeEmb.exists_equiv E I φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := by
    rw [Fintype.card_congr e, ← NumberField.Embeddings.card (FR E) ℂ]
    refine Fintype.card_congr (Equiv.ofBijective (fun f => Complex.ofRealHom.comp f) ⟨fun f f' h => ?_, fun f => ?_⟩)
    · ext x
      have := congrArg (fun u : FR E →+* ℂ => u x) h
      simpa using this
    · exact ⟨(IsTotallyReal.complexEmbedding_isReal f).embedding, by ext x; simp⟩
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  have hθF : algebraMap K E θ₀ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i⟩ := hI
    have h1 := he i x
    simp only at hx
    rw [hx, hφι, hθ₀] at h1
    have := congrArg Complex.im h1
    simp at this
    exact τ₀.im_pos.ne' this
  obtain ⟨n, N, L₀, hn, hN, h2N, hLev, hmem⟩ := GlobalTheory.RoadE.exists_level E (algebraMap K E θ₀) (condQ 𝔣 Q) y 2 hc hθF two_pos
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Fact (1 < N) := ⟨Nat.le_of_dvd hN h2N⟩
  obtain ⟨hω₀, hω₁, h4, h6, hG, hA⟩ := GlobalTheory.T.eisenstein_weierstrass_torsion_conj_transport K d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hTT 1 c₁ τ₀ τ₁ hT₀ hT₁ _ _ rfl rfl
  obtain ⟨A, hAt, hAw⟩ := hA N
  have hmem₁ := GlobalTheory.RoadE.ConjLat.twist_lattice K ι E (condQ 𝔣 Q) y t 𝔞 θ₀ (c₁ * θ₁) c₁ Λ₀ Λ₁ c₁ τ₀ τ₁ N A n L₀ hK2 hc hL0 hT₀ hθ₀ hinv hL1 hT₁
    (by simp [hθ₁]) (by simp) (by simpa using hAt) hn hLev hmem
  have hc₁E : (c₁ : E) ≠ 0 := by exact_mod_cast hc₁.ne'
  have hc₁C : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁.ne'
  let α : Eˣ := (Units.mk0 (c₁ : E) hc₁E)⁻¹
  have hα : (α : E) = (c₁ : E)⁻¹ := by simp [α]
  have hSt := (hS E I φ hf hφ).1 s hs
  set y₁ := y * (upIdele K E t)⁻¹ with hy₁
  have hlat : (fun x => (α : E) * x) '' lattice (condQ 𝔣 Q) y₁ =
      lattice (condQ 𝔣 Q) (Units.map (algebraMap E (Af E)).toMonoidHom α * y₁) := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mul_mem_lattice_princ _ _ α x).2 hx
    · intro hx
      refine ⟨(α⁻¹ : Eˣ) * x, (mul_mem_lattice_princ _ _ α _).1 ?_, ?_⟩ <;> simpa using hx
  have hH := ((hSt.1 (condQ 𝔣 Q) y₁ hc).2 κ' α S' hSS').1
  have hmem₂ : ∀ x : Fin 2 → FR E, x ∈ HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N)) ↔
      ∃ y' ∈ (fun x => (α : E) * x) '' lattice (condQ 𝔣 Q) y₁, (n : E) * y' = (x 0 : E) * algebraMap K E θ₁ + (x 1 : E) := by
    intro x
    rw [hmem₁]
    simp only [map_mul, map_ratCast, Set.mem_image, exists_exists_and_eq_and, hα]
    refine exists_congr fun w => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · field_simp
      linear_combination h
    · field_simp at h
      linear_combination h
  have hr0 : ∃ x : K, starRingEnd ℂ (ι x) ≠ ι x := ⟨θ₀, fun h => by
    rw [hθ₀, Complex.conj_eq_iff_im] at h
    exact τ₀.im_pos.ne' h⟩
  obtain ⟨π, hπ⟩ := GlobalTheory.LatConjOne.exists_perm ι φ g hφ hφK hg hr0
  have hπ' : ∀ i x, g (φ i x) = φ (π i) x := fun i x => by
    have := congrArg (fun h : E →+* ℂ => h x) (hπ i); simpa using this
  have hκπ : ∀ i, κ' (π i) = κ i := fun i => hκ i (π i) (hπ' i)
  have hsum : ∑ i, κ' i = ∑ i, κ i := (Fintype.sum_equiv π _ _ fun i => (hκπ i).symm).symm
  let σ : Emb (FR E) ≃ Emb (FR E) := e.symm.trans (π.trans e)
  have hσ : ∀ (j : Emb (FR E)) (x : FR E), g ((j x : ℝ) : ℂ) = ((σ j x : ℝ) : ℂ) := fun j x => by
    have h1 := he (e.symm j) x
    rw [e.apply_symm_apply] at h1
    rw [← h1, hπ', he]; rfl
  let v : Fin 2 → ZMod N := ![1, 0]
  have hv : v ≠ 0 := fun h => by
    have := congrFun h 0
    simp [v] at this
  have V0 := value_eq hE E I φ e (algebraMap K E θ₀) τ₀ _ L₀ n s N d κ (wB N v) S Ω₀ 1 _ hf hs hN hLev he
    (fun i => by rw [hφι, hθ₀]) hn hmem hcard (hSt.1 _ y hc).1 hSS one_ne_zero rfl
  have V1 := value_eq hE E I φ e (algebraMap K E θ₁) τ₁ _ (HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N))) n s N d κ'
    (wB N (vmul v A)) _ Ω₁ c₁ _ hf hs hN (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel _ N L₀ _ hLev) he
    (fun i => by rw [hφι, hθ₁]) hn hmem₂ hcard (by rw [hlat]; exact (hSt.1 _ _ hc).1) hH hc₁C rfl
  obtain ⟨a, haz⟩ := GlobalTheory.WpFam.exists_unit_zetaAct N g
  have T := sum_transport g σ (2 * s) (2 * s * Module.finrank ℚ (FR E)) (fun j => κ (e.symm j)) (fun j => κ' (e.symm j))
    (fun j => by simp [σ, hκπ])
    (((Real.pi / τ₀.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N v τ₀)
    (((Real.pi / τ₁.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N (vmul v A) τ₁) _ _
    (fun μ => hfun (2 * s) L₀ μ (wB N v) τ₀)
    (fun μ => hfun (2 * s) (HilbFam.twist N L₀ (A : Matrix (Fin 2) (Fin 2) (ZMod N))) μ (wB N (vmul v A)) τ₁)
    (by rw [GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity, GlobalTheory.T.weierstrass_eisenstein_nonholomorphic_identity, neg_div, neg_div, add_div, add_div, map_neg, map_add, hG, (hAw v).1])
    (fun μ => by
      have h := GlobalTheory.T.transport_modularFamily_GL2ZMod_weierstrass g N N (wt (2 * s) μ) a A _
        (fun β => hfun (2 * s) (HilbFam.twist N L₀ ((β : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))
          (fun j => μ (σ.symm j)) (wB N (vmul v β))) τ₀ τ₁ _ _ hN dvd_rfl haz
        (GlobalTheory.T.hilbert_family_weierstrass_twist hE (FR E) hf s N L₀ hs hLev v μ)
        (fun β => GlobalTheory.T.galois_conj_qExpansion_family_diag_one_unit hE (FR E) hf s N L₀ hs hLev z hz g a μ _ v haz (fun i j hij => by
          have : j = σ i := by
            ext x
            have := (hij x).symm.trans (hσ i x)
            exact_mod_cast this
          simp [this]) hv β) hω₀ h4 h6 hAw 1
      have hv1 : vmul v 1 = v := by simp [vmul]
      simp only [Units.val_one, one_mul, hv1, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L₀ hLev] at h
      exact h)
  have hse : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
  rw [hse] at T
  rw [hsum] at V1
  have hlam : (lamInf φ (2 * s) κ' α)⁻¹ = (c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) := by
    have : ∀ i, (φ i α) ^ (2 * s + κ' i) * (starRingEnd ℂ (φ i α))⁻¹ ^ κ' i = ((c₁ : ℂ) ^ (2 * s))⁻¹ := fun i => by
      rw [hα, map_inv₀, map_ratCast, map_inv₀, map_ratCast, inv_inv, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hc₁C, one_pow,
        mul_one, inv_pow]
    rw [lamInf, Finset.prod_congr rfl fun i _ => this i, Finset.prod_const, Finset.card_univ, hcard, inv_pow, inv_inv, ← pow_mul]
  have hC0 : C0 E d (2 * s) κ = C0 E d (2 * s) κ' := by
    rw [cmValueConst_eq, cmValueConst_eq, hsum]
    congr 2
    exact Fintype.prod_equiv π _ _ fun i => by rw [hκπ]
  simp only [neg_zero, Complex.cpow_zero, mul_one, hlam] at V1
  have hmpos : (0 : ℝ) < modF t := by
    rw [← hmod]
    have h1 : 0 < nrm 𝔞 * τ₀.im := by
      rw [← hcov]
      have : (0 : ℝ) < c₁ := by exact_mod_cast hc₁
      have := τ₁.im_pos
      positivity
    exact (pos_iff_pos_of_mul_pos h1).2 τ₀.im_pos
  have hm0 : ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hmpos.ne')
  have hr : ((2 * τ₁.im / Real.sqrt d : ℝ) : ℂ) * (c₁ : ℂ) ^ 2 = ((modF t : ℝ) : ℂ) * q := by
    have : (2 * τ₁.im / Real.sqrt d : ℝ) * (c₁ : ℝ) ^ 2 = modF t * q := by
      rw [← hq, ← hmod]
      linear_combination (2 / Real.sqrt d) * hcov
    exact_mod_cast this
  have hr' := congrArg (fun x : ℂ => x ^ (∑ i, κ i)) hr
  simp only [mul_pow] at hr'
  rw [V0, hq]
  simp only [map_mul, map_pow, map_neg, map_one, one_pow, Complex.ofReal_ratCast, map_ratCast, map_natCast]
  rw [mul_one Ω₀] at T
  simp only [mul_one]
  rw [T]
  unfold coordIn at V1 ⊢
  rw [hC0]
  rw [hsum] at V1
  apply mul_left_cancel₀ (mul_ne_zero hm0 (pow_ne_zero (2 * s * Module.finrank ℚ (FR E)) hc₁C))
  generalize (∑ μ ∈ Finset.Iic (fun j ↦ κ' (e.symm j)), (_ : ℂ)) / _ = X at V1 ⊢
  rw [pow_add (c₁ : ℂ), pow_mul (c₁ : ℂ) 2 (∑ i, κ i)] at V1
  have hmi := mul_inv_cancel₀ hm0
  linear_combination -V1 - ((-1) ^ (∑ i, κ i) * (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) *
    (c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * X) * hr' -
    ((c₁ : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * (C0 E d (2 * s) κ' : ℂ) * S' 0 /
      Ω₁ ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)) * hmi

end GlobalTheory.LatConjEll
