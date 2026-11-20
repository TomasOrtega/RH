import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMapRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSupLatticeComponentEq
import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SmallScal

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l c n La hU`. Use `haveI : IsTotallyComplex c.F := GlobalTheory.CompHS.isTotallyComplex_coeff c`. Take `⟨𝔞, h0, h1, h2⟩` from `GlobalTheory.BetaEx.exists_index_ideal La.Ln La.La inf_le_left (GlobalTheory.BetaEx.bdd_of_unimod La hU) (fun m hm => by`. Take `⟨a, ha, h⟩` from `GlobalTheory.BetaEx.exists_smul_std m`. Conclude with `⟨a, ha, La.La.smul_mem a hm, h⟩)`.

Use `set idx : ℕ := (La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index with hidx`. Establish `h2' : Ideal.absNorm 𝔞 = idx` using `h2`. Establish `hidx0 : idx ≠ 0`. Rewrite using `[← h2']`. Conclude with `fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)`.

Establish `e : ∀ τ, idealAt c La.Ln τ = Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c La.La τ`. Introduce `τ`. Unfold `idealAt`. Rewrite using `[← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.Ln), ← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.La)]`. Use `GlobalTheory.BetaEx.span_image_smul (embF c τ) 𝔞 (GlobalTheory.BetaEx.detSpan La.La)` as an intermediate fact.

Rewrite `this` using `[← h1]`. Conclude with `this`. Set `φ : (E →+* ℂ) → (𝓞 E →+* 𝓞 c.F)` to `fun τ => RingOfIntegers.mapRingHom (embF c τ)`. Set `B : FractionalIdeal (𝓞 c.F)⁰ c.F` to `∏ τ : E →+* ℂ, ((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) ^ Dw.mult τ`. Establish `hS : ∀ τ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ≤ (((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F)`.

Introduce `τ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `(FractionalIdeal.mem_coeIdeal _).2 ⟨φ τ a, Ideal.mem_map_of_mem _ ha, rfl⟩`. Establish `hSB : ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ≤ (B : Submodule (𝓞 c.F) c.F)`.

Establish `: (B : Submodule (𝓞 c.F) c.F) = FractionalIdeal.coeSubmoduleHom (𝓞 c.F)⁰ c.F B` using `rfl`. Rewrite using `[this, map_prod]`. Use `Finset.prod_le_prod' fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_le_pow_left' (hS τ) _`.

Take `⟨k, hk⟩ : ∃ k, k = InfinitePlace.nrComplexPlaces c.F` from `⟨_, rfl⟩`. Establish `hnF : Module.finrank ℚ c.F = 2 * k` using `hk ▸ IsTotallyComplex.finrank c.F`. Establish `hnE : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E` using `IsTotallyComplex.finrank E`. Establish `hk0 : k ≠ 0` using `by have := Module.finrank_pos (R := ℚ) (M := c.F); omega`. Establish `hdvd : Module.finrank ℚ E ∣ Module.finrank ℚ c.F` using `(GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ (Classical.arbitrary _)) 𝔞).1`.

Establish `hexp : Module.finrank ℚ c.F / Module.finrank ℚ E * ∑ τ : E →+* ℂ, Dw.mult τ = (Dw.p + Dw.q) * k`. Rewrite using `[GlobalTheory.RefSum.sum_mult]`. Take `⟨t, ht⟩` from `hdvd`. Establish `hE0 : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Rewrite using `[ht, Nat.mul_div_cancel_left _ hE0, hnE, Nat.mul_div_cancel_left _ (by norm_num)]`.

Rewrite `hnF` using `[ht, hnE]`. Establish `: InfinitePlace.nrComplexPlaces E * t = k` using `by linarith`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hNB : FractionalIdeal.absNorm B = ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k`.

Simplify using `only [B, map_prod, map_pow, FractionalIdeal.coeIdeal_absNorm]`. Simplify using `only [fun τ => (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ τ) 𝔞).2, h2']`. Rewrite using `[← pow_mul, ← hexp, pow_mul, Finset.prod_pow_eq_pow_sum]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hX0 : (0 : ℝ) < (idx : ℝ) ^ (Dw.p + Dw.q)` using `pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hidx0) _`. Establish `hB0 : B ≠ 0`. Introduce `hB`. Use `hNB` as an intermediate fact. Rewrite `this` using `[hB, map_zero]`.

Establish `h' : ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hidx0))`. Conclude with `h' this.symm`. Use `set X : ℝ := (idx : ℝ) ^ (Dw.p + Dw.q) with hXdef`. Use `set R : ℝ := Real.exp (fieldSz c.F) ^ 2 with hR`. Establish `hR0 : 0 < R` using `by positivity`.

Establish `hg : 0 < R / X` using `div_pos hR0 hX0`. Establish `hcard : Fintype.card (InfinitePlace c.F) = k`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hk]`. Establish `hd1 : (1 : ℝ) ≤ |(discr c.F : ℝ)|`. Use `Int.one_le_abs (discr_ne_zero c.F)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `hdR : |(discr c.F : ℝ)| ≤ R ^ k`. Rewrite using `[hR, ← pow_mul, ← Real.exp_nat_mul, ← Real.exp_log (lt_of_lt_of_le one_pos hd1)]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `hn : (0 : ℝ) < Module.finrank ℚ c.F` using `by exact_mod_cast Module.finrank_pos`.

Establish `hfs` using `GlobalTheory.CovTop.log_rd_le_fieldSz c.F`. Establish `hlog` using `Real.log_natCast_nonneg (Module.finrank ℚ c.F)`. Establish `: Real.log |(discr c.F : ℝ)| ≤ (Module.finrank ℚ c.F : ℝ) * fieldSz c.F`. Rewrite `hfs` using `[div_le_iff₀ hn]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `this` using `[hnF]`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : Real.sqrt |(discr c.F : ℝ)| ≤ |(discr c.F : ℝ)|` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hsq0 : 0 < Real.sqrt |(discr c.F : ℝ)|` using `Real.sqrt_pos.2 (by linarith)`.

Take `⟨b, hb, hb0, hbw⟩` from `Formalism.ExtensionFiltration.mk_lt c.F (Units.mk0 B⁻¹ (inv_ne_zero hB0)) (fun _ => Real.sqrt (R / X)) (fun _ => Real.sqrt_pos.2 hg) (by`. Rewrite using `[Units.val_mk0, map_inv₀, hNB, Finset.prod_const, Finset.card_univ, hcard, Real.sq_sqrt hg.le, ← hk, div_pow]`. Use `push_cast`. Rewrite using `[← hXdef]`. Establish `hXk : 0 < X ^ k` using `pow_pos hX0 k`.

Rewrite using `[inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hXk, mul_div_assoc', div_mul_cancel₀ _ hXk.ne']`. Combine the equalities or inequalities in the displayed calculation. Use `⟨b, hb0, ?_, fun σ => ?_⟩` and prove the remaining obligations. Establish `hsb : Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F) ≤ 1`. Establish `h1' : Submodule.span (𝓞 c.F) {b} ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F)` using `Submodule.span_le.2 (Set.singleton_subset_iff.2 hb)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [e, mul_pow, Finset.prod_mul_distrib]`. Rewrite using `[← mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `hbw (InfinitePlace.mk σ)`.

Rewrite `h1` using `[InfinitePlace.apply]`. Establish `h3 : ‖σ b‖ ^ 2 < R / X` using `(Real.lt_sqrt (norm_nonneg _)).1 h1`. Rewrite `h3` using `[lt_div_iff₀ hX0]`. Conclude with `h3.le`.
-/
theorem exists_small_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : Coeff l) (n : ℕ) (La : GenLat E n), La.Unimod → ∃ s : c.F, s ≠ 0 ∧ Submodule.span (𝓞 c.F) {s} * ∏ τ : E →+* ℂ, idealAt c La.Ln τ ^ Dw.mult τ ≤ ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ ∧ ∀ σ : c.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ (Dw.p + Dw.q) ≤ Real.exp (fieldSz c.F) ^ 2 := by
  intro E _ _ _ H Dw l c n La hU
  haveI : IsTotallyComplex c.F := GlobalTheory.CompHS.isTotallyComplex_coeff c
  obtain ⟨𝔞, h0, h1, h2⟩ := GlobalTheory.BetaEx.exists_index_ideal La.Ln La.La inf_le_left
    (GlobalTheory.BetaEx.bdd_of_unimod La hU) (fun m hm => by
      obtain ⟨a, ha, h⟩ := GlobalTheory.BetaEx.exists_smul_std m
      exact ⟨a, ha, La.La.smul_mem a hm, h⟩)
  set idx : ℕ := (La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index with hidx
  have h2' : Ideal.absNorm 𝔞 = idx := h2
  have hidx0 : idx ≠ 0 := by
    rw [← h2']; exact fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)

  have e : ∀ τ, idealAt c La.Ln τ =
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c La.La τ := by
    intro τ
    unfold idealAt
    rw [← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.Ln),
      ← GlobalTheory.BetaEx.span_image_span (embF c τ) (detSet La.La)]
    have := GlobalTheory.BetaEx.span_image_smul (embF c τ) 𝔞 (GlobalTheory.BetaEx.detSpan La.La)
    rw [← h1] at this
    exact this
  let φ : (E →+* ℂ) → (𝓞 E →+* 𝓞 c.F) := fun τ => RingOfIntegers.mapRingHom (embF c τ)
  let B : FractionalIdeal (𝓞 c.F)⁰ c.F :=
    ∏ τ : E →+* ℂ, ((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) ^ Dw.mult τ

  have hS : ∀ τ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ≤
      (((𝔞.map (φ τ) : Ideal (𝓞 c.F)) : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) := by
    intro τ
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨φ τ a, Ideal.mem_map_of_mem _ ha, rfl⟩
  have hSB : ∏ τ : E →+* ℂ, Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ ≤
      (B : Submodule (𝓞 c.F) c.F) := by
    have : (B : Submodule (𝓞 c.F) c.F) = FractionalIdeal.coeSubmoduleHom (𝓞 c.F)⁰ c.F B := rfl
    rw [this, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_pow]
    exact pow_le_pow_left' (hS τ) _

  obtain ⟨k, hk⟩ : ∃ k, k = InfinitePlace.nrComplexPlaces c.F := ⟨_, rfl⟩
  have hnF : Module.finrank ℚ c.F = 2 * k := hk ▸ IsTotallyComplex.finrank c.F
  have hnE : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have hk0 : k ≠ 0 := by have := Module.finrank_pos (R := ℚ) (M := c.F); omega
  have hdvd : Module.finrank ℚ E ∣ Module.finrank ℚ c.F :=
    (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ (Classical.arbitrary _)) 𝔞).1
  have hexp : Module.finrank ℚ c.F / Module.finrank ℚ E * ∑ τ : E →+* ℂ, Dw.mult τ = (Dw.p + Dw.q) * k := by
    rw [GlobalTheory.RefSum.sum_mult]
    obtain ⟨t, ht⟩ := hdvd
    have hE0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    rw [ht, Nat.mul_div_cancel_left _ hE0, hnE, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [ht, hnE] at hnF
    have : InfinitePlace.nrComplexPlaces E * t = k := by linarith
    rw [← this]; ring
  have hNB : FractionalIdeal.absNorm B = ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k := by
    simp only [B, map_prod, map_pow, FractionalIdeal.coeIdeal_absNorm]
    simp only [fun τ => (GlobalTheory.absNorm_map_ringOfIntegers_hom E c.F (φ τ) 𝔞).2, h2']
    rw [← pow_mul, ← hexp, pow_mul, Finset.prod_pow_eq_pow_sum]
    push_cast
    ring
  have hX0 : (0 : ℝ) < (idx : ℝ) ^ (Dw.p + Dw.q) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hidx0) _
  have hB0 : B ≠ 0 := by
    intro hB
    have := hNB
    rw [hB, map_zero] at this
    have h' : ((idx : ℚ) ^ (Dw.p + Dw.q)) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hidx0))
    exact h' this.symm

  set X : ℝ := (idx : ℝ) ^ (Dw.p + Dw.q) with hXdef
  set R : ℝ := Real.exp (fieldSz c.F) ^ 2 with hR
  have hR0 : 0 < R := by positivity
  have hg : 0 < R / X := div_pos hR0 hX0
  have hcard : Fintype.card (InfinitePlace c.F) = k := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hk]
  have hd1 : (1 : ℝ) ≤ |(discr c.F : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero c.F)
    exact_mod_cast this
  have hdR : |(discr c.F : ℝ)| ≤ R ^ k := by
    rw [hR, ← pow_mul, ← Real.exp_nat_mul, ← Real.exp_log (lt_of_lt_of_le one_pos hd1)]
    apply Real.exp_le_exp.2
    have hn : (0 : ℝ) < Module.finrank ℚ c.F := by exact_mod_cast Module.finrank_pos
    have hfs := GlobalTheory.CovTop.log_rd_le_fieldSz c.F
    have hlog := Real.log_natCast_nonneg (Module.finrank ℚ c.F)
    have : Real.log |(discr c.F : ℝ)| ≤ (Module.finrank ℚ c.F : ℝ) * fieldSz c.F := by
      rw [div_le_iff₀ hn] at hfs; linarith
    rw [hnF] at this
    push_cast at this ⊢
    linarith
  have hsq : Real.sqrt |(discr c.F : ℝ)| ≤ |(discr c.F : ℝ)| :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hsq0 : 0 < Real.sqrt |(discr c.F : ℝ)| := Real.sqrt_pos.2 (by linarith)
  obtain ⟨b, hb, hb0, hbw⟩ := Formalism.ExtensionFiltration.mk_lt c.F (Units.mk0 B⁻¹ (inv_ne_zero hB0))
    (fun _ => Real.sqrt (R / X)) (fun _ => Real.sqrt_pos.2 hg) (by
      rw [Units.val_mk0, map_inv₀, hNB, Finset.prod_const, Finset.card_univ, hcard, Real.sq_sqrt hg.le, ← hk,
        div_pow]
      push_cast
      rw [← hXdef]
      have hXk : 0 < X ^ k := pow_pos hX0 k
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hXk, mul_div_assoc', div_mul_cancel₀ _ hXk.ne']
      calc (2 : ℝ) ^ k * Real.sqrt |(discr c.F : ℝ)| < Real.pi ^ k * Real.sqrt |(discr c.F : ℝ)| :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) hk0) hsq0
        _ ≤ Real.pi ^ k * R ^ k := by gcongr; exact hsq.trans hdR)
  refine ⟨b, hb0, ?_, fun σ => ?_⟩
  ·
    have hsb : Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F) ≤ 1 := by
      have h1' : Submodule.span (𝓞 c.F) {b} ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) :=
        Submodule.span_le.2 (Set.singleton_subset_iff.2 hb)
      calc Submodule.span (𝓞 c.F) {b} * (B : Submodule (𝓞 c.F) c.F)
          ≤ ((B⁻¹ : FractionalIdeal (𝓞 c.F)⁰ c.F) : Submodule (𝓞 c.F) c.F) * (B : Submodule (𝓞 c.F) c.F) :=
            mul_le_mul' h1' le_rfl
        _ = 1 := by rw [← FractionalIdeal.coe_mul, inv_mul_cancel₀ hB0, FractionalIdeal.coe_one]
    simp only [e, mul_pow, Finset.prod_mul_distrib]
    rw [← mul_assoc]
    calc Submodule.span (𝓞 c.F) {b} * (∏ τ : E →+* ℂ,
            Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) ^ Dw.mult τ) *
            ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ
        ≤ 1 * ∏ τ : E →+* ℂ, idealAt c La.La τ ^ Dw.mult τ :=
          mul_le_mul' ((mul_le_mul' le_rfl hSB).trans hsb) le_rfl
      _ = _ := one_mul _
  ·
    have h1 := hbw (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h1
    have h3 : ‖σ b‖ ^ 2 < R / X := (Real.lt_sqrt (norm_nonneg _)).1 h1
    rw [lt_div_iff₀ hX0] at h3
    exact h3.le

end GlobalTheory.SmallScal
