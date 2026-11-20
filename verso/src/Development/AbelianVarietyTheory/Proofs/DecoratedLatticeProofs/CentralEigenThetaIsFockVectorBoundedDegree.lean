import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitWeightRealCenterActionFockMonomialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.SeeSaw.CenFockPf

variable {D : D7}

/- English proof (translation)
Unfold `thPair`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.smul_apply, smul_eq_mul, star_mul']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem thPair_smul_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ) (f g : Mx D m n → ℂ) :
    thPair μ 𝓕 (a • f) (b • g) = (a * star b) * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [heisO, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisO_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f - g) = heisO ψ S T u f - heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.sub_apply]; ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun u hu => by rw [heisO_sub, hf.1 u hu, hg.1 u hu], fun e he u hu hh => by rw [heisO_sub, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩`.
-/
theorem isLatVac_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f - g) :=
  ⟨fun u hu => by rw [heisO_sub, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_sub, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

/- English proof (translation)
Unfold `comb`. Rewrite using `[Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]`. Use function extensionality and compare the values at `w`. Simplify using `[heisO, symplOH, symplO, hO]`.
-/
theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext w
  simp [heisO, symplOH, symplO, hO]

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]`. Substitute `hu` using the available equality. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem isFinComb_single_zero (S T : HSp D) : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j; simp

section Pair

variable {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))

/- English proof (translation)
Unfold `thPair`. Establish `e : ∀ w, g w * star ((∑ i ∈ s, a i • h i) w) = ∑ i ∈ s, star (a i) * (g w * star (h i w))`. Introduce `w`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Repeatedly rewrite using `[e]`. Rewrite using `[integral_finset_sum _ fun i _ => (hi i).const_mul _]`. Conclude with `Finset.sum_congr rfl fun i _ => integral_const_mul _ _`.
-/
theorem thPair_sum_right {ι : Type} (s : Finset ι) (a : ι → ℂ) (g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hi : ∀ i, Integrable (fun w => g w * star (h i w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 g (∑ i ∈ s, a i • h i) = ∑ i ∈ s, star (a i) * thPair μ 𝓕 g (h i) := by
  unfold thPair
  have e : ∀ w, g w * star ((∑ i ∈ s, a i • h i) w) = ∑ i ∈ s, star (a i) * (g w * star (h i w)) := by
    intro w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => (hi i).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/- English proof (translation)
Unfold `thPair`. Establish `e : ∀ w, (f - ∑ i ∈ s, a i • h i) w * star (g w) = f w * star (g w) - ∑ i ∈ s, a i * (h i w * star (g w))`. Introduce `w`. Simplify using `only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_mul]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Repeatedly rewrite using `[e]`. Rewrite using `[integral_sub hf (integrable_finset_sum _ fun i _ => (hi i).const_mul _), integral_finset_sum _ fun i _ => (hi i).const_mul _]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => integral_const_mul _ _`.
-/
theorem thPair_sub_sum_left {ι : Type} (s : Finset ι) (a : ι → ℂ) (f g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hf : Integrable (fun w => f w * star (g w)) (μ.restrict 𝓕))
    (hi : ∀ i, Integrable (fun w => h i w * star (g w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 (f - ∑ i ∈ s, a i • h i) g = thPair μ 𝓕 f g - ∑ i ∈ s, a i * thPair μ 𝓕 (h i) g := by
  unfold thPair
  have e : ∀ w, (f - ∑ i ∈ s, a i • h i) w * star (g w) = f w * star (g w) - ∑ i ∈ s, a i * (h i w * star (g w)) := by
    intro w
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_sub hf (integrable_finset_sum _ fun i _ => (hi i).const_mul _),
    integral_finset_sum _ fun i _ => (hi i).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end Pair

/- English proof (translation)
Establish `ip : ∀ (a b : X → ℂ) (ha : MemLp a 2 ν) (hb : MemLp b 2 ν), inner ℂ (hb.toLp b) (ha.toLp a) = ∫ w, a w * star (b w) ∂ν`. Introduce `a b ha hb`. Rewrite using `[L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with w h1 h2`.

Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules. Set `H : ι → Lp ℂ 2 ν` to `fun i => (hh i).toLp (h i)`. Set `K : Submodule ℂ (Lp ℂ 2 ν)` to `Submodule.span ℂ (Set.range H)`. Use `haveI : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range H)`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 (K.starProjection_apply_mem (hf.toLp f))`. Use `⟨c, fun j => ?_⟩` and prove the remaining obligations. Establish `h0` using `(Submodule.mem_orthogonal K _).1 (K.sub_starProjection_mem_orthogonal (hf.toLp f)) (H j) (Submodule.subset_span ⟨j, rfl⟩)`. Rewrite `h0` using `[← hc, inner_sub_right, inner_sum, sub_eq_zero]`. Rewrite using `[← ip f (h j) hf (hh j)]`.

Use `h0.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[inner_smul_right, ← ip (h i) (h j) (hh i) (hh j)]`.
-/
theorem exists_orth_coeff {X : Type} [MeasurableSpace X] (ν : Measure X) {ι : Type} [Fintype ι] (f : X → ℂ) (h : ι → X → ℂ)
    (hf : MemLp f 2 ν) (hh : ∀ i, MemLp (h i) 2 ν) :
    ∃ c : ι → ℂ, ∀ j, ∫ w, f w * star (h j w) ∂ν = ∑ i, c i * ∫ w, h i w * star (h j w) ∂ν := by
  have ip : ∀ (a b : X → ℂ) (ha : MemLp a 2 ν) (hb : MemLp b 2 ν),
      inner ℂ (hb.toLp b) (ha.toLp a) = ∫ w, a w * star (b w) ∂ν := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with w h1 h2
    rw [h1, h2]
    simp
  let H : ι → Lp ℂ 2 ν := fun i => (hh i).toLp (h i)
  let K : Submodule ℂ (Lp ℂ 2 ν) := Submodule.span ℂ (Set.range H)
  haveI : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range H)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (K.starProjection_apply_mem (hf.toLp f))
  refine ⟨c, fun j => ?_⟩
  have h0 := (Submodule.mem_orthogonal K _).1 (K.sub_starProjection_mem_orthogonal (hf.toLp f)) (H j)
    (Submodule.subset_span ⟨j, rfl⟩)
  rw [← hc, inner_sub_right, inner_sum, sub_eq_zero] at h0
  rw [← ip f (h j) hf (hh j)]
  refine h0.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [inner_smul_right, ← ip (h i) (h j) (hh i) (hh j)]

/- English proof (translation)
Establish `hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ)` using `fun φ => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ`. Use `⟨fun u hu => ?_, fun e he u hu hh => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u) (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2)) (hvac.2.lat.1 u hu) φ`. Conclude with `GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u (GlobalTheory.VacGood.infPart_latO hu) (hvac.2.lat.2 e he u hu hh) φ`.
-/
theorem isLatVac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2)) (hvac.2.lat.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu) (hvac.2.lat.2 e he u hu hh) φ

/- English proof (translation)
Establish `h` using `GlobalTheory.WeilPairing.thPair_om_eq D ψ S T χ χ' om hW v p f g hf hg`. Rewrite `h` using `[ha, hb]`. Establish `h'` using `(thPair_smul_smul v.μ v.𝓕 a b f g).symm.trans h`. Establish `hbb : star b * b = 1`. Use `Complex.conj_mul' b` as an intermediate fact.

Rewrite `this` using `[hb1]`. Simplify using `using this`. Establish `: (a - b) * thPair v.μ v.𝓕 f g = 0`. Take the linear combination `b * h' - a * thPair v.μ v.𝓕 f g * hbb`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab.symm)`.
-/
theorem thPair_eq_zero_of_eigen {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χ χ' om) (v : VolM D T.rank S.rank) (p : GA D S × GA D T) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {a b : ℂ} (ha : om p f = a • f) (hb : om p g = b • g)
    (hb1 : ‖b‖ = 1) (hab : b ≠ a) : thPair v.μ v.𝓕 f g = 0 := by
  have h := GlobalTheory.WeilPairing.thPair_om_eq D ψ S T χ χ' om hW v p f g hf hg
  rw [ha, hb] at h
  have h' := (thPair_smul_smul v.μ v.𝓕 a b f g).symm.trans h
  have hbb : star b * b = 1 := by
    have := Complex.conj_mul' b
    rw [hb1] at this
    simpa using this
  have : (a - b) * thPair v.μ v.𝓕 f g = 0 := by
    linear_combination b * h' - a * thPair v.μ v.𝓕 f g * hbb
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab.symm)

/- English proof (translation)
Introduce `D ψ θ hθ S T x y hx hy k hk χ`. Take `⟨wt, hwt, hfin⟩` from `GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial D ψ θ hθ S T x y hx hy k hk`. Take `⟨χS, χT, hW⟩` from `hk.weil`. Take `⟨v⟩` from `(GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank`. Use `set pt := pureTensorO ψ θ S T x.s y.s x.B y.B k.vac with hpt`.

Establish `hth : ∀ φ, IsThetaFunO ψ S T (pt φ)` using `fun φ => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hk.vac.1 hθ x.s x.B y.s y.B hk.vac.2.theta φ`. Establish `heig : ∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → k.om (z, 1) (pt (MvPolynomial.monomial α 1)) = wt α z • pt (MvPolynomial.monomial α 1)`. Introduce `α z hz hzc`. Use `(hwt α z hz hzc).2 _ (isFinComb_single_zero S T)` as an intermediate fact. Rewrite `this` using `[comb_single_zero]`. Then use the resulting hypothesis.

Establish `hL2 : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → MemLp g 2 (v.μ.restrict v.𝓕)` using `fun hg => GlobalTheory.Size.memLp_theta hk.vac.1 v.covol.1 v.covol.2.1 hg`. Establish `hint : ∀ {g g' : WO S T → ℂ}, IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → Integrable (fun w => g w * star (g' w)) (v.μ.restrict v.𝓕)` using `fun hg hg' => GlobalTheory.Size.integrableOn_mul_conj hk.vac.1 v.covol.1 v.covol.2.1 hg hg'`. Use `set A := (hfin χ).toFinset with hA`. Establish `hmem : ∀ α, α ∈ A ↔ ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z` using `fun α => by`. Rewrite using `[hA, Set.Finite.mem_toFinset]`.

Both sides reduce to the same expression. Set `mon : A → PolF D T.rank S.rank` to `fun α => MvPolynomial.monomial α.1 1`. Use `⟨Submodule.span ℂ (Set.range mon), FiniteDimensional.span_of_finite ℂ (Set.finite_range mon), ?_⟩` and prove the remaining obligations. Introduce `f hf hlat hχ`. Take `⟨c, hc⟩` from `exists_orth_coeff (v.μ.restrict v.𝓕) f (fun α : A => pt (mon α)) (hL2 hf) (fun α => hL2 (hth _))`.

Use `⟨∑ α, c α • mon α, (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hg` using `GlobalTheory.OrientedHeis.theta_sub hf (hth (∑ α, c α • mon α))`. Establish `hgl` using `isLatVac_sub ψ S T hlat (isLatVac_pureTensorO hk.vac (∑ α, c α • mon α))`. Establish `hsum : pt (∑ α, c α • mon α) = ∑ α, c α • pt (mon α)` using `by simp only [map_sum, map_smul]`. Establish `hmono : ∀ β, thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt (MvPolynomial.monomial β 1)) = 0`.

Introduce `β`. Rewrite using `[hsum]`. Use `(thPair_sub_sum_left v.μ v.𝓕 Finset.univ c f _ (fun α => pt (mon α)) (hint hf (hth _)) (fun α => hint (hth _) (hth _))).trans ?_` and prove the remaining obligations. Distinguish the cases in `hβ : β ∈ A`. Conclude with `sub_eq_zero.2 (hc ⟨β, hβ⟩)`.

Rewrite `hβ` using `[hmem] at hβ push_neg`. Take `⟨z, hz, hzc, hne⟩` from `hβ`. Rewrite using `[thPair_eq_zero_of_eigen hW v (z, 1) hf (hth _) (hχ z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1 hne, zero_sub, neg_eq_zero]`. Use `Finset.sum_eq_zero fun α _ => ?_` and prove the remaining obligations. Rewrite using `[thPair_eq_zero_of_eigen hW v (z, 1) (hth _) (hth _) (heig α.1 z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1 (by rw [(hmem α.1).1 α.2 z hz hzc]; exact hne), mul_zero]`.

Use `sub_eq_zero.1 (GlobalTheory.FockTotal.eq_zero_of_orth_fock D ψ θ hθ S T x y hx hy k.vac hk.vac v _ hg hgl fun Q => ?_)` and prove the remaining obligations. Establish `hQ : pt Q = ∑ β ∈ Q.support, MvPolynomial.coeff β Q • pt (MvPolynomial.monomial β 1)` using `by conv_lhs => rw [Q.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`.

Use `show thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt Q) = 0`. Rewrite using `[hQ]`. Use `(thPair_sum_right v.μ v.𝓕 Q.support (fun β => MvPolynomial.coeff β Q) _ (fun β => pt (MvPolynomial.monomial β 1)) (fun β => hint hg (hth _))).trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_eq_zero fun β _ => by rw [hmono, mul_zero]`.
-/
theorem cenFock : ∀ D : D7, CenFock D := by
  intro D ψ θ hθ S T x y hx hy k hk χ
  classical
  obtain ⟨wt, hwt, hfin⟩ := GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial D ψ θ hθ S T x y hx hy k hk
  obtain ⟨χS, χT, hW⟩ := hk.weil
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  set pt := pureTensorO ψ θ S T x.s y.s x.B y.B k.vac with hpt
  have hth : ∀ φ, IsThetaFunO ψ S T (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hk.vac.1 hθ x.s x.B y.s y.B hk.vac.2.theta φ
  have heig : ∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) →
      k.om (z, 1) (pt (MvPolynomial.monomial α 1)) = wt α z • pt (MvPolynomial.monomial α 1) := by
    intro α z hz hzc
    have := (hwt α z hz hzc).2 _ (isFinComb_single_zero S T)
    rwa [comb_single_zero] at this
  have hL2 : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → MemLp g 2 (v.μ.restrict v.𝓕) := fun hg =>
    GlobalTheory.Size.memLp_theta hk.vac.1 v.covol.1 v.covol.2.1 hg
  have hint : ∀ {g g' : WO S T → ℂ}, IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Integrable (fun w => g w * star (g' w)) (v.μ.restrict v.𝓕) := fun hg hg' =>
    GlobalTheory.Size.integrableOn_mul_conj hk.vac.1 v.covol.1 v.covol.2.1 hg hg'
  set A := (hfin χ).toFinset with hA
  have hmem : ∀ α, α ∈ A ↔ ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z := fun α => by
    rw [hA, Set.Finite.mem_toFinset]; rfl
  let mon : A → PolF D T.rank S.rank := fun α => MvPolynomial.monomial α.1 1
  refine ⟨Submodule.span ℂ (Set.range mon), FiniteDimensional.span_of_finite ℂ (Set.finite_range mon), ?_⟩
  intro f hf hlat hχ
  obtain ⟨c, hc⟩ := exists_orth_coeff (v.μ.restrict v.𝓕) f (fun α : A => pt (mon α)) (hL2 hf) (fun α => hL2 (hth _))
  refine ⟨∑ α, c α • mon α, (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, rfl⟩, ?_⟩
  have hg := GlobalTheory.OrientedHeis.theta_sub hf (hth (∑ α, c α • mon α))
  have hgl := isLatVac_sub ψ S T hlat (isLatVac_pureTensorO hk.vac (∑ α, c α • mon α))
  have hsum : pt (∑ α, c α • mon α) = ∑ α, c α • pt (mon α) := by simp only [map_sum, map_smul]
  have hmono : ∀ β, thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt (MvPolynomial.monomial β 1)) = 0 := by
    intro β
    rw [hsum]
    refine (thPair_sub_sum_left v.μ v.𝓕 Finset.univ c f _ (fun α => pt (mon α)) (hint hf (hth _))
      (fun α => hint (hth _) (hth _))).trans ?_
    by_cases hβ : β ∈ A
    · exact sub_eq_zero.2 (hc ⟨β, hβ⟩)
    · rw [hmem] at hβ
      push_neg at hβ
      obtain ⟨z, hz, hzc, hne⟩ := hβ
      rw [thPair_eq_zero_of_eigen hW v (z, 1) hf (hth _) (hχ z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1 hne, zero_sub,
        neg_eq_zero]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [thPair_eq_zero_of_eigen hW v (z, 1) (hth _) (hth _) (heig α.1 z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1
        (by rw [(hmem α.1).1 α.2 z hz hzc]; exact hne), mul_zero]
  refine sub_eq_zero.1 (GlobalTheory.FockTotal.eq_zero_of_orth_fock D ψ θ hθ S T x y hx hy k.vac hk.vac v _ hg hgl fun Q => ?_)
  have hQ : pt Q = ∑ β ∈ Q.support, MvPolynomial.coeff β Q • pt (MvPolynomial.monomial β 1) := by
    conv_lhs => rw [Q.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  show thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt Q) = 0
  rw [hQ]
  refine (thPair_sum_right v.μ v.𝓕 Q.support (fun β => MvPolynomial.coeff β Q) _
    (fun β => pt (MvPolynomial.monomial β 1)) (fun β => hint hg (hth _))).trans ?_
  exact Finset.sum_eq_zero fun β _ => by rw [hmono, mul_zero]

end GlobalTheory.SeeSaw.CenFockPf
