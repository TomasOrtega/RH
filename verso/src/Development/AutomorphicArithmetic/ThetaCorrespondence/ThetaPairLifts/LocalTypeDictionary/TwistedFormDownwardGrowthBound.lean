import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUniformFiniteBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUniformFiniteBoundStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownGrowth
open GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.DownApprox
open scoped ENNReal
set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi`. Take `⟨Ae, d, H⟩` from `GlobalTheory.KernelSeminorm.thetaGrowth D (neg (G.P (i + 1)).V).rank (G.P i).V.rank`. Use `⟨Ae, fun K Fm v hF Φ hΦ ε hε => ?_⟩` and prove the remaining obligations. Establish `hθ : IsInfFam R.θ` using `hRB.inf`. Establish `hW` using `(hG.arrows.dn i hi).weil`.

Establish `hω : IsWeilDatumO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ((G.dn i).ω.toSgn true)` using `hW`. Choose the witnesses or unpack the hypotheses as in `⟨hν, hfd⟩ : (G.mP (i + 1)).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by`. Establish `h` using `hG.meas.P (i + 1) hi`. Distinguish the cases in `hd : i + 1 = D.R.m`. Conclude with `⟨(h.1 hd).1.1, (h.1 hd).2⟩`.

Conclude with `⟨(h.2 hd).1.1, (h.2 hd).2⟩`. Establish `hFv : ∀ k ∈ K, GlobalTheory.Grow.RapidDec (G.P (i + 1)).V (Fm k (v k))` using `fun k hk => by`. Establish `h` using `GlobalTheory.LowVanishObj.multT_apply_cusp R.θ (G.P (i + 1)).M ∅ 1 (Fm k) (hF k hk) (v k)`. Conclude with `(GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ h.1 h.2).rapidDec`. Establish `hB : ∀ k ∈ K, ∃ B : ℝ, ∀ g, ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ B` using `fun k hk => (hFv k hk).decay Ae`.

Use `choose! B hB using hB`. Take `⟨μ, 𝓓, hμ⟩` from `GlobalTheory.Size.exists_isCovolOne (neg (G.P (i + 1)).V) (G.P i).V`. Take `⟨U, hU, hΦU, happ⟩` from `GlobalTheory.FockDensity.fockDense D _ _ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) R.θ R.ψ hω.std hθ μ 𝓓 hμ Φ hΦ`. Use `haveI : BorelSpace (GA D (G.P (i + 1)).V) := ⟨rfl⟩`. Use `haveI hfin : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) := isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν hfd)`.

Establish `hker : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) → ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ g h, ‖thetaKO (G.dn i).ω g h f‖ ≤ Kc * (GlobalTheory.Size.sobO …`. Introduce `U' hU'`. Take `⟨C, hC0, hC⟩` from `(H (neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU'`. Use `⟨C * 2 ^ Ae, by positivity, fun f hf g h => ?_⟩` and prove the remaining obligations. Establish `hb` using `(hC _ _ ((G.dn i).ω.toSgn true) hω μ 𝓓 hμ f hf).2`.

Establish `hinv : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, thetaKO (G.dn i).ω (γ * g) h f = thetaKO (G.dn i).ω g h f` using `fun γ hγ g => by`. Establish `e1 : (((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) : GA D (neg (G.P (i + 1)).V) × GA D (G.P i).V) = ((ofSgn true (G.P (i + 1)).V).symm γ, 1) * ((ofSgn true (G.P (i + 1)).V).symm g, h)` using `by simp`. Use `show ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) f 0 = ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm g, h) f 0`. Rewrite using `[e1, map_mul, Module.End.mul_apply]`. Conclude with `hω.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω.om_pres _ _ hf.1)`.

Establish `hgr : ∀ g, ‖thetaKO (G.dn i).ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ Ae` using `fun g => by`. Use `hb ((ofSgn true (G.P (i + 1)).V).symm g) h` as an intermediate fact. Use `this.trans_eq ?_` and prove the remaining obligations. Use `show C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * (GlobalTheory.Grow.height (G.P (i + 1)).V g * GlobalTheory.Grow.height (G.P i).V h) ^ Ae = _`. Expand and normalize the polynomial expressions, which then agree.

Use `(GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO (G.dn i).ω g h f) hinv hgr g).trans_eq ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hbound : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) → ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ k ∈ K, ∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h f * …`. Introduce `U' hU'`. Take `⟨Kc, hK0, hK⟩` from `hker U' hU'`.

Use `⟨Kc, hK0, fun f hf k hk h => ?_⟩` and prove the remaining obligations. Establish `hs : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal` using `ENNReal.toReal_nonneg`. Establish `hcont : Continuous fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g` using `((hω.om_cont f hf.1 0).comp ((continuous_ofSgn_symm true _).prodMk continuous_const)).mul (hFv k hk).continuous`. Establish `h5 : 0 ≤ GlobalTheory.Grow.height (G.P i).V h ^ Ae` using `pow_nonneg (GlobalTheory.Grow.height_pos _ h).le Ae`. Establish `hpt : ∀ g, ‖thetaKO (G.dn i).ω g h f * Fm k (v k) g‖ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * GlobalTheory.Grow.height (G.P i).V h ^ Ae`.

Introduce `g`. Rewrite using `[norm_mul]`. Establish `h1` using `hK f hf g h`. Establish `h3 : ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ max (B k) 0` using `(hB k hk g).trans (le_max_left _ _)`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨Integrable.of_bound hcont.aestronglyMeasurable _ (.of_forall hpt), ?_⟩` and prove the remaining obligations. Use `(norm_integral_le_of_norm_le_const (.of_forall hpt)).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Measure.real, Measure.restrict_apply_univ]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨Kc, hK0, hMb⟩` from `hbound U hU`.

Establish `hvol : 0 ≤ ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal` using `ENNReal.toReal_nonneg`. Establish `hBs : 0 ≤ ∑ k ∈ K, max (B k) 0` using `Finset.sum_nonneg fun k _ => le_max_right _ _`. Establish `hM0 : 0 ≤ Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0` using `by positivity`. Take `⟨r, -, hr0', hrε⟩` from `ENNReal.lt_iff_exists_real_btwn.1 hε`. Establish `hrpos : 0 < r` using `ENNReal.ofReal_pos.1 hr0'`.

Use `set M := Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 with hMdef`. Establish `hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (r / (M + 1))` using `ENNReal.ofReal_pos.2 (by positivity)`. Take `⟨g₀, hgS, hgU, hlt⟩` from `happ d _ hδ`. Take `⟨n, f, p, hf, rfl⟩` from `exists_sum_of_mem_fockSpan hgS`. Set `f' : ℕ → (WO (G.P (i + 1)).V (G.P i).V → ℂ)` to `fun j => if hj : j < n then f ⟨j, hj⟩ else 0`.

Set `p' : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)` to `fun j => if hj : j < n then p ⟨j, hj⟩ else 0`. Use `⟨Finset.range n, f', p', fun j hj => ?_, ?_⟩` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.1 hj`. Simplify using `only [f', dif_pos hj']`. Conclude with `(isVacF_negFr _ _ _).1 (hf _)`.

Establish `hpt : ∀ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l) = fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)` using `fun l => ptF_negFr _ _ (f l) (p l)`. Establish `hint : ∀ l, ∀ k ∈ K, ∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν`. Introduce `l k hk h`. Establish `ht : IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))` using `GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ (hf l).1 (p l)`. Take `⟨U', hU', hl'⟩` from `GlobalTheory.Size.isTheta_iff_level.1 ht`.

Take `⟨_, _, hb⟩` from `hbound U' hU'`. Rewrite using `[← hpt l]`. Conclude with `(hb _ hl' k hk h).1`. Establish `hΨU` using `sub_mem hΦU hgU`. Establish `e : ∀ k ∈ K, ∀ h, (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * Fm k (v k) g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g ∂(G.mP (i + 1)).ν = ∫ g in (G.mP (i + 1)).fd, theta …`.

Introduce `k hk h`. Rewrite using `[← integral_finset_sum _ fun l _ => hint l k hk h, ← integral_sub (hMb Φ hΦU k hk h).1 (integrable_finset_sum _ fun l _ => hint l k hk h)]`. Use `integral_congr_ae (.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul, hpt]`. Establish `hsw : ∀ h, ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν = ∑ k ∈ K, ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G …`.

Introduce `h`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun j => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν) n]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Simplify using `only [f', p', dif_pos l.isLt, Fin.eta]`. Use `set s := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))).toReal with hsdef`. Establish `hs0 : 0 ≤ s` using `ENNReal.toReal_nonneg`. Establish `hs` using `ENNReal.toReal_lt_of_lt_ofReal hlt`. Establish `hle : GlobalTheory.Size.growthSize (G.P i).V Ae (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * (Fm k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f …`.

Use `(GlobalTheory.Size.growthSize_le_iff (mul_nonneg hM0 hs0)).2 fun h => ?_` and prove the remaining obligations. Rewrite using `[hsw h, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k hk => e k hk h]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hMdef, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_le_sum fun k hk => ((hMb _ hΨU k hk h).2).trans_eq ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `hle.trans_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hrε)` and prove the remaining obligations. Establish `hM1 : 0 < M + 1` using `by linarith`. Establish `h1 : (M + 1) * s < r`. Use `mul_lt_mul_of_pos_left hs hM1` as an intermediate fact.

Rewrite `this` using `[mul_div_cancel₀ _ hM1.ne']`. Then use the resulting hypothesis. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem downward_growth_approximation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi
  classical
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg (G.P (i + 1)).V).rank (G.P i).V.rank
  refine ⟨Ae, fun K Fm v hF Φ hΦ ε hε => ?_⟩
  have hθ : IsInfFam R.θ := hRB.inf
  have hW := (hG.arrows.dn i hi).weil
  have hω : IsWeilDatumO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i))
      ((G.dn i).ω.toSgn true) := hW
  obtain ⟨hν, hfd⟩ : (G.mP (i + 1)).ν.IsHaarMeasure ∧
      IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    have h := hG.meas.P (i + 1) hi
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have hFv : ∀ k ∈ K, GlobalTheory.Grow.RapidDec (G.P (i + 1)).V (Fm k (v k)) := fun k hk => by
    have h := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ (G.P (i + 1)).M ∅ 1 (Fm k) (hF k hk) (v k)
    exact (GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ h.1 h.2).rapidDec
  have hB : ∀ k ∈ K, ∃ B : ℝ, ∀ g, ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ B :=
    fun k hk => (hFv k hk).decay Ae
  choose! B hB using hB
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, happ⟩ := GlobalTheory.FockDensity.fockDense D _ _ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) R.θ R.ψ
    hω.std hθ μ 𝓓 hμ Φ hΦ
  haveI : BorelSpace (GA D (G.P (i + 1)).V) := ⟨rfl⟩
  haveI hfin : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν hfd)
  have hker : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ g h,
        ‖thetaKO (G.dn i).ω g h f‖ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
          GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨C, hC0, hC⟩ := (H (neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU'
    refine ⟨C * 2 ^ Ae, by positivity, fun f hf g h => ?_⟩
    have hb := (hC _ _ ((G.dn i).ω.toSgn true) hω μ 𝓓 hμ f hf).2
    have hinv : ∀ γ ∈ GQ (G.P (i + 1)).V, ∀ g, thetaKO (G.dn i).ω (γ * g) h f = thetaKO (G.dn i).ω g h f := fun γ hγ g => by
      have e1 : (((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) : GA D (neg (G.P (i + 1)).V) × GA D (G.P i).V) =
          ((ofSgn true (G.P (i + 1)).V).symm γ, 1) * ((ofSgn true (G.P (i + 1)).V).symm g, h) := by simp
      show ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm (γ * g), h) f 0 =
        ((G.dn i).ω.toSgn true) ((ofSgn true (G.P (i + 1)).V).symm g, h) f 0
      rw [e1, map_mul, Module.End.mul_apply]
      exact hω.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω.om_pres _ _ hf.1)
    have hgr : ∀ g, ‖thetaKO (G.dn i).ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        GlobalTheory.Grow.height (G.P i).V h ^ Ae) * GlobalTheory.Grow.height (G.P (i + 1)).V g ^ Ae := fun g => by
      have := hb ((ofSgn true (G.P (i + 1)).V).symm g) h
      refine this.trans_eq ?_
      show C * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal *
        (GlobalTheory.Grow.height (G.P (i + 1)).V g * GlobalTheory.Grow.height (G.P i).V h) ^ Ae = _
      ring
    refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO (G.dn i).ω g h f) hinv hgr g).trans_eq ?_
    ring
  have hbound : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ k ∈ K, ∀ h,
        IntegrableOn (fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν ∧
        ‖∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h f * Fm k (v k) g ∂(G.mP (i + 1)).ν‖ ≤
          Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal *
            GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
    intro U' hU'
    obtain ⟨Kc, hK0, hK⟩ := hker U' hU'
    refine ⟨Kc, hK0, fun f hf k hk h => ?_⟩
    have hs : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
    have hcont : Continuous fun g => thetaKO (G.dn i).ω g h f * Fm k (v k) g :=
      ((hω.om_cont f hf.1 0).comp ((continuous_ofSgn_symm true _).prodMk continuous_const)).mul (hFv k hk).continuous
    have h5 : 0 ≤ GlobalTheory.Grow.height (G.P i).V h ^ Ae := pow_nonneg (GlobalTheory.Grow.height_pos _ h).le Ae
    have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h f * Fm k (v k) g‖ ≤
        Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max (B k) 0 * GlobalTheory.Grow.height (G.P i).V h ^ Ae := by
      intro g
      rw [norm_mul]
      have h1 := hK f hf g h
      have h3 : ‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ max (B k) 0 :=
        (hB k hk g).trans (le_max_left _ _)
      calc ‖thetaKO (G.dn i).ω g h f‖ * ‖Fm k (v k) g‖
          ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae *
              GlobalTheory.Grow.height (G.P i).V h ^ Ae * ‖Fm k (v k) g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae *
              (‖Fm k (v k) g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae) := by ring
        _ ≤ Kc * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae * max (B k) 0 := by
          gcongr
        _ = _ := by ring
    refine ⟨Integrable.of_bound hcont.aestronglyMeasurable _ (.of_forall hpt), ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall hpt)).trans (le_of_eq ?_)
    simp only [Measure.real, Measure.restrict_apply_univ]
    ring
  obtain ⟨Kc, hK0, hMb⟩ := hbound U hU
  have hvol : 0 ≤ ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal := ENNReal.toReal_nonneg
  have hBs : 0 ≤ ∑ k ∈ K, max (B k) 0 := Finset.sum_nonneg fun k _ => le_max_right _ _
  have hM0 : 0 ≤ Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 := by positivity
  obtain ⟨r, -, hr0', hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr0'
  set M := Kc * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal * ∑ k ∈ K, max (B k) 0 with hMdef
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (r / (M + 1)) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨g₀, hgS, hgU, hlt⟩ := happ d _ hδ
  obtain ⟨n, f, p, hf, rfl⟩ := exists_sum_of_mem_fockSpan hgS
  let f' : ℕ → (WO (G.P (i + 1)).V (G.P i).V → ℂ) := fun j => if hj : j < n then f ⟨j, hj⟩ else 0
  let p' : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) := fun j => if hj : j < n then p ⟨j, hj⟩ else 0
  refine ⟨Finset.range n, f', p', fun j hj => ?_, ?_⟩
  · have hj' := Finset.mem_range.1 hj
    simp only [f', dif_pos hj']
    exact (isVacF_negFr _ _ _).1 (hf _)
  have hpt : ∀ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l) =
      fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l) := fun l => ptF_negFr _ _ (f l) (p l)
  have hint : ∀ l, ∀ k ∈ K, ∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h
      (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    intro l k hk h
    have ht : IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V
        (ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) :=
      GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ (hf l).1 (p l)
    obtain ⟨U', hU', hl'⟩ := GlobalTheory.Size.isTheta_iff_level.1 ht
    obtain ⟨_, _, hb⟩ := hbound U' hU'
    rw [← hpt l]
    exact (hb _ hl' k hk h).1
  have hΨU := sub_mem hΦU hgU
  have e : ∀ k ∈ K, ∀ h, (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * Fm k (v k) g ∂(G.mP (i + 1)).ν) -
      ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
        Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) * Fm k (v k) g
          ∂(G.mP (i + 1)).ν := by
    intro k hk h
    rw [← integral_finset_sum _ fun l _ => hint l k hk h,
      ← integral_sub (hMb Φ hΦU k hk h).1 (integrable_finset_sum _ fun l _ => hint l k hk h)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul, hpt]
  have hsw : ∀ h, ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν =
      ∑ k ∈ K, ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * Fm k (v k) g ∂(G.mP (i + 1)).ν := by
    intro h
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * Fm k (v k) g ∂(G.mP (i + 1)).ν) n]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [f', p', dif_pos l.isLt, Fin.eta]
  set s := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d
    (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hs := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hle : GlobalTheory.Size.growthSize (G.P i).V Ae (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ *
      (Fm k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ Finset.range n, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f' j) (p' j)) * (Fm k (v k)) g ∂(G.mP (i + 1)).ν) ≤
      ENNReal.ofReal (M * s) := by
    refine (GlobalTheory.Size.growthSize_le_iff (mul_nonneg hM0 hs0)).2 fun h => ?_
    rw [hsw h, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun k hk => e k hk h]
    refine (norm_sum_le _ _).trans ?_
    rw [hMdef, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ((hMb _ hΨU k hk h).2).trans_eq ?_
    ring
  refine hle.trans_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hrε)
  have hM1 : 0 < M + 1 := by linarith
  have h1 : (M + 1) * s < r := by
    have := mul_lt_mul_of_pos_left hs hM1
    rwa [mul_div_cancel₀ _ hM1.ne'] at this
  nlinarith
end GlobalTheory.DownGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.DownGrowth.downward_growth_approximation | exact _root_.GlobalTheory.DownGrowth.downward_growth_approximation | (intros; apply _root_.GlobalTheory.DownGrowth.downward_growth_approximation <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.twisted_form_downward_growth_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @_root_.GlobalTheory.DownGrowth.downward_growth_approximation | exact _root_.GlobalTheory.DownGrowth.downward_growth_approximation | (intros; apply _root_.GlobalTheory.DownGrowth.downward_growth_approximation <;> assumption)
end
