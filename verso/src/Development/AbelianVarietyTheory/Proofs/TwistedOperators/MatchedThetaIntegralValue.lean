import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedIntegralFiniteSupportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisingTranslateCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConst

/- English proof (translation)
Introduce `γ hγ u`. Establish `hm` using `W.om_is (.mu t i j) ⟨i.2.le, j.2⟩`. Establish `hc` using `W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩`. Unfold `kerSmall`. Use `Finsupp.sum_congr fun d hd => ?_` and prove the remaining obligations.

Take `⟨h2, h1⟩` from `GlobalTheory.SmallRoute.theta_of_matched hΘ hd`. Use `congr 1`. Use `congr 1`. Use `show thetaKO (W.om (.mu t i j)) (γ * u) g d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2`. Unfold `thetaKO`.

Establish `e : ((γ * u, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (γ, 1) * (u, g)` using `by simp`. Rewrite using `[e, map_mul]`. Conclude with `hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)`. Use `show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2`. Unfold `thetaKO`.

Establish `e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) = (1, γ) * (negGA _ g₁, u)` using `by simp`. Rewrite using `[e, map_mul]`. Conclude with `hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)`.
-/
theorem kerSmall_rat_mid {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, kerSmall W Θ' g g₁ (γ * u) = kerSmall W Θ' g g₁ u := by
  intro γ hγ u
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨h2, h1⟩ := GlobalTheory.SmallRoute.theta_of_matched hΘ hd
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (γ * u) g d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul]
    exact hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V ν hH`. Establish `hmp : MeasurePreserving (fun x : GA D V => x * k⁻¹) ν ν` using `measurePreserving_mul_right ν k⁻¹`. Establish `ht : IsFundamentalDomain (GQ V) ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν` using `hfd.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id (fun g x => by simp [Subgroup.smul_def, mul_assoc])`. Establish `hinv : ∀ (g : GQ V) (x : GA D V), F (g • x) = F x` using `fun g x => hF g g.2 x`. Establish `hmp2 : MeasurePreserving (fun x : GA D V => x * k) ν ν` using `measurePreserving_mul_right ν k`.

Establish `hpre : (fun x : GA D V => x * k) ⁻¹' ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) = fd`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hemb : MeasurableEmbedding (fun x : GA D V => x * k)` using `(MeasurableEquiv.mulRight k).measurableEmbedding`. Establish `h1 : IntegrableOn F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν` using `(hfd.integrableOn_iff ht hinv).1 hint`.

Establish `e1 : ∫ u in fd, F (u * k) ∂ν = ∫ u in (fun x : GA D V => x * k⁻¹) ⁻¹' fd, F u ∂ν`. Use `hmp2.setIntegral_preimage_emb hemb F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd)` as an intermediate fact. Rewrite `this` using `[hpre]`. Conclude with `this`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hpre]`. Conclude with `(hmp2.integrableOn_comp_preimage hemb).2 h1`. Rewrite using `[e1]`. Conclude with `(hfd.setIntegral_eq ht hinv).symm`.
-/
theorem setIntegral_mul_right {D : D7} (V : HSp D) (ν : Measure (GA D V)) [hH : ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (k : GA D V) :
    IntegrableOn (fun u => F (u * k)) fd ν ∧ ∫ u in fd, F (u * k) ∂ν = ∫ u in fd, F u ∂ν := by
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V ν hH
  have hmp : MeasurePreserving (fun x : GA D V => x * k⁻¹) ν ν := measurePreserving_mul_right ν k⁻¹
  have ht : IsFundamentalDomain (GQ V) ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν :=
    hfd.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  have hinv : ∀ (g : GQ V) (x : GA D V), F (g • x) = F x := fun g x => hF g g.2 x
  have hmp2 : MeasurePreserving (fun x : GA D V => x * k) ν ν := measurePreserving_mul_right ν k
  have hpre : (fun x : GA D V => x * k) ⁻¹' ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) = fd := by
    ext x; simp
  have hemb : MeasurableEmbedding (fun x : GA D V => x * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have h1 : IntegrableOn F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν := (hfd.integrableOn_iff ht hinv).1 hint
  have e1 : ∫ u in fd, F (u * k) ∂ν = ∫ u in (fun x : GA D V => x * k⁻¹) ⁻¹' fd, F u ∂ν := by
    have := hmp2.setIntegral_preimage_emb hemb F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd)
    rw [hpre] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    exact (hmp2.integrableOn_comp_preimage hemb).2 h1
  · rw [e1]; exact (hfd.setIntegral_eq ht hinv).symm

/- English proof (translation)
Introduce `γ hγ u`. Unfold `translates`. Use `Finsupp.sum_congr fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, hF γ hγ]`.
-/
theorem translates_left_inv {D : D7} {V : HSp D} (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (w : GA D V →₀ ℂ) : ∀ γ ∈ GQ V, ∀ u, translates w F (γ * u) = translates w F u := by
  intro γ hγ u
  unfold translates
  refine Finsupp.sum_congr fun k _ => ?_
  rw [mul_assoc, hF γ hγ]

/- English proof (translation)
Establish `h` using `fun k => setIntegral_mul_right V ν fd hfd F hF hint k`. Establish `e : translates w F = fun u => ∑ k ∈ w.support, w k * F (u * k)`. Use function extensionality and compare the values at `u`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `⟨integrable_finset_sum _ fun k _ => (h k).1.const_mul _, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ fun k _ => (h k).1.const_mul _]`. Simplify using `only [integral_const_mul, (h _).2]`. Rewrite using `[zdeg, Finsupp.sum, Finset.sum_mul]`.
-/
theorem integral_translates {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (w : GA D V →₀ ℂ) :
    IntegrableOn (translates w F) fd ν ∧ ∫ u in fd, translates w F u ∂ν = zdeg w * ∫ u in fd, F u ∂ν := by
  have h := fun k => setIntegral_mul_right V ν fd hfd F hF hint k
  have e : translates w F = fun u => ∑ k ∈ w.support, w k * F (u * k) := by
    funext u; rfl
  rw [e]
  refine ⟨integrable_finset_sum _ fun k _ => (h k).1.const_mul _, ?_⟩
  rw [integral_finset_sum _ fun k _ => (h k).1.const_mul _]
  simp only [integral_const_mul, (h _).2]
  rw [zdeg, Finsupp.sum, Finset.sum_mul]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `only [translates, Finsupp.sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, mul_assoc, hab x hx y hy]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem translates_comm {H : Type} [Monoid H] (F : H → ℂ) (a b : H →₀ ℂ)
    (hab : ∀ x ∈ a.support, ∀ y ∈ b.support, x * y = y * x) :
    translates a (translates b F) = translates b (translates a F) := by
  funext u
  simp only [translates, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  rw [mul_assoc, mul_assoc, hab x hx y hy]; ring

/- English proof (translation)
Rewrite using `[← (integral_translates V ν fd hfd _ (translates_left_inv F hF b) hb a).2, ← (integral_translates V ν fd hfd _ (translates_left_inv F hF a) ha b).2, translates_comm F a b hab]`.
-/
theorem zdeg_mul_integral_comm {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (a b : GA D V →₀ ℂ) (hab : ∀ x ∈ a.support, ∀ y ∈ b.support, x * y = y * x)
    (ha : IntegrableOn (translates a F) fd ν) (hb : IntegrableOn (translates b F) fd ν) :
    zdeg a * ∫ u in fd, translates b F u ∂ν = zdeg b * ∫ u in fd, translates a F u ∂ν := by
  rw [← (integral_translates V ν fd hfd _ (translates_left_inv F hF b) hb a).2,
    ← (integral_translates V ν fd hfd _ (translates_left_inv F hF a) ha b).2, translates_comm F a b hab]

/- English proof (translation)
Introduce `h1 h2 h3 h4 h5`. Take `⟨C1, H1⟩` from `GlobalTheory.T.matched_integral_finite_support h1 h2 h3 h4 h5`. Take `⟨C2, H2⟩` from `GlobalTheory.T.matched_integral_euler_product h1 h2 h3 h4 h5`. Use `⟨max C1 C2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨x1, K1⟩` from `H1 ε CF (le_trans (le_max_left _ _) hCF)`.

Take `⟨x2, K2⟩` from `H2 ε CF (le_trans (le_max_right _ _) hCF)`. Use `⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩` and prove the remaining obligations. Establish `k1` using `K1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS`. Establish `k2` using `K2 D large₂ he (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS`. Introduce `G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁`.

Use `set f := kerSmall W Θ' g g₁ with hf`. Establish `hfd` using `(hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund`. Use `haveI := hfd.1`. Establish `hinv : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, f (γ * u) = f u` using `kerSmall_rat_mid W B ρ t i j Θ Θ' hΘ g g₁`. Establish `key` using `zdeg_mul_integral_comm (G.V (.grid i j)) (M.ν _) (M.fd _) hfd.2 f hinv`.

Take `⟨v₀, -, w₀, hw₀, hi₀, hs₀⟩` from `k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ ∅`. Use `⟨(∫ u in M.fd _, translates w₀ f u ∂M.ν _) / zdeg w₀, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨z', P, hz'f, hz'd, hz'P⟩` from `k1 G W hW B ρ hρ t i j Θ Θ' hΘ g g₁ z`. Take `⟨v, hv, w, hw, hi, hs⟩` from `k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ (insert v₀ P)`. Establish `hvP : v ∉ P` using `fun h => hv (Finset.mem_insert_of_mem h)`.

Establish `hv0 : v ≠ v₀` using `fun h => hv (h ▸ Finset.mem_insert_self _ _)`. Establish `c1 : ∀ x ∈ w.support, ∀ y ∈ z'.support, x * y = y * x`. Introduce `x hx y hy`. Take `⟨x', rfl⟩` from `hs x hx`. Conclude with `GlobalTheory.AdelicU.commute_emb _ _ x' (hz'P y hy v hvP)`.

Establish `c2 : ∀ x ∈ w.support, ∀ y ∈ w₀.support, x * y = y * x`. Introduce `x hx y hy`. Take `⟨x', rfl⟩` from `hs x hx`. Take `⟨y', rfl⟩` from `hs₀ y hy`. Conclude with `GlobalTheory.AdelicU.commute_emb _ _ x' (GlobalTheory.AdelicU.proj_emb_ne _ _ hv0 y')`.

Establish `hz'i : IntegrableOn (translates z' f) (M.fd _) (M.ν _)` using `by rw [hz'f]; exact hz`. Establish `e1` using `key w z' c1 hi hz'i`. Establish `e2` using `key w w₀ c2 hi hi₀`. Rewrite `e1` using `[hz'f, hz'd]`. Rewrite using `[mul_div_assoc', eq_div_iff hw₀]`.

Apply `mul_left_cancel₀ hw` to reduce the goal to its premises. Take the linear combination `zdeg w₀ * e1 - zdeg z * e2`.
-/
theorem regIntegral_const : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ J : ℂ, ∀ z, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) →
    ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ = zdeg z * J := by
  intro h1 h2 h3 h4 h5
  obtain ⟨C1, H1⟩ := GlobalTheory.T.matched_integral_finite_support h1 h2 h3 h4 h5
  obtain ⟨C2, H2⟩ := GlobalTheory.T.matched_integral_euler_product h1 h2 h3 h4 h5
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, K1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, K2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have k1 := K1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS
  have k2 := K2 D large₂ he (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS
  intro G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁
  set f := kerSmall W Θ' g g₁ with hf
  have hfd := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI := hfd.1
  have hinv : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, f (γ * u) = f u := kerSmall_rat_mid W B ρ t i j Θ Θ' hΘ g g₁
  have key := zdeg_mul_integral_comm (G.V (.grid i j)) (M.ν _) (M.fd _) hfd.2 f hinv
  obtain ⟨v₀, -, w₀, hw₀, hi₀, hs₀⟩ := k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ ∅
  refine ⟨(∫ u in M.fd _, translates w₀ f u ∂M.ν _) / zdeg w₀, fun z hz => ?_⟩
  obtain ⟨z', P, hz'f, hz'd, hz'P⟩ := k1 G W hW B ρ hρ t i j Θ Θ' hΘ g g₁ z
  classical
  obtain ⟨v, hv, w, hw, hi, hs⟩ := k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ (insert v₀ P)
  have hvP : v ∉ P := fun h => hv (Finset.mem_insert_of_mem h)
  have hv0 : v ≠ v₀ := fun h => hv (h ▸ Finset.mem_insert_self _ _)
  have c1 : ∀ x ∈ w.support, ∀ y ∈ z'.support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (hz'P y hy v hvP)
  have c2 : ∀ x ∈ w.support, ∀ y ∈ w₀.support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    obtain ⟨y', rfl⟩ := hs₀ y hy
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (GlobalTheory.AdelicU.proj_emb_ne _ _ hv0 y')
  have hz'i : IntegrableOn (translates z' f) (M.fd _) (M.ν _) := by rw [hz'f]; exact hz
  have e1 := key w z' c1 hi hz'i
  have e2 := key w w₀ c2 hi hi₀
  rw [hz'f, hz'd] at e1
  rw [mul_div_assoc', eq_div_iff hw₀]
  apply mul_left_cancel₀ hw
  linear_combination zdeg w₀ * e1 - zdeg z * e2

end GlobalTheory.SmallConst

end
