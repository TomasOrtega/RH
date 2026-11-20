import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjMemStandardLeviOfReducibleCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestDataTraceIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEqZeroOfCommuteSepAlg
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitTorusZero

open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

variable {D : D7} {V : HSp D}

/- English proof (translation)
Set `A : Finset (Finset (SV (wittIndex V)))` to `Finset.univ.filter fun P => IsPar P ∧ ∃ g : GF V, rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P`. Establish `hA : (∅ : Finset (SV (wittIndex V))) ∈ A`. Simplify using `only [A, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `⟨⟨by simp, by simp⟩, 1, ?_⟩` and prove the remaining obligations. Simplify using `[WittFrame.levi]`.

Take `⟨P, hPA, hmax⟩` from `A.exists_max_image Finset.card ⟨_, hA⟩`. Take `⟨hP, g, hg⟩` from `(Finset.mem_filter.1 hPA).2`. Use `⟨g, P, hP, hg, fun g' P' hP' h' => hmax P' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP', g' * g, ?_⟩)⟩` and prove the remaining obligations. Establish `e : g' * g * γ * (g' * g)⁻¹ = g' * (g * γ * g⁻¹) * g'⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `h'`.
-/
theorem exists_minLevi (Φ : WittFrame V) (γ : GF V) :
    ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsMinLevi Φ (g * γ * g⁻¹) P := by
  classical
  let A : Finset (Finset (SV (wittIndex V))) := Finset.univ.filter fun P =>
    IsPar P ∧ ∃ g : GF V, rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P
  have hA : (∅ : Finset (SV (wittIndex V))) ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨by simp, by simp⟩, 1, ?_⟩
    simp [WittFrame.levi]
  obtain ⟨P, hPA, hmax⟩ := A.exists_max_image Finset.card ⟨_, hA⟩
  obtain ⟨hP, g, hg⟩ := (Finset.mem_filter.1 hPA).2
  refine ⟨g, P, hP, hg, fun g' P' hP' h' => hmax P' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP', g' * g, ?_⟩)⟩
  have e : g' * g * γ * (g' * g)⁻¹ = g' * (g * γ * g⁻¹) * g'⁻¹ := by group
  rw [e]; exact h'

/- English proof (translation)
Rewrite using `[GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]`. Conclude with `⟨g, rfl⟩`.
-/
theorem rat_mem_GQ (g : GF V) : rat V g ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨g, rfl⟩

/- English proof (translation)
Establish `hg` using `rat_mem_GQ g`. Establish `e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ)`. Use extensionality with `δ`. Simplify using `only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩`. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨rat V g * k, mul_mem hg hk, by group⟩`. Introduce `𝓕 h𝓕`.

Use `h 𝓕 h𝓕` as an intermediate fact. Unfold `HasClassInt classKernel at *`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem zeroClause_of_conj (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ g : GF V)
    (h : ZeroClause μ f (rat V (g * γ * g⁻¹))) : ZeroClause μ f (rat V γ) := by
  have hg := rat_mem_GQ g
  have e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ) := by
    ext δ
    simp only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨rat V g * k, mul_mem hg hk, by group⟩
  intro 𝓕 h𝓕
  have := h 𝓕 h𝓕
  unfold HasClassInt classKernel at *
  rw [e] at this
  exact this

/- English proof (translation)
Establish `hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V` using `fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk`. Set `ι : ratClass (GQ V) γ → GQ V` to `fun δ => ⟨δ, hmem δ⟩`. Establish `hι : Function.Injective ι` using `fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)`. Apply `summable_of_hasFiniteSupport` to reduce the goal to its premises. Use `((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_` and prove the remaining obligations.

Introduce `δ hδ`. Conclude with `hδ`.
-/
theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)` as an intermediate fact. Rewrite `this` using `[hφ.lift_descend]`. Conclude with `memLp_one_iff_integrable.1 this`. Rewrite using `[GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]`.

Conclude with `congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm`.
-/
theorem fd_of_quot {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) (hi : Integrable (descend (GQ V) φ) (autMeasure V μ)) :
    IntegrableOn φ 𝓕 μ ∧ ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)
    rw [hφ.lift_descend] at this
    exact memLp_one_iff_integrable.1 this
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

/- English proof (translation)
Use `set C := max (max c c') 1`. Establish `h1 : c ≤ C` using `(le_max_left _ _).trans (le_max_left _ _)`. Establish `h2 : c' ≤ C` using `(le_max_right _ _).trans (le_max_left _ _)`. Establish `h3 : 1 ≤ C` using `le_max_right _ _`. Establish `key : ∀ b, b ≤ C → Regular b (WithLp.toLp 2 fun i : Fin k => C * ((k : ℝ) - i) : A0 k)` using `fun b hb => by`.

Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `: (i : ℝ) + 1 ≤ j` using `by exact_mod_cast hij`. Use the polynomial consequences of the given equalities and inequalities. Establish `: (i : ℝ) + 1 ≤ k` using `by exact_mod_cast i.2`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `⟨_, key c h1, key c' h2⟩`.
-/
theorem exists_regular {k : ℕ} (c c' : ℝ) : ∃ T : A0 k, Regular c T ∧ Regular c' T := by
  set C := max (max c c') 1
  have h1 : c ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : c' ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : 1 ≤ C := le_max_right _ _
  have key : ∀ b, b ≤ C → Regular b (WithLp.toLp 2 fun i : Fin k => C * ((k : ℝ) - i) : A0 k) := fun b hb => by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      nlinarith
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast i.2
      nlinarith
  exact ⟨_, key c h1, key c' h2⟩

/- English proof (translation)
Establish `: LocallyCompactSpace (cent γ)` using `(GlobalTheory.Orb.isClosed_cent γ).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Conclude with `⟨Measure.haar, inferInstance⟩`.
-/
theorem exists_haar_cent (γ : GA D V) : ∃ dt : Measure (cent γ), dt.IsHaarMeasure := by
  have : LocallyCompactSpace (cent γ) := (GlobalTheory.Orb.isClosed_cent γ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

/- English proof (translation)
Introduce `hLW hPC hTV hRS D V lam S M T U μa μf μ _ _ fa ff hTD γ hreg hirr hna`. Take `⟨Φ, L, a, hgood⟩` from `exists_isGood V`. Take `⟨g, P, hP⟩` from `exists_minLevi Φ γ`. Use `zeroClause_of_conj μ _ γ g ?_` and prove the remaining obligations. Use `set γ0 := g * γ * g⁻¹ with hγ0`.

Establish `hreg0 : IsRegSS γ0.1.1` using `by show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)`. Unfold `IsRegSS`. Rewrite using `[Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Conclude with `hreg`. Establish `hPne : P ≠ ∅`.

Take `⟨g', P', hpar', hne', hmem'⟩` from `GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly hTD.1.pos hRS Φ γ hreg hirr hna`. Establish `e : g' * g⁻¹ * γ0 * (g' * g⁻¹)⁻¹ = g' * γ * g'⁻¹` using `by rw [hγ0]; group`. Establish `hle` using `hP.2.2 (g' * g⁻¹) P' hpar' (e ▸ hmem')`. Introduce and unpack `rfl`. Use `Finset.card_pos.2 hne'` as an intermediate fact.

Rewrite `hle` using `[Finset.card_empty]`. Use linear arithmetic over natural numbers and integers. Establish `hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V` using `(IsTestFnG.isPureTensor ⟨fa, ff, hTD.2.2.2.2.2.1, hTD.2.2.2.2.2.2, rfl⟩).2`. Take `⟨c1, hc1⟩` from `((hLW.2 D V Φ L a hgood).2 μ).1 _ hf`. Take `⟨dt, hdt⟩` from `exists_haar_cent (rat V γ0)`.

Take `⟨c2, hc2⟩` from `((hLW.2 D V Φ L a hgood).2 μ).2 _ hf γ0 hreg0 P hP dt`. Take `⟨Tr, h1, h2⟩` from `exists_regular (k := wittIndex V) c1 c2`. Establish `hint` using `(hc1 Tr h1).1 _ (GlobalTheory.regSS_conjClass_isSSClass γ0 hreg0)`. Establish `heq` using `(hc2 Tr h2).2`. Establish `hz` using `GlobalTheory.T.elliptic_trace_from_model hLW hPC hTV hRS D V lam S M T U μa μf μ fa ff hTD Φ L a hgood γ0 hreg0 P hP hPne dt Tr`.

Establish `hk : kT Φ (levelAll D.sp.cm.sig V.gram L a) {δ | IsConj γ0 δ} (tensor D.sp.cm.sig V.gram fa ff) Tr = classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff)`. Use function extensionality and compare the values at `(GlobalTheory.T.test_data_trace_identity hPC hTD Φ _ γ0 Tr)`. Rewrite `hint`, `heq` using `[hk]`. Introduce `𝓕 h𝓕`. Establish `hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff))` using `fun δ hδ x => classKernel_mul _ _ hδ x`.

Take `⟨hi, hv⟩` from `fd_of_quot h𝓕 hinv hint`. Use `⟨summable_class (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2 (rat_mem_GQ γ0), hi, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, heq, hz, mul_zero]`.
-/
theorem hyperZero : GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm →
    GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → HyperZero := by
  intro hLW hPC hTV hRS D V lam S M T U μa μf μ _ _ fa ff hTD γ hreg hirr hna
  obtain ⟨Φ, L, a, hgood⟩ := exists_isGood V
  obtain ⟨g, P, hP⟩ := exists_minLevi Φ γ
  refine zeroClause_of_conj μ _ γ g ?_
  set γ0 := g * γ * g⁻¹ with hγ0
  have hreg0 : IsRegSS γ0.1.1 := by
    show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
    unfold IsRegSS
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hreg
  have hPne : P ≠ ∅ := by
    obtain ⟨g', P', hpar', hne', hmem'⟩ := GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly hTD.1.pos hRS Φ γ hreg hirr hna
    have e : g' * g⁻¹ * γ0 * (g' * g⁻¹)⁻¹ = g' * γ * g'⁻¹ := by rw [hγ0]; group
    have hle := hP.2.2 (g' * g⁻¹) P' hpar' (e ▸ hmem')
    rintro rfl
    have := Finset.card_pos.2 hne'
    rw [Finset.card_empty] at hle
    omega
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V :=
    (IsTestFnG.isPureTensor ⟨fa, ff, hTD.2.2.2.2.2.1, hTD.2.2.2.2.2.2, rfl⟩).2
  obtain ⟨c1, hc1⟩ := ((hLW.2 D V Φ L a hgood).2 μ).1 _ hf
  obtain ⟨dt, hdt⟩ := exists_haar_cent (rat V γ0)
  obtain ⟨c2, hc2⟩ := ((hLW.2 D V Φ L a hgood).2 μ).2 _ hf γ0 hreg0 P hP dt
  obtain ⟨Tr, h1, h2⟩ := exists_regular (k := wittIndex V) c1 c2
  have hint := (hc1 Tr h1).1 _ (GlobalTheory.regSS_conjClass_isSSClass γ0 hreg0)
  have heq := (hc2 Tr h2).2
  have hz := GlobalTheory.T.elliptic_trace_from_model hLW hPC hTV hRS D V lam S M T U μa μf μ fa ff hTD Φ L a hgood γ0 hreg0 P hP hPne dt Tr
  have hk : kT Φ (levelAll D.sp.cm.sig V.gram L a) {δ | IsConj γ0 δ} (tensor D.sp.cm.sig V.gram fa ff) Tr =
      classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff) :=
    funext (GlobalTheory.T.test_data_trace_identity hPC hTD Φ _ γ0 Tr)
  rw [hk] at hint heq
  intro 𝓕 h𝓕
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff)) :=
    fun δ hδ x => classKernel_mul _ _ hδ x
  obtain ⟨hi, hv⟩ := fd_of_quot h𝓕 hinv hint
  refine ⟨summable_class (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2 (rat_mem_GQ γ0), hi, ?_⟩
  rw [hv, heq, hz, mul_zero]

end GlobalTheory.SplitTorusZero
