import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeTieCompareStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelComparisonLimitStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootFundamentalWeightDualityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalenceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

/- English proof (translation)
Consider the cases of `A`. Consider the cases of `B`. Consider the cases of `ha`. Consider the cases of `hh`. Both sides reduce to the same expression.
-/
theorem hermLine_ext {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {A B : HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A; cases B; cases ha; cases hh; rfl

/- English proof (translation)
Apply `hermLine_ext` to reduce the goal to its premises. Simplify using `only [Top.combLine, Function.comp]`. Conclude with `Equiv.sum_comp e (fun j => n j • (ℓ j).a)`. Use function extensionality and compare the values at `z`. Simplify using `only [Top.combLine, Function.comp]`.

Conclude with `Equiv.prod_comp e (fun j => (ℓ j).h z ^ n j)`.
-/
theorem combLine_equiv {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (e : J ≃ J) :
    Top.combLine (ℓ ∘ e) (n ∘ e) = Top.combLine ℓ n := by
  apply hermLine_ext
  · simp only [Top.combLine, Function.comp]
    exact Equiv.sum_comp e (fun j => n j • (ℓ j).a)
  · funext z
    simp only [Top.combLine, Function.comp]
    exact Equiv.prod_comp e (fun j => (ℓ j).h z ^ n j)

def relab {Ψ : Type} (π : Ψ ≃ Ψ) (N : ℕ) : Ψ × Fin N ≃ Ψ × Fin N := Equiv.prodCongr π (Equiv.refl _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem relab_apply {Ψ : Type} (π : Ψ ≃ Ψ) (N : ℕ) (a : Ψ × Fin N) : relab π N a = (π a.1, a.2) := rfl

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

/- English proof (translation)
Establish `hfi` using `GlobalTheory.T.root_fundamental_weight_duality Ψ N`. Simplify using `only [Top.combLine] at hr ⊢`. Repeatedly rewrite using `[hl, hr, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul, (hfi r _).1, ite_smul, one_smul, zero_smul]`.

Simplify using the standard rewrite rules.
-/
theorem degComb {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (sing ref line : Ψ × Fin N → HermLine ι) (hl : ∀ a, (line a).a = (ref a).a)
    (hr : ∀ a, (ref a).a = (Top.combLine sing (fundOnRoot a)).a) (r : Ψ × Fin N) :
    (Top.combLine line (rootOnFund r)).a = (sing r).a := by
  have hfi := GlobalTheory.T.root_fundamental_weight_duality Ψ N
  simp only [Top.combLine] at hr ⊢
  simp_rw [hl, hr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, (hfi r _).1, ite_smul, one_smul, zero_smul]
  simp

/- English proof (translation)
Substitute `h₁ h₂` using the available equality. Conclude with `hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ Re₁ Re₂ β b hv₁ hv₂ hy hβ hβy hA₁ hA₂ hS w`.
-/
theorem cmpSt_of_eq (hC : CmpSt) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k)
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : PB.AnSys D σ)
    (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂)
    (h₁ : mCoordIdeal (y ∘ v₁) = P₁) (h₂ : mCoordIdeal (y ∘ v₂) = P₂) (β : MRing ι) (b : K → ℕ)
    (hv₁ : IsBlockMap κ₁ v₁) (hv₂ : IsBlockMap κ₂ v₂) (hy : IsArithVar (mCoordIdeal y) (D + 1))
    (hβ : IsMultiHomog β b) (hβy : β ∉ mCoordIdeal y) (hA₁ : AlgOver Re₁) (hA₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a) (w : Fin (D + 1) → σ) :
    Tendsto (fun t =>
      (IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) : ℝ) *
          II K₁ ι₁ P₁ (D + 1) (fun j => Re₁.line (w j) t) -
        (IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) : ℝ) *
          II K₂ ι₂ P₂ (D + 1) (fun j => Re₂.line (w j) t)) (𝓝[>] 0) (𝓝 0) := by
  subst h₁ h₂
  exact hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ Re₁ Re₂ β b hv₁ hv₂ hy hβ hβy hA₁ hA₂ hS w

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

/- English proof (translation)
Introduce `hIn hC hT hU II hII E _ _ _ H D l Xo c O _ β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR w`. Take `⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩` from `GlobalTheory.T.twisted_hodge_tie_compare hT hU E H D l Xo c O β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR`. Establish `hJ` using `GlobalTheory.T.block_pullback_herm_line M.K M.ι K ι κ v hbv`. Establish `hJ'` using `GlobalTheory.T.block_pullback_herm_line M'.K M'.ι K ι κ' v' hbv'`. Establish `hmpp : IsMultiProjPrime (mCoordIdeal y)` using `harith.2.1`.

Take `⟨hc1, -, -, hc4⟩` from `GlobalTheory.T.iso_line_on_equivalence K ι (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)`. Set `f` to `relab π (D.p + D.q)`. Set `Lr : CMType H × Fin (D.p + D.q) → HermLine ι` to `fun r => (hJ.1 (T.sing r)).exists.choose`. Set `Lr' : CMType H × Fin (D.p + D.q) → HermLine ι` to `fun r => (hJ'.1 (T'.sing (f r))).exists.choose`. Establish `hLr : ∀ r, IsPullHerm κ v (T.sing r) (Lr r)` using `fun r => (hJ.1 (T.sing r)).exists.choose_spec`.

Establish `hLr' : ∀ r, IsPullHerm κ' v' (T'.sing (f r)) (Lr' r)` using `fun r => (hJ'.1 (T'.sing (f r))).exists.choose_spec`. Establish `hfi` using `GlobalTheory.T.root_fundamental_weight_duality (CMType H) (D.p + D.q)`. Establish `hfun : ∀ a, fundOnRoot (f a) ∘ f = fundOnRoot a` using `fun a => funext fun r => ((hfi a r).2 π).2`. Establish `hsame : ∀ a, SameSing T.Re (T'.Re.comap f) (mCoordIdeal y) κ v κ' v' b a a`. Introduce `a`.

Establish `e2 : Top.combLine T'.sing (fundOnRoot (f a)) = Top.combLine (T'.sing ∘ f) (fundOnRoot a)`. Rewrite using `[← hfun a, combLine_equiv]`. Use `GlobalTheory.T.realisation_fibre_product_compatible K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy (T'.Sy.comap f) T.Re (T'.Re.comap f) b a a (Top.combLine T.sing (fundOnRoot a)) (Top.combLine T'.sing (fundOnRoot (f a))) (Top.combLine Lr (fundOnRoot a)) (Top. …` and prove the remaining obligations. Rewrite using `[e2]`. Conclude with `hc4 _ _ κ' v' _ (T'.sing ∘ f) Lr' (fundOnRoot a) hbv' hLr'`.

Establish `hword` using `cmpSt_of_eq hC II hII K ι M.K M.ι M'.K M'.ι κ v κ' v' Ω y _ _ T.Sy (T'.Sy.comap f) M.P M'.P T.Re (T'.Re.comap f) hP hP' b d hbv hbv' harith hmh hb T.alg T'.alg hsame`. Establish `hδ : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * M.δ = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * M'.δ`. Rewrite using `[T.δ_eq, T'.δ_eq, mul_left_comm, hdeg, mul_left_comm]`. Establish `hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t)`. Rewrite using `[Filter.eventually_all]`.

Introduce `a`. Use `filter_upwards [Ioo_mem_nhdsGT (T.Sy.reg a).1, Ioo_mem_nhdsGT (T'.Sy.reg (f a)).1] with t ht1 ht2`. Conclude with `⟨T.Re.line_smooth a t ht1.1 ht1.2.le, T'.Re.line_smooth _ t ht2.1 ht2.2.le⟩`. Establish `hroot : ∀ r, rootOnFund (f.symm r) = rootOnFund r ∘ f` using `fun r => funext fun a => by`. Establish `h` using `((hfi (f.symm r) a).2 π).1`.

Rewrite using `[← h]`. Conclude with `congrArg (fun x => rootOnFund x (f a)) (f.apply_symm_apply r)`. Establish `hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t)) ∧ (∀ r, (M.x t (f.symm r)).a = (Top.combLine (fun a => T.Re.line a t) (rootOnFund (f.symm r))).a ∧ ∀ z ∈ mcPts M.P, (M.x t (f.symm r)).h z = (Top.combLine (fun a => T.Re.line a t) …` using `by filter_upwards [hsm, T.line_eq, T'.line_eq] with t hs1 hl1 hl2`. Use `⟨hs1, fun r => ⟨?_, fun z hz => hl1 _ z hz⟩, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[M.x_deg, ← T.sing_deg]`.

Conclude with `(degComb T.sing T.Re.ref (fun a => T.Re.line a t) (fun a => T.Re.line_deg a t) T.ref_deg _).symm`. Establish `e : Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r)) = Top.combLine (fun a => T'.Re.line a t) (rootOnFund r)`. Rewrite using `[hroot r]`. Conclude with `combLine_equiv (fun a => T'.Re.line a t) (rootOnFund r) f`. Rewrite using `[e]`.

Use `⟨?_, fun z hz => hl2 r z hz⟩` and prove the remaining obligations. Rewrite using `[M'.x_deg, ← T'.sing_deg]`. Conclude with `(degComb T'.sing T'.Re.ref (fun a => T'.Re.line a t) (fun a => T'.Re.line_deg a t) T'.ref_deg _).symm`. Establish `hmain` using `GlobalTheory.T.root_model_comparison_limit hIn II hII (CMType H) (D.p + D.q) M M' (CMType H × Fin (D.p + D.q)) (fun t a => T.Re.line a t) (fun t a => T'.Re.line (f a) t) (fun r => rootOnFund (f.symm r)) f.symm _ _ hne hδ hev hword (f ∘ w)`. Simplify using `only [Function.comp_apply, Equiv.symm_apply_apply] at hmain`.

Conclude with `hmain`.
-/
theorem cmpPair : PB.Inputs → CmpSt → HodgeComparisonCompatibility → ThetaUnifAV → CmpPair := by
  intro hIn hC hT hU II hII E _ _ _ H D l Xo c O _ β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR w
  classical
  obtain ⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩ :=
    GlobalTheory.T.twisted_hodge_tie_compare hT hU E H D l Xo c O β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR
  have hJ := GlobalTheory.T.block_pullback_herm_line M.K M.ι K ι κ v hbv
  have hJ' := GlobalTheory.T.block_pullback_herm_line M'.K M'.ι K ι κ' v' hbv'
  have hmpp : IsMultiProjPrime (mCoordIdeal y) := harith.2.1
  obtain ⟨hc1, -, -, hc4⟩ := GlobalTheory.T.iso_line_on_equivalence K ι (mCoordIdeal y)
    {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)
  let f := relab π (D.p + D.q)
  let Lr : CMType H × Fin (D.p + D.q) → HermLine ι := fun r => (hJ.1 (T.sing r)).exists.choose
  let Lr' : CMType H × Fin (D.p + D.q) → HermLine ι := fun r => (hJ'.1 (T'.sing (f r))).exists.choose
  have hLr : ∀ r, IsPullHerm κ v (T.sing r) (Lr r) := fun r => (hJ.1 (T.sing r)).exists.choose_spec
  have hLr' : ∀ r, IsPullHerm κ' v' (T'.sing (f r)) (Lr' r) := fun r => (hJ'.1 (T'.sing (f r))).exists.choose_spec
  have hfi := GlobalTheory.T.root_fundamental_weight_duality (CMType H) (D.p + D.q)
  have hfun : ∀ a, fundOnRoot (f a) ∘ f = fundOnRoot a := fun a => funext fun r => ((hfi a r).2 π).2
  have hsame : ∀ a, SameSing T.Re (T'.Re.comap f) (mCoordIdeal y) κ v κ' v' b a a := by
    intro a
    have e2 : Top.combLine T'.sing (fundOnRoot (f a)) = Top.combLine (T'.sing ∘ f) (fundOnRoot a) := by
      rw [← hfun a, combLine_equiv]
    refine GlobalTheory.T.realisation_fibre_product_compatible K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy (T'.Sy.comap f)
      T.Re (T'.Re.comap f) b a a (Top.combLine T.sing (fundOnRoot a)) (Top.combLine T'.sing (fundOnRoot (f a)))
      (Top.combLine Lr (fundOnRoot a)) (Top.combLine Lr' (fundOnRoot a)) hbv hbv'
      (hc4 _ _ κ v _ _ _ (fundOnRoot a) hbv hLr) ?_ (T.ref_deg a) (T'.ref_deg (f a)) (T.sing_eq a)
      (T'.sing_eq (f a)) hmpp (hc1 _ Lr Lr' (fundOnRoot a) fun r => hiso r _ _ (hLr r) (hLr' r))
    rw [e2]
    exact hc4 _ _ κ' v' _ (T'.sing ∘ f) Lr' (fundOnRoot a) hbv' hLr'
  have hword := cmpSt_of_eq hC II hII K ι M.K M.ι M'.K M'.ι κ v κ' v' Ω y _ _ T.Sy (T'.Sy.comap f) M.P M'.P
    T.Re (T'.Re.comap f) hP hP' b d hbv hbv' harith hmh hb T.alg T'.alg hsame
  have hδ : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * M.δ =
      IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * M'.δ := by
    rw [T.δ_eq, T'.δ_eq, mul_left_comm, hdeg, mul_left_comm]
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t) := by
    rw [Filter.eventually_all]
    intro a
    filter_upwards [Ioo_mem_nhdsGT (T.Sy.reg a).1, Ioo_mem_nhdsGT (T'.Sy.reg (f a)).1] with t ht1 ht2
    exact ⟨T.Re.line_smooth a t ht1.1 ht1.2.le, T'.Re.line_smooth _ t ht2.1 ht2.2.le⟩
  have hroot : ∀ r, rootOnFund (f.symm r) = rootOnFund r ∘ f := fun r => funext fun a => by
    have h := ((hfi (f.symm r) a).2 π).1
    rw [← h]
    exact congrArg (fun x => rootOnFund x (f a)) (f.apply_symm_apply r)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t)) ∧
      (∀ r, (M.x t (f.symm r)).a = (Top.combLine (fun a => T.Re.line a t) (rootOnFund (f.symm r))).a ∧
        ∀ z ∈ mcPts M.P, (M.x t (f.symm r)).h z = (Top.combLine (fun a => T.Re.line a t) (rootOnFund (f.symm r))).h z) ∧
      ∀ r, (M'.x t r).a = (Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r))).a ∧
        ∀ z ∈ mcPts M'.P, (M'.x t r).h z = (Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r))).h z := by
    filter_upwards [hsm, T.line_eq, T'.line_eq] with t hs1 hl1 hl2
    refine ⟨hs1, fun r => ⟨?_, fun z hz => hl1 _ z hz⟩, fun r => ?_⟩
    · rw [M.x_deg, ← T.sing_deg]
      exact (degComb T.sing T.Re.ref (fun a => T.Re.line a t) (fun a => T.Re.line_deg a t) T.ref_deg _).symm
    · have e : Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r)) =
          Top.combLine (fun a => T'.Re.line a t) (rootOnFund r) := by
        rw [hroot r]
        exact combLine_equiv (fun a => T'.Re.line a t) (rootOnFund r) f
      rw [e]
      refine ⟨?_, fun z hz => hl2 r z hz⟩
      rw [M'.x_deg, ← T'.sing_deg]
      exact (degComb T'.sing T'.Re.ref (fun a => T'.Re.line a t) (fun a => T'.Re.line_deg a t) T'.ref_deg _).symm
  have hmain := GlobalTheory.T.root_model_comparison_limit hIn II hII (CMType H) (D.p + D.q) M M' (CMType H × Fin (D.p + D.q))
    (fun t a => T.Re.line a t) (fun t a => T'.Re.line (f a) t) (fun r => rootOnFund (f.symm r)) f.symm _ _
    hne hδ hev hword (f ∘ w)
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hmain
  exact hmain

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop
