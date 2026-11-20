import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArchNormUnique

open MeasureTheory GlobalTheory.ArchMetricCompare GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

/- English proof (translation)
Rewrite using `[latticeMean_eq Λ volume hF hf, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, smul_eq_mul, div_eq_inv_mul]`. Both sides reduce to the same expression.
-/
theorem mean_eq {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Fd : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ Fd volume) {f : (Fin g → ℂ) → ℝ}
    (hf : ∀ a ∈ Λ, ∀ x, f (x + a) = f x) :
    (∫ z in Fd, f z) / (volume Fd).toReal = latticeMean Λ f := by
  rw [latticeMean_eq Λ volume hF hf, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, smul_eq_mul,
    div_eq_inv_mul]
  rfl

/- English proof (translation)
Take `⟨-, A, _, φ, u, Hm, χ, θ, Fd, hp, hu, o, hθ, hF, -, -, -, rfl⟩` from `h`. Take `⟨-, A', _, φ', u', Hm', χ', θ', Fd', hp', hu', o', hθ', hF', -, -, -, rfl⟩` from `h'`. Take `⟨e, he, heψ⟩` from `grpPullback_iso hp hp'`. Take `⟨-, -, -, -, t1, t2, -⟩` from `AHWeil.tangent_and_weil_of_isAH hU (pullPol P hp') P.g u' Hm' χ' hu'`. Take `⟨F, hFe, hFΛ, -, -⟩` from `HomLinear.exists_linear_of_isMonHom A A' (pullPol P hp).isAb (pullPol P hp').isAb _ _ P.g P.g u u' t1 t2 e.hom he`.

Establish `hL` using `pull_isLB P.isLB φ`. Establish `hL'` using `pull_isLB P.isLB φ'`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : LBIso ((P.L.pull φ').pull e.hom.left) (P.L.pull φ) := by`. Establish `h0 : LBIso (P.L.pull φ') (P.L.pull φ')` using `⟨idIso _, idIso_isGen hL'⟩`. Establish `h1` using `(PolFibre.lbIso_pull_comp h0 e.hom.left).symm`.

Rewrite `h1` using `[heψ]`. Then use the resulting hypothesis. Establish `hHH : ∀ z w, hermForm Hm' (F z) (F w) = hermForm Hm z w` using `fun z w => by`. Simplify using `using hermForm_pull_eq_of_lbIso_pow A A' _ _ hL hL' _ _ u u' Hm χ Hm' χ' hu hu' e.hom F hFe 1 1 ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ z w`. Establish `hinj : Function.Injective F` using `(injective_iff_map_eq_zero F).2 fun z hz => by`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `hu.2.1 z hne`. Establish `h2` using `hHH z z`. Rewrite `h2` using `[hz]`. Express the relevant statement in the definitionally equal form `0 < (hermForm Hm z z).re at h1`. Rewrite `h1` using `[← h2]`.

Simplify using `[hermForm] at h1`. Set `T` to `LinearEquiv.ofInjectiveEndo F hinj`. Establish `hT : ∀ z, T z = F z` using `fun _ => rfl`. Establish `hx : ∀ z, (u'.ex (F z)).left ≫ φ' = (u.ex z).left ≫ φ` using `fun z => by`. Rewrite using `[hFe, Over.comp_left, Category.assoc, heψ]`.

Establish `hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ` using `fun z => ⟨fun hz => by`. Rewrite `hz` using `[← u'.ker, hFe, ← (u'.ker 0).2 u'.Λ.zero_mem, ← map_zero F, hFe, cancel_mono]`. Rewrite using `[← u.ker, hz, u.ker]`. Conclude with `u.Λ.zero_mem, hFΛ z⟩`. Set `U : P.L.ι → (Fin P.g → ℂ) → Prop` to `fun j z => ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U fun _ => j`.

Establish `U' : ∀ j z, U j z → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ (P.L.pull φ').U fun _ => j` using `fun j z hz => (le_pull_iff _ _ _ _).2 ((hx z).symm ▸ (le_pull_iff _ _ _ _).1 hz)`. Establish `Uc : ∀ z, ∃ j, U j z` using `fun z => by`. Take `⟨j, hj⟩` from `exists_chart_at hL (u.ex z).left`. Conclude with `⟨j PUnit.unit, hj⟩`. Set `Pm : u.Λ →+ (Fin P.g → ℂ)` to `u.Λ.subtype.toAddMonoidHom`.

Establish `hr : Set.range Pm = u.Λ` using `Subtype.range_coe`. Establish `hr' : Pm.range = u.Λ.toAddSubgroup` using `SetLike.coe_injective hr`. Establish `hfr : ∀ j z, U j z → u'.fr (fun _ => j) (F z) = u.fr (fun _ => j) z` using `GeneratorNorm.frames_eq Pm (by rw [hr']; exact u.discrete) (by rw [hr]; exact u.full) U (fun j => (u.hol _ 0).1) Uc (fun j z a hz => by`. Use `ex_add_period u z a` as an intermediate fact. Simplify using `only [U] at hz ⊢`.

Conclude with `this ▸ hz)`. Use the proof step `(fun j j' z => valAt' ((u.ex z).left ≫ φ) (P.L.U j ⊓ P.L.U j') (P.L.g j j').val)`. Use the proof step `(fun j => u.fr fun _ => j) (fun j z => u'.fr (fun _ => j) (F z))`. Use the proof step `(fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))`. Use the proof step `(fun j => u.fr_hol _)`.

Use the proof step `(fun j => (u'.fr_hol _).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn (U' j))`. Use the proof step `(fun j z => u.fr_ne _ z)`. Use the proof step `(fun j j' z h1 h2 => by`. Establish `h3` using `(top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩`. Rewrite using `[u.fr_compat _ _ z h3, val_pull_g _ _ _ _ _ h3])`.

Use the proof step `(fun j j' z h1 h2 => by`. Establish `h3` using `(top_le_preimage_inf _ _ _).2 ⟨U' j z h1, U' j' z h2⟩`. Use `show u'.fr _ (F z) = _ * u'.fr _ (F z)`. Rewrite using `[u'.fr_compat _ _ _ h3, val_pull_g _ _ _ _ _ h3, hx])`. Use the proof step `(fun j hj => by`.

Establish `h0 : ⊤ ≤ (P.L.pull (eSec P.A)).U fun _ => j`. Establish `h1` using `(le_pull_iff _ _ _ _).1 hj`. Rewrite `h1` using `[TangentOrigin.ex_zero_left]`. Use `(le_spMap_iff σ _).1 ((le_pull_iff _ _ _ _).2 ?_)` and prove the remaining obligations. Conclude with `PolBaseChange.eSec_comm hp ▸ h1`.

Use `show u'.fr _ (F 0) = _`. Rewrite using `[map_zero, o' j h0, o j h0])`. Use the proof step `(fun a j z hz => by show ‖u.fr _ z‖ = _ * ‖u.fr _ (z + a)‖`. Rewrite using `[hu.2.2.2 a _ z hz, norm_mul, norm_mul, hu.2.2.1, _root_.one_mul]`. Conclude with `congrArg (· * _) (GeneratorNorm.norm_factor Hm z a))`.

Use the proof step `(fun a j z hz => by show ‖u'.fr _ (F z)‖ = _ * ‖u'.fr _ (F (z + a))‖`. Rewrite using `[hu'.2.2.2 ⟨F a, hFΛ a a.2⟩ _ _ (U' j z hz), norm_mul, norm_mul, hu'.2.2.1, _root_.one_mul, map_add, ← hHH, ← hHH]`. Conclude with `congrArg (· * _) (GeneratorNorm.norm_factor Hm' (F z) (F a)))`. Establish `hθθ : ∀ z, θ' (F z) = θ z` using `fun z => by`. Take `⟨j, hj⟩` from `Uc z`.

Establish `h1` using `hθ' j (F z) ((le_pull_iff _ _ _ _).1 (U' j z hj))`. Rewrite `h1` using `[hx, hθ j z ((le_pull_iff _ _ _ _).1 hj), hfr j z hj]`. Conclude with `(mul_right_cancel₀ (u.fr_ne _ z hj) h1).symm`. Establish `hff : ∀ z, ‖θ' (F z)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (F z)) = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)` using `fun z => by`. Rewrite using `[hθθ, show hermSq Hm' (F z) = hermSq Hm z from congrArg Complex.re (hHH z z)]`.

Establish `hper : ∀ a ∈ u.Λ, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm (z + a)) = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z)` using `fun a ha z => by`. Take `⟨th, hth⟩` from `sec_pull_down ((isGen_iff _).1 (idIso_isGen hL)) P.isLB hL s`. Establish `hth` using `KeyPow.appLE_eq_of_stalk _ s th (hth _ (𝟙 _))`. Use `weight_periodic hL hu (s := th) (fun j z hz => ?_) ⟨a, ha⟩ z` and prove the remaining obligations. Establish `e` using `val_via _ s th hth (u.ex z).left (j PUnit.unit) j ((top_le_preimage_inf _ _ _).2 ⟨hz, hz⟩)`.

Use `Eq.trans ?_ (hθ (j PUnit.unit) z ((le_pull_iff _ _ _ _).1 hz))` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `((congrArg (· * _) (val_g_self hL _ j hz)).trans (_root_.one_mul _)).symm`. Establish `hper' : ∀ a ∈ u'.Λ, ∀ z, ‖θ' (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (z + a)) = ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' z)` using `fun a ha z => by`. Take `⟨a, rfl⟩` from `T.surjective a`.

Take `⟨z, rfl⟩` from `T.surjective z`. Rewrite using `[← map_add, hT, hT, hff, hff, hper a ((hΛ a).1 ha)]`. Use `haveI := u.discrete`. Use `haveI := u'.discrete`. Use `haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩`.

Use `haveI : IsZLattice ℝ u'.Λ := ⟨u'.full⟩`. Rewrite using `[mean_eq u.Λ hF hper, mean_eq u'.Λ hF' hper', ← latticeMean_comp_equiv u.Λ u'.Λ (T.restrictScalars ℝ).toContinuousLinearEquiv hΛ hper']`. Conclude with `congrArg _ (funext fun z => (hff z).symm)`.
-/
theorem archimedean_l2_norm_unique (hU : ThetaUnifAV) {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {s : P.L.Sec} {v v' : ℝ} (h : IsL2SquareIntegralProblem P rig σ s v)
    (h' : IsL2SquareIntegralProblem P rig σ s v') : v = v' := by
  obtain ⟨-, A, _, φ, u, Hm, χ, θ, Fd, hp, hu, o, hθ, hF, -, -, -, rfl⟩ := h
  obtain ⟨-, A', _, φ', u', Hm', χ', θ', Fd', hp', hu', o', hθ', hF', -, -, -, rfl⟩ := h'
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hp hp'
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU (pullPol P hp') P.g u' Hm' χ' hu'
  obtain ⟨F, hFe, hFΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A A' (pullPol P hp).isAb (pullPol P hp').isAb
    _ _ P.g P.g u u' t1 t2 e.hom he
  have hL := pull_isLB P.isLB φ
  have hL' := pull_isLB P.isLB φ'
  obtain ⟨t, ht⟩ : LBIso ((P.L.pull φ').pull e.hom.left) (P.L.pull φ) := by
    have h0 : LBIso (P.L.pull φ') (P.L.pull φ') := ⟨idIso _, idIso_isGen hL'⟩
    have h1 := (PolFibre.lbIso_pull_comp h0 e.hom.left).symm
    rwa [heψ] at h1
  have hHH : ∀ z w, hermForm Hm' (F z) (F w) = hermForm Hm z w := fun z w => by
    simpa using hermForm_pull_eq_of_lbIso_pow A A' _ _ hL hL' _ _ u u' Hm χ Hm' χ' hu hu' e.hom F hFe 1 1
      ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ z w
  have hinj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz => by
    by_contra hne
    have h1 := hu.2.1 z hne
    have h2 := hHH z z
    rw [hz] at h2
    change 0 < (hermForm Hm z z).re at h1
    rw [← h2] at h1
    simp [hermForm] at h1
  let T := LinearEquiv.ofInjectiveEndo F hinj
  have hT : ∀ z, T z = F z := fun _ => rfl
  have hx : ∀ z, (u'.ex (F z)).left ≫ φ' = (u.ex z).left ≫ φ := fun z => by
    rw [hFe, Over.comp_left, Category.assoc, heψ]
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => ⟨fun hz => by
    rw [← u'.ker, hFe, ← (u'.ker 0).2 u'.Λ.zero_mem, ← map_zero F, hFe, cancel_mono] at hz
    rw [← u.ker, hz, u.ker]
    exact u.Λ.zero_mem, hFΛ z⟩
  let U : P.L.ι → (Fin P.g → ℂ) → Prop := fun j z => ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U fun _ => j
  have U' : ∀ j z, U j z → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ (P.L.pull φ').U fun _ => j := fun j z hz =>
    (le_pull_iff _ _ _ _).2 ((hx z).symm ▸ (le_pull_iff _ _ _ _).1 hz)
  have Uc : ∀ z, ∃ j, U j z := fun z => by
    obtain ⟨j, hj⟩ := exists_chart_at hL (u.ex z).left
    exact ⟨j PUnit.unit, hj⟩
  let Pm : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hr : Set.range Pm = u.Λ := Subtype.range_coe
  have hr' : Pm.range = u.Λ.toAddSubgroup := SetLike.coe_injective hr
  have hfr : ∀ j z, U j z → u'.fr (fun _ => j) (F z) = u.fr (fun _ => j) z :=
    GeneratorNorm.frames_eq Pm (by rw [hr']; exact u.discrete) (by rw [hr]; exact u.full) U (fun j => (u.hol _ 0).1) Uc
      (fun j z a hz => by
        have := ex_add_period u z a
        simp only [U] at hz ⊢
        exact this ▸ hz)
      (fun j j' z => valAt' ((u.ex z).left ≫ φ) (P.L.U j ⊓ P.L.U j') (P.L.g j j').val)
      (fun j => u.fr fun _ => j) (fun j z => u'.fr (fun _ => j) (F z))
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun j => u.fr_hol _)
      (fun j => (u'.fr_hol _).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn (U' j))
      (fun j z => u.fr_ne _ z)
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩
        rw [u.fr_compat _ _ z h3, val_pull_g _ _ _ _ _ h3])
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨U' j z h1, U' j' z h2⟩
        show u'.fr _ (F z) = _ * u'.fr _ (F z)
        rw [u'.fr_compat _ _ _ h3, val_pull_g _ _ _ _ _ h3, hx])
      (fun j hj => by
        have h0 : ⊤ ≤ (P.L.pull (eSec P.A)).U fun _ => j := by
          have h1 := (le_pull_iff _ _ _ _).1 hj
          rw [TangentOrigin.ex_zero_left] at h1
          refine (le_spMap_iff σ _).1 ((le_pull_iff _ _ _ _).2 ?_)
          exact PolBaseChange.eSec_comm hp ▸ h1
        show u'.fr _ (F 0) = _
        rw [map_zero, o' j h0, o j h0])
      (fun a j z hz => by
        show ‖u.fr _ z‖ = _ * ‖u.fr _ (z + a)‖
        rw [hu.2.2.2 a _ z hz, norm_mul, norm_mul, hu.2.2.1, _root_.one_mul]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm z a))
      (fun a j z hz => by
        show ‖u'.fr _ (F z)‖ = _ * ‖u'.fr _ (F (z + a))‖
        rw [hu'.2.2.2 ⟨F a, hFΛ a a.2⟩ _ _ (U' j z hz), norm_mul, norm_mul, hu'.2.2.1, _root_.one_mul, map_add,
          ← hHH, ← hHH]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm' (F z) (F a)))
  have hθθ : ∀ z, θ' (F z) = θ z := fun z => by
    obtain ⟨j, hj⟩ := Uc z
    have h1 := hθ' j (F z) ((le_pull_iff _ _ _ _).1 (U' j z hj))
    rw [hx, hθ j z ((le_pull_iff _ _ _ _).1 hj), hfr j z hj] at h1
    exact (mul_right_cancel₀ (u.fr_ne _ z hj) h1).symm
  have hff : ∀ z, ‖θ' (F z)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (F z)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun z => by
    rw [hθθ, show hermSq Hm' (F z) = hermSq Hm z from congrArg Complex.re (hHH z z)]
  have hper : ∀ a ∈ u.Λ, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm (z + a)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun a ha z => by
    obtain ⟨th, hth⟩ := sec_pull_down ((isGen_iff _).1 (idIso_isGen hL)) P.isLB hL s
    have hth := KeyPow.appLE_eq_of_stalk _ s th (hth _ (𝟙 _))
    refine weight_periodic hL hu (s := th) (fun j z hz => ?_) ⟨a, ha⟩ z
    have e := val_via _ s th hth (u.ex z).left (j PUnit.unit) j ((top_le_preimage_inf _ _ _).2 ⟨hz, hz⟩)
    refine Eq.trans ?_ (hθ (j PUnit.unit) z ((le_pull_iff _ _ _ _).1 hz))
    rw [e]
    exact ((congrArg (· * _) (val_g_self hL _ j hz)).trans (_root_.one_mul _)).symm
  have hper' : ∀ a ∈ u'.Λ, ∀ z, ‖θ' (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (z + a)) =
      ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' z) := fun a ha z => by
    obtain ⟨a, rfl⟩ := T.surjective a
    obtain ⟨z, rfl⟩ := T.surjective z
    rw [← map_add, hT, hT, hff, hff, hper a ((hΛ a).1 ha)]
  haveI := u.discrete
  haveI := u'.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : IsZLattice ℝ u'.Λ := ⟨u'.full⟩
  rw [mean_eq u.Λ hF hper, mean_eq u'.Λ hF' hper',
    ← latticeMean_comp_equiv u.Λ u'.Λ (T.restrictScalars ℝ).toContinuousLinearEquiv hΛ hper']
  exact congrArg _ (funext fun z => (hff z).symm)

/- English proof (translation)
Introduce `hK K _ P σ v v'`. Use `⟨fun rig th _ h h' => archimedean_l2_norm_unique hK.theta ((isL2Sq_iff_isThNormAt P rig σ th v).2 h) ((isL2Sq_iff_isThNormAt P rig σ th v').2 h'), ?_⟩` and prove the remaining obligations. Introduce and unpack `t ht ⟨Q, φ, w, x, hp, hw, hx, u, Hm, χ, z, hu, hz, rfl⟩ ⟨Q', φ', w', x', hp', hw', hx', u', Hm', χ', z', hu', hz', rfl⟩`. Establish `e` using `CM.LieMetric.hermForm_eq hK.theta (P := P) (s := σ) ⟨g_eq hp, hp, LBIso.symm ⟨w, hw⟩⟩ ⟨g_eq hp', hp', LBIso.symm ⟨w', hw'⟩⟩ hu hu' (I := PUnit) (v := fun _ => t) (fun _ => ht) (w := fun _ => x) (w' := fun _ => x') (W := fun _ => z) (W' := fun _ => z') (fun _ => ⟨hx, hz⟩) (fun _ = …`. Conclude with `congrArg (fun c : ℂ => Real.log (Real.pi * c.re) / 2) e`.
-/
theorem norms_unique : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v v' : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), rig.IsGen → Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th σ v' → v = v') ∧ ∀ η' : epsR K ⟶ P.A, IsTangent η' → Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' σ v' → v = v' := by
  intro hK K _ P σ v v'
  refine ⟨fun rig th _ h h' => archimedean_l2_norm_unique hK.theta ((isL2Sq_iff_isThNormAt P rig σ th v).2 h)
    ((isL2Sq_iff_isThNormAt P rig σ th v').2 h'), ?_⟩
  rintro t ht ⟨Q, φ, w, x, hp, hw, hx, u, Hm, χ, z, hu, hz, rfl⟩ ⟨Q', φ', w', x', hp', hw', hx', u', Hm', χ', z', hu', hz', rfl⟩
  have e := CM.LieMetric.hermForm_eq hK.theta (P := P) (s := σ) ⟨g_eq hp, hp, LBIso.symm ⟨w, hw⟩⟩
    ⟨g_eq hp', hp', LBIso.symm ⟨w', hw'⟩⟩ hu hu' (I := PUnit) (v := fun _ => t) (fun _ => ht)
    (w := fun _ => x) (w' := fun _ => x') (W := fun _ => z) (W' := fun _ => z') (fun _ => ⟨hx, hz⟩) (fun _ => ⟨hx', hz'⟩)
    PUnit.unit PUnit.unit
  exact congrArg (fun c : ℂ => Real.log (Real.pi * c.re) / 2) e

end GlobalTheory.ArchNormUnique
