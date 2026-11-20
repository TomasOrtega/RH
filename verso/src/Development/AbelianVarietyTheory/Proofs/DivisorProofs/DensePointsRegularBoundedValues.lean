import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherCoordinatesSInfRootsOfUnityEqBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRootLeMaxOneSumNormCoeff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UltrametricRootLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFromSpecImageOfSInfAsIdealEqBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedFromSpecOfIsMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSupportSumLogMaxOneAdicAbv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WAddLeMax
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeRestrictAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermTopStalkClosedPointTo

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ Y N f ⟨U, ⟨x₀, hx₀⟩, hU⟩`. Take `⟨V, hVa, hxV, hVU⟩` from `Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens hx₀`. Establish `hV : IsAffineOpen V` using `hVa`. Establish `hgV : genericPoint Y.X ∈ V` using `gen_mem hxV`. Use `haveI : Nonempty V := ⟨⟨x₀, hxV⟩⟩`.

Set `ρ : F →+* Γ(Y.X, V)` to `(Y.X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp (algebraMap F Γ(Y.X, ⊤))`. Use `letI : Algebra F Γ(Y.X, V) := ρ.toAlgebra`. Use `haveI : Algebra.FiniteType F Γ(Y.X, V) := GlobalTheory.ProjVar.Var.finiteType_restrict_affineOpen F Y V hV`. Use `choose g hg using fun i => exists_fnOf_eq hgV (fun x hx => hU x (hVU hx) i)`. Take `⟨d, t, hint, hinf⟩` from `GlobalTheory.exists_noether_coordinates_sInf_rootsOfUnity_eq_bot F Γ(Y.X, V)`.

Use `choose p hpm hp0 using fun i => hint (g i)`. Set `M : Set (PrimeSpectrum Γ(Y.X, V))` to `{m | m.asIdeal.IsMaximal ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ t j ^ n - 1 ∈ m.asIdeal}`. Establish `hmemV : ∀ m : PrimeSpectrum Γ(Y.X, V), hV.fromSpec m ∈ V` using `fun m => (hV.range_fromSpec ▸ ⟨m, rfl⟩ : hV.fromSpec m ∈ (V : Set Y.X))`. Establish `hvan : ∀ m : PrimeSpectrum Γ(Y.X, V), ∀ b ∈ m.asIdeal, hV.fromSpec m ∉ Y.X.basicOpen b`. Introduce `m b hb h`.

Establish `h' : m ∈ hV.fromSpec ⁻¹ᵁ Y.X.basicOpen b` using `h`. Rewrite `h'` using `[hV.fromSpec_preimage_basicOpen]`. Conclude with `h' hb`. Establish `hpush : ∀ (K : Type) [Field K] (φ : Γ(Y.X, V) →+* K) (i : Fin N), (p i).eval₂ (MvPolynomial.eval₂Hom (φ.comp ρ) (fun j => φ (t j))) (φ (g i)) = 0`. Introduce `K _ φ i`.

Establish `e : φ.comp (MvPolynomial.aeval t).toRingHom = MvPolynomial.eval₂Hom (φ.comp ρ) (fun j => φ (t j))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[MvPolynomial.aeval_C]`. Both sides reduce to the same expression.

Introduce `j`. Simplify using the standard rewrite rules. Use `congrArg φ (hp0 i)` as an intermediate fact. Rewrite `this` using `[Polynomial.hom_eval₂, map_zero, e]`. Conclude with `this`.

Establish `hroot : ∀ (K : Type) [Field K] (φ : Γ(Y.X, V) →+* K) (m : PrimeSpectrum Γ(Y.X, V)), m ∈ M → (∀ b ∈ m.asIdeal, φ b = 0) → ∀ j, ∃ n : ℕ, n ≠ 0 ∧ φ (t j) ^ n = 1`. Introduce `K _ φ m hm hφ j`. Take `⟨n, hn, hmem⟩` from `hm.2 j`. Use `⟨n, hn.ne', ?_⟩` and prove the remaining obligations. Use `hφ _ hmem` as an intermediate fact.

Rewrite `this` using `[map_sub, map_pow, map_one, sub_eq_zero]`. Conclude with `this`. Set `Cs : Finset F` to `Finset.univ.biUnion fun i => (Finset.range (p i).natDegree).biUnion fun l => ((p i).coeff l).support.image fun s => ((p i).coeff l).coeff s`. Establish `hCs : ∀ i, ∀ l < (p i).natDegree, ∀ s ∈ ((p i).coeff l).support, ((p i).coeff l).coeff s ∈ Cs`. Introduce `i l hl s hs`.

Simplify using `only [Cs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_image]`. Conclude with `⟨i, l, hl, s, hs, rfl⟩`. Set `bb : HeightOneSpectrum (𝓞 F) → ℝ` to `fun v => ∑ c ∈ Cs, Real.log (max 1 (NumberField.HeightOneSpectrum.adicAbv F v c))`. Set `T : Fin N → ℝ` to `fun i => ∑ l ∈ Finset.range (p i).natDegree, ∑ s ∈ ((p i).coeff l).support, ∑ τ : F →+* ℂ, ‖τ (((p i).coeff l).coeff s)‖`. Establish `hT : ∀ i, 0 ≤ T i` using `fun i => by positivity`.

Set `aa : ℝ` to `1 + ∑ i, T i`. Use `⟨hV.fromSpec '' M, ?_, ?_, ?_, aa, bb, GlobalTheory.finite_support_sum_log_max_one_adicAbv F Cs, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `GlobalTheory.VarPts.isClosed_fromSpec_of_isMaximal F Y V hV m hm.1`. Use `GlobalTheory.dense_fromSpec_image_of_sInf_asIdeal_eq_bot Y.X V hV ⟨x₀, hxV⟩ M ?_` and prove the remaining obligations.

Use `hinf using 2` and compare the differences between its conclusion and the goal. Use extensionality with `I`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Conclude with `hm`.

Introduce `hI`. Conclude with `⟨⟨I, hI.1.isPrime⟩, hI, rfl⟩`. Introduce and unpack `_ ⟨m, hm, rfl⟩ i`. Conclude with `hU _ (hVU (hmemV m)) i`. Introduce and unpack `_ ⟨m, hm, rfl⟩`.

Use `⟨fun σ z hz i => ?_, fun v e y hy i => ?_⟩` and prove the remaining obligations. Establish `hzV : z ∈ GlobalTheory.CxPts.ptsIn Y.str σ V` using `GlobalTheory.CxPts.mem_ptsIn.2 (show under z ∈ V from hz ▸ hmemV m)`. Set `φ` to `GlobalTheory.CxPts.evHom hzV`. Establish `hφ : ∀ b ∈ m.asIdeal, φ b = 0`. Introduce `b hb`.

Assume the negation of the conclusion as `h0`. Rewrite `h0` using `[← GlobalTheory.CxPts.ev_eq hzV]`. Use `GlobalTheory.CxPts.mem_ptsIn.1 ((GlobalTheory.CxPts.mem_ptsIn_basicOpen hzV b).2 h0)` as an intermediate fact. Conclude with `hvan m b hb (hz ▸ this)`. Establish `hζ : ∀ j, ‖φ (t j)‖ ≤ 1`.

Introduce `j`. Take `⟨n, hn, h1⟩` from `hroot ℂ φ m hm hφ j`. Establish `h2 : ‖φ (t j)‖ ^ n = 1` using `by rw [← norm_pow, h1, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2).le`. Rewrite using `[← hg i, ratVal_fnOf hzV, GlobalTheory.CxPts.ev_eq hzV]`.

Establish `hb` using `GlobalTheory.norm_root_le_max_one_sum_norm_coeff (φ.comp ρ) (fun j => φ (t j)) hζ (p i) (hpm i) (φ (g i)) (hpush ℂ φ i)`. Use `hb.trans (max_le (by have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hT i; simp only [aa]; linarith) ?_)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun s _ => ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun τ : F →+* ℂ => ‖τ (((p i).coeff l).coeff s)‖) (fun τ _ => norm_nonneg _) (Finset.mem_univ (φ.comp ρ))`.

Use `_ ≤ ∑ i, T i := Finset.single_le_sum (fun i _ => hT i) (Finset.mem_univ i)`. Use `_ ≤ aa := by simp only [aa]; linarith`. Take `⟨φ, hφv, hφ0, hφc⟩` from `GlobalTheory.TrueGeo.AlgPtHom.exists_evalHom F Y V y (hy ▸ hmemV m)`. Establish `hφ : ∀ b ∈ m.asIdeal, φ b = 0` using `fun b hb => hφ0 b (hy ▸ hvan m b hb)`. Establish `hζ : ∀ j, e.w (φ (t j)) ≤ 1`.

Introduce `j`. Take `⟨n, hn, h1⟩` from `hroot _ φ m hm hφ j`. Establish `h2 : e.w (φ (t j)) ^ n = 1` using `by rw [← map_pow, h1, map_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (e.w.nonneg _) hn).1 h2).le`. Establish `hbb : 0 ≤ bb v` using `Finset.sum_nonneg fun c _ => Real.log_nonneg (le_max_left _ _)`.

Rewrite using `[← hg i, hφv]`. Use `GlobalTheory.ultrametric_root_le e.w (GlobalTheory.TrueGeo.Ext.w_add_le_max F v e) (φ.comp ρ) (fun j => φ (t j)) hζ (p i) (hpm i) (φ (g i)) (hpush _ φ i) (Real.exp (bb v)) (Real.one_le_exp hbb) (fun l hl s hs => ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply]`. Use `erw [hφc, e.w_alg]`. Use `set c := ((p i).coeff l).coeff s`.

Establish `hpos : 0 < max 1 (NumberField.HeightOneSpectrum.adicAbv F v c)` using `lt_of_lt_of_le one_pos (le_max_left _ _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dense_closedPoints_bounded : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : ℕ) (f : Fin N → Y.Fn),
  (∃ U : Y.X.Opens, (U : Set Y.X).Nonempty ∧ ∀ x ∈ U, ∀ i, RegAt x (f i)) →
  ∃ S : Set Y.X, (∀ x ∈ S, IsClosed ({x} : Set Y.X)) ∧ Dense S ∧ (∀ x ∈ S, ∀ i, RegAt x (f i)) ∧
    ∃ (a : ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support b).Finite ∧ ∀ x ∈ S,
      (∀ (σ : F →+* ℂ) (z : Pts Y σ), under z = x → ∀ i, ‖ratVal (f i) z‖ ≤ a) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), below y.1 = x → ∀ i,
        e.w (valAt y.1 (f i)) ≤ Real.exp (b v)) := by
  classical
  intro F _ _ Y N f ⟨U, ⟨x₀, hx₀⟩, hU⟩
  obtain ⟨V, hVa, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens hx₀
  have hV : IsAffineOpen V := hVa
  have hgV : genericPoint Y.X ∈ V := gen_mem hxV
  haveI : Nonempty V := ⟨⟨x₀, hxV⟩⟩
  let ρ : F →+* Γ(Y.X, V) :=
    (Y.X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp (algebraMap F Γ(Y.X, ⊤))
  letI : Algebra F Γ(Y.X, V) := ρ.toAlgebra
  haveI : Algebra.FiniteType F Γ(Y.X, V) := GlobalTheory.ProjVar.Var.finiteType_restrict_affineOpen F Y V hV
  choose g hg using fun i => exists_fnOf_eq hgV (fun x hx => hU x (hVU hx) i)
  obtain ⟨d, t, hint, hinf⟩ := GlobalTheory.exists_noether_coordinates_sInf_rootsOfUnity_eq_bot F Γ(Y.X, V)
  choose p hpm hp0 using fun i => hint (g i)
  let M : Set (PrimeSpectrum Γ(Y.X, V)) :=
    {m | m.asIdeal.IsMaximal ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ t j ^ n - 1 ∈ m.asIdeal}
  have hmemV : ∀ m : PrimeSpectrum Γ(Y.X, V), hV.fromSpec m ∈ V := fun m =>
    (hV.range_fromSpec ▸ ⟨m, rfl⟩ : hV.fromSpec m ∈ (V : Set Y.X))
  have hvan : ∀ m : PrimeSpectrum Γ(Y.X, V), ∀ b ∈ m.asIdeal, hV.fromSpec m ∉ Y.X.basicOpen b := by
    intro m b hb h
    have h' : m ∈ hV.fromSpec ⁻¹ᵁ Y.X.basicOpen b := h
    rw [hV.fromSpec_preimage_basicOpen] at h'
    exact h' hb
  have hpush : ∀ (K : Type) [Field K] (φ : Γ(Y.X, V) →+* K) (i : Fin N),
      (p i).eval₂ (MvPolynomial.eval₂Hom (φ.comp ρ) (fun j => φ (t j))) (φ (g i)) = 0 := by
    intro K _ φ i
    have e : φ.comp (MvPolynomial.aeval t).toRingHom =
        MvPolynomial.eval₂Hom (φ.comp ρ) (fun j => φ (t j)) := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [MvPolynomial.aeval_C]; rfl
      · intro j; simp
    have := congrArg φ (hp0 i)
    rw [Polynomial.hom_eval₂, map_zero, e] at this
    exact this
  have hroot : ∀ (K : Type) [Field K] (φ : Γ(Y.X, V) →+* K) (m : PrimeSpectrum Γ(Y.X, V)),
      m ∈ M → (∀ b ∈ m.asIdeal, φ b = 0) → ∀ j, ∃ n : ℕ, n ≠ 0 ∧ φ (t j) ^ n = 1 := by
    intro K _ φ m hm hφ j
    obtain ⟨n, hn, hmem⟩ := hm.2 j
    refine ⟨n, hn.ne', ?_⟩
    have := hφ _ hmem
    rw [map_sub, map_pow, map_one, sub_eq_zero] at this
    exact this
  let Cs : Finset F := Finset.univ.biUnion fun i => (Finset.range (p i).natDegree).biUnion fun l =>
    ((p i).coeff l).support.image fun s => ((p i).coeff l).coeff s
  have hCs : ∀ i, ∀ l < (p i).natDegree, ∀ s ∈ ((p i).coeff l).support,
      ((p i).coeff l).coeff s ∈ Cs := by
    intro i l hl s hs
    simp only [Cs, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_image]
    exact ⟨i, l, hl, s, hs, rfl⟩
  let bb : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ∑ c ∈ Cs, Real.log (max 1 (NumberField.HeightOneSpectrum.adicAbv F v c))
  let T : Fin N → ℝ := fun i => ∑ l ∈ Finset.range (p i).natDegree, ∑ s ∈ ((p i).coeff l).support,
    ∑ τ : F →+* ℂ, ‖τ (((p i).coeff l).coeff s)‖
  have hT : ∀ i, 0 ≤ T i := fun i => by positivity
  let aa : ℝ := 1 + ∑ i, T i
  refine ⟨hV.fromSpec '' M, ?_, ?_, ?_, aa, bb, GlobalTheory.finite_support_sum_log_max_one_adicAbv F Cs, ?_⟩
  · rintro _ ⟨m, hm, rfl⟩; exact GlobalTheory.VarPts.isClosed_fromSpec_of_isMaximal F Y V hV m hm.1
  · refine GlobalTheory.dense_fromSpec_image_of_sInf_asIdeal_eq_bot Y.X V hV ⟨x₀, hxV⟩ M ?_
    convert hinf using 2
    ext I; constructor
    · rintro ⟨m, hm, rfl⟩; exact hm
    · intro hI; exact ⟨⟨I, hI.1.isPrime⟩, hI, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩ i
    exact hU _ (hVU (hmemV m)) i
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨fun σ z hz i => ?_, fun v e y hy i => ?_⟩
  · have hzV : z ∈ GlobalTheory.CxPts.ptsIn Y.str σ V := GlobalTheory.CxPts.mem_ptsIn.2 (show under z ∈ V from hz ▸ hmemV m)
    let φ := GlobalTheory.CxPts.evHom hzV
    have hφ : ∀ b ∈ m.asIdeal, φ b = 0 := by
      intro b hb
      by_contra h0
      rw [← GlobalTheory.CxPts.ev_eq hzV] at h0
      have := GlobalTheory.CxPts.mem_ptsIn.1 ((GlobalTheory.CxPts.mem_ptsIn_basicOpen hzV b).2 h0)
      exact hvan m b hb (hz ▸ this)
    have hζ : ∀ j, ‖φ (t j)‖ ≤ 1 := by
      intro j
      obtain ⟨n, hn, h1⟩ := hroot ℂ φ m hm hφ j
      have h2 : ‖φ (t j)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2).le
    rw [← hg i, ratVal_fnOf hzV, GlobalTheory.CxPts.ev_eq hzV]
    have hb := GlobalTheory.norm_root_le_max_one_sum_norm_coeff (φ.comp ρ) (fun j => φ (t j)) hζ (p i) (hpm i) (φ (g i)) (hpush ℂ φ i)
    refine hb.trans (max_le (by have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hT i; simp only [aa]; linarith) ?_)
    calc _ ≤ T i := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun s _ => ?_
          exact Finset.single_le_sum (f := fun τ : F →+* ℂ => ‖τ (((p i).coeff l).coeff s)‖)
            (fun τ _ => norm_nonneg _) (Finset.mem_univ (φ.comp ρ))
      _ ≤ ∑ i, T i := Finset.single_le_sum (fun i _ => hT i) (Finset.mem_univ i)
      _ ≤ aa := by simp only [aa]; linarith
  · obtain ⟨φ, hφv, hφ0, hφc⟩ := GlobalTheory.TrueGeo.AlgPtHom.exists_evalHom F Y V y (hy ▸ hmemV m)
    have hφ : ∀ b ∈ m.asIdeal, φ b = 0 := fun b hb => hφ0 b (hy ▸ hvan m b hb)
    have hζ : ∀ j, e.w (φ (t j)) ≤ 1 := by
      intro j
      obtain ⟨n, hn, h1⟩ := hroot _ φ m hm hφ j
      have h2 : e.w (φ (t j)) ^ n = 1 := by rw [← map_pow, h1, map_one]
      exact ((pow_eq_one_iff_of_nonneg (e.w.nonneg _) hn).1 h2).le
    have hbb : 0 ≤ bb v := Finset.sum_nonneg fun c _ => Real.log_nonneg (le_max_left _ _)
    rw [← hg i, hφv]
    refine GlobalTheory.ultrametric_root_le e.w (GlobalTheory.TrueGeo.Ext.w_add_le_max F v e) (φ.comp ρ) (fun j => φ (t j)) hζ (p i) (hpm i) (φ (g i))
      (hpush _ φ i) (Real.exp (bb v)) (Real.one_le_exp hbb) (fun l hl s hs => ?_)
    rw [RingHom.comp_apply]
    erw [hφc, e.w_alg]
    set c := ((p i).coeff l).coeff s
    have hpos : 0 < max 1 (NumberField.HeightOneSpectrum.adicAbv F v c) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    calc NumberField.HeightOneSpectrum.adicAbv F v c ≤ max 1 (NumberField.HeightOneSpectrum.adicAbv F v c) :=
          le_max_right _ _
      _ = Real.exp (Real.log (max 1 (NumberField.HeightOneSpectrum.adicAbv F v c))) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (bb v) := Real.exp_le_exp.2 (Finset.single_le_sum
          (f := fun c => Real.log (max 1 (NumberField.HeightOneSpectrum.adicAbv F v c)))
          (fun c _ => Real.log_nonneg (le_max_left _ _)) (hCs i l hl s hs))

end GlobalTheory
