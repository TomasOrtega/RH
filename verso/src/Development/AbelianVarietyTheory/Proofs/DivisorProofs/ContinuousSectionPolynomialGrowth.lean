import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.SectionGrowth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {B : LB Y}

/- English proof (translation)
Take `⟨j, hy₀j⟩ : ∃ j, y₀ ∈ ptsIn p σ (B.U j)` from `⟨_, mem_pick hB y₀⟩`. Take `⟨W, hWa, hzW, hWle⟩` from `(Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (Opens.mem_inf.2 ⟨mem_ptsIn.1 hy₀, mem_ptsIn.1 hy₀j⟩ : y₀.1 (IsLocalRing.closedPoint ℂ) ∈ Q ⊓ B.U j)`. Establish `hWQ : W ≤ Q` using `hWle.trans inf_le_left`. Establish `hWj : W ≤ B.U j` using `hWle.trans inf_le_right`. Establish `hy₀W : y₀ ∈ ptsIn p σ W` using `mem_ptsIn.2 hzW`.

Use `set η' : Γ(Y, W) := resG Y hWQ η with hη'`. Establish `hD : Y.basicOpen η' = W ⊓ (Q ⊓ V)`. Rewrite using `[← hη]`. Conclude with `Y.basicOpen_res η (homOfLE hWQ).op`. Establish `hDij : Y.basicOpen η' ≤ B.U i ⊓ B.U j`.

Rewrite using `[hD]`. Conclude with `le_inf (inf_le_right.trans (inf_le_right.trans hV)) (inf_le_left.trans hWj)`. Use `hWa.isLocalization_basicOpen η'` as an intermediate fact. Take `⟨⟨a, _, n, rfl⟩, han⟩` from `IsLocalization.surj (Submonoid.powers η') (resG Y hDij (B.g i j).val)`. Rewrite `han` using `[map_pow]`.

Use `⟨fun y => ev p σ W a y * s j y, n, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((continuousOn_ev a).continuousAt ((isOpen_ptsIn W).mem_nhds hy₀W)).mul ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hy₀j))`. Use `filter_upwards [(isOpen_ptsIn W).mem_nhds hy₀W] with y hyW hyV`. Establish `hyQ : y ∈ ptsIn p σ Q` using `ptsIn_mono hWQ hyW`. Establish `hyj : y ∈ ptsIn p σ (B.U j)` using `ptsIn_mono hWj hyW`.

Establish `hyi : y ∈ ptsIn p σ (B.U i)` using `ptsIn_mono hV hyV`. Establish `hyQV : y ∈ ptsIn p σ (Q ⊓ V)` using `mem_ptsIn_inf.2 ⟨hyQ, hyV⟩`. Establish `huv : ev p σ V u y * ev p σ Q η y = 1`. Establish `h1` using `congrArg (fun f => ev p σ (Q ⊓ V) f y) hu`. Rewrite `h1` using `[ev_mul, ev_res _ hyQV, ev_res _ hyQV, ev_one hyQV]`. Then use the resulting hypothesis.

Establish `hηne : ev p σ Q η y ≠ 0` using `fun h0 => by`. Rewrite `huv` using `[h0, mul_zero]`. Conclude with `zero_ne_one huv`. Establish `hηW : ev p σ W η' y = ev p σ Q η y` using `ev_res hWQ hyW η`. Establish `hyD : y ∈ ptsIn p σ (Y.basicOpen η')` using `(mem_ptsIn_basicOpen hyW η').2 (hηW ▸ hηne)`.

Establish `hal : ∀ b : Γ(Y, W), ev p σ (Y.basicOpen η') (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen η') b) y = ev p σ W b y` using `fun b => ev_res (Y.basicOpen_le η') hyD b`. Establish `e1` using `congrArg (evHom hyD) han`. Rewrite `e1` using `[map_mul, map_pow, ← ev_eq hyD, ← ev_eq hyD, ← ev_eq hyD, hal, hal, ev_res hDij hyD, hηW]`. Establish `hg : gv p σ B i j y = ev p σ (B.U i ⊓ B.U j) (B.g i j).val y` using `rfl`. Establish `hun : (ev p σ V u y * ev p σ Q η y) ^ n = 1` using `by rw [huv, one_pow]`.

Use `show s i y = ev p σ W a y * s j y * ev p σ V u y ^ n`. Rewrite using `[hs.1 i j y hyi hyj, hg]`. Take the linear combination `(s j y * ev p σ V u y ^ n) * e1 - (ev p σ (B.U i ⊓ B.U j) (B.g i j).val y * s j y) * hun`.
-/
theorem local_factor (hB : B.IsLB) {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ fibSec p σ B)
    (hc : ∀ j, ContinuousOn (s j) (ptsIn p σ (B.U j))) {i : B.ι} {V Q : Y.Opens} (hV : V ≤ B.U i)
    (u : Γ(Y, V)) (η : Γ(Y, Q)) (hη : Y.basicOpen η = Q ⊓ V)
    (hu : resG Y (inf_le_right : Q ⊓ V ≤ V) u * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1)
    {y₀ : CxPts p σ} (hy₀ : y₀ ∈ ptsIn p σ Q) :
    ∃ (F : CxPts p σ → ℂ) (N : ℕ), ContinuousAt F y₀ ∧
      ∀ᶠ y in 𝓝 y₀, y ∈ ptsIn p σ V → s i y = F y * ev p σ V u y ^ N := by

  obtain ⟨j, hy₀j⟩ : ∃ j, y₀ ∈ ptsIn p σ (B.U j) := ⟨_, mem_pick hB y₀⟩
  obtain ⟨W, hWa, hzW, hWle⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (Opens.mem_inf.2 ⟨mem_ptsIn.1 hy₀, mem_ptsIn.1 hy₀j⟩ :
      y₀.1 (IsLocalRing.closedPoint ℂ) ∈ Q ⊓ B.U j)
  have hWQ : W ≤ Q := hWle.trans inf_le_left
  have hWj : W ≤ B.U j := hWle.trans inf_le_right
  have hy₀W : y₀ ∈ ptsIn p σ W := mem_ptsIn.2 hzW

  set η' : Γ(Y, W) := resG Y hWQ η with hη'
  have hD : Y.basicOpen η' = W ⊓ (Q ⊓ V) := by
    rw [← hη]
    exact Y.basicOpen_res η (homOfLE hWQ).op
  have hDij : Y.basicOpen η' ≤ B.U i ⊓ B.U j := by
    rw [hD]
    exact le_inf (inf_le_right.trans (inf_le_right.trans hV)) (inf_le_left.trans hWj)

  have := hWa.isLocalization_basicOpen η'
  obtain ⟨⟨a, _, n, rfl⟩, han⟩ :=
    IsLocalization.surj (Submonoid.powers η') (resG Y hDij (B.g i j).val)
  rw [map_pow] at han
  refine ⟨fun y => ev p σ W a y * s j y, n, ?_, ?_⟩
  · exact ((continuousOn_ev a).continuousAt ((isOpen_ptsIn W).mem_nhds hy₀W)).mul
      ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hy₀j))
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hy₀W] with y hyW hyV
    have hyQ : y ∈ ptsIn p σ Q := ptsIn_mono hWQ hyW
    have hyj : y ∈ ptsIn p σ (B.U j) := ptsIn_mono hWj hyW
    have hyi : y ∈ ptsIn p σ (B.U i) := ptsIn_mono hV hyV
    have hyQV : y ∈ ptsIn p σ (Q ⊓ V) := mem_ptsIn_inf.2 ⟨hyQ, hyV⟩
    have huv : ev p σ V u y * ev p σ Q η y = 1 := by
      have h1 := congrArg (fun f => ev p σ (Q ⊓ V) f y) hu
      rwa [ev_mul, ev_res _ hyQV, ev_res _ hyQV, ev_one hyQV] at h1
    have hηne : ev p σ Q η y ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at huv
      exact zero_ne_one huv
    have hηW : ev p σ W η' y = ev p σ Q η y := ev_res hWQ hyW η
    have hyD : y ∈ ptsIn p σ (Y.basicOpen η') :=
      (mem_ptsIn_basicOpen hyW η').2 (hηW ▸ hηne)
    have hal : ∀ b : Γ(Y, W),
        ev p σ (Y.basicOpen η') (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen η') b) y = ev p σ W b y :=
      fun b => ev_res (Y.basicOpen_le η') hyD b
    have e1 := congrArg (evHom hyD) han
    rw [map_mul, map_pow, ← ev_eq hyD, ← ev_eq hyD, ← ev_eq hyD, hal, hal, ev_res hDij hyD,
      hηW] at e1
    have hg : gv p σ B i j y = ev p σ (B.U i ⊓ B.U j) (B.g i j).val y := rfl
    have hun : (ev p σ V u y * ev p σ Q η y) ^ n = 1 := by rw [huv, one_pow]
    show s i y = ev p σ W a y * s j y * ev p σ V u y ^ n
    rw [hs.1 i j y hyi hyj, hg]
    linear_combination (s j y * ev p σ V u y ^ n) * e1 -
      (ev p σ (B.U i ⊓ B.U j) (B.g i j).val y * s j y) * hun

/- English proof (translation)
Use `choose C m hC hev using h`. Take `⟨t, -, ht⟩` from `isCompact_univ.elim_nhds_subcover (fun x₀ => {x | x ∈ S → f x ≤ C x₀ * T x ^ m x₀}) (fun x₀ _ => hev x₀)`. Use `⟨∑ x₀ ∈ t, C x₀, t.sup m, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨x₀, hx₀t, hx₀⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ x))`. Establish `h1 : f x ≤ C x₀ * T x ^ m x₀` using `hx₀ hx`.

Establish `h2 : T x ^ m x₀ ≤ T x ^ t.sup m` using `pow_le_pow_right₀ (hT x) (Finset.le_sup hx₀t)`. Establish `h3 : C x₀ ≤ ∑ x₀ ∈ t, C x₀` using `Finset.single_le_sum (fun i _ => hC i) hx₀t`. Establish `h4 : 0 ≤ T x ^ t.sup m` using `pow_nonneg (zero_le_one.trans (hT x)) _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem global_bound {X : Type*} [TopologicalSpace X] [CompactSpace X] (S : Set X) (f T : X → ℝ)
    (hT : ∀ x, 1 ≤ T x)
    (h : ∀ x₀, ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ᶠ x in 𝓝 x₀, x ∈ S → f x ≤ C * T x ^ m) :
    ∃ (C : ℝ) (m : ℕ), ∀ x ∈ S, f x ≤ C * T x ^ m := by
  choose C m hC hev using h
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x₀ => {x | x ∈ S → f x ≤ C x₀ * T x ^ m x₀}) (fun x₀ _ => hev x₀)
  refine ⟨∑ x₀ ∈ t, C x₀, t.sup m, fun x hx => ?_⟩
  obtain ⟨x₀, hx₀t, hx₀⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have h1 : f x ≤ C x₀ * T x ^ m x₀ := hx₀ hx
  have h2 : T x ^ m x₀ ≤ T x ^ t.sup m := pow_le_pow_right₀ (hT x) (Finset.le_sup hx₀t)
  have h3 : C x₀ ≤ ∑ x₀ ∈ t, C x₀ := Finset.single_le_sum (fun i _ => hC i) hx₀t
  have h4 : 0 ≤ T x ^ t.sup m := pow_nonneg (zero_le_one.trans (hT x)) _
  calc f x ≤ C x₀ * T x ^ m x₀ := h1
    _ ≤ C x₀ * T x ^ t.sup m := mul_le_mul_of_nonneg_left h2 (hC x₀)
    _ ≤ (∑ x₀ ∈ t, C x₀) * T x ^ t.sup m := mul_le_mul_of_nonneg_right h3 h4

end GlobalTheory.SectionGrowth

namespace GlobalTheory

/- English proof (translation)
Introduce `Y p hp B hB s hs hc i V n u hV hloc`. Use `CxPts.compactSpace (RingHom.id ℂ) hp` as an intermediate fact. Take `⟨C, m, hCm⟩` from `SectionGrowth.global_bound (ptsIn p (RingHom.id ℂ) V) (fun y => ‖s i y‖) (fun y => 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) (fun y => le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => norm_nonneg _)) (by`. Introduce `y₀`. Take `⟨Q, η, l, hzQ, hη, hu⟩` from `hloc (y₀.1 (IsLocalRing.closedPoint ℂ))`.

Take `⟨F, N, hF, hev⟩` from `SectionGrowth.local_factor hB hs hc hV (u l) η hη hu (mem_ptsIn.2 hzQ)`. Establish `hFb : ∀ᶠ y in 𝓝 y₀, ‖F y‖ < ‖F y₀‖ + 1` using `hF.norm.eventually (gt_mem_nhds (lt_add_one _))`. Use `⟨‖F y₀‖ + 1, N, by positivity, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev, hFb] with y hy1 hy2 hyV`. Establish `hle : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤ 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖`.

Use `Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖) (fun l _ => norm_nonneg _) (Finset.mem_univ l)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `show ‖s i y‖ ≤ (‖F y₀‖ + 1) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ N`. Rewrite using `[hy1 hyV, norm_mul, norm_pow]`. Conclude with `mul_le_mul hy2.le (pow_le_pow_left₀ (norm_nonneg _) hle N) (by positivity) (by positivity))`.

Conclude with `⟨C, m, hCm⟩`.
-/
theorem continuous_section_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), V ≤ B.U i → (∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧ resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1) → ∃ (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hp B hB s hs hc i V n u hV hloc
  have := CxPts.compactSpace (RingHom.id ℂ) hp
  obtain ⟨C, m, hCm⟩ := SectionGrowth.global_bound (ptsIn p (RingHom.id ℂ) V) (fun y => ‖s i y‖)
    (fun y => 1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖)
    (fun y => le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => norm_nonneg _)) (by
      intro y₀
      obtain ⟨Q, η, l, hzQ, hη, hu⟩ := hloc (y₀.1 (IsLocalRing.closedPoint ℂ))
      obtain ⟨F, N, hF, hev⟩ :=
        SectionGrowth.local_factor hB hs hc hV (u l) η hη hu (mem_ptsIn.2 hzQ)
      have hFb : ∀ᶠ y in 𝓝 y₀, ‖F y‖ < ‖F y₀‖ + 1 :=
        hF.norm.eventually (gt_mem_nhds (lt_add_one _))
      refine ⟨‖F y₀‖ + 1, N, by positivity, ?_⟩
      filter_upwards [hev, hFb] with y hy1 hy2 hyV
      have hle : ‖ev p (RingHom.id ℂ) V (u l) y‖ ≤
          1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ := by
        have := Finset.single_le_sum (f := fun l => ‖ev p (RingHom.id ℂ) V (u l) y‖)
          (fun l _ => norm_nonneg _) (Finset.mem_univ l)
        linarith
      show ‖s i y‖ ≤ (‖F y₀‖ + 1) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ N
      rw [hy1 hyV, norm_mul, norm_pow]
      exact mul_le_mul hy2.le (pow_le_pow_left₀ (norm_nonneg _) hle N) (by positivity)
        (by positivity))
  exact ⟨C, m, hCm⟩

end GlobalTheory
