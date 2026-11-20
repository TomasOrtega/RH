import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.CubicPeriodConstant
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CharacterNondegenerate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalUpperUnipotentAdelicUpperUnipotent

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BlockInfGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

/- English proof (translation)
Introduce `i l hil` and use `by change (cornerGL k (sInf E) c).val i l = _ rw [GlobalTheory.CuspRep.cornerGL_apply_loctri, hc i l hil, sub_add_cancel]`.
-/
theorem blk_infGL {j : ℕ} {c : GL (Fin k) (Cinf E)} (hc : GlobalTheory j c) : GlobalTheory j (infGL E k c) := fun i l hil => by
  change (cornerGL k (sInf E) c).val i l = _
  rw [GlobalTheory.CuspRep.cornerGL_apply_loctri, hc i l hil, sub_add_cancel]

end BlockInfGL

open BlockInfGL jumpWindows.CharacterNondegenerate in
/- English proof (translation)
Introduce `hS7 hS10 hG0 hG5 _ hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m hn _ U hU x C hxY hsm hlev hBump`. Take `⟨hcI, hcLI, hcIf, -, -, -, hcomm, -, hb, -, -, -, -, -, hcontI⟩` from `hG0 E k`. Take `⟨hΛ, hRt, hGood, hlaw⟩` from `hG5 E k ψ hψ`. Take `⟨hdec, -, -, hBlk1, -⟩` from `hS10 (Cinf E) k (n + 1)`. Take `⟨hP2u, -, hU01, hPre0, -, hGP, -⟩` from `hP2 E k ψ hψ`.

Take `⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hB⟩` from `hBump`. Establish `hU' : infGL E k ⁻¹' U ∈ 𝓝 (1 : GL (Fin k) (Cinf E))` using `hcontI.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)`. Take `⟨η, r, hη1, hr1, hmir, hnn, ⟨C', hC'c, hC'U, hC'B, hC'd⟩, hv⟩` from `hS7 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly n hn (chi ψ) (continuous_chi hψ) (fun z => hψ.norm _) (chi_nondeg hψ) _ hU'`. Take `⟨x', hsm', hvP⟩` from `hv x hsm`. Set `ZY : Submodule ℂ (XB E k)` to `Submodule.comap (J : XB E k →ₗ[ℂ] XB E k) Y`.

Establish `hZYc : IsClosed (ZY : Set (XB E k))` using `hY.closed.preimage J.continuous`. Establish `hZYi : ∀ g, ∀ y ∈ ZY, (ρ.comp (infGL E k)) g y ∈ ZY`. Introduce `g y hy`. Use `show J (ρ (infGL E k g) y) ∈ Y`. Rewrite using `[hW.inter]`.

Conclude with `hY.stable _ (fun w _ => hcLI w g) _ hy`. Take `⟨hx'Y, hvΛ⟩` from `hvP ZY hZYc hZYi hxY`. Establish `whB : ∀ φ : XB E k, Good ψ (k - 1) φ → ∀ (y : UnipotentBlockColumnIndex k (n + 1) (n + 1) → Cinf E) (g : GA E k), Wh ψ φ (infGL E k (blkU y) * g) = chi ψ (lastE (n + 1) y) * Wh ψ φ g`. Introduce `φ hφ y g`. Rewrite using `[hb, chi_apply, sInf_lastE]`.

Conclude with `(hlaw φ hφ).2.2 (n + 1) n.succ_pos _ g`. Establish `lawOf : ∀ g' : GA E k, cInf g' = 1 → ∀ Λ : XB E k →L[ℂ] ℂ, (∀ φ : XB E k, Good ψ (k - 1) φ → Λ φ = Wh ψ φ g') → ∀ y ∈ ZY, ∀ y' : UnipotentBlockColumnIndex k (n + 1) (n + 1) → Cinf E, (Λ.comp J) ((ρ.comp (infGL E k)) (blkU y') y) = chi ψ (lastE (n + 1) y') * (Λ.comp J) y`. Introduce `g' hg' Λ hΛg y hy y'`. Establish `hy' : Good ψ (k - 1) (J y)` using `hY.good _ hy`. Express the relevant statement in the definitionally equal form `Λ (J (ρ (infGL E k (blkU y')) y)) = _ * Λ (J y)`.

Rewrite using `[hW.inter, hΛg _ (hGood _ _ hy'), hΛg _ hy', hRt, hcomm g' hg', whB _ hy']`. Establish `conv : ∀ (g' : GA E k) (Λ : XB E k →L[ℂ] ℂ), (∀ φ : XB E k, Good ψ (k - 1) φ → Λ φ = Wh ψ φ g') → ∀ v : XB E k, J v ∈ Y → ∀ h, (Λ.comp J) ((ρ.comp (infGL E k)) h v) = Wh ψ (J v) (g' * infGL E k h)`. Introduce `g' Λ hΛg v hv h`. Express the relevant statement in the definitionally equal form `Λ (J (ρ (infGL E k h) v)) = _`. Rewrite using `[hW.inter, hΛg _ (hGood _ _ (hY.good _ hv)), hRt]`.

Establish `goodx : Good ψ (k - 1) (J x)` using `hY.good _ hxY`. Establish `goodx' : Good ψ (k - 1) (J x')` using `hY.good _ hx'Y`. Establish `hW10 : Wh ψ (J x) 1 ≠ 0` using `by rw [hW1]; exact Complex.ofReal_ne_zero.2 ht₀.ne'`. Establish `pre0 : Pre ψ 0 (whit ψ (k - 1) (J x))` using `hPre0 (k - 1) (by omega) _ (hGP (k - 1) _ goodx)`. Establish `law0 : ∀ u, UU 0 u → ∀ g, Wh ψ (J x) (u * g) = psN ψ u * Wh ψ (J x) g` using `fun u hu g => hP2u 0 _ pre0 u (hU01 u hu) g`.

Use `⟨x', infGL E k '' C', ?_, hx'Y, hsm', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Conclude with `hC'U hc`. Introduce `w hw`. Use `Filter.mem_of_superset (hlev w hw) fun u hu => ?_` and prove the remaining obligations.

Establish `hu' : Rt E k (fl k w u) (J x) = J x` using `hu`. Set `T : XB E k →L[ℂ] XB E k` to `(Rt E k (fl k w u)).comp J - J`. Establish `key : ∀ y, T y = 0 ↔ Rt E k (fl k w u) (J y) = J y` using `fun y => by simp [T, sub_eq_zero]`. Establish `hk` using `(hvP (LinearMap.ker (T : XB E k →ₗ[ℂ] XB E k)) T.isClosed_ker (fun g y hy => by`. Rewrite `hy`, the goal using `[LinearMap.mem_ker]`.

Use `(key _).2 ?_` and prove the remaining obligations. Establish `hy'` using `(key y).1 hy`. Establish `hc : ∀ φ : XB E k, Rt E k (fl k w u) (Rt E k (infGL E k g) φ) = Rt E k (infGL E k g) (Rt E k (fl k w u) φ)` using `fun φ => by`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, hcomm _ (hcIf w u), map_mul, ContinuousLinearMap.mul_apply]`. Use `show Rt E k (fl k w u) (J (ρ (infGL E k g) y)) = J (ρ (infGL E k g) y)`.

Rewrite using `[hW.inter, hc, hy'])`. Use the proof step `(LinearMap.mem_ker.2 ((key x).2 hu'))).1`. Rewrite `hk` using `[LinearMap.mem_ker]`. Conclude with `(key x').1 hk`. Introduce and unpack `_ ⟨c, hc, rfl⟩`.

Conclude with `blk_infGL (hC'B c hc)`. Use `⟨hCc.mul (hC'c.image hcontI), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, _, ⟨c, _, rfl⟩, rfl⟩ w hw`. Rewrite using `[map_mul, hcLI, mul_one]`. Conclude with `hCS a ha w hw`.

Take `⟨Λ₁, hΛ₁⟩` from `hΛ 1`. Establish `e1` using `hvΛ (Λ₁.comp J) (lawOf 1 (map_one _) Λ₁ hΛ₁) 1 hBlk1`. Rewrite `e1` using `[conv 1 Λ₁ hΛ₁ x' hx'Y, conv 1 Λ₁ hΛ₁ x hxY, hr1, map_one, one_mul]`. Take `⟨s, hs, hηs⟩` from `hnn 1`. Establish `hs' : 0 < s` using `lt_of_le_of_ne hs fun h0 => hη1 (by rw [hηs, ← h0, Complex.ofReal_zero])`.

Conclude with `⟨s * t₀, mul_pos hs' ht₀, by rw [e1, hηs, hW1, Complex.ofReal_mul]⟩`. Introduce `g hg hWg`. Take `⟨hgI, hgL⟩` from `hg`. Take `⟨y, h, hh, hyh⟩` from `hdec (cInf g) hgI`. Take `⟨g', hg'⟩ : ∃ g' : GA E k, g' = (infGL E k (cInf g))⁻¹ * g` from `⟨_, rfl⟩`.

Establish `hg'1 : cInf g' = 1` using `by rw [hg', map_mul, map_inv, hcI, inv_mul_cancel]`. Establish `hgeq : g = infGL E k (blkU y) * (g' * infGL E k h)`. Rewrite using `[hcomm g' hg'1 h, ← mul_assoc, ← map_mul, ← hyh, hg', mul_inv_cancel_left]`. Take `⟨Λ, hΛg⟩` from `hΛ g'`. Establish `e` using `hvΛ (Λ.comp J) (lawOf g' hg'1 Λ hΛg) h hh`.

Rewrite `e` using `[conv g' Λ hΛg x' hx'Y, conv g' Λ hΛg x hxY]`. Establish `hWg' : Wh ψ (J x') g = chi ψ (lastE (n + 1) y) * (η h * Wh ψ (J x) (g' * infGL E k (r h)))`. Rewrite using `[hgeq, whB _ goodx', e]`. Rewrite `hWg`, the goal using `[hWg']`. Establish `hη : η h ≠ 0` using `fun h0 => hWg (by rw [h0, zero_mul, mul_zero])`.

Establish `hW0 : Wh ψ (J x) (g' * infGL E k (r h)) ≠ 0` using `fun h0 => hWg (by rw [h0, mul_zero, mul_zero])`. Take `⟨c, hc, hhc⟩` from `hC'd h hh hη`. Take `⟨s, hs, hηs⟩` from `hnn h`. Establish `hOm : Om n m (g' * infGL E k (r h))`. Use `⟨?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hg'1, one_mul, hcI]`. Conclude with `hmir h hh hη`. Rewrite using `[map_mul, hcLI, mul_one, hg', map_mul, map_inv, hcLI, inv_one, one_mul]`. Conclude with `hgL w`. Take `⟨n₀, c₁, hc₁, t₁, hn₀, hn₀S, heq₀, ht₁, hWeq⟩` from `hB _ hOm hW0`.

Establish `huu : UU 0 (infGL E k (blkU y) * n₀)` using `cubicPeriodConstant.unipotent_zero_mul (by rw [hb]; exact cubicPeriodConstant.blkU_unipotent_zero _) hn₀`. Establish `hpsN : psN ψ (infGL E k (blkU y) * n₀) = chi ψ (lastE (n + 1) y) * psN ψ n₀`. Establish `e1` using `law0 _ huu 1`. Establish `e2` using `law0 n₀ hn₀ 1`. Establish `e3` using `whB (J x) goodx y n₀`.

Rewrite `e1`, `e2` using `[mul_one]`. Rewrite `e3` using `[e1, e2]`. Conclude with `mul_right_cancel₀ hW10 (by rw [e3, mul_assoc])`. Establish `hih : infGL E k h = infGL E k (r h) * infGL E k c` using `by rw [← map_mul, ← hhc]`. Use `⟨infGL E k (blkU y) * n₀, c₁ * infGL E k c, Set.mem_image2_of_mem hc₁ (Set.mem_image_of_mem _ hc), s * t₁, huu, fun w hw => ?_, ?_, mul_nonneg hs ht₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hcLI, one_mul]`. Conclude with `hn₀S w hw`. Rewrite using `[hgeq, hih, ← mul_assoc g', heq₀]`. Simplify using `only [mul_assoc]`. Rewrite using `[hWeq, hηs, hpsN]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem infinite_place_step_of : jumpWindows.S7 → jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → jumpWindows.G5 → jumpWindows.G5b → P2 → InfinitePlaceStep := by
  intro hS7 hS10 hG0 hG5 _ hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m hn _ U hU x C hxY hsm hlev hBump
  obtain ⟨hcI, hcLI, hcIf, -, -, -, hcomm, -, hb, -, -, -, -, -, hcontI⟩ := hG0 E k
  obtain ⟨hΛ, hRt, hGood, hlaw⟩ := hG5 E k ψ hψ
  obtain ⟨hdec, -, -, hBlk1, -⟩ := hS10 (Cinf E) k (n + 1)
  obtain ⟨hP2u, -, hU01, hPre0, -, hGP, -⟩ := hP2 E k ψ hψ
  obtain ⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hB⟩ := hBump
  have hU' : infGL E k ⁻¹' U ∈ 𝓝 (1 : GL (Fin k) (Cinf E)) :=
    hcontI.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU)
  obtain ⟨η, r, hη1, hr1, hmir, hnn, ⟨C', hC'c, hC'U, hC'B, hC'd⟩, hv⟩ :=
    hS7 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly n hn (chi ψ)
      (continuous_chi hψ) (fun z => hψ.norm _) (chi_nondeg hψ) _ hU'
  obtain ⟨x', hsm', hvP⟩ := hv x hsm

  let ZY : Submodule ℂ (XB E k) := Submodule.comap (J : XB E k →ₗ[ℂ] XB E k) Y
  have hZYc : IsClosed (ZY : Set (XB E k)) := hY.closed.preimage J.continuous
  have hZYi : ∀ g, ∀ y ∈ ZY, (ρ.comp (infGL E k)) g y ∈ ZY := by
    intro g y hy
    show J (ρ (infGL E k g) y) ∈ Y
    rw [hW.inter]
    exact hY.stable _ (fun w _ => hcLI w g) _ hy
  obtain ⟨hx'Y, hvΛ⟩ := hvP ZY hZYc hZYi hxY
  have whB : ∀ φ : XB E k, Good ψ (k - 1) φ → ∀ (y : UnipotentBlockColumnIndex k (n + 1) (n + 1) → Cinf E) (g : GA E k),
      Wh ψ φ (infGL E k (blkU y) * g) = chi ψ (lastE (n + 1) y) * Wh ψ φ g := by
    intro φ hφ y g
    rw [hb, chi_apply, sInf_lastE]
    exact (hlaw φ hφ).2.2 (n + 1) n.succ_pos _ g
  have lawOf : ∀ g' : GA E k, cInf g' = 1 → ∀ Λ : XB E k →L[ℂ] ℂ,
      (∀ φ : XB E k, Good ψ (k - 1) φ → Λ φ = Wh ψ φ g') →
      ∀ y ∈ ZY, ∀ y' : UnipotentBlockColumnIndex k (n + 1) (n + 1) → Cinf E,
        (Λ.comp J) ((ρ.comp (infGL E k)) (blkU y') y) = chi ψ (lastE (n + 1) y') * (Λ.comp J) y := by
    intro g' hg' Λ hΛg y hy y'
    have hy' : Good ψ (k - 1) (J y) := hY.good _ hy
    change Λ (J (ρ (infGL E k (blkU y')) y)) = _ * Λ (J y)
    rw [hW.inter, hΛg _ (hGood _ _ hy'), hΛg _ hy', hRt, hcomm g' hg', whB _ hy']
  have conv : ∀ (g' : GA E k) (Λ : XB E k →L[ℂ] ℂ), (∀ φ : XB E k, Good ψ (k - 1) φ → Λ φ = Wh ψ φ g') →
      ∀ v : XB E k, J v ∈ Y → ∀ h, (Λ.comp J) ((ρ.comp (infGL E k)) h v) = Wh ψ (J v) (g' * infGL E k h) := by
    intro g' Λ hΛg v hv h
    change Λ (J (ρ (infGL E k h) v)) = _
    rw [hW.inter, hΛg _ (hGood _ _ (hY.good _ hv)), hRt]
  have goodx : Good ψ (k - 1) (J x) := hY.good _ hxY
  have goodx' : Good ψ (k - 1) (J x') := hY.good _ hx'Y
  have hW10 : Wh ψ (J x) 1 ≠ 0 := by rw [hW1]; exact Complex.ofReal_ne_zero.2 ht₀.ne'
  have pre0 : Pre ψ 0 (whit ψ (k - 1) (J x)) := hPre0 (k - 1) (by omega) _ (hGP (k - 1) _ goodx)
  have law0 : ∀ u, UU 0 u → ∀ g, Wh ψ (J x) (u * g) = psN ψ u * Wh ψ (J x) g :=
    fun u hu g => hP2u 0 _ pre0 u (hU01 u hu) g
  refine ⟨x', infGL E k '' C', ?_, hx'Y, hsm', ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hC'U hc
  ·
    intro w hw
    refine Filter.mem_of_superset (hlev w hw) fun u hu => ?_
    have hu' : Rt E k (fl k w u) (J x) = J x := hu
    let T : XB E k →L[ℂ] XB E k := (Rt E k (fl k w u)).comp J - J
    have key : ∀ y, T y = 0 ↔ Rt E k (fl k w u) (J y) = J y := fun y => by simp [T, sub_eq_zero]
    have hk := (hvP (LinearMap.ker (T : XB E k →ₗ[ℂ] XB E k)) T.isClosed_ker (fun g y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        refine (key _).2 ?_
        have hy' := (key y).1 hy
        have hc : ∀ φ : XB E k, Rt E k (fl k w u) (Rt E k (infGL E k g) φ) =
            Rt E k (infGL E k g) (Rt E k (fl k w u) φ) := fun φ => by
          rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm _ (hcIf w u), map_mul,
            ContinuousLinearMap.mul_apply]
        show Rt E k (fl k w u) (J (ρ (infGL E k g) y)) = J (ρ (infGL E k g) y)
        rw [hW.inter, hc, hy'])
      (LinearMap.mem_ker.2 ((key x).2 hu'))).1
    rw [LinearMap.mem_ker] at hk
    exact (key x').1 hk
  · rintro _ ⟨c, hc, rfl⟩
    exact blk_infGL (hC'B c hc)
  refine ⟨hCc.mul (hC'c.image hcontI), ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, _, ⟨c, _, rfl⟩, rfl⟩ w hw
    rw [map_mul, hcLI, mul_one]
    exact hCS a ha w hw
  · obtain ⟨Λ₁, hΛ₁⟩ := hΛ 1
    have e1 := hvΛ (Λ₁.comp J) (lawOf 1 (map_one _) Λ₁ hΛ₁) 1 hBlk1
    rw [conv 1 Λ₁ hΛ₁ x' hx'Y, conv 1 Λ₁ hΛ₁ x hxY, hr1, map_one, one_mul] at e1
    obtain ⟨s, hs, hηs⟩ := hnn 1
    have hs' : 0 < s := lt_of_le_of_ne hs fun h0 => hη1 (by rw [hηs, ← h0, Complex.ofReal_zero])
    exact ⟨s * t₀, mul_pos hs' ht₀, by rw [e1, hηs, hW1, Complex.ofReal_mul]⟩
  · intro g hg hWg
    obtain ⟨hgI, hgL⟩ := hg
    obtain ⟨y, h, hh, hyh⟩ := hdec (cInf g) hgI
    obtain ⟨g', hg'⟩ : ∃ g' : GA E k, g' = (infGL E k (cInf g))⁻¹ * g := ⟨_, rfl⟩
    have hg'1 : cInf g' = 1 := by rw [hg', map_mul, map_inv, hcI, inv_mul_cancel]
    have hgeq : g = infGL E k (blkU y) * (g' * infGL E k h) := by
      rw [hcomm g' hg'1 h, ← mul_assoc, ← map_mul, ← hyh, hg', mul_inv_cancel_left]
    obtain ⟨Λ, hΛg⟩ := hΛ g'
    have e := hvΛ (Λ.comp J) (lawOf g' hg'1 Λ hΛg) h hh
    rw [conv g' Λ hΛg x' hx'Y, conv g' Λ hΛg x hxY] at e
    have hWg' : Wh ψ (J x') g = chi ψ (lastE (n + 1) y) * (η h * Wh ψ (J x) (g' * infGL E k (r h))) := by
      rw [hgeq, whB _ goodx', e]
    rw [hWg'] at hWg ⊢
    have hη : η h ≠ 0 := fun h0 => hWg (by rw [h0, zero_mul, mul_zero])
    have hW0 : Wh ψ (J x) (g' * infGL E k (r h)) ≠ 0 := fun h0 => hWg (by rw [h0, mul_zero, mul_zero])
    obtain ⟨c, hc, hhc⟩ := hC'd h hh hη
    obtain ⟨s, hs, hηs⟩ := hnn h
    have hOm : Om n m (g' * infGL E k (r h)) := by
      refine ⟨?_, fun w => ?_⟩
      · rw [map_mul, hg'1, one_mul, hcI]
        exact hmir h hh hη
      · rw [map_mul, hcLI, mul_one, hg', map_mul, map_inv, hcLI, inv_one, one_mul]
        exact hgL w
    obtain ⟨n₀, c₁, hc₁, t₁, hn₀, hn₀S, heq₀, ht₁, hWeq⟩ := hB _ hOm hW0
    have huu : UU 0 (infGL E k (blkU y) * n₀) := cubicPeriodConstant.unipotent_zero_mul (by rw [hb]; exact cubicPeriodConstant.blkU_unipotent_zero _) hn₀
    have hpsN : psN ψ (infGL E k (blkU y) * n₀) = chi ψ (lastE (n + 1) y) * psN ψ n₀ := by
      have e1 := law0 _ huu 1
      have e2 := law0 n₀ hn₀ 1
      have e3 := whB (J x) goodx y n₀
      rw [mul_one] at e1 e2
      rw [e1, e2] at e3
      exact mul_right_cancel₀ hW10 (by rw [e3, mul_assoc])
    have hih : infGL E k h = infGL E k (r h) * infGL E k c := by rw [← map_mul, ← hhc]
    refine ⟨infGL E k (blkU y) * n₀, c₁ * infGL E k c, Set.mem_image2_of_mem hc₁ (Set.mem_image_of_mem _ hc),
      s * t₁, huu, fun w hw => ?_, ?_, mul_nonneg hs ht₁, ?_⟩
    · rw [map_mul, hcLI, one_mul]
      exact hn₀S w hw
    · rw [hgeq, hih, ← mul_assoc g', heq₀]
      simp only [mul_assoc]
    · rw [hWeq, hηs, hpsN]
      push_cast
      ring

end PositivityTheory.AdelicQuotientData

end
