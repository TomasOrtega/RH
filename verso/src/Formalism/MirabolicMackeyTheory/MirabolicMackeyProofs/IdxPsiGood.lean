import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

/- English proof (translation)
Unfold `sc`. Rewrite using `[Submodule.mem_map]`. Both sides reduce to the same expression.
-/
theorem mem_sc {K : Type} [Field K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ sc a A ↔ ∃ y ∈ A, a • y = x := by
  unfold sc
  rw [Submodule.mem_map]
  rfl

/- English proof (translation)
Unfold `IdxPsiGood`. Introduce `K _ _ _ Z _ _ _ _ _ w Zψ V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0Z σ hσ hThσ u hu hucut a E r ha hE hr δ hδ hδi`. Establish `hVB` using `valuation_basic_properties K w`. Establish `hcc : ∀ (W W' : Submodule K Z) (A : Submodule (𝓞 K) Z), W' ≤ W → cut W' (cut W A) = cut W' A`. Introduce `W W' A hWW`.

Use extensionality with `x`. Simplify using `only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, _⟩, h3⟩`. Conclude with `⟨h1, h3⟩`.

Introduce and unpack `⟨h1, h3⟩`. Conclude with `⟨⟨h1, hWW h3⟩, h3⟩`. Use `set L : Submodule K Z := Zψ ⊓ V₀ with hL`. Establish `hLZ : L ≤ Zψ` using `inf_le_left`. Use `set N : Submodule (𝓞 K) Z := M ⊓ sc a⁻¹ Th with hN`.

Establish `hNl : IsLatIn ⊤ N` using `hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)`. Establish `hNM : N ≤ M` using `inf_le_left`. Establish `hX : IsLatIn L (cut L M)` using `(hCut K Z w ⊤ L M M hM hM le_rfl le_top).1`. Establish `hB0 : IsLatIn L (cut L N)` using `(hCut K Z w ⊤ L N N hNl hNl le_rfl le_top).1`. Establish `hMψ : IsLatIn Zψ (cut Zψ M)` using `(hCut K Z w ⊤ Zψ M M hM hM le_rfl le_top).1`.

Establish `hNψ : IsLatIn Zψ (cut Zψ N)` using `(hCut K Z w ⊤ Zψ N N hNl hNl le_rfl le_top).1`. Establish `hThKψ : IsLatIn Zψ (cut Zψ ThK)` using `(hCut K Z w ⊤ Zψ ThK ThK hThK hThK le_rfl le_top).1`. Establish `hu' : (u : K) ≠ 0` using `by exact_mod_cast hu`. Establish `hc : a * σ⁻¹ ≠ 0` using `mul_ne_zero ha (inv_ne_zero hσ)`. Establish `hTh0 : IsLatIn Zψ Th0` using `by show Th0.FG ∧ Submodule.span K (Th0 : Set Z) = Zψ`.

Use `⟨hTh0fg, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Conclude with `Submodule.span_le.mpr (fun x hx => hTh0Z hx)`. Establish `h1` using `(hSc K Z w Zψ (cut Zψ ThK) (cut Zψ ThK) hThKψ hThKψ (u : K) hu').1`. Establish `h2 : Submodule.span K ((sc (u : K) (cut Zψ ThK) : Submodule (𝓞 K) Z) : Set Z) = Zψ` using `h1.2`. Rewrite using `[← h2]`.

Conclude with `Submodule.span_mono (SetLike.coe_subset_coe.mpr hucut)`. Establish `hcutTh0 : cut V₀ Th0 = cut L Th0`. Use extensionality with `x`. Simplify using `only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hL]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, hTh0Z h1, h2⟩`. Introduce and unpack `⟨h1, _, h2⟩`. Conclude with `⟨h1, h2⟩`. Establish `hT : IsLatIn L (cut V₀ Th0)`.

Rewrite using `[hcutTh0]`. Conclude with `(hCut K Z w Zψ L Th0 Th0 hTh0 hTh0 le_rfl hLZ).1`. Use `⟨hT, ?_⟩` and prove the remaining obligations. Establish `hB1` using `hSc K Z w L (cut L M) (cut L N) hX hB0 (a * σ⁻¹) hc`. Establish `hB2` using `hSc K Z w L (cut L M) (sc (a * σ⁻¹) (cut L N)) hX hB1.1 (u : K) hu'`.

Establish `hle2 : sc (u : K) (sc (a * σ⁻¹) (cut L N)) ≤ cut V₀ Th0`. Introduce `x hx`. Rewrite `hx` using `[mem_sc]`. Take `⟨y, hy, rfl⟩` from `hx`. Rewrite `hy` using `[mem_sc]`.

Take `⟨z, hz, rfl⟩` from `hy`. Simplify using `only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hN, hL] at hz ⊢`. Take `⟨⟨_, hz2⟩, hzψ, hzV⟩` from `hz`. Rewrite `hz2` using `[mem_sc]`. Take `⟨t, ht, rfl⟩` from `hz2`.

Take `⟨k, hk, rfl⟩` from `(mem_sc σ ThK t).1 (hThσ ht)`. Establish `hkey : (a * σ⁻¹) • a⁻¹ • σ • k = k`. Rewrite using `[smul_smul, smul_smul]`. Establish `h1 : a * σ⁻¹ * a⁻¹ * σ = 1` using `by field_simp`. Rewrite using `[h1, one_smul]`.

Establish `hkψ : k ∈ Zψ`. Establish `h1` using `Zψ.smul_mem (a * σ⁻¹) hzψ`. Rewrite `h1` using `[hkey]`. Then use the resulting hypothesis. Establish `hkV : k ∈ V₀`. Establish `h1` using `V₀.smul_mem (a * σ⁻¹) hzV`.

Rewrite `h1` using `[hkey]`. Then use the resulting hypothesis. Rewrite using `[hkey]`. Establish `hkc : k ∈ cut Zψ ThK`. Simplify using `only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]`. Conclude with `⟨hk, hkψ⟩`.

Conclude with `⟨hucut ((mem_sc _ _ _).2 ⟨k, hkc, rfl⟩), V₀.smul_mem _ hkV⟩`. Establish `hmono` using `hMono K Z w L (cut L M) (sc (u : K) (sc (a * σ⁻¹) (cut L N))) (cut V₀ Th0) hX hB2.1 hT hle2`. Establish `hNMψ : cut Zψ N ≤ cut Zψ M`. Unfold `cut`. Conclude with `inf_le_inf_right _ hNM`.

Establish `hcut2` using `(hCut K Z w Zψ L (cut Zψ M) (cut Zψ N) hMψ hNψ hNMψ hLZ).2.2`. Rewrite `hcut2` using `[hcc Zψ L M hLZ, hcc Zψ L N hLZ]`. Establish `hv : vw w (a * σ⁻¹) = (E : ℤ) - vw w σ`. Rewrite using `[hVB.1 a σ⁻¹ ha (inv_ne_zero hσ), hVB.2.2.2.2.2.1 σ, hE]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hmono` using `[hB2.2, hB1.2, hv]`. Establish `h1 : (δ : ℝ) * (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤ (lix w M N : ℝ) + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)`. Conclude with `hδi` after adjusting the coercions. Establish `hJ : (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤ (r + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)) / (δ : ℝ)`. Rewrite using `[le_div_iff₀ (by exact_mod_cast hδ)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : (lix w (cut L M) (cut V₀ Th0) : ℝ) ≤ (lix w (cut L M) (cut L N) : ℝ) + (finrank K L : ℝ) * ((E : ℝ) - (vw w σ : ℝ)) + (finrank K L : ℝ) * (vw w (u : K) : ℝ)`. Conclude with `hmono` after adjusting the coercions. Establish `hc2 : (lix w (cut L M) (cut L N) : ℝ) ≤ lix w (cut Zψ M) (cut Zψ N)`. Conclude with `hcut2` after adjusting the coercions.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem idxPsiGood_of (hMono : IdxMono) (hSc : IdxScaleIn) (hCut : IdxCutLe) (hInt : LatInter) :
    IdxPsiGood := by
  unfold IdxPsiGood
  intro K _ _ _ Z _ _ _ _ _ w Zψ V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0Z σ hσ hThσ u hu
    hucut a E r ha hE hr δ hδ hδi
  have hVB := valuation_basic_properties K w

  have hcc : ∀ (W W' : Submodule K Z) (A : Submodule (𝓞 K) Z), W' ≤ W →
      cut W' (cut W A) = cut W' A := by
    intro W W' A hWW
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, hWW h3⟩, h3⟩
  set L : Submodule K Z := Zψ ⊓ V₀ with hL
  have hLZ : L ≤ Zψ := inf_le_left
  set N : Submodule (𝓞 K) Z := M ⊓ sc a⁻¹ Th with hN
  have hNl : IsLatIn ⊤ N := hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)
  have hNM : N ≤ M := inf_le_left
  have hX : IsLatIn L (cut L M) := (hCut K Z w ⊤ L M M hM hM le_rfl le_top).1
  have hB0 : IsLatIn L (cut L N) := (hCut K Z w ⊤ L N N hNl hNl le_rfl le_top).1
  have hMψ : IsLatIn Zψ (cut Zψ M) := (hCut K Z w ⊤ Zψ M M hM hM le_rfl le_top).1
  have hNψ : IsLatIn Zψ (cut Zψ N) := (hCut K Z w ⊤ Zψ N N hNl hNl le_rfl le_top).1
  have hThKψ : IsLatIn Zψ (cut Zψ ThK) := (hCut K Z w ⊤ Zψ ThK ThK hThK hThK le_rfl le_top).1
  have hu' : (u : K) ≠ 0 := by exact_mod_cast hu
  have hc : a * σ⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hσ)

  have hTh0 : IsLatIn Zψ Th0 := by
    show Th0.FG ∧ Submodule.span K (Th0 : Set Z) = Zψ
    refine ⟨hTh0fg, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.mpr (fun x hx => hTh0Z hx)
    · have h1 := (hSc K Z w Zψ (cut Zψ ThK) (cut Zψ ThK) hThKψ hThKψ (u : K) hu').1
      have h2 : Submodule.span K ((sc (u : K) (cut Zψ ThK) : Submodule (𝓞 K) Z) : Set Z) = Zψ :=
        h1.2
      rw [← h2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr hucut)
  have hcutTh0 : cut V₀ Th0 = cut L Th0 := by
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hL]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hTh0Z h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  have hT : IsLatIn L (cut V₀ Th0) := by
    rw [hcutTh0]
    exact (hCut K Z w Zψ L Th0 Th0 hTh0 hTh0 le_rfl hLZ).1
  refine ⟨hT, ?_⟩
  have hB1 := hSc K Z w L (cut L M) (cut L N) hX hB0 (a * σ⁻¹) hc
  have hB2 := hSc K Z w L (cut L M) (sc (a * σ⁻¹) (cut L N)) hX hB1.1 (u : K) hu'

  have hle2 : sc (u : K) (sc (a * σ⁻¹) (cut L N)) ≤ cut V₀ Th0 := by
    intro x hx
    rw [mem_sc] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_sc] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hN, hL] at hz ⊢
    obtain ⟨⟨_, hz2⟩, hzψ, hzV⟩ := hz
    rw [mem_sc] at hz2
    obtain ⟨t, ht, rfl⟩ := hz2
    obtain ⟨k, hk, rfl⟩ := (mem_sc σ ThK t).1 (hThσ ht)
    have hkey : (a * σ⁻¹) • a⁻¹ • σ • k = k := by
      rw [smul_smul, smul_smul]
      have h1 : a * σ⁻¹ * a⁻¹ * σ = 1 := by field_simp
      rw [h1, one_smul]
    have hkψ : k ∈ Zψ := by
      have h1 := Zψ.smul_mem (a * σ⁻¹) hzψ
      rwa [hkey] at h1
    have hkV : k ∈ V₀ := by
      have h1 := V₀.smul_mem (a * σ⁻¹) hzV
      rwa [hkey] at h1
    rw [hkey]
    have hkc : k ∈ cut Zψ ThK := by
      simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact ⟨hk, hkψ⟩
    exact ⟨hucut ((mem_sc _ _ _).2 ⟨k, hkc, rfl⟩), V₀.smul_mem _ hkV⟩
  have hmono := hMono K Z w L (cut L M) (sc (u : K) (sc (a * σ⁻¹) (cut L N))) (cut V₀ Th0)
    hX hB2.1 hT hle2
  have hNMψ : cut Zψ N ≤ cut Zψ M := by
    unfold cut
    exact inf_le_inf_right _ hNM
  have hcut2 := (hCut K Z w Zψ L (cut Zψ M) (cut Zψ N) hMψ hNψ hNMψ hLZ).2.2
  rw [hcc Zψ L M hLZ, hcc Zψ L N hLZ] at hcut2
  have hv : vw w (a * σ⁻¹) = (E : ℤ) - vw w σ := by
    rw [hVB.1 a σ⁻¹ ha (inv_ne_zero hσ), hVB.2.2.2.2.2.1 σ, hE]
    ring
  rw [hB2.2, hB1.2, hv] at hmono
  have h1 : (δ : ℝ) * (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (lix w M N : ℝ) + (finrank K Z : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hδi
  have hJ : (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (r + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)) / (δ : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hδ)]
    linarith
  have hm : (lix w (cut L M) (cut V₀ Th0) : ℝ) ≤ (lix w (cut L M) (cut L N) : ℝ) +
      (finrank K L : ℝ) * ((E : ℝ) - (vw w σ : ℝ)) + (finrank K L : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hmono
  have hc2 : (lix w (cut L M) (cut L N) : ℝ) ≤ lix w (cut Zψ M) (cut Zψ N) := by
    exact_mod_cast hcut2
  nlinarith

end Formalism.EigenvalueLevelCeiling
