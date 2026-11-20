import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.BlockHyp

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ S _ _ π m hm horth M N hMfg hNfg hMsp hNsp hMint hNint`. Use `haveI : FiniteDimensional K V := by`. Take `⟨s, hs⟩` from `hMfg`. Use `Module.finite_def.mpr ⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[← hMsp, ← hs, Submodule.span_span_of_tower]`.

Use `set P : V →ₗ[K] V := ∑ t, π t with hP`. Establish `hcomp : ∀ s t z, π s (π t z) = if s = t then π t z else 0`. Introduce `s t z`. Use `congrArg (fun f => f z) (horth s t)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`.

Rewrite using `[this]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Both sides reduce to the same expression.

Establish `hPπ : ∀ s z, P (π s z) = π s z`. Introduce `s z`. Rewrite using `[hP, LinearMap.sum_apply]`. Simplify using `only [hcomp]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ s]`.

Simplify using the standard rewrite rules. Establish `hYs : ∀ s, LinearMap.range (π s) ≤ LinearMap.range P`. Introduce and unpack `s _ ⟨z, rfl⟩`. Conclude with `⟨π s z, hPπ s z⟩`. Establish `hdec : ∀ y ∈ LinearMap.range P, y = ∑ s, π s y`.

Introduce and unpack `_ ⟨z, rfl⟩`. Establish `: ∀ s, π s (P z) = π s z`. Introduce `s`. Rewrite using `[hP, LinearMap.sum_apply, map_sum]`. Simplify using `only [hcomp]`.

Rewrite using `[Finset.sum_ite_eq Finset.univ s]`. Simplify using the standard rewrite rules. Simplify using `only [this]`. Rewrite using `[hP, LinearMap.sum_apply]`. Establish `hfix : ∀ s t y, y ∈ LinearMap.range (π s) → π t y = if t = s then y else 0`.

Introduce and unpack `s t _ ⟨z, rfl⟩`. Rewrite using `[hcomp]`. Use `set σ : (S → V) →ₗ[K] V := ∑ s, LinearMap.proj s with hσd`. Establish `hσ : ∀ x : S → V, σ x = ∑ s, x s` using `fun x => by simp [hσd, LinearMap.sum_apply]`. Use `set YS : Submodule K (S → V) := Submodule.pi Set.univ fun s => LinearMap.range (π s) with hYS`.

Establish `hσinj : ∀ x ∈ YS, σ x = 0 → x = 0`. Introduce `x hx h0`. Use function extensionality and compare the values at `t`. Establish `: π t (σ x) = x t`. Rewrite using `[hσ, map_sum]`.

Simplify using `only [fun s => hfix s t (x s) (hx s (Set.mem_univ s))]`. Rewrite using `[Finset.sum_ite_eq Finset.univ t]`. Simplify using the standard rewrite rules. Rewrite using `[← this, h0, map_zero]`. Both sides reduce to the same expression.

Establish `hσmap : YS.map σ = LinearMap.range P`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[hσ]`. Conclude with `Submodule.sum_mem _ fun s _ => hYs s (hx s (Set.mem_univ s))`.

Introduce `y hy`. Use `⟨fun s => π s y, fun s _ => ⟨y, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hσ]`. Conclude with `(hdec y hy).symm`. Establish `hrk : ∀ L : Submodule (𝓞 K) V, Submodule.span K (L : Set V) = ⊤ → Formalism.HN.rkK (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K)) = ∑ s, Formalism.HN.rkK (L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))`.

Introduce `L hL`. Rewrite using `[rk_cut L hL]`. Simplify using `only [rk_cut L hL]`. Set `f : (∀ s, LinearMap.range (π s)) →ₗ[K] LinearMap.range P` to `LinearMap.codRestrict _ (σ ∘ₗ LinearMap.pi (fun s => (LinearMap.range (π s)).subtype ∘ₗ LinearMap.proj s)) (fun x => by`. Rewrite using `[← hσmap]`.

Conclude with `⟨_, fun s _ => (x s).2, rfl⟩)`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `h` using `congrArg Subtype.val hxy`.

Simplify using `only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply] at h`. Rewrite `h` using `[← sub_eq_zero, ← map_sub]`. Use `hσinj _ (Submodule.sub_mem _ (fun s _ => (x s).2) (fun s _ => (y s).2)) h` as an intermediate fact. Use function extensionality and compare the values at `s`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `congrFun this s` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Introduce and unpack `⟨y, hy⟩`. Use `⟨fun s => ⟨π s y, y, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply]`. Rewrite using `[hσ]`. Conclude with `(hdec y hy).symm`. Rewrite using `[← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]`. Use `⟨hrk M hMsp, fun w => ?_⟩` and prove the remaining obligations.

Establish `side : ∀ L : Submodule (𝓞 K) V, L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ s, ∀ x ∈ L, x ∈ LinearMap.range P → ((m : ℕ) : 𝓞 K) • π s x ∈ L) → ((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map (σ.restrictScalars (𝓞 K))).FG ∧ Submodule.span K …`. Introduce `L hL hLsp hLint`. Establish `fgpi : (Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).FG` using `Submodule.fg_pi fun s => fg_cut L hL _`. Establish `hsp : Submodule.span K (((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map (σ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = LinearMap.range P`. Rewrite using `[Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, span_pi_eq]`.

Simplify using `only [cut_span L hLsp]`. Conclude with `hσmap`. Establish `hle : (Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map (σ.restrictScalars (𝓞 K)) ≤ L ⊓ (LinearMap.range P).restrictScalars (𝓞 K)`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Simplify using `only [LinearMap.coe_restrictScalars]`.

Rewrite using `[hσ]`. Use `Submodule.mem_inf.mpr ⟨L.sum_mem fun s _ => (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).1, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun s _ => hYs s (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).2`. Establish `hfgY` using `fg_cut L hL (LinearMap.range P)`. Establish `hspY` using `cut_span L hLsp (LinearMap.range P)`.

Use `⟨fgpi.map _, hsp, idx_nonneg_of_le hI w _ _ hfgY (fgpi.map _) (hspY.trans hsp.symm) hle, idx_le_nat hI w _ _ hfgY (fgpi.map _) (hspY.trans hsp.symm) m hm hle ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx'` using `Submodule.mem_inf.mp hx`. Use `⟨fun s => ((m : ℕ) : 𝓞 K) • π s x, fun s _ => Submodule.mem_inf.mpr ⟨hLint s x hx'.1 hx'.2, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem]`.

Use `⟨((m : ℕ) : K) • x, ?_⟩` and prove the remaining obligations. Use `show π s (((m : ℕ) : K) • x) = ((m : ℕ) : 𝓞 K) • π s x`. Rewrite using `[map_smul, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K)]`. Simplify using `only [LinearMap.coe_restrictScalars]`. Rewrite using `[hσ, ← Finset.smul_sum, ← hdec x hx'.2]`.

Take `⟨fgA, spA, hA0, hA1⟩` from `side M hMfg hMsp hMint`. Take `⟨fgB, spB, hB0, hB1⟩` from `side N hNfg hNsp hNint`. Rewrite `hB1` using `[rk_cut N hNsp (LinearMap.range P), ← rk_cut M hMsp (LinearMap.range P)]`. Use `set MY := M ⊓ (LinearMap.range P).restrictScalars (𝓞 K)`. Use `set NY := N ⊓ (LinearMap.range P).restrictScalars (𝓞 K)`.

Use `set A := (Submodule.pi Set.univ fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map (σ.restrictScalars (𝓞 K))`. Use `set B := (Submodule.pi Set.univ fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map (σ.restrictScalars (𝓞 K))`. Establish `fgMY` using `fg_cut M hMfg (LinearMap.range P)`. Establish `fgNY` using `fg_cut N hNfg (LinearMap.range P)`. Establish `sMY` using `cut_span M hMsp (LinearMap.range P)`.

Establish `sNY` using `cut_span N hNsp (LinearMap.range P)`. Establish `c1` using `idx_chain hI w MY A NY fgMY fgA fgNY (sMY.trans spA.symm) (sNY.trans spA.symm)`. Establish `c2` using `idx_chain hI w A B NY fgA fgB fgNY (spA.trans spB.symm) (sNY.trans spB.symm)`. Establish `hmemYS : ∀ L : Submodule (𝓞 K) V, ∀ x ∈ Submodule.pi Set.univ (fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)), x ∈ YS` using `fun L x hx s _ => (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).2`. Establish `c3` using `idx_map_inj hI w σ (Submodule.pi Set.univ fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (Submodule.pi Set.univ fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (Submodule.fg_pi fun s => fg_cut M hMfg _) (Submodule.fg_pi fun s => fg_cut N hNfg _) (by rw [s …`.

Establish `c4` using `idx_pi hI w (fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (fun s => fg_cut M hMfg _) (fun s => fg_cut N hNfg _) (fun s => by rw [cut_span M hMsp, cut_span N hNsp])`. Establish `c5 : idxAt w B NY = -idxAt w NY B` using `idx_anti w B NY`. Establish `key : idxAt w MY NY = idxAt w MY A + (∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))) - idxAt w NY B`. Rewrite using `[c1, c2, c5, ← c3, c4]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hD1 : -((Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K)) ≤ idxAt w MY NY - ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))` using `by rw [key]; linarith`. Establish `hD2 : idxAt w MY NY - ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) ≤ (Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K)`. Rewrite using `[key]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin : |((idxAt w MY NY - ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) : ℤ) : ℝ)| ≤ (((Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K) : ℤ) : ℝ)`.

Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Conclude with `hD1` after adjusting the coercions. Conclude with `hD2` after adjusting the coercions. Move the coercions through the operations in `at hfin`.

Conclude with `hfin`.
-/
theorem sum_index_formula (hI : IdxCalc) : SumIdx := by
  intro K _ _ V _ _ _ _ S _ _ π m hm horth M N hMfg hNfg hMsp hNsp hMint hNint
  haveI : FiniteDimensional K V := by
    obtain ⟨s, hs⟩ := hMfg
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [← hMsp, ← hs, Submodule.span_span_of_tower]
  set P : V →ₗ[K] V := ∑ t, π t with hP
  have hcomp : ∀ s t z, π s (π t z) = if s = t then π t z else 0 := by
    intro s t z
    have := congrArg (fun f => f z) (horth s t)
    simp only [LinearMap.comp_apply] at this
    rw [this]; split_ifs with h
    · subst h; rfl
    · rfl
  have hPπ : ∀ s z, P (π s z) = π s z := by
    intro s z
    rw [hP, LinearMap.sum_apply]
    simp only [hcomp]
    rw [Finset.sum_ite_eq' Finset.univ s]; simp
  have hYs : ∀ s, LinearMap.range (π s) ≤ LinearMap.range P := by
    rintro s _ ⟨z, rfl⟩; exact ⟨π s z, hPπ s z⟩
  have hdec : ∀ y ∈ LinearMap.range P, y = ∑ s, π s y := by
    rintro _ ⟨z, rfl⟩
    have : ∀ s, π s (P z) = π s z := by
      intro s
      rw [hP, LinearMap.sum_apply, map_sum]
      simp only [hcomp]
      rw [Finset.sum_ite_eq Finset.univ s]; simp
    simp only [this]
    rw [hP, LinearMap.sum_apply]
  have hfix : ∀ s t y, y ∈ LinearMap.range (π s) → π t y = if t = s then y else 0 := by
    rintro s t _ ⟨z, rfl⟩
    rw [hcomp]

  set σ : (S → V) →ₗ[K] V := ∑ s, LinearMap.proj s with hσd
  have hσ : ∀ x : S → V, σ x = ∑ s, x s := fun x => by simp [hσd, LinearMap.sum_apply]
  set YS : Submodule K (S → V) := Submodule.pi Set.univ fun s => LinearMap.range (π s) with hYS
  have hσinj : ∀ x ∈ YS, σ x = 0 → x = 0 := by
    intro x hx h0
    funext t
    have : π t (σ x) = x t := by
      rw [hσ, map_sum]
      simp only [fun s => hfix s t (x s) (hx s (Set.mem_univ s))]
      rw [Finset.sum_ite_eq Finset.univ t]; simp
    rw [← this, h0, map_zero]; rfl
  have hσmap : YS.map σ = LinearMap.range P := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hσ]
      exact Submodule.sum_mem _ fun s _ => hYs s (hx s (Set.mem_univ s))
    · intro y hy
      refine ⟨fun s => π s y, fun s _ => ⟨y, rfl⟩, ?_⟩
      rw [hσ]; exact (hdec y hy).symm
  have hrk : ∀ L : Submodule (𝓞 K) V, Submodule.span K (L : Set V) = ⊤ →
      Formalism.HN.rkK (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K)) =
        ∑ s, Formalism.HN.rkK (L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) := by
    intro L hL
    rw [rk_cut L hL]
    simp only [rk_cut L hL]
    let f : (∀ s, LinearMap.range (π s)) →ₗ[K] LinearMap.range P := LinearMap.codRestrict _
      (σ ∘ₗ LinearMap.pi (fun s => (LinearMap.range (π s)).subtype ∘ₗ LinearMap.proj s))
      (fun x => by
        rw [← hσmap]; exact ⟨_, fun s _ => (x s).2, rfl⟩)
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have h := congrArg Subtype.val hxy
        simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply] at h
        rw [← sub_eq_zero, ← map_sub] at h
        have := hσinj _ (Submodule.sub_mem _ (fun s _ => (x s).2) (fun s _ => (y s).2)) h
        funext s
        apply Subtype.ext
        have := congrFun this s
        simpa [sub_eq_zero] using this
      · rintro ⟨y, hy⟩
        refine ⟨fun s => ⟨π s y, y, rfl⟩, ?_⟩
        apply Subtype.ext
        simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply]
        rw [hσ]
        exact (hdec y hy).symm
    rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]
  refine ⟨hrk M hMsp, fun w => ?_⟩

  have side : ∀ L : Submodule (𝓞 K) V, L.FG → Submodule.span K (L : Set V) = ⊤ →
      (∀ s, ∀ x ∈ L, x ∈ LinearMap.range P → ((m : ℕ) : 𝓞 K) • π s x ∈ L) →
      ((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K))).FG ∧
      Submodule.span K (((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = LinearMap.range P ∧
      0 ≤ idxAt w (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K))
        ((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K))) ∧
      idxAt w (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K))
        ((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K))) ≤
        (Formalism.HN.rkK (L ⊓ (LinearMap.range P).restrictScalars (𝓞 K)) : ℤ) * vAdd w ((m : ℕ) : K) := by
    intro L hL hLsp hLint
    have fgpi : (Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).FG :=
      Submodule.fg_pi fun s => fg_cut L hL _
    have hsp : Submodule.span K (((Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
          (σ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = LinearMap.range P := by
      rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, span_pi_eq]
      simp only [cut_span L hLsp]
      exact hσmap
    have hle : (Submodule.pi Set.univ fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
        (σ.restrictScalars (𝓞 K)) ≤ L ⊓ (LinearMap.range P).restrictScalars (𝓞 K) := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [LinearMap.coe_restrictScalars]
      rw [hσ]
      refine Submodule.mem_inf.mpr ⟨L.sum_mem fun s _ => (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).1, ?_⟩
      exact Submodule.sum_mem _ fun s _ => hYs s (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).2
    have hfgY := fg_cut L hL (LinearMap.range P)
    have hspY := cut_span L hLsp (LinearMap.range P)
    refine ⟨fgpi.map _, hsp, idx_nonneg_of_le hI w _ _ hfgY (fgpi.map _) (hspY.trans hsp.symm) hle,
      idx_le_nat hI w _ _ hfgY (fgpi.map _) (hspY.trans hsp.symm) m hm hle ?_⟩
    intro x hx
    have hx' := Submodule.mem_inf.mp hx
    refine ⟨fun s => ((m : ℕ) : 𝓞 K) • π s x, fun s _ => Submodule.mem_inf.mpr ⟨hLint s x hx'.1 hx'.2, ?_⟩, ?_⟩
    · rw [Submodule.restrictScalars_mem]
      refine ⟨((m : ℕ) : K) • x, ?_⟩
      show π s (((m : ℕ) : K) • x) = ((m : ℕ) : 𝓞 K) • π s x
      rw [map_smul, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K)]
    · simp only [LinearMap.coe_restrictScalars]
      rw [hσ, ← Finset.smul_sum, ← hdec x hx'.2]
  obtain ⟨fgA, spA, hA0, hA1⟩ := side M hMfg hMsp hMint
  obtain ⟨fgB, spB, hB0, hB1⟩ := side N hNfg hNsp hNint
  rw [rk_cut N hNsp (LinearMap.range P), ← rk_cut M hMsp (LinearMap.range P)] at hB1
  set MY := M ⊓ (LinearMap.range P).restrictScalars (𝓞 K)
  set NY := N ⊓ (LinearMap.range P).restrictScalars (𝓞 K)
  set A := (Submodule.pi Set.univ fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
    (σ.restrictScalars (𝓞 K))
  set B := (Submodule.pi Set.univ fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)).map
    (σ.restrictScalars (𝓞 K))
  have fgMY := fg_cut M hMfg (LinearMap.range P)
  have fgNY := fg_cut N hNfg (LinearMap.range P)
  have sMY := cut_span M hMsp (LinearMap.range P)
  have sNY := cut_span N hNsp (LinearMap.range P)
  have c1 := idx_chain hI w MY A NY fgMY fgA fgNY (sMY.trans spA.symm) (sNY.trans spA.symm)
  have c2 := idx_chain hI w A B NY fgA fgB fgNY (spA.trans spB.symm) (sNY.trans spB.symm)
  have hmemYS : ∀ L : Submodule (𝓞 K) V, ∀ x ∈ Submodule.pi Set.univ
      (fun s => L ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)), x ∈ YS :=
    fun L x hx s _ => (Submodule.mem_inf.mp (hx s (Set.mem_univ s))).2
  have c3 := idx_map_inj hI w σ (Submodule.pi Set.univ fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
    (Submodule.pi Set.univ fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
    (Submodule.fg_pi fun s => fg_cut M hMfg _) (Submodule.fg_pi fun s => fg_cut N hNfg _)
    (by rw [span_pi_eq, span_pi_eq]; simp only [cut_span M hMsp, cut_span N hNsp])
    (fun x hx h0 => hσinj x (hmemYS M x hx) h0) (fun x hx h0 => hσinj x (hmemYS N x hx) h0)
  have c4 := idx_pi hI w (fun s => M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
    (fun s => N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) (fun s => fg_cut M hMfg _)
    (fun s => fg_cut N hNfg _) (fun s => by rw [cut_span M hMsp, cut_span N hNsp])
  have c5 : idxAt w B NY = -idxAt w NY B := idx_anti w B NY
  have key : idxAt w MY NY = idxAt w MY A +
      (∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))) - idxAt w NY B := by
    rw [c1, c2, c5, ← c3, c4]; ring
  have hD1 : -((Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K)) ≤ idxAt w MY NY -
      ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) := by rw [key]; linarith
  have hD2 : idxAt w MY NY - ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) ≤ (Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K) := by
    rw [key]; linarith
  have hfin : |((idxAt w MY NY - ∑ s, idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
        (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) : ℤ) : ℝ)| ≤
      (((Formalism.HN.rkK MY : ℤ) * vAdd w ((m : ℕ) : K) : ℤ) : ℝ) := by
    rw [abs_le]; constructor
    · exact_mod_cast hD1
    · exact_mod_cast hD2
  push_cast at hfin
  exact hfin

end PI.Dv.TIW
