import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

open MeasureTheory GlobalTheory.SplitWeil ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n r : ℕ}

/- English proof (translation)
Introduce `_ hy i l` and use `(hy i l).trans h`.
-/
theorem ballM_mono_loc {c c' : kˣ} (h : valuation k (c : k) ≤ valuation k (c' : k))
    (x : Matrix (Fin n) (Fin r) k) : ballM c x ⊆ ballM c' x :=
  fun _ hy i l => (hy i l).trans h

/- English proof (translation)
Introduce `i l`. Simplify using the standard rewrite rules.
-/
theorem mem_ballM_self_loc (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x := by
  intro i l
  simp

/- English proof (translation)
Take `⟨hlc, hcs⟩ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1` from `Φ.2`. Use `IsCompact.of_isClosed_subset hcs ?_ (subset_tsupport _)` and prove the remaining obligations. Establish `h` using `(hlc.isClopen_fiber 0).isOpen`. Rewrite using `[← isOpen_compl_iff]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Simplify using `[Function.mem_support]`.
-/
theorem isCompact_support_SB (Φ : SB (Matrix (Fin n) (Fin r) k)) :
    IsCompact (Function.support Φ.1) := by
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  refine IsCompact.of_isClosed_subset hcs ?_ (subset_tsupport _)
  have h := (hlc.isClopen_fiber 0).isOpen
  rw [← isOpen_compl_iff]
  convert h using 1
  ext x
  simp [Function.mem_support]

/- English proof (translation)
Introduce `k _ _ _ _ n r P Φ hΦ`. Take `⟨hball, hsmall, hdec⟩` from `hB k n r`. Establish `hpick : ∀ x : {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ, ∀ Ψ : SB (Matrix (Fin n) (Fin r) k), (∀ y, (Ψ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0 → y ∈ ballM c x.1 ∧ (Φ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0) → Ψ ∈ P`. Introduce `x`. Take `⟨U, hU, hxU, hP⟩` from `hΦ x.1 x.2`.

Take `⟨c, -, hc⟩` from `hsmall x.1 U (hU.mem_nhds hxU)`. Conclude with `⟨c, fun Ψ hΨ => hP Ψ fun y hy => ⟨hc (hΨ y hy).1, (hΨ y hy).2⟩⟩`. Use `choose cs hcs using hpick`. Take `⟨t, ht⟩` from `(isCompact_support_SB Φ).elim_finite_subcover (fun x => ballM (cs x) x.1) (fun x => (hball (cs x) x.1).1) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, mem_ballM_self_loc _ _⟩)`. Take `⟨c₀, hc₀⟩` from `hdec Φ`.

Establish `hmin : ∀ s : Finset {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ, valuation k (c : k) ≤ valuation k (c₀ : k) ∧ ∀ i ∈ s, valuation k (c : k) ≤ valuation k (cs i : k)`. Introduce `s`. Use `Finset.induction_on s ⟨c₀, le_rfl, by simp⟩ ?_` and prove the remaining obligations. Introduce `a s _ ih`. Take `⟨c, hc1, hc2⟩` from `ih`.

Break down `le_total (valuation k (c : k)) (valuation k (cs a : k)) with h | h` into its components or cases. Use `⟨c, hc1, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `h`.

Conclude with `hc2 i hi`. Use `⟨cs a, h.trans hc1, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `le_rfl`.

Conclude with `h.trans (hc2 i hi)`. Take `⟨c, hcc₀, hcci⟩` from `hmin t`. Take `⟨S, hS, hsum⟩` from `hc₀ c hcc₀`. Establish `hind : ∀ x, ((ballM c x).indicator fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k)` using `fun x => (hball c x).2.2.1`. Establish `hterm : ∀ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x • (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) ∈ P`.

Introduce `x hx`. Establish `hx0 : (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0` using `(hS x hx x (mem_ballM_self_loc c x)).2`. Take `⟨i, hi, hxi⟩` from `Set.mem_iUnion₂.1 (ht (show x ∈ Function.support (Φ : Matrix (Fin n) (Fin r) k → ℂ) from hx0))`. Establish `hsub : ballM c x ⊆ ballM (cs i) i.1`. Rewrite using `[← (hball (cs i) i.1).2.2.2.1 x hxi]`.

Conclude with `ballM_mono_loc (hcci i hi) x`. Apply `P.smul_mem` to reduce the goal to its premises. Apply `hcs i` to reduce the goal to its premises. Introduce `y hy`. Establish `hy' : y ∈ ballM c x`.

Assume the negation of the conclusion as `hn`. Conclude with `hy (by simp [Set.indicator, hn])`. Conclude with `⟨hsub hy', by rw [(hS x hx y hy').1]; exact hx0⟩`. Establish `hΦeq : Φ = ∑ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x • (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k))`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `hsum.trans ?_` and prove the remaining obligations. Simplify using `[Submodule.coe_sum, Submodule.coe_smul]`. Rewrite using `[hΦeq]`. Conclude with `P.sum_mem hterm`.
-/
theorem loc (hB : BallSt) : LocSt := by
  intro k _ _ _ _ n r P Φ hΦ
  obtain ⟨hball, hsmall, hdec⟩ := hB k n r
  have hpick : ∀ x : {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      ∀ Ψ : SB (Matrix (Fin n) (Fin r) k),
        (∀ y, (Ψ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0 →
          y ∈ ballM c x.1 ∧ (Φ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0) → Ψ ∈ P := by
    intro x
    obtain ⟨U, hU, hxU, hP⟩ := hΦ x.1 x.2
    obtain ⟨c, -, hc⟩ := hsmall x.1 U (hU.mem_nhds hxU)
    exact ⟨c, fun Ψ hΨ => hP Ψ fun y hy => ⟨hc (hΨ y hy).1, (hΨ y hy).2⟩⟩
  choose cs hcs using hpick
  obtain ⟨t, ht⟩ := (isCompact_support_SB Φ).elim_finite_subcover
    (fun x => ballM (cs x) x.1) (fun x => (hball (cs x) x.1).1)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, mem_ballM_self_loc _ _⟩)
  obtain ⟨c₀, hc₀⟩ := hdec Φ
  have hmin : ∀ s : Finset {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      valuation k (c : k) ≤ valuation k (c₀ : k) ∧
        ∀ i ∈ s, valuation k (c : k) ≤ valuation k (cs i : k) := by
    intro s
    classical
    refine Finset.induction_on s ⟨c₀, le_rfl, by simp⟩ ?_
    intro a s _ ih
    obtain ⟨c, hc1, hc2⟩ := ih
    rcases le_total (valuation k (c : k)) (valuation k (cs a : k)) with h | h
    · refine ⟨c, hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h
      · exact hc2 i hi
    · refine ⟨cs a, h.trans hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_rfl
      · exact h.trans (hc2 i hi)
  obtain ⟨c, hcc₀, hcci⟩ := hmin t
  obtain ⟨S, hS, hsum⟩ := hc₀ c hcc₀
  have hind : ∀ x, ((ballM c x).indicator fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) :=
    fun x => (hball c x).2.2.1
  have hterm : ∀ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) ∈ P := by
    intro x hx
    have hx0 : (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 := (hS x hx x (mem_ballM_self_loc c x)).2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht (show x ∈ Function.support (Φ : Matrix (Fin n) (Fin r) k → ℂ) from hx0))
    have hsub : ballM c x ⊆ ballM (cs i) i.1 := by
      rw [← (hball (cs i) i.1).2.2.2.1 x hxi]
      exact ballM_mono_loc (hcci i hi) x
    apply P.smul_mem
    apply hcs i
    intro y hy
    have hy' : y ∈ ballM c x := by
      by_contra hn
      exact hy (by simp [Set.indicator, hn])
    exact ⟨hsub hy', by rw [(hS x hx y hy').1]; exact hx0⟩
  have hΦeq : Φ = ∑ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) := by
    apply Subtype.ext
    refine hsum.trans ?_
    simp [Submodule.coe_sum, Submodule.coe_smul]
  rw [hΦeq]
  exact P.sum_mem hterm

end PositivityTheory.Rg.Ming
