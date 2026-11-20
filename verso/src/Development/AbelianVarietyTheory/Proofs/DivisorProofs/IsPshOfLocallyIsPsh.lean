import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshLimitIsPshStatement

namespace GlobalTheory.PshLocal

open ReciprocityTheory.AnForm.A Metric Filter Topology Set

/- English proof (translation)
Introduce `z hz`. Take `⟨V, hVo, hzV, hV⟩` from `h z hz`. Introduce `y hy`. Use `hV z hzV y hy` as an intermediate fact. Rewrite `this` using `[nhdsWithin_eq_nhds.2 (hVo.mem_nhds hzV)]`. Then use the resulting hypothesis.
-/
theorem usc_of_local {D : ℕ} (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ)
    (h : ∀ z ∈ U, ∃ V : Set (Fin D → ℂ), IsOpen V ∧ z ∈ V ∧ UpperSemicontinuousOn φ V) :
    ∀ z ∈ U, UpperSemicontinuousAt φ z := by
  intro z hz
  obtain ⟨V, hVo, hzV, hV⟩ := h z hz
  intro y hy
  have := hV z hzV y hy
  rwa [nhdsWithin_eq_nhds.2 (hVo.mem_nhds hzV)] at this

/- English proof (translation)
Conclude with `WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)`.
-/
theorem two_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

/- English proof (translation)
Introduce `D U φ hU hloc`. Set `ρ : Mollifier D` to `(mollifierInhabit_thm D).some`. Set `𝒱 : Type` to `{V : Set (Fin D → ℂ) // IsOpen V ∧ IsPsh V φ}`. Set `ε : ℕ → ℝ` to `fun n => 1 / ((n : ℝ) + 1)`. Establish `hε : ∀ n, 0 < ε n` using `fun n => by positivity`.

Set `Vn : ℕ → Set (Fin D → ℂ)` to `fun n => ⋃ V : 𝒱, shrink V.1 (ε n)`. Set `ψ : ℕ → (Fin D → ℂ) → ℝ` to `fun n => molli ρ (ε n) φ`. Establish `M1` using `fun (V : 𝒱) => mollify_thm D ρ V.1 φ V.2.1 V.2.2`. Establish `hopen : ∀ n, IsOpen (Vn n)` using `fun n => isOpen_iUnion fun V => ((M1 V).1 (ε n) (hε n)).1`. Establish `hpsh : ∀ n, IsPsh (Vn n) (ψ n)`.

Introduce `n`. Establish `hcd : ContDiffOn ℝ 2 (ψ n) (Vn n)`. Apply `contDiffOn_of_locally_contDiffOn` to reduce the goal to its premises. Introduce `x hx`. Take `⟨V, hxV⟩` from `mem_iUnion.1 hx`.

Take `⟨ho, hc, -, -⟩` from `(M1 V).1 (ε n) (hε n)`. Conclude with `⟨_, ho, hxV, (hc.of_le two_le_top).mono inter_subset_right⟩`. Use `(isPsh_iff_isLeviPsh_thm D _ _ (hopen n) hcd).2 ⟨hcd, fun z hz w => ?_⟩` and prove the remaining obligations. Take `⟨V, hzV⟩` from `mem_iUnion.1 hz`. Take `⟨ho, hc, hp, -⟩` from `(M1 V).1 (ε n) (hε n)`.

Establish `hc2 : ContDiffOn ℝ 2 (ψ n) (shrink V.1 (ε n))` using `hc.of_le two_le_top`. Conclude with `((isPsh_iff_isLeviPsh_thm D _ _ ho hc2).1 hp).2 z hzV w`. Establish `huscAt : ∀ z ∈ U, UpperSemicontinuousAt φ z` using `usc_of_local U φ fun z hz => by`. Take `⟨V, a, b, c⟩` from `hloc z hz`. Conclude with `⟨V, a, b, c.1⟩`.

Establish `husc : UpperSemicontinuousOn φ U` using `fun z hz => (huscAt z hz).upperSemicontinuousWithinAt U`. Use `GlobalTheory.T.psh_limit_is_psh D U φ ψ Vn hU husc hpsh ?_ ?_` and prove the remaining obligations. Introduce `K hK hKU`. Establish `hcov : K ⊆ ⋃ V : 𝒱, V.1` using `fun z hz => by`. Take `⟨V, a, b, c⟩` from `hloc z (hKU hz)`.

Conclude with `mem_iUnion.2 ⟨⟨V, a, c⟩, b⟩`. Take `⟨δ, hδ, hball⟩` from `lebesgue_number_lemma_of_metric hK (fun V : 𝒱 => V.2.1) hcov`. Establish `hδ2 : 0 ≤ δ / 2` using `by positivity`. Establish `hK'c : IsCompact (cthickening (δ / 2) K)` using `hK.cthickening`. Establish `huscK' : UpperSemicontinuousOn φ (cthickening (δ / 2) K)`.

Introduce `x hx`. Rewrite `hx` using `[hK.cthickening_eq_biUnion_closedBall hδ2]`. Take `⟨y, hyK, hxy⟩` from `mem_iUnion₂.1 hx`. Take `⟨V, hV⟩` from `hball y hyK`. Establish `hxV : x ∈ V.1` using `hV (closedBall_subset_ball (by linarith) hxy)`.

Establish `: UpperSemicontinuousAt φ x`. Introduce `t ht`. Use `V.2.2.1 x hxV t ht` as an intermediate fact. Rewrite `this` using `[nhdsWithin_eq_nhds.2 (V.2.1.mem_nhds hxV)]`. Then use the resulting hypothesis. Conclude with `this.upperSemicontinuousWithinAt _`.

Take `⟨M, hM⟩` from `huscK'.bddAbove_of_isCompact hK'c`. Take `⟨N, hN⟩` from `exists_nat_one_div_lt (by positivity : (0 : ℝ) < δ / 2)`. Use `⟨N, M, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hεn : ε n ≤ δ / 2`. Establish `: ε n ≤ ε N` using `Nat.one_div_le_one_div hn`.

Conclude with `this.trans hN.le`. Establish `key : ∀ z ∈ K, ∃ V : 𝒱, z ∈ shrink V.1 (ε n)` using `fun z hz => by`. Take `⟨V, hV⟩` from `hball z hz`. Conclude with `⟨V, (closedBall_subset_ball (by linarith)).trans hV⟩`. Use `⟨fun z hz => mem_iUnion.2 (key z hz), fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨V, hzV⟩` from `key z hz`. Establish `h1 : ψ n z ≤ polyMax φ z (ε n)` using `(((M1 V).1 (ε n) (hε n)).2.2.2 z hzV).2`. Use `h1.trans (csSup_le ⟨φ z, mem_image_of_mem _ (mem_closedBall_self (hε n).le)⟩ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hM (mem_image_of_mem _ (closedBall_subset_cthickening hz (δ / 2) (closedBall_subset_closedBall hεn hx)))`.

Introduce `z hz`. Take `⟨V, a, b, c⟩` from `hloc z hz`. Use `((M1 ⟨V, a, c⟩).2 z b).comp ?_` and prove the remaining obligations. Conclude with `tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => hε n⟩`.
-/
theorem isPsh_of_local : ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U →
    (∀ z ∈ U, ∃ V : Set (Fin D → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) →
    ReciprocityTheory.AnForm.A.IsPsh U φ := by
  intro D U φ hU hloc
  classical
  let ρ : Mollifier D := (mollifierInhabit_thm D).some
  let 𝒱 : Type := {V : Set (Fin D → ℂ) // IsOpen V ∧ IsPsh V φ}
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  let Vn : ℕ → Set (Fin D → ℂ) := fun n => ⋃ V : 𝒱, shrink V.1 (ε n)
  let ψ : ℕ → (Fin D → ℂ) → ℝ := fun n => molli ρ (ε n) φ
  have M1 := fun (V : 𝒱) => mollify_thm D ρ V.1 φ V.2.1 V.2.2
  have hopen : ∀ n, IsOpen (Vn n) := fun n => isOpen_iUnion fun V => ((M1 V).1 (ε n) (hε n)).1

  have hpsh : ∀ n, IsPsh (Vn n) (ψ n) := by
    intro n
    have hcd : ContDiffOn ℝ 2 (ψ n) (Vn n) := by
      apply contDiffOn_of_locally_contDiffOn
      intro x hx
      obtain ⟨V, hxV⟩ := mem_iUnion.1 hx
      obtain ⟨ho, hc, -, -⟩ := (M1 V).1 (ε n) (hε n)
      exact ⟨_, ho, hxV, (hc.of_le two_le_top).mono inter_subset_right⟩
    refine (isPsh_iff_isLeviPsh_thm D _ _ (hopen n) hcd).2 ⟨hcd, fun z hz w => ?_⟩
    obtain ⟨V, hzV⟩ := mem_iUnion.1 hz
    obtain ⟨ho, hc, hp, -⟩ := (M1 V).1 (ε n) (hε n)
    have hc2 : ContDiffOn ℝ 2 (ψ n) (shrink V.1 (ε n)) := hc.of_le two_le_top
    exact ((isPsh_iff_isLeviPsh_thm D _ _ ho hc2).1 hp).2 z hzV w
  have huscAt : ∀ z ∈ U, UpperSemicontinuousAt φ z :=
    usc_of_local U φ fun z hz => by
      obtain ⟨V, a, b, c⟩ := hloc z hz
      exact ⟨V, a, b, c.1⟩
  have husc : UpperSemicontinuousOn φ U := fun z hz =>
    (huscAt z hz).upperSemicontinuousWithinAt U
  refine GlobalTheory.T.psh_limit_is_psh D U φ ψ Vn hU husc hpsh ?_ ?_
  · intro K hK hKU
    have hcov : K ⊆ ⋃ V : 𝒱, V.1 := fun z hz => by
      obtain ⟨V, a, b, c⟩ := hloc z (hKU hz)
      exact mem_iUnion.2 ⟨⟨V, a, c⟩, b⟩
    obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hK (fun V : 𝒱 => V.2.1) hcov
    have hδ2 : 0 ≤ δ / 2 := by positivity
    have hK'c : IsCompact (cthickening (δ / 2) K) := hK.cthickening
    have huscK' : UpperSemicontinuousOn φ (cthickening (δ / 2) K) := by
      intro x hx
      rw [hK.cthickening_eq_biUnion_closedBall hδ2] at hx
      obtain ⟨y, hyK, hxy⟩ := mem_iUnion₂.1 hx
      obtain ⟨V, hV⟩ := hball y hyK
      have hxV : x ∈ V.1 := hV (closedBall_subset_ball (by linarith) hxy)
      have : UpperSemicontinuousAt φ x := by
        intro t ht
        have := V.2.2.1 x hxV t ht
        rwa [nhdsWithin_eq_nhds.2 (V.2.1.mem_nhds hxV)] at this
      exact this.upperSemicontinuousWithinAt _
    obtain ⟨M, hM⟩ := huscK'.bddAbove_of_isCompact hK'c
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < δ / 2)
    refine ⟨N, M, fun n hn => ?_⟩
    have hεn : ε n ≤ δ / 2 := by
      have : ε n ≤ ε N := Nat.one_div_le_one_div hn
      exact this.trans hN.le
    have key : ∀ z ∈ K, ∃ V : 𝒱, z ∈ shrink V.1 (ε n) := fun z hz => by
      obtain ⟨V, hV⟩ := hball z hz
      exact ⟨V, (closedBall_subset_ball (by linarith)).trans hV⟩
    refine ⟨fun z hz => mem_iUnion.2 (key z hz), fun z hz => ?_⟩
    obtain ⟨V, hzV⟩ := key z hz
    have h1 : ψ n z ≤ polyMax φ z (ε n) := (((M1 V).1 (ε n) (hε n)).2.2.2 z hzV).2
    refine h1.trans (csSup_le ⟨φ z, mem_image_of_mem _ (mem_closedBall_self (hε n).le)⟩ ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hM (mem_image_of_mem _
      (closedBall_subset_cthickening hz (δ / 2) (closedBall_subset_closedBall hεn hx)))
  · intro z hz
    obtain ⟨V, a, b, c⟩ := hloc z hz
    refine ((M1 ⟨V, a, c⟩).2 z b).comp ?_
    exact tendsto_nhdsWithin_iff.2
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => hε n⟩

end GlobalTheory.PshLocal
