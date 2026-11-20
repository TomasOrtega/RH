import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FrameTrans

/- English proof (translation)
Use extensionality with `a b`. Establish `hb` using `congrFun h b`. Simplify using `only [colFrame] at hb`. Establish `h0` using `Fintype.linearIndependent_iff.1 he (fun a => T a b - T' a b) (by simp only [sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.2 hb) a`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem colFrame_injective {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {e : Fin r → V}
    (he : LinearIndependent Ω e) {T T' : Matrix (Fin r) (Fin r) Ω} (h : colFrame e T = colFrame e T') : T = T' := by
  ext a b
  have hb := congrFun h b
  simp only [colFrame] at hb
  have h0 := Fintype.linearIndependent_iff.1 he (fun a => T a b - T' a b)
    (by simp only [sub_smul, Finset.sum_sub_distrib]; exact sub_eq_zero.2 hb) a
  exact sub_eq_zero.1 h0

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hsum : ∑ a, (g.mulVec c a) • w a = 0`. Rewrite using `[← hc]`. Simplify using `only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]`. Establish `h0 : g.mulVec c = 0` using `funext (Fintype.linearIndependent_iff.1 hw _ hsum)`. Establish `hc0 : c = 0` using `Matrix.eq_zero_of_mulVec_eq_zero hg.ne_zero h0`. Introduce `i`.

Rewrite using `[hc0]`. Both sides reduce to the same expression.
-/
theorem linearIndependent_colFrame {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {w : Fin r → V}
    (hw : LinearIndependent Ω w) {g : Matrix (Fin r) (Fin r) Ω} (hg : IsUnit g.det) :
    LinearIndependent Ω (colFrame w g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : ∑ a, (g.mulVec c a) • w a = 0 := by
    rw [← hc]
    simp only [colFrame, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [_root_.mul_comm]
  have h0 : g.mulVec c = 0 := funext (Fintype.linearIndependent_iff.1 hw _ hsum)
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hg.ne_zero h0
  intro i
  rw [hc0]
  rfl

/- English proof (translation)
Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 h`. Conclude with `⟨fun k => (a k : Ω), fun k => (a k).2, ha.symm⟩`.
-/
theorem exists_regular_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {p : Cpt ξ} {r : ℕ} {e : Fin r → E} {v : E}
    (h : v ∈ Submodule.span (regAt ξ p) (Set.range e)) :
    ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ v = ∑ a, c a • e a := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  exact ⟨fun k => (a k : Ω), fun k => (a k).2, ha.symm⟩

/- English proof (translation)
Establish `hex : ∀ l : Fin r, ∃ f : Fin r → Ω, (∀ k : Fin r, ¬ (k : ℕ) < (l : ℕ) + 1 → f k = 0) ∧ b l = ∑ k, f k • b₀ k`. Introduce `l`. Establish `h1 : b l ∈ flagStep Ω b₀ ((l : ℕ) + 1)`. Rewrite using `[← hF]`. Conclude with `Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩`.

Take `⟨f, hf, hs⟩` from `(Finsupp.mem_span_image_iff_linearCombination Ω).1 h1`. Use `⟨f, fun k hk => (Finsupp.mem_supported' Ω f).1 hf k hk, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs, Finsupp.linearCombination_apply]`. Conclude with `Finsupp.sum_fintype f (fun i a => a • b₀ i) (fun k => zero_smul Ω _)`. Use `choose f hf0 hf using hex`.

Use `⟨fun k l => f l k, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Use `hf0 j i ?_` and prove the remaining obligations. Establish `: (j : ℕ) < i` using `hij'`.

Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `l`. Conclude with `hf l`.
-/
theorem exists_triangular {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b₀ : Fin r → V}
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) :
    ∃ U : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ b = colFrame b₀ U := by
  have hex : ∀ l : Fin r, ∃ f : Fin r → Ω, (∀ k : Fin r, ¬ (k : ℕ) < (l : ℕ) + 1 → f k = 0) ∧
      b l = ∑ k, f k • b₀ k := by
    intro l
    have h1 : b l ∈ flagStep Ω b₀ ((l : ℕ) + 1) := by
      rw [← hF]
      exact Submodule.subset_span ⟨l, Nat.lt_succ_self _, rfl⟩
    obtain ⟨f, hf, hs⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
    refine ⟨f, fun k hk => (Finsupp.mem_supported' Ω f).1 hf k hk, ?_⟩
    rw [← hs, Finsupp.linearCombination_apply]
    exact Finsupp.sum_fintype f (fun i a => a • b₀ i) (fun k => zero_smul Ω _)
  choose f hf0 hf using hex
  refine ⟨fun k l => f l k, ?_, ?_⟩
  · intro i j hij
    have hij' : j < i := hij
    refine hf0 j i ?_
    have : (j : ℕ) < i := hij'
    omega
  · funext l
    exact hf l

/- English proof (translation)
Establish `h : colFrame b₀ U l - U l l • b₀ l = ∑ a ∈ Finset.univ.erase l, U a l • b₀ a`. Rewrite using `[colFrame, ← Finset.add_sum_erase _ _ (Finset.mem_univ l), add_sub_cancel_left]`. Rewrite using `[h]`. Use `Submodule.sum_mem _ fun a ha => ?_` and prove the remaining obligations. Establish `hne : a ≠ l` using `Finset.ne_of_mem_erase ha`.

Distinguish the cases in `hlt : (a : ℕ) < l`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hlt, rfl⟩)`. Establish `hla : l < a` using `lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)`. Rewrite using `[hU hla, zero_smul]`. Conclude with `zero_mem _`.
-/
theorem sub_diag_mem {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} (b₀ : Fin r → V)
    {U : Matrix (Fin r) (Fin r) Ω} (hU : U.BlockTriangular id) (l : Fin r) :
    colFrame b₀ U l - U l l • b₀ l ∈ flagStep Ω b₀ l := by
  have h : colFrame b₀ U l - U l l • b₀ l = ∑ a ∈ Finset.univ.erase l, U a l • b₀ a := by
    rw [colFrame, ← Finset.add_sum_erase _ _ (Finset.mem_univ l), add_sub_cancel_left]
  rw [h]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hne : a ≠ l := Finset.ne_of_mem_erase ha
  by_cases hlt : (a : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, hlt, rfl⟩)
  · have hla : l < a := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
    rw [hU hla, zero_smul]
    exact zero_mem _

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ L r w P g p hw hg he hFl`. Take `⟨V, hV, b, hbF, hbL⟩` from `hFl p (Set.mem_univ p)`. Establish `hb : L.IsFrameAt b p` using `hbL p (Set.mem_univ p) hV`. Establish `hb₀` using `linearIndependent_colFrame hw hg`. Take `⟨U, hU, hbU⟩` from `exists_triangular hbF`.

Establish `hexR : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ b l = ∑ a, c a • colFrame w P a`. Introduce `l`. Use `exists_regular_coeff ?_` and prove the remaining obligations. Rewrite using `[← he.2, hb.2]`. Conclude with `Submodule.subset_span ⟨l, rfl⟩`.

Establish `hexR' : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ colFrame w P l = ∑ a, c a • b a`. Introduce `l`. Use `exists_regular_coeff ?_` and prove the remaining obligations. Rewrite using `[← hb.2, he.2]`. Conclude with `Submodule.subset_span ⟨l, rfl⟩`.

Use `choose c hc hcs using hexR`. Use `choose c' hc' hcs' using hexR'`. Take `⟨Rm, hRm, hbR⟩ : ∃ Rm : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm a l ∈ regAt ξ p) ∧ b = colFrame (colFrame w P) Rm` from `⟨fun a l => c l a, fun a l => hc l a, funext hcs⟩`. Take `⟨Rm', hRm', heR⟩ : ∃ Rm' : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm' a l ∈ regAt ξ p) ∧ colFrame w P = colFrame b Rm'` from `⟨fun a l => c' l a, fun a l => hc' l a, funext hcs'⟩`. Use `⟨U, Rm, Rm', hU, hRm, hRm', ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `colFrame_injective he.1 ?_` and prove the remaining obligations. Rewrite using `[colFrame_mul, ← hbR, ← heR, colFrame_one]`. Use `colFrame_injective hw ?_` and prove the remaining obligations. Rewrite using `[colFrame_mul, colFrame_mul, ← hbU, ← hbR]`. Introduce `l`.

Use `FlagGrGen.gr_isGenAt X Ω ξ E L r (colFrame w g) b p l (U l l) hb₀ hbF hb ?_` and prove the remaining obligations. Rewrite using `[hbU]`. Conclude with `sub_diag_mem _ hU l`.
-/
theorem exists_adapted : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (w : Fin r → E) (P g : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω w → IsUnit g.det → L.IsFrameAt (colFrame w P) p → L.IsFlagVBOn Set.univ (colFrame w g) → ∃ U Rm Rm' : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ (∀ a b, Rm a b ∈ regAt ξ p) ∧ (∀ a b, Rm' a b ∈ regAt ξ p) ∧ Rm * Rm' = 1 ∧ g * U = P * Rm ∧ ∀ l, (L.gr (colFrame w g) l).IsGenAt p (U l l) := by
  intro X Ω _ ξ E _ _ L r w P g p hw hg he hFl
  obtain ⟨V, hV, b, hbF, hbL⟩ := hFl p (Set.mem_univ p)
  have hb : L.IsFrameAt b p := hbL p (Set.mem_univ p) hV
  have hb₀ := linearIndependent_colFrame hw hg
  obtain ⟨U, hU, hbU⟩ := exists_triangular hbF
  have hexR : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ b l = ∑ a, c a • colFrame w P a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← he.2, hb.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hexR' : ∀ l : Fin r, ∃ c : Fin r → Ω, (∀ a, c a ∈ regAt ξ p) ∧ colFrame w P l = ∑ a, c a • b a := by
    intro l
    refine exists_regular_coeff ?_
    rw [← hb.2, he.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose c hc hcs using hexR
  choose c' hc' hcs' using hexR'
  obtain ⟨Rm, hRm, hbR⟩ : ∃ Rm : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm a l ∈ regAt ξ p) ∧
      b = colFrame (colFrame w P) Rm := ⟨fun a l => c l a, fun a l => hc l a, funext hcs⟩
  obtain ⟨Rm', hRm', heR⟩ : ∃ Rm' : Matrix (Fin r) (Fin r) Ω, (∀ a l, Rm' a l ∈ regAt ξ p) ∧
      colFrame w P = colFrame b Rm' := ⟨fun a l => c' l a, fun a l => hc' l a, funext hcs'⟩
  refine ⟨U, Rm, Rm', hU, hRm, hRm', ?_, ?_, ?_⟩
  · refine colFrame_injective he.1 ?_
    rw [colFrame_mul, ← hbR, ← heR, colFrame_one]
  · refine colFrame_injective hw ?_
    rw [colFrame_mul, colFrame_mul, ← hbU, ← hbR]
  · intro l
    refine FlagGrGen.gr_isGenAt X Ω ξ E L r (colFrame w g) b p l (U l l) hb₀ hbF hb ?_
    rw [hbU]
    exact sub_diag_mem _ hU l

end GlobalTheory.CompanionTheory.Ar.PB.FrameTrans
