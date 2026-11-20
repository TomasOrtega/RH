import Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdPropositionOfClass
import Formalism.LocalToGlobal.GlobalTheory.GL4.FockNExtCNu
import Formalism.LocalToGlobal.GlobalTheory.GL4.MuMaxLeMon
import Formalism.LocalToGlobal.GlobalTheory.GL4.ShortAtMeanLog
import Formalism.LocalToGlobal.Columns.MaxSlopeSummandOfFock

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ClassMap (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0), (∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, Formalism.MainNotions.flipTwoThree.ShortAt D u c y) →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (B : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < B v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        B v * normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (B v) ≤
        ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

/- English proof (translation)
Introduce `u CV c hy`. Use `(columnHypotheses D u).tc` as an intermediate fact. Take `⟨φ, I, B, hinj, hI0, hint, hB, hnorm, hnum⟩` from `h u CV c hy`. Establish `hne : (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) ≠ ⊥`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (NC_ne_bot CV c)`.

Introduce `h0`. Establish `hm : φ.restrictScalars (𝓞 D.what₂.LL) x ∈ (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL))` using `⟨x, hx, rfl⟩`. Rewrite `hm` using `[h0, Submodule.mem_bot]`. Conclude with `hx0 (hinj hx (zero_mem _) (by rw [map_zero]; exact hm))`. Establish `hm` using `muMax_le_mon D.what₂.LL ((D.fm u).lam 0) ((D.fm u).lat 0).b ((D.fm u).lat 0).X ((D.fm u).lat_good 0).1 (NC CV c) (((D.fm u).lat_good 0).2.1.map _) φ hinj hne I hI0 hint B hB hnorm (monCnu ((D.fm u).lam 0)) (monCnu_pos _) (monW_ge_cNu _)`.

Establish `hl` using `log_monCnu ((D.fm u).lam 0) (rank_zero_pos D)`. Rewrite `hm` using `[hl]`. Establish `hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ` using `fun τ => by`. Unfold `dW`. Use `push_cast`.

Conclude with `sum_natWeight_eq_colAbsShifted D u τ`. Establish `hN : ((D.R.N 0 : ℕ) : ℝ) = (D.R.k : ℝ)` using `by rw [Ranks.N_zero]`. Simplify using `only [hdW, hN] at hm`. Establish `hk : (0 : ℝ) < D.R.k` using `by exact_mod_cast columnCount_pos D`. Establish `hv : (0 : ℝ) < D.host.v` using `by have := two_le_half_rootDiscr D; linarith`.

Establish `hR : (∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) + Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) = (∑ τ, (colAbsP D u τ * Real.log (D.R.k : ℝ) + Real.log (cNu ((D.fm u).lam 0 τ).natW))) + ∑ τ, (colAbsP D u τ …`. Establish `e4 : Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) = Real.log (D.R.k : ℝ) + Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)`. Rewrite using `[← Real.log_mul hk.ne' (by positivity)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[e4]`. Expand and normalize the polynomial expressions, which then agree. Use `show muMaxDef ((D.fm u).lat 0).b ((D.fm u).lat 0).X (NC CV c) ≤ _`.

Rewrite using `[hR]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slopeMaxClass_of_map (D : D7) (h : ClassMap D) : SlopeMaxClass D := by
  intro u CV c hy
  have := (columnHypotheses D u).tc
  obtain ⟨φ, I, B, hinj, hI0, hint, hB, hnorm, hnum⟩ := h u CV c hy
  have hne : (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (NC_ne_bot CV c)
    intro h0
    have hm : φ.restrictScalars (𝓞 D.what₂.LL) x ∈ (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact hx0 (hinj hx (zero_mem _) (by rw [map_zero]; exact hm))
  have hm := muMax_le_mon D.what₂.LL ((D.fm u).lam 0) ((D.fm u).lat 0).b ((D.fm u).lat 0).X ((D.fm u).lat_good 0).1 (NC CV c)
    (((D.fm u).lat_good 0).2.1.map _) φ hinj hne I hI0 hint B hB hnorm (monCnu ((D.fm u).lam 0))
    (monCnu_pos _) (monW_ge_cNu _)
  have hl := log_monCnu ((D.fm u).lam 0) (rank_zero_pos D)
  rw [hl] at hm
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hN : ((D.R.N 0 : ℕ) : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
  simp only [hdW, hN] at hm
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
  have hv : (0 : ℝ) < D.host.v := by have := two_le_half_rootDiscr D; linarith
  have hR : (∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, (colAbsP D u τ * Real.log (D.R.k : ℝ) + Real.log (cNu ((D.fm u).lam 0 τ).natW))) +
      ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)) := by
    have e4 : Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) =
        Real.log (D.R.k : ℝ) + Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
      rw [← Real.log_mul hk.ne' (by positivity)]
      congr 1
      ring
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [e4]
    ring
  show muMaxDef ((D.fm u).lat 0).b ((D.fm u).lat 0).X (NC CV c) ≤ _
  rw [hR]
  linarith

/- English proof (translation)
The claim follows from `Link6F_of_class fun D => slopeMaxClass_of_map D (h D)`.
-/
theorem Link6F_of_map (h : ∀ D, ClassMap D) : Link6F := Link6F_of_class fun D => slopeMaxClass_of_map D (h D)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Take `⟨r, hr, he⟩` from `(columnHypotheses D u).pos w.embedding (y a) (hy.2.1.ne_zero a)`. Rewrite using `[he, Complex.ofReal_re]`. Conclude with `hr`.
-/
theorem shortAt_pos (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y) (w : InfinitePlace D.host.E) (a : Fin (D.R.N 0)) :
    0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
  obtain ⟨r, hr, he⟩ := (columnHypotheses D u).pos w.embedding (y a) (hy.2.1.ne_zero a)
  rw [he, Complex.ofReal_re]
  exact hr

def ClassMapT (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V), Formalism.MainNotions.flipTwoThree.ShortAt D u c y →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (Dv : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < Dv v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        ((∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW ((D.fm u).lam 0 τ)) * Dv v) *
          normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) ≤
        -∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)

/- English proof (translation)
Introduce `u CV c hy`. Take `⟨y, hy⟩` from `hy`. Use `(columnHypotheses D u).tc` as an intermediate fact. Use `(columnHypotheses D u).tcE` as an intermediate fact. Establish `hposE` using `shortAt_pos D u c y hy`.

Take `⟨φ, I, Dv, hinj, hI0, hint, hD, hnorm, hnum⟩` from `h u CV c y hy`. Use `set G : InfinitePlace D.what₂.LL → D.what₂.Tau → ℝ := fun v τ => ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re with hG`. Establish `hN0 : 0 < D.R.N 0` using `rank_zero_pos D`. Establish `hGc : ∀ v τ, G v τ = ∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re` using `fun v τ => Finset.sum_congr rfl fun a _ => (re_comap (CV.rho τ) v _).symm`. Establish `hGpos : ∀ v τ, 0 < G v τ` using `fun v τ => by`.

Rewrite using `[hGc]`. Conclude with `Finset.sum_pos (fun a _ => hposE _ a) ⟨⟨0, hN0⟩, Finset.mem_univ _⟩`. Use `⟨φ, I, fun v => (∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v, hinj, hI0, hint, fun v => mul_pos (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _) (hD v), hnorm, ?_⟩` and prove the remaining obligations. Establish `hlog : ∀ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) = (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * Real.log (G v τ)) + Real.log (Dv v)` using `fun v => by`. Rewrite using `[Real.log_mul (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _).ne' (hD v).ne', Real.log_prod (fun τ _ => (pow_pos (hGpos v τ) _).ne')]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun τ _ => Real.log_pow _ _`. Establish `hmean : ∀ τ, (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ) ≤ Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)`. Introduce `τ`. Establish `h1` using `mean_over_places_comap D.host.E D.what₂.LL (CV.rho τ) (fun w => Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re))`.

Establish `h2 : (∑ v, Real.log (G v τ)) = ∑ v : InfinitePlace D.what₂.LL, Real.log (∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re)` using `Finset.sum_congr rfl fun v _ => by rw [hGc]`. Rewrite using `[h2, h1]`. Conclude with `shortAt_mean_log D u c y hy hposE`. Establish `hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ` using `fun τ => by`. Unfold `dW`.

Use `push_cast`. Conclude with `sum_natWeight_eq_colAbsShifted D u τ`. Establish `hsplit : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) = (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) + (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v)`. Simplify using `only [hlog, Finset.sum_add_distrib, mul_add]`. Use `congr 1`.

Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun v _ => by ring`. Establish `hbound : (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) ≤ ∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)` using `Finset.sum_le_sum fun τ _ => by`. Rewrite using `[← hdW τ]`.

Conclude with `mul_le_mul_of_nonneg_left (hmean τ) (Nat.cast_nonneg _)`. Rewrite using `[hsplit]`. Establish `e : (∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) = (∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)) - ∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)` using `Finset.sum_sub_distrib _ _`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem class_map_of_archimedean (D : D7) (h : ClassMapT D) : ClassMap D := by
  intro u CV c hy
  obtain ⟨y, hy⟩ := hy
  have := (columnHypotheses D u).tc
  have := (columnHypotheses D u).tcE
  have hposE := shortAt_pos D u c y hy
  obtain ⟨φ, I, Dv, hinj, hI0, hint, hD, hnorm, hnum⟩ := h u CV c y hy
  set G : InfinitePlace D.what₂.LL → D.what₂.Tau → ℝ := fun v τ => ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re with hG
  have hN0 : 0 < D.R.N 0 := rank_zero_pos D
  have hGc : ∀ v τ, G v τ = ∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re := fun v τ =>
    Finset.sum_congr rfl fun a _ => (re_comap (CV.rho τ) v _).symm
  have hGpos : ∀ v τ, 0 < G v τ := fun v τ => by
    rw [hGc]
    exact Finset.sum_pos (fun a _ => hposE _ a) ⟨⟨0, hN0⟩, Finset.mem_univ _⟩
  refine ⟨φ, I, fun v => (∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v, hinj, hI0, hint,
    fun v => mul_pos (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _) (hD v), hnorm, ?_⟩
  have hlog : ∀ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * Real.log (G v τ)) + Real.log (Dv v) := fun v => by
    rw [Real.log_mul (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _).ne' (hD v).ne',
      Real.log_prod (fun τ _ => (pow_pos (hGpos v τ) _).ne')]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => Real.log_pow _ _
  have hmean : ∀ τ, (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ) ≤ Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
    intro τ
    have h1 := mean_over_places_comap D.host.E D.what₂.LL (CV.rho τ)
      (fun w => Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re))
    have h2 : (∑ v, Real.log (G v τ)) = ∑ v : InfinitePlace D.what₂.LL,
        Real.log (∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re) :=
      Finset.sum_congr rfl fun v _ => by rw [hGc]
    rw [h2, h1]
    exact shortAt_mean_log D u c y hy hposE
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hsplit : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) := by
    simp only [hlog, Finset.sum_add_distrib, mul_add]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun v _ => by ring
  have hbound : (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) ≤
      ∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) :=
    Finset.sum_le_sum fun τ _ => by
      rw [← hdW τ]
      exact mul_le_mul_of_nonneg_left (hmean τ) (Nat.cast_nonneg _)
  rw [hsplit]
  have e : (∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) -
      (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)) -
        ∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u) := Finset.sum_sub_distrib _ _
  rw [e]
  linarith

/- English proof (translation)
The claim follows from `Link6F_of_map fun D => class_map_of_archimedean D (h D)`.
-/
theorem third_link_of_archimedean (h : ∀ D, ClassMapT D) : Link6F := Link6F_of_map fun D => class_map_of_archimedean D (h D)

/- English proof (translation)
The claim follows from `packet_of_third_proposition (third_link_of_archimedean h)`.
-/
theorem packetFamily_of_classMapT (h : ∀ D, ClassMapT D) : KudlaFamilyOfMinkowskiTransference := packet_of_third_proposition (third_link_of_archimedean h)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
