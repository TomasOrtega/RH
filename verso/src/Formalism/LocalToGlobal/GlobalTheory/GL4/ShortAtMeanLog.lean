import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
import Formalism.GL3MeanSquares.HookFormulaTorsion.ColumnParametrizationOffDiagonal

open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Formalism.HN

/- English proof (translation)
Establish `h1 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ z`. Establish `h : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z` using `by first`. Consider the case `exact trace_eq_sum_embeddings ℂ (x := z)`. Consider the case `exact trace_eq_sum_embeddings (E := ℂ) (x := z)`. Consider the case `exact trace_eq_sum_embeddings (F := ℂ) (x := z)`.

Consider the case `exact (trace_eq_sum_embeddings ℂ : _)`. Rewrite using `[show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from (eq_ratCast _ _).symm, h]`. Conclude with `(Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ z) (fun σ : E →ₐ[ℚ] ℂ => σ z) (fun _ => rfl)).symm`. Establish `h2 : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ φ : E →+* ℂ, (φ z).re`. Rewrite using `[← Complex.re_sum, ← h1, Complex.ratCast_re]`.

Rewrite using `[h2, ← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ : E →+* ℂ => (φ z).re)]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hfib : ∀ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), (φ z).re = (w.embedding z).re`. Introduce `φ hφ`. Establish `hw` using `(Finset.mem_filter.mp hφ).2`.

Substitute `hw` using the available equality. Break down `InfinitePlace.embedding_mk_eq φ with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]`. Rewrite using `[Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]`.

Establish `hm : w.mult = 2` using `InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩`. Rewrite using `[hm]`. Evaluate the numerical expressions.
-/
theorem trace_re_sum (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding z).re := by
  classical
  have h1 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ z := by
    have h : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z := by
      first
      | exact trace_eq_sum_embeddings ℂ (x := z)
      | exact trace_eq_sum_embeddings (E := ℂ) (x := z)
      | exact trace_eq_sum_embeddings (F := ℂ) (x := z)
      | exact (trace_eq_sum_embeddings ℂ : _)
    rw [show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from
      (eq_ratCast _ _).symm, h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ z)
      (fun σ : E →ₐ[ℚ] ℂ => σ z) (fun _ => rfl)).symm
  have h2 : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ φ : E →+* ℂ, (φ z).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ)
    (fun φ : E →+* ℂ => (φ z).re)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w),
      (φ z).re = (w.embedding z).re := by
    intro φ hφ
    have hw := (Finset.mem_filter.mp hφ).2
    subst hw
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  have hm : w.mult = 2 := InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  rw [hm]
  norm_num

/- English proof (translation)
Rewrite using `[← InfinitePlace.sum_mult_eq]`. Establish `h : ∀ w : InfinitePlace E, w.mult = 2` using `fun w => InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩`. Simplify using `only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Unfold `nPl`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_nPl (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : 2 * nPl E = Module.finrank ℚ E := by
  classical
  rw [← InfinitePlace.sum_mult_eq]
  have h : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold nPl
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hT : 0 < ∑ i, S i`. Establish `: Nonempty ι` using `Fintype.card_pos_iff.mp (by exact_mod_cast hn)`. Conclude with `Finset.sum_pos (fun i _ => hS i) Finset.univ_nonempty`. Use `set M := (∑ i, S i) / (Fintype.card ι : ℝ) with hM`. Establish `hMpos : 0 < M` using `div_pos hT hn`.

Establish `h1 : ∀ i, Real.log (S i) - Real.log M ≤ S i / M - 1`. Introduce `i`. Rewrite using `[← Real.log_div (hS i).ne' hMpos.ne']`. Conclude with `Real.log_le_sub_one_of_pos (div_pos (hS i) hMpos)`. Establish `h2 : ∑ i, (Real.log (S i) - Real.log M) ≤ ∑ i, (S i / M - 1)` using `Finset.sum_le_sum fun i _ => h1 i`.

Establish `h3 : (∑ i, S i) / M = (Fintype.card ι : ℝ)`. Use `hT.ne'` as an intermediate fact. Use `hn.ne'` as an intermediate fact. Rewrite using `[hM]`. Clear the denominators using the available nonvanishing facts.

Rewrite `h2` using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, h3, Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma sum_log_le_card_mul_log_mean_of_pos {ι : Type*} [Fintype ι] (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hn : 0 < (Fintype.card ι : ℝ)) :
    ∑ i, Real.log (S i) ≤ (Fintype.card ι : ℝ) * Real.log ((∑ i, S i) / Fintype.card ι) := by
  have hT : 0 < ∑ i, S i := by
    have : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hn)
    exact Finset.sum_pos (fun i _ => hS i) Finset.univ_nonempty
  set M := (∑ i, S i) / (Fintype.card ι : ℝ) with hM
  have hMpos : 0 < M := div_pos hT hn
  have h1 : ∀ i, Real.log (S i) - Real.log M ≤ S i / M - 1 := by
    intro i
    rw [← Real.log_div (hS i).ne' hMpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hS i) hMpos)
  have h2 : ∑ i, (Real.log (S i) - Real.log M) ≤ ∑ i, (S i / M - 1) :=
    Finset.sum_le_sum fun i _ => h1 i
  have h3 : (∑ i, S i) / M = (Fintype.card ι : ℝ) := by
    have := hT.ne'
    have := hn.ne'
    rw [hM]
    field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, h3, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one] at h2
  linarith

/- English proof (translation)
Take `⟨-, -, htr⟩` from `hy`. Establish `hk : D.R.N 0 = D.R.k` using `Formalism.BasicNotions.Ranks.N_zero D.R`. Establish `hfin` using `Formalism.MainNotions.flipTwoThree.b_finrank_host D`. Establish `hnf : nPl D.host.E = D.R.f`. Establish `h2` using `two_nPl D.host.E`.

Rewrite `h2` using `[hfin]`. Use linear arithmetic over natural numbers and integers. Establish `hfo : D.R.f = 2 * D.R.ord` using `by first`. Consider the case `exact Formalism.BasicNotions.Ranks.f_eq_ord`. Consider the case `exact Formalism.BasicNotions.Ranks.f_eq_ord D.R`.

Consider the case `exact Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)`. Establish `hf : 0 < D.R.f`. Use `D.R.m_le_f` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hfR : (0 : ℝ) < D.R.f` using `by exact_mod_cast hf`. Establish `hbound : ∀ a, ∑ w : InfinitePlace D.host.E, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤ (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2)`. Introduce `a`. Establish `h` using `htr a`. Rewrite `h` using `[trace_re_sum, div_le_iff₀ (by linarith), ← Finset.mul_sum]`.

Use polynomial arithmetic with `[h]`. Establish `hS : ∀ w : InfinitePlace D.host.E, 0 < ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re`. Introduce `w`. Establish `hne : (Finset.univ : Finset (Fin (D.R.N 0))).Nonempty`. Use `⟨⟨0, ?_⟩, Finset.mem_univ _⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `Finset.sum_pos (fun a _ => hpos w a) hne`. Establish `htot : ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤ (D.R.k : ℝ) * ((D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2))`.

Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcard : (nPl D.host.E : ℝ) = (Fintype.card (InfinitePlace D.host.E) : ℝ)` using `rfl`. Establish `hcf : (Fintype.card (InfinitePlace D.host.E) : ℝ) = D.R.f`. Rewrite using `[← hcard]`.

Conclude with `hnf` after adjusting the coercions. Establish `hnpos : (0 : ℝ) < (Fintype.card (InfinitePlace D.host.E) : ℝ)` using `by rw [hcf]; exact hfR`. Establish `key` using `sum_log_le_card_mul_log_mean_of_pos _ hS hnpos`. Establish `hTpos : 0 < ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re` using `Finset.sum_pos (fun w _ => hS w) (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by exact_mod_cast hnpos)))`. Rewrite using `[hcard, div_le_iff₀ hnpos]`.

Use `key.trans ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `mul_le_mul_of_nonneg_right ?_ hnpos.le` and prove the remaining obligations. Apply `Real.log_le_log (div_pos hTpos hnpos)` to reduce the goal to its premises. Rewrite using `[div_le_iff₀ hnpos, hcf]`.

Use polynomial arithmetic with `[htot]`.
-/
theorem shortAt_mean_log (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) [IsTotallyComplex D.host.E]
    (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y)
    (hpos : ∀ (w : InfinitePlace D.host.E) a, 0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re) :
    (∑ w : InfinitePlace D.host.E, Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re)) / (nPl D.host.E : ℝ) ≤
      Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
  classical
  obtain ⟨-, -, htr⟩ := hy
  have hk : D.R.N 0 = D.R.k := Formalism.BasicNotions.Ranks.N_zero D.R
  have hfin := Formalism.MainNotions.flipTwoThree.b_finrank_host D
  have hnf : nPl D.host.E = D.R.f := by
    have h2 := two_nPl D.host.E
    rw [hfin] at h2
    omega
  have hfo : D.R.f = 2 * D.R.ord := by
    first
    | exact Formalism.BasicNotions.Ranks.f_eq_ord
    | exact Formalism.BasicNotions.Ranks.f_eq_ord D.R
    | exact Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)
  have hf : 0 < D.R.f := by
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hbound : ∀ a, ∑ w : InfinitePlace D.host.E, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) := by
    intro a
    have h := htr a
    rw [trace_re_sum, div_le_iff₀ (by linarith), ← Finset.mul_sum] at h
    nlinarith [h]
  have hS : ∀ w : InfinitePlace D.host.E, 0 < ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
    intro w
    have hne : (Finset.univ : Finset (Fin (D.R.N 0))).Nonempty := by
      refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
      rw [hk]
      have := D.R.m_add_three_le_k
      omega
    exact Finset.sum_pos (fun a _ => hpos w a) hne
  have htot : ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.k : ℝ) * ((D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2)) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _a : Fin (D.R.N 0), (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) :=
          Finset.sum_le_sum fun a _ => hbound a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hk, nsmul_eq_mul]
  have hcard : (nPl D.host.E : ℝ) = (Fintype.card (InfinitePlace D.host.E) : ℝ) := rfl
  have hcf : (Fintype.card (InfinitePlace D.host.E) : ℝ) = D.R.f := by
    rw [← hcard]
    exact_mod_cast hnf
  have hnpos : (0 : ℝ) < (Fintype.card (InfinitePlace D.host.E) : ℝ) := by rw [hcf]; exact hfR
  have key := sum_log_le_card_mul_log_mean_of_pos _ hS hnpos
  have hTpos : 0 < ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re :=
    Finset.sum_pos (fun w _ => hS w)
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by exact_mod_cast hnpos)))
  rw [hcard, div_le_iff₀ hnpos]
  refine key.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hnpos.le
  apply Real.log_le_log (div_pos hTpos hnpos)
  rw [div_le_iff₀ hnpos, hcf]
  nlinarith [htot]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
