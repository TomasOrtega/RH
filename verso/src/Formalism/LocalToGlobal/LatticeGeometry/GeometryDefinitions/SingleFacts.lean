import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower

noncomputable section

open Module Matrix NumberField Formalism.BasicNotions Formalism.HN

namespace Formalism.L2.Geo.Def.G1

section Line

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

section Single

variable {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

omit [IsTotallyComplex K] [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem majAt_self (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (e : V) :
    (Formalism.HermitianLatticesTheory.majAt b X v e e).re = Formalism.HermitianLatticesTheory.normAt b X v e ^ 2 := by
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Use `set Le : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {e} with hLe`. Establish `hfg : Le.FG` using `Submodule.fg_span (Set.finite_singleton e)`. Establish `hne : Le ≠ ⊥`. Introduce `h`. Establish `: e ∈ Le` using `Submodule.subset_span rfl`.

Rewrite `this` using `[h]`. Conclude with `he ((Submodule.mem_bot _).1 this)`. Establish `hrk : rkK Le = 1`. Unfold `rkK`. Rewrite using `[hLe, Submodule.span_span_of_tower]`.

Conclude with `finrank_span_singleton he`. Establish `hli : LinearIndependent K (fun _ : Fin 1 => e)` using `LinearIndependent.of_subsingleton 0 he`. Establish `hrange : Set.range (fun _ : Fin 1 => e) = {e}` using `Set.range_const`. Establish `hht` using `(htGram K V ι b X hX 1 (fun _ => e) hli).1`. Rewrite `hht` using `[hrange]`.

Establish `hdet : ∀ v, (gramPl b X v (fun _ : Fin 1 => e)).det.re = Formalism.HermitianLatticesTheory.normAt b X v e ^ 2`. Introduce `v`. Rewrite using `[Matrix.det_fin_one, ← majAt_self]`. Both sides reduce to the same expression. Rewrite `hht` using `[Finset.prod_congr rfl fun v _ => hdet v]`.

Establish `hpos` using `(plLat K V ι b X hX Le hfg).2.2`. Establish `hne0 : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v e ^ 2 ≠ 0`. Establish `h1 : (∏ v, Formalism.HermitianLatticesTheory.normAt b X v e ^ 2) ≠ 0` using `by rw [← hht]; exact hpos.ne'`. Introduce `v`. Conclude with `Finset.prod_ne_zero_iff.1 h1 v (Finset.mem_univ v)`.

Establish `hN : ∀ v, 0 < Formalism.HermitianLatticesTheory.normAt b X v e`. Introduce `v`. Establish `h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt b X v e` using `Real.sqrt_nonneg _`. Break down `h0.lt_or_eq with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd (by rw [← h]; norm_num) (hne0 v)`. Use `⟨hN, ?_⟩` and prove the remaining obligations. Establish `hmu` using `(sizeMu K V ι b X hX Le hfg hne).2.1`. Rewrite using `[hmu]`. Unfold `size`.

Rewrite using `[Real.log_rpow hpos, hrk, hht, Real.log_prod (fun v _ => hne0 v)]`. Simplify using `only [Real.log_pow, ← Finset.mul_sum]`. Establish `hf : (nPl K : ℝ) ≠ 0`. Unfold `nPl`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem single_facts (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (e : V) (he : e ≠ 0) :
    (∀ v, 0 < Formalism.HermitianLatticesTheory.normAt b X v e) ∧
      muDef b X (Submodule.span (𝓞 K) {e}) = -(2 / (nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v e) := by
  set Le : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {e} with hLe
  have hfg : Le.FG := Submodule.fg_span (Set.finite_singleton e)
  have hne : Le ≠ ⊥ := by
    intro h
    have : e ∈ Le := Submodule.subset_span rfl
    rw [h] at this
    exact he ((Submodule.mem_bot _).1 this)
  have hrk : rkK Le = 1 := by
    unfold rkK
    rw [hLe, Submodule.span_span_of_tower]
    exact finrank_span_singleton he
  have hli : LinearIndependent K (fun _ : Fin 1 => e) := LinearIndependent.of_subsingleton 0 he
  have hrange : Set.range (fun _ : Fin 1 => e) = {e} := Set.range_const
  have hht := (htGram K V ι b X hX 1 (fun _ => e) hli).1
  rw [hrange] at hht
  have hdet : ∀ v, (gramPl b X v (fun _ : Fin 1 => e)).det.re = Formalism.HermitianLatticesTheory.normAt b X v e ^ 2 := by
    intro v
    rw [Matrix.det_fin_one, ← majAt_self]
    rfl
  rw [Finset.prod_congr rfl fun v _ => hdet v] at hht
  have hpos := (plLat K V ι b X hX Le hfg).2.2
  have hne0 : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v e ^ 2 ≠ 0 := by
    have h1 : (∏ v, Formalism.HermitianLatticesTheory.normAt b X v e ^ 2) ≠ 0 := by rw [← hht]; exact hpos.ne'
    intro v
    exact Finset.prod_ne_zero_iff.1 h1 v (Finset.mem_univ v)
  have hN : ∀ v, 0 < Formalism.HermitianLatticesTheory.normAt b X v e := by
    intro v
    have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt b X v e := Real.sqrt_nonneg _
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; norm_num) (hne0 v)
  refine ⟨hN, ?_⟩
  have hmu := (sizeMu K V ι b X hX Le hfg hne).2.1
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk, hht, Real.log_prod (fun v _ => hne0 v)]
  simp only [Real.log_pow, ← Finset.mul_sum]
  have hf : (nPl K : ℝ) ≠ 0 := by
    unfold nPl
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

end Single

/- English proof (translation)
Establish `hsp : Submodule.span K (T : Set (Fin n → K)) = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `: finrank K (Submodule.span K (T : Set (Fin n → K))) = n` using `hrk`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Set `B : HLat K` to `{ V := Fin n → K, ι := Fin n, b := Pi.basisFun K (Fin n), X := Y, L := T }`. Establish `hB : B.Good` using `⟨hY, hfg, hsp⟩`. Establish `hBr : B.rank = n` using `hrk`. Establish `h` using `bridge_hn_mu_holds K B hB (by rw [hBr]; exact hn)`. Rewrite `h` using `[hBr]`.

Establish `h1 : B.mu = muDef (Pi.basisFun K (Fin n)) Y T` using `rfl`. Establish `h2 : B.lcv = Formalism.DivisionValues.lcv Y T` using `rfl`. Rewrite using `[← h1, ← h2, h]`. Establish `: (n : ℝ) ≠ 0` using `by exact_mod_cast hn.ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem lcv_eq_mu {n : ℕ} (hn : 0 < n) (Y : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hY : ∀ v, IsUnit (Y v).det)
    (T : Submodule (𝓞 K) (Fin n → K)) (hfg : T.FG) (hrk : rkK T = n) :
    Formalism.DivisionValues.lcv Y T = -(n : ℝ) * muDef (Pi.basisFun K (Fin n)) Y T := by
  have hsp : Submodule.span K (T : Set (Fin n → K)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have : finrank K (Submodule.span K (T : Set (Fin n → K))) = n := hrk
    rw [this]; simp
  let B : HLat K := { V := Fin n → K, ι := Fin n, b := Pi.basisFun K (Fin n), X := Y, L := T }
  have hB : B.Good := ⟨hY, hfg, hsp⟩
  have hBr : B.rank = n := hrk
  have h := bridge_hn_mu_holds K B hB (by rw [hBr]; exact hn)
  rw [hBr] at h
  have h1 : B.mu = muDef (Pi.basisFun K (Fin n)) Y T := rfl
  have h2 : B.lcv = Formalism.DivisionValues.lcv Y T := rfl
  rw [← h1, ← h2, h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end Line

end Formalism.L2.Geo.Def.G1
