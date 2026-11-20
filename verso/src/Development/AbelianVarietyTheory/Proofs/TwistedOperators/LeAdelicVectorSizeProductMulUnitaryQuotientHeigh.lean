import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceRelativeNormLeLocalSizePowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceRelativeNormLeMaxEmbeddingPowStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.HtOrth
open scoped NNReal TensorProduct

namespace GlobalTheory.SeenSize

variable {D : D7}

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul]`.
-/
theorem mt_mul_mt_inv (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  simp [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul]

/- English proof (translation)
Rewrite using `[seen, mulVec_mulVec, mt_mul_mt_inv, one_mulVec]`.
-/
theorem mulVec_seen (V : HSp D) (g : GA D V) (ξ : Fin V.rank → D.host.E) :
    Formalism.L2.Theta.mt V g *ᵥ seen V g ξ = fun i => incA D (ξ i) := by
  rw [seen, mulVec_mulVec, mt_mul_mt_inv, one_mulVec]

/- English proof (translation)
Rewrite using `[map_inv, map_inv, htFin, htOf_inv]`. Both sides reduce to the same expression.
-/
theorem htFin_inv (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g⁻¹)) =
      htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g)) := by
  rw [map_inv, map_inv, htFin, htOf_inv]; rfl

end GlobalTheory.SeenSize

namespace GlobalTheory.SeenSize
variable {D : D7}
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bc_fin_apply (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F)) (i j : Fin V.rank) :
    (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g)).val i j = compFin D.host.F D.host.E v (Formalism.L2.Theta.mt V g i j) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bc_inf_apply (V : HSp D) (g : GA D V) (w : InfinitePlace D.host.F) (i j : Fin V.rank) :
    (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)).val i j = compInf D.host.F D.host.E w (Formalism.L2.Theta.mt V g i j) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulVec_apply' {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D)) (x : Fin n → AE D) (i : Fin n) :
    (M *ᵥ x) i = ∑ j, M i j * x j := rfl

/- English proof (translation)
Establish `h1` using `(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y).le_opNNNorm (EuclideanSpace.single j 1)`. Establish `h2` using `PiLp.nnnorm_apply_le (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i`. Establish `h3 : Matrix.toEuclideanCLM (n` using `Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1) i = y i j := by`. Express the relevant statement in the definitionally equal form `∑ k, y i k * (EuclideanSpace.single j (1 : ℂ)) k = _`. Simplify using `[Pi.single_apply]`.

Rewrite `h2` using `[h3]`. Use `h2.trans (h1.trans ?_)` and prove the remaining obligations. Simplify using `[opNorm]`.
-/
theorem entry_le_opNorm {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖y i j‖₊ ≤ opNorm y := by
  have h1 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y).le_opNNNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.nnnorm_apply_le (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1)) i
  have h3 : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y (EuclideanSpace.single j 1) i = y i j := by
    change ∑ k, y i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp [Pi.single_apply]
  rw [h3] at h2
  refine h2.trans (h1.trans ?_)
  simp [opNorm]

/- English proof (translation)
Use `Finset.sup_le fun i _ => ?_` and prove the remaining obligations. Establish `hM : ∀ j, absFin D.host.F v (compFin D.host.F D.host.E v (Formalism.L2.Theta.mt V g i j)) ≤ htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g))` using `fun j => by`. Rewrite using `[← bc_fin_apply]`. Conclude with `(absFin_le_normFin D.host.F v _ i j).trans (le_htOf _ _)`. Rewrite using `[mulVec_apply', map_sum]`.

Use `absFin_sum_le _ v _ _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `(absFin_mul_le _ v _ _).trans (mul_le_mul' (hM j) ?_)` and prove the remaining obligations. Conclude with `Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))) (Finset.mem_univ j)`.
-/
theorem vFin_mulVec_le (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Fin V.rank → AE D) :
    vFin v (Formalism.L2.Theta.mt V g *ᵥ x) ≤
      htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g)) * vFin v x := by
  refine Finset.sup_le fun i _ => ?_
  have hM : ∀ j, absFin D.host.F v (compFin D.host.F D.host.E v (Formalism.L2.Theta.mt V g i j)) ≤
      htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g)) := fun j => by
    rw [← bc_fin_apply]
    exact (absFin_le_normFin D.host.F v _ i j).trans (le_htOf _ _)
  rw [mulVec_apply', map_sum]
  refine absFin_sum_le _ v _ _ fun j _ => ?_
  rw [map_mul]
  refine (absFin_mul_le _ v _ _).trans (mul_le_mul' (hM j) ?_)
  exact Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))) (Finset.mem_univ j)

/- English proof (translation)
Unfold `vInf`. Use `Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin n => ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊) (Finset.mem_univ (τ, j))` and compare the differences between its conclusion and the goal.
-/
theorem le_vInf (w : InfinitePlace D.host.F) {n : ℕ} (x : Fin n → AE D) (τ : EmbOver D.host.E w) (j : Fin n) :
    ‖infEmb τ (compInf D.host.F D.host.E w (x j))‖₊ ≤ vInf w x := by
  classical
  unfold vInf
  convert Finset.le_sup (f := fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊) (Finset.mem_univ (τ, j))

/- English proof (translation)
Rewrite using `[nnnorm_mul]`. Conclude with `mul_le_mul' ha hb`.
-/
theorem nnnorm_mul_le_of_le {a b : ℂ} {c d : ℝ≥0} (ha : ‖a‖₊ ≤ c) (hb : ‖b‖₊ ≤ d) : ‖a * b‖₊ ≤ c * d := by
  rw [nnnorm_mul]; exact mul_le_mul' ha hb

/- English proof (translation)
Use `Finset.sup_le fun p _ => ?_` and prove the remaining obligations. Take `⟨τ, i⟩` from `p`. Establish `hM : ∀ j, ‖infEmb τ (compInf D.host.F D.host.E w (Formalism.L2.Theta.mt V g i j))‖₊ ≤ htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g))` using `fun j => by`. Rewrite using `[← bc_inf_apply]`. Conclude with `(entry_le_opNorm ((Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)).val.map (infEmb τ)) i j).trans (((normInf_le_iff D.host.F w).1 le_rfl τ).trans (le_htOf _ _))`.

Establish `hx : ∀ j, ‖infEmb τ (compInf D.host.F D.host.E w (x j))‖₊ ≤ vInf w x` using `fun j => le_vInf w x τ j`. Establish `hφ : ∀ a b : AE D, infEmb τ (compInf D.host.F D.host.E w (a * b)) = infEmb τ (compInf D.host.F D.host.E w a) * infEmb τ (compInf D.host.F D.host.E w b)` using `fun a b => ((infEmb τ).comp (compInf D.host.F D.host.E w)).map_mul a b`. Rewrite using `[mulVec_apply', map_sum, map_sum]`. Use `(nnnorm_sum_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hφ]`. Conclude with `nnnorm_mul_le_of_le (hM j) (hx j)`. Use `_ = (V.rank : ℝ≥0) * (htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)) * vInf w x) := by`. Simplify using the standard rewrite rules. Use `_ ≤ ((V.rank : ℝ≥0) + 1) * (htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)) * vInf w x) := mul_le_mul' (le_add_of_nonneg_right zero_le_one) le_rfl`.

Use `_ = _ := (mul_assoc _ _ _).symm`.
-/
theorem vInf_mulVec_le (V : HSp D) (g : GA D V) (w : InfinitePlace D.host.F) (x : Fin V.rank → AE D) :
    vInf w (Formalism.L2.Theta.mt V g *ᵥ x) ≤
      ((V.rank : ℝ≥0) + 1) * htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)) * vInf w x := by
  refine Finset.sup_le fun p _ => ?_
  obtain ⟨τ, i⟩ := p
  have hM : ∀ j, ‖infEmb τ (compInf D.host.F D.host.E w (Formalism.L2.Theta.mt V g i j))‖₊ ≤
      htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)) := fun j => by
    rw [← bc_inf_apply]
    exact (entry_le_opNorm ((Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)).val.map (infEmb τ)) i j).trans
      (((normInf_le_iff D.host.F w).1 le_rfl τ).trans (le_htOf _ _))
  have hx : ∀ j, ‖infEmb τ (compInf D.host.F D.host.E w (x j))‖₊ ≤ vInf w x := fun j => le_vInf w x τ j
  have hφ : ∀ a b : AE D, infEmb τ (compInf D.host.F D.host.E w (a * b)) =
      infEmb τ (compInf D.host.F D.host.E w a) * infEmb τ (compInf D.host.F D.host.E w b) := fun a b =>
    ((infEmb τ).comp (compInf D.host.F D.host.E w)).map_mul a b
  rw [mulVec_apply', map_sum, map_sum]
  refine (nnnorm_sum_le _ _).trans ?_
  calc ∑ j, ‖infEmb τ (compInf D.host.F D.host.E w (Formalism.L2.Theta.mt V g i j * x j))‖₊
      ≤ ∑ _j : Fin V.rank, htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)) * vInf w x :=
        Finset.sum_le_sum fun j _ => by
          rw [hφ]; exact nnnorm_mul_le_of_le (hM j) (hx j)
    _ = (V.rank : ℝ≥0) * (htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)) * vInf w x) := by
        simp
    _ ≤ ((V.rank : ℝ≥0) + 1) * (htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g)) * vInf w x) :=
        mul_le_mul' (le_add_of_nonneg_right zero_le_one) le_rfl
    _ = _ := (mul_assoc _ _ _).symm

end GlobalTheory.SeenSize

namespace GlobalTheory.SeenSize
variable {D : D7}

/- English proof (translation)
Simplify using `[compFin, incA, inclR]`.
-/
theorem compFin_incA (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E) :
    compFin D.host.F D.host.E v (incA D y) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] y := by
  simp [compFin, incA, inclR]

/- English proof (translation)
Simplify using `[compInf, incA, inclR]`.
-/
theorem infEmb_compInf_incA (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w) (y : D.host.E) :
    infEmb τ (compInf D.host.F D.host.E w (incA D y)) = τ.1 y := by
  simp [compInf, incA, inclR]

/- English proof (translation)
Establish `h` using `(FinitePlace.hasFiniteMulSupport hx).preimage (f := FinitePlace.equivHeightOneSpectrum.symm) (Equiv.injective _).injOn`. Use `h.subset fun v hv h1 => hv ?_` and prove the remaining obligations. Establish `h2 : FinitePlace.mk v x = 1` using `h1`. Rewrite `h2` using `[FinitePlace.mk_apply]`. Conclude with `NNReal.eq h2`.
-/
theorem finite_of_norm {x : D.host.F} (hx : x ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 D.host.F) => ‖algebraMap D.host.F (Fv D.host.F v) x‖₊).Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hx).preimage
    (f := FinitePlace.equivHeightOneSpectrum.symm) (Equiv.injective _).injOn
  refine h.subset fun v hv h1 => hv ?_
  have h2 : FinitePlace.mk v x = 1 := h1
  rw [FinitePlace.mk_apply] at h2
  exact NNReal.eq h2

/- English proof (translation)
Use `haveI : IsTotallyReal D.host.F := D.sp.cm.totReal`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hξ`. Establish `hx : Algebra.norm D.host.F (ξ i) ≠ 0` using `Algebra.norm_ne_zero_iff.2 hi`. Establish `hd : Module.finrank D.host.F D.host.E ≠ 0` using `Module.finrank_pos.ne'`. Establish `ha : ∀ v, ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ ≤ vFin v (fun i => incA D (ξ i)) ^ Module.finrank D.host.F D.host.E` using `fun v => by`.

Use `(GlobalTheory.T.finitePlace_relativeNorm_le_localSize_pow D v (ξ i)).trans (pow_le_pow_left₀ zero_le ?_ _)` and prove the remaining obligations. Rewrite using `[← compFin_incA]`. Conclude with `Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i)))) (Finset.mem_univ i)`. Establish `hA : ∀ w : InfinitePlace D.host.F, w (Algebra.norm D.host.F (ξ i)) ≤ (vInf w (fun i => incA D (ξ i)) : ℝ) ^ Module.finrank D.host.F D.host.E` using `fun w => GlobalTheory.T.infinitePlace_relativeNorm_le_maxEmbedding_pow D w (ξ i) _ fun τ => by rw [← infEmb_compInf_incA]; exact le_vInf w (fun i => incA D (ξ i)) τ i`. Establish `hfin : (Function.mulSupport fun v => vFin v (fun i => incA D (ξ i))).Finite`.

Establish `h1 : ∀ᶠ v in Filter.cofinite, vFin v (fun i => incA D (ξ i)) ≤ 1`. Use `Filter.eventually_all.2 fun j => eventually_absFin_le_one D.host.F (incA D (ξ j))` as an intermediate fact. Conclude with `this.mono fun v hv => Finset.sup_le fun j _ => hv j`. Use `((Filter.eventually_cofinite.1 h1).union (finite_of_norm hx)).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Function.mem_mulSupport, not_le] at hc`. Apply `hv` to reduce the goal to its premises. Use `le_antisymm (not_lt.1 hc.1) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Use `(ha v).trans_lt (pow_lt_one₀ zero_le hlt hd)` as an intermediate fact. Rewrite `this` using `[hc.2]`. Conclude with `lt_irrefl _ this`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hm : ∀ w : InfinitePlace D.host.F, w.mult = 1` using `fun w => by`.

Simplify using `[InfinitePlace.mult, IsTotallyReal.isReal w]`. Establish `hP` using `NumberField.prod_abs_eq_one hx`. Simplify using `only [hm, pow_one] at hP`. Rewrite `hP` using `[← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]`. Simplify using `only [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.mk_apply] at hP`.

Establish `hQ : (∏ w : InfinitePlace D.host.F, ‖w.embedding (Algebra.norm D.host.F (ξ i))‖₊) * ∏ᶠ v, ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ = 1`. Apply `NNReal.coe_injective` to reduce the goal to its premises. Establish `e : ((∏ᶠ v, ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ : ℝ≥0) : ℝ) = ∏ᶠ v, ((‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ : ℝ≥0) : ℝ)` using `MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective _`. Rewrite using `[NNReal.coe_mul, NNReal.coe_prod, e]`. Simplify using `only [coe_nnnorm, InfinitePlace.norm_embedding_eq, NNReal.coe_one]`.

Conclude with `hP`. Establish `hfa : (Function.mulSupport fun v => vFin v (fun i => incA D (ξ i)) ^ Module.finrank D.host.F D.host.E).Finite` using `hfin.subset (Function.mulSupport_pow _ _)`. Establish `hle : (1 : ℝ≥0) ≤ ((∏ w, vInf w (fun i => incA D (ξ i))) * ∏ᶠ v, vFin v (fun i => incA D (ξ i))) ^ Module.finrank D.host.F D.host.E`. Rewrite using `[← hQ, mul_pow, ← Finset.prod_pow, finprod_pow hfin]`. Use `mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_) (finprod_le_finprod' (finite_of_norm hx) hfa ha)` and prove the remaining obligations.

Rewrite using `[← NNReal.coe_le_coe, coe_nnnorm, InfinitePlace.norm_embedding_eq, NNReal.coe_pow]`. Conclude with `hA w`. Establish `h1 : (1 : ℝ≥0) ≤ (∏ w, vInf w (fun i => incA D (ξ i))) * ∏ᶠ v, vFin v (fun i => incA D (ξ i))`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Conclude with `absurd hle (not_le.2 (pow_lt_one₀ zero_le hlt hd))`. Conclude with `h1` after adjusting the coercions.
-/
theorem rat_size {n : ℕ} (ξ : Fin n → D.host.E) (hξ : ξ ≠ 0) :
    (Function.mulSupport fun v => vFin v (fun i => incA D (ξ i))).Finite ∧ 1 ≤ vsize (fun i => incA D (ξ i)) := by
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
  have hx : Algebra.norm D.host.F (ξ i) ≠ 0 := Algebra.norm_ne_zero_iff.2 hi
  have hd : Module.finrank D.host.F D.host.E ≠ 0 := Module.finrank_pos.ne'
  have ha : ∀ v, ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ ≤
      vFin v (fun i => incA D (ξ i)) ^ Module.finrank D.host.F D.host.E := fun v => by
    refine (GlobalTheory.T.finitePlace_relativeNorm_le_localSize_pow D v (ξ i)).trans (pow_le_pow_left₀ zero_le ?_ _)
    rw [← compFin_incA]
    exact Finset.le_sup (f := fun i => absFin D.host.F v (compFin D.host.F D.host.E v (incA D (ξ i))))
      (Finset.mem_univ i)
  have hA : ∀ w : InfinitePlace D.host.F, w (Algebra.norm D.host.F (ξ i)) ≤
      (vInf w (fun i => incA D (ξ i)) : ℝ) ^ Module.finrank D.host.F D.host.E := fun w =>
    GlobalTheory.T.infinitePlace_relativeNorm_le_maxEmbedding_pow D w (ξ i) _ fun τ => by rw [← infEmb_compInf_incA]; exact le_vInf w (fun i => incA D (ξ i)) τ i
  have hfin : (Function.mulSupport fun v => vFin v (fun i => incA D (ξ i))).Finite := by
    have h1 : ∀ᶠ v in Filter.cofinite, vFin v (fun i => incA D (ξ i)) ≤ 1 := by
      have := Filter.eventually_all.2 fun j => eventually_absFin_le_one D.host.F (incA D (ξ j))
      exact this.mono fun v hv => Finset.sup_le fun j _ => hv j
    refine ((Filter.eventually_cofinite.1 h1).union (finite_of_norm hx)).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Function.mem_mulSupport, not_le] at hc
    apply hv
    refine le_antisymm (not_lt.1 hc.1) ?_
    by_contra hlt
    push_neg at hlt
    have := (ha v).trans_lt (pow_lt_one₀ zero_le hlt hd)
    rw [hc.2] at this
    exact lt_irrefl _ this
  refine ⟨hfin, ?_⟩
  have hm : ∀ w : InfinitePlace D.host.F, w.mult = 1 := fun w => by
    simp [InfinitePlace.mult, IsTotallyReal.isReal w]
  have hP := NumberField.prod_abs_eq_one hx
  simp only [hm, pow_one] at hP
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at hP
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.mk_apply] at hP
  have hQ : (∏ w : InfinitePlace D.host.F, ‖w.embedding (Algebra.norm D.host.F (ξ i))‖₊) *
      ∏ᶠ v, ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ = 1 := by
    apply NNReal.coe_injective
    have e : ((∏ᶠ v, ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ : ℝ≥0) : ℝ) =
        ∏ᶠ v, ((‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F (ξ i))‖₊ : ℝ≥0) : ℝ) :=
      MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective _
    rw [NNReal.coe_mul, NNReal.coe_prod, e]
    simp only [coe_nnnorm, InfinitePlace.norm_embedding_eq, NNReal.coe_one]
    exact hP
  have hfa : (Function.mulSupport fun v =>
      vFin v (fun i => incA D (ξ i)) ^ Module.finrank D.host.F D.host.E).Finite :=
    hfin.subset (Function.mulSupport_pow _ _)
  have hle : (1 : ℝ≥0) ≤ ((∏ w, vInf w (fun i => incA D (ξ i))) * ∏ᶠ v, vFin v (fun i => incA D (ξ i))) ^
      Module.finrank D.host.F D.host.E := by
    rw [← hQ, mul_pow, ← Finset.prod_pow, finprod_pow hfin]
    refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_) (finprod_le_finprod' (finite_of_norm hx) hfa ha)
    rw [← NNReal.coe_le_coe, coe_nnnorm, InfinitePlace.norm_embedding_eq, NNReal.coe_pow]
    exact hA w
  have h1 : (1 : ℝ≥0) ≤ (∏ w, vInf w (fun i => incA D (ξ i))) * ∏ᶠ v, vFin v (fun i => incA D (ξ i)) := by
    by_contra hlt
    push_neg at hlt
    exact absurd hle (not_le.2 (pow_lt_one₀ zero_le hlt hd))
  exact_mod_cast h1

end GlobalTheory.SeenSize

namespace GlobalTheory.SeenSize
variable {D : D7}

/- English proof (translation)
Take `⟨hA, -⟩` from `rat_size ξ hξ`. Establish `e1` using `mulVec_seen V g ξ`. Establish `e2 : Formalism.L2.Theta.mt V g⁻¹ *ᵥ (fun i => incA D (ξ i)) = seen V g ξ` using `rfl`. Generalize the expression as in `(fun i => incA D (ξ i)) = y at hA e1 e2 ⊢`. Generalize the expression as in `seen V g ξ = x at e1 e2 ⊢`.

Establish `hH` using `finite_mulSupport_htFin D.host.F (matHom V g)`. Establish `hX : (Function.mulSupport fun v => vFin v x).Finite`. Use `(hA.union hH).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hc`.

Apply `hv` to reduce the goal to its premises. Establish `h1` using `vFin_mulVec_le V g⁻¹ v y`. Rewrite `h1` using `[e2, htFin_inv, hc.2, one_mul, hc.1]`. Establish `h2` using `vFin_mulVec_le V g v x`. Rewrite `h2` using `[e1, hc.2, one_mul, hc.1]`.

Conclude with `le_antisymm h1 h2`. Establish `hI : ∏ w, vInf w y ≤ ((V.rank : ℝ≥0) + 1) ^ Fintype.card (InfinitePlace D.host.F) * (∏ w, htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g))) * ∏ w, vInf w x`. Rewrite using `[← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod' fun w _ => ?_` and prove the remaining obligations. Use `vInf_mulVec_le V g w x` as an intermediate fact.

Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Establish `hF : ∏ᶠ v, vFin v y ≤ (∏ᶠ v, htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g))) * ∏ᶠ v, vFin v x`. Rewrite using `[← finprod_mul_distrib hH hX]`. Use `finprod_le_finprod' hA ((hH.union hX).subset (Function.mulSupport_mul _ _)) fun v => ?_` and prove the remaining obligations. Use `vFin_mulVec_le V g v x` as an intermediate fact.

Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Establish `key` using `mul_le_mul' hI hF`. Establish `e4 : GlobalTheory.Grow.height V g = (((∏ w, htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g))) * ∏ᶠ v, htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g)) : ℝ≥0) : ℝ)` using `rfl`. Rewrite using `[vsize, vsize, e4]`. Use `(NNReal.coe_le_coe.2 key).trans (le_of_eq ?_)` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vsize_rat_le (V : HSp D) (g : GA D V) (ξ : Fin V.rank → D.host.E) (hξ : ξ ≠ 0) :
    vsize (fun i => incA D (ξ i)) ≤
      ((V.rank : ℝ) + 1) ^ Fintype.card (InfinitePlace D.host.F) * GlobalTheory.Grow.height V g * vsize (seen V g ξ) := by
  obtain ⟨hA, -⟩ := rat_size ξ hξ
  have e1 := mulVec_seen V g ξ
  have e2 : Formalism.L2.Theta.mt V g⁻¹ *ᵥ (fun i => incA D (ξ i)) = seen V g ξ := rfl
  generalize (fun i => incA D (ξ i)) = y at hA e1 e2 ⊢
  generalize seen V g ξ = x at e1 e2 ⊢
  have hH := finite_mulSupport_htFin D.host.F (matHom V g)
  have hX : (Function.mulSupport fun v => vFin v x).Finite := by
    refine (hA.union hH).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hc
    apply hv
    have h1 := vFin_mulVec_le V g⁻¹ v y
    rw [e2, htFin_inv, hc.2, one_mul, hc.1] at h1
    have h2 := vFin_mulVec_le V g v x
    rw [e1, hc.2, one_mul, hc.1] at h2
    exact le_antisymm h1 h2
  have hI : ∏ w, vInf w y ≤ ((V.rank : ℝ≥0) + 1) ^ Fintype.card (InfinitePlace D.host.F) *
      (∏ w, htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g))) * ∏ w, vInf w x := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun w _ => ?_
    have := vInf_mulVec_le V g w x
    rwa [e1] at this
  have hF : ∏ᶠ v, vFin v y ≤ (∏ᶠ v, htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g))) *
      ∏ᶠ v, vFin v x := by
    rw [← finprod_mul_distrib hH hX]
    refine finprod_le_finprod' hA ((hH.union hX).subset (Function.mulSupport_mul _ _)) fun v => ?_
    have := vFin_mulVec_le V g v x
    rwa [e1] at this
  have key := mul_le_mul' hI hF
  have e4 : GlobalTheory.Grow.height V g = (((∏ w, htInf D.host.F w (Formalism.UG.bc (compInf D.host.F D.host.E w) (matHom V g))) *
      ∏ᶠ v, htFin D.host.F v (Formalism.UG.bc (compFin D.host.F D.host.E v) (matHom V g)) : ℝ≥0) : ℝ) := rfl
  rw [vsize, vsize, e4]
  refine (NNReal.coe_le_coe.2 key).trans (le_of_eq ?_)
  push_cast
  ring
end GlobalTheory.SeenSize

namespace GlobalTheory.SeenSize
variable {D : D7}

/- English proof (translation)
Simplify using `[Formalism.L2.Theta.mt, map_mul, Units.val_mul]`.
-/
theorem mt_mul (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

/- English proof (translation)
Take `⟨γ₀, h0⟩` from `(GlobalTheory.MixModel.mem_GQ_iff V γ).1 hγ`. Establish `h1 : Formalism.L2.Theta.mt V γ = γ₀.map (incA D)` using `h0.symm`. Establish `h2 : (fun i => incA D ((γ₀ *ᵥ ξ) i)) = Formalism.L2.Theta.mt V γ *ᵥ fun i => incA D (ξ i)`. Rewrite using `[h1]`. Use function extensionality and compare the values at `i`.

Conclude with `RingHom.map_mulVec (incA D) γ₀ ξ i`. Establish `h3 : Formalism.L2.Theta.mt V γ⁻¹ * Formalism.L2.Theta.mt V γ = 1`. Simplify using `using mt_mul_mt_inv V γ⁻¹`. Use `⟨γ₀ *ᵥ ξ, fun h => hξ ?_, ?_⟩` and prove the remaining obligations. Establish `h4 : Formalism.L2.Theta.mt V γ *ᵥ (fun i => incA D (ξ i)) = 0`.

Rewrite using `[← h2, h]`. Use function extensionality and compare the values at `i`. Conclude with `map_zero _`. Establish `h5 : (fun i => incA D (ξ i)) = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mulVec_mulVec, h3, one_mulVec]`. Use `_ = 0 := by rw [h4, mulVec_zero]`. Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.MixModel.incA_injective ((congrFun h5 i).trans (map_zero _).symm)`. Rewrite using `[seen, seen, h2, mulVec_mulVec, ← mt_mul, show (γ * g)⁻¹ * γ = g⁻¹ by group]`.
-/
theorem exists_seen_mul {V : HSp D} {γ : GA D V} (hγ : γ ∈ GQ V) (g : GA D V) {ξ : Fin V.rank → D.host.E}
    (hξ : ξ ≠ 0) : ∃ η : Fin V.rank → D.host.E, η ≠ 0 ∧ seen V (γ * g) η = seen V g ξ := by
  obtain ⟨γ₀, h0⟩ := (GlobalTheory.MixModel.mem_GQ_iff V γ).1 hγ
  have h1 : Formalism.L2.Theta.mt V γ = γ₀.map (incA D) := h0.symm
  have h2 : (fun i => incA D ((γ₀ *ᵥ ξ) i)) = Formalism.L2.Theta.mt V γ *ᵥ fun i => incA D (ξ i) := by
    rw [h1]; funext i; exact RingHom.map_mulVec (incA D) γ₀ ξ i
  have h3 : Formalism.L2.Theta.mt V γ⁻¹ * Formalism.L2.Theta.mt V γ = 1 := by
    simpa using mt_mul_mt_inv V γ⁻¹
  refine ⟨γ₀ *ᵥ ξ, fun h => hξ ?_, ?_⟩
  · have h4 : Formalism.L2.Theta.mt V γ *ᵥ (fun i => incA D (ξ i)) = 0 := by
      rw [← h2, h]; funext i; exact map_zero _
    have h5 : (fun i => incA D (ξ i)) = 0 := by
      calc (fun i => incA D (ξ i)) = Formalism.L2.Theta.mt V γ⁻¹ *ᵥ (Formalism.L2.Theta.mt V γ *ᵥ fun i => incA D (ξ i)) := by
            rw [mulVec_mulVec, h3, one_mulVec]
        _ = 0 := by rw [h4, mulVec_zero]
    funext i
    exact GlobalTheory.MixModel.incA_injective ((congrFun h5 i).trans (map_zero _).symm)
  · rw [seen, seen, h2, mulVec_mulVec, ← mt_mul, show (γ * g)⁻¹ * γ = g⁻¹ by group]

end GlobalTheory.SeenSize

namespace GlobalTheory.SeenSize

/- English proof (translation)
Introduce `D V`. Use `set K : ℝ := ((V.rank : ℝ) + 1) ^ Fintype.card (InfinitePlace D.host.F) with hK`. Establish `hK0 : 0 < K` using `by positivity`. Use `⟨(2 * K)⁻¹, 1, by positivity, fun g ξ hξ => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hle⟩` from `GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V g`.

Take `⟨η, hη, he⟩` from `exists_seen_mul hγ g hξ`. Establish `h1` using `(rat_size η hη).2.trans (vsize_rat_le V (γ * g) η hη)`. Rewrite `h1` using `[he, ← hK]`. Establish `hs` using `vsize_nonneg (seen V g ξ)`. Rewrite using `[pow_one, inv_le_iff_one_le_mul₀' (by positivity)]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_vsize_mul_quotHeight : ∀ (D : D7) (V : HSp D), ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ (g : GA D V)
    (ξ : Fin V.rank → D.host.E), ξ ≠ 0 → c ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ) * GlobalTheory.Grow.quotHeight V g ^ N := by
  intro D V
  set K : ℝ := ((V.rank : ℝ) + 1) ^ Fintype.card (InfinitePlace D.host.F) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨(2 * K)⁻¹, 1, by positivity, fun g ξ hξ => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V g
  obtain ⟨η, hη, he⟩ := exists_seen_mul hγ g hξ
  have h1 := (rat_size η hη).2.trans (vsize_rat_le V (γ * g) η hη)
  rw [he, ← hK] at h1
  have hs := vsize_nonneg (seen V g ξ)
  rw [pow_one, inv_le_iff_one_le_mul₀' (by positivity)]
  calc (1 : ℝ) ≤ K * GlobalTheory.Grow.height V (γ * g) * vsize (seen V g ξ) := h1
    _ ≤ K * (2 * GlobalTheory.Grow.quotHeight V g) * vsize (seen V g ξ) := by gcongr
    _ = _ := by ring

end GlobalTheory.SeenSize
