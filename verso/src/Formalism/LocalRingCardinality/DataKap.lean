import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.PrincipalHermitianLattice

noncomputable section

namespace Formalism.BasicNotions

open scoped BigOperators

namespace DV

def eQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℚ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then (D.hc τ).e ⟨j - 1, by omega⟩ else 0

def sigPar (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k - 1 then (D.hc τ).v ⟨i, h⟩
  else if hb : i - (D.R.k - 1) < D.R.m then -(D.hc τ).b ⟨i - (D.R.k - 1), hb⟩ else 0

def aPlusQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  sigPar D τ i + eQ D j τ - ((D.R.nV : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((D.R.k : ℚ) + j - 1) - ((D.R.m : ℚ) - j)) / 2

def aMinusQ (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ℚ :=
  (if h : j + c < D.R.m then (D.hc τ).b ⟨j + c, h⟩ else 0) - eQ D j τ - ((D.R.t : ℚ) + 1 + 2 * (c : ℚ)) / 2

def aPlus (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℝ := ((aPlusQ D j τ i : ℚ) : ℝ)

def aMinus (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ℝ := ((aMinusQ D j τ c : ℚ) : ℝ)

def KapDef (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ,
    (∀ i : Fin (D.R.sigW j).1, (D.what₂.kaBig j τ i : ℚ) = aPlusQ D j τ i) ∧
    (∀ c : Fin (D.R.sigW j).2, (D.what₂.kaSmall j τ c : ℚ) = -aMinusQ D j τ c)

/- English proof (translation)
Unfold `eQ wSz`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eQ_cast (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ((eQ D j τ : ℚ) : ℝ) = wSz D j τ := by
  unfold eQ wSz
  split_ifs <;> simp

/- English proof (translation)
Unfold `eQ`. Use `split_ifs`. Conclude with `(D.hc τ).e_int _`. Conclude with `⟨0, by simp⟩`.
-/
theorem eQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ∃ z : ℤ, eQ D j τ = z := by
  unfold eQ
  split_ifs
  · exact (D.hc τ).e_int _
  · exact ⟨0, by simp⟩

/- English proof (translation)
Unfold `sigPar`. Use `split_ifs`. Conclude with `(D.hc τ).v_int _`. Take `⟨z, hz⟩` from `(D.hc τ).b_int ⟨i - (D.R.k - 1), by assumption⟩`. Conclude with `⟨-z, by rw [hz]; simp⟩`.

Conclude with `⟨0, by simp⟩`.
-/
theorem sigPar_int (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ∃ z : ℤ, sigPar D τ i = z := by
  unfold sigPar
  split_ifs
  · exact (D.hc τ).v_int _
  · obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨i - (D.R.k - 1), by assumption⟩
    exact ⟨-z, by rw [hz]; simp⟩
  · exact ⟨0, by simp⟩

/- English proof (translation)
Establish `h : 1 ≤ R.k + R.m` using `by have := R.two_le_m; omega`. Unfold `Ranks.nV Ranks.r`. Move the coercions through the operations in `[Nat.cast_sub h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nV_cast (R : Ranks) : (R.nV : ℚ) = (R.k : ℚ) + R.m - 1 + R.t := by
  have h : 1 ≤ R.k + R.m := by have := R.two_le_m; omega
  unfold Ranks.nV Ranks.r
  push_cast [Nat.cast_sub h]
  ring

/- English proof (translation)
Unfold `aPlusQ`. Rewrite using `[nV_cast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aPlusQ_eq (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) :
    aPlusQ D j τ i = sigPar D τ i + eQ D j τ - ((D.R.k : ℚ) + j - 1 - 1 - i) - ((D.R.t : ℚ) + 1) / 2 := by
  unfold aPlusQ
  rw [nV_cast]
  ring

/- English proof (translation)
Take `⟨a, ha⟩` from `sigPar_int D τ i`. Take `⟨b, hb⟩` from `eQ_int D j τ`. Take `⟨s, hs⟩` from `D.R.t_odd`. Use `⟨a + b - ((D.R.k : ℤ) + j - 1 - 1 - i) - (s + 1), ?_⟩` and prove the remaining obligations. Rewrite using `[aPlusQ_eq, ha, hb, hs]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aPlusQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ∃ z : ℤ, aPlusQ D j τ i = z := by
  obtain ⟨a, ha⟩ := sigPar_int D τ i
  obtain ⟨b, hb⟩ := eQ_int D j τ
  obtain ⟨s, hs⟩ := D.R.t_odd
  refine ⟨a + b - ((D.R.k : ℤ) + j - 1 - 1 - i) - (s + 1), ?_⟩
  rw [aPlusQ_eq, ha, hb, hs]
  push_cast
  ring

/- English proof (translation)
Take `⟨b, hb⟩` from `eQ_int D j τ`. Take `⟨s, hs⟩` from `D.R.t_odd`. Establish `h1 : ∃ a : ℤ, (if h : j + c < D.R.m then (D.hc τ).b ⟨j + c, h⟩ else 0) = (a : ℚ)` using `by split_ifs`. Conclude with `(D.hc τ).b_int _`. Conclude with `⟨0, by simp⟩`.

Take `⟨a, ha⟩` from `h1`. Use `⟨a - b - (s + 1 + c), ?_⟩` and prove the remaining obligations. Unfold `aMinusQ`. Rewrite using `[ha, hb, hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aMinusQ_int (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) : ∃ z : ℤ, aMinusQ D j τ c = z := by
  obtain ⟨b, hb⟩ := eQ_int D j τ
  obtain ⟨s, hs⟩ := D.R.t_odd
  have h1 : ∃ a : ℤ, (if h : j + c < D.R.m then (D.hc τ).b ⟨j + c, h⟩ else 0) = (a : ℚ) := by
    split_ifs
    · exact (D.hc τ).b_int _
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := h1
  refine ⟨a - b - (s + 1 + c), ?_⟩
  unfold aMinusQ
  rw [ha, hb, hs]
  push_cast
  ring

/- English proof (translation)
Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hi : ¬ (D.R.k + j - 1 - 1 < D.R.k - 1)` using `by omega`. Establish `hb : D.R.k + j - 1 - 1 - (D.R.k - 1) < D.R.m` using `by omega`. Establish `hidx : D.R.k + j - 1 - 1 - (D.R.k - 1) = j - 1` using `by omega`. Establish `hc : ((D.R.k + j - 1 - 1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1`.

Establish `: D.R.k + j - 1 - 1 = D.R.k + j - 2` using `by omega`. Rewrite using `[this, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hg` using `(D.hc τ).gap_be ⟨j - 1, by omega⟩`.

Rewrite using `[aPlusQ_eq, hc]`. Unfold `sigPar eQ`. Rewrite using `[dif_neg hi, dif_pos hb, dif_pos ⟨h1, h2⟩]`. Establish `: (⟨D.R.k + j - 1 - 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩` using `Fin.ext hidx`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem aPlusQ_last (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    1 ≤ aPlusQ D j τ (D.R.k + j - 1 - 1) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hi : ¬ (D.R.k + j - 1 - 1 < D.R.k - 1) := by omega
  have hb : D.R.k + j - 1 - 1 - (D.R.k - 1) < D.R.m := by omega
  have hidx : D.R.k + j - 1 - 1 - (D.R.k - 1) = j - 1 := by omega
  have hc : ((D.R.k + j - 1 - 1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : D.R.k + j - 1 - 1 = D.R.k + j - 2 := by omega
    rw [this, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hg := (D.hc τ).gap_be ⟨j - 1, by omega⟩
  rw [aPlusQ_eq, hc]
  unfold sigPar eQ
  rw [dif_neg hi, dif_pos hb, dif_pos ⟨h1, h2⟩]
  have : (⟨D.R.k + j - 1 - 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext hidx
  rw [this]
  linarith

/- English proof (translation)
Establish `hg` using `(D.hc τ).gap_eb ⟨j - 1, by omega⟩ (by show j - 1 + 1 < D.R.m; omega)`. Establish `hidx : (⟨j - 1 + 1, by omega⟩ : Fin D.R.m) = ⟨j + 0, by omega⟩` using `Fin.ext (by show j - 1 + 1 = j + 0; omega)`. Unfold `aMinusQ eQ`. Rewrite using `[dif_pos (by omega : j + 0 < D.R.m), dif_pos ⟨h1, h2.le⟩]`. Rewrite `hg` using `[hidx]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem aMinusQ_last (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) (τ : D.what₂.Tau) :
    1 ≤ aMinusQ D j τ 0 := by
  have hg := (D.hc τ).gap_eb ⟨j - 1, by omega⟩ (by show j - 1 + 1 < D.R.m; omega)
  have hidx : (⟨j - 1 + 1, by omega⟩ : Fin D.R.m) = ⟨j + 0, by omega⟩ := Fin.ext (by show j - 1 + 1 = j + 0; omega)
  unfold aMinusQ eQ
  rw [dif_pos (by omega : j + 0 < D.R.m), dif_pos ⟨h1, h2.le⟩]
  rw [hidx] at hg
  push_cast
  linarith

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun j τ i => (aPlusQ_int D j τ i).choose, fun j τ c => -(aMinusQ_int D j τ c).choose, fun j τ => ⟨fun i => (aPlusQ_int D j τ i).choose_spec.symm, fun c => by push_cast; rw [← (aMinusQ_int D j τ c).choose_spec]⟩⟩`.
-/
theorem exists_blocks (D : D7) :
    ∃ (kb : ∀ j, D.what₂.Tau → Fin (D.R.sigW j).1 → ℤ) (ks : ∀ j, D.what₂.Tau → Fin (D.R.sigW j).2 → ℤ),
      ∀ j τ, (∀ i, (kb j τ i : ℚ) = aPlusQ D j τ i) ∧ (∀ c, (ks j τ c : ℚ) = -aMinusQ D j τ c) :=
  ⟨fun j τ i => (aPlusQ_int D j τ i).choose, fun j τ c => -(aMinusQ_int D j τ c).choose,
    fun j τ => ⟨fun i => (aPlusQ_int D j τ i).choose_spec.symm,
      fun c => by push_cast; rw [← (aMinusQ_int D j τ c).choose_spec]⟩⟩

def lamTr (D : D7) (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) : ℝ :=
  (LinearMap.trace ℂ (D.what₂.Mj j)
    (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ ((D.what₂.isot j π).starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j))).re /
    (Module.finrank ℂ (D.what₂.isot j π) : ℝ)

def LamDef (D : D7) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ π, D.what₂.isot j π ≠ ⊥ → D.what₂.lamP μ j π = lamTr D μ j π

def LamScalar (D : D7) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ π, ∃ c : ℝ, ∀ x ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = (c : ℂ) • x

/- English proof (translation)
Use `set W := D.what₂.isot j π with hW`. Establish `hP : LinearMap.IsProj W (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j)` using `⟨fun x => W.starProjection_apply_mem x, fun x hx => Submodule.starProjection_eq_self_iff.2 hx⟩`. Establish `hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) = (c : ℂ) • (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j)`. Use extensionality with `y`. Conclude with `hc _ (W.starProjection_apply_mem y)`.

Establish `hf : (Module.finrank ℂ W : ℝ) ≠ 0`. Establish `: 0 < Module.finrank ℂ W` using `Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 h0)`. Conclude with `this.ne'` after adjusting the coercions. Use `show (LinearMap.trace ℂ (D.what₂.Mj j) (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j))).re / (Module.finrank ℂ W : ℝ) = c`. Rewrite using `[hT, map_smul, hP.trace, smul_eq_mul]`.

Establish `: ((c : ℂ) * ((Module.finrank ℂ W : ℕ) : ℂ)).re = c * (Module.finrank ℂ W : ℝ)`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]`. Rewrite using `[this, mul_div_assoc, div_self hf, mul_one]`.
-/
theorem lamTr_of_scalar (D : D7) (μ : D.what₂.Tup) (j : ℕ) (π : D.what₂.FT) (c : ℝ) (h0 : D.what₂.isot j π ≠ ⊥)
    (hc : ∀ x ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = (c : ℂ) • x) : lamTr D μ j π = c := by
  set W := D.what₂.isot j π with hW
  have hP : LinearMap.IsProj W (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) :=
    ⟨fun x => W.starProjection_apply_mem x, fun x hx => Submodule.starProjection_eq_self_iff.2 hx⟩
  have hT : D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) =
      (c : ℂ) • (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j) := by
    ext y
    exact hc _ (W.starProjection_apply_mem y)
  have hf : (Module.finrank ℂ W : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℂ W := Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 h0)
    exact_mod_cast this.ne'
  show (LinearMap.trace ℂ (D.what₂.Mj j) (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j ∘ₗ
    (W.starProjection : D.what₂.Mj j →ₗ[ℂ] D.what₂.Mj j))).re / (Module.finrank ℂ W : ℝ) = c
  rw [hT, map_smul, hP.trace, smul_eq_mul]
  have : ((c : ℂ) * ((Module.finrank ℂ W : ℕ) : ℂ)).re = c * (Module.finrank ℂ W : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this, mul_div_assoc, div_self hf, mul_one]

def lamProd (D : D7) {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
  ∏ σ, ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ)

end DV

namespace RowSide

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
  [FiniteDimensional ℂ EE] (S : RowSide D EE)

def iiStar : EE →ₗ[ℂ] EE := S.iotaQ D.what₂.mu0 ∘ₗ LinearMap.adjoint (S.iotaQ D.what₂.mu0)

def kapRatio {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ := (LinearMap.det S.iiStar).re / DV.lamProd D ty

def kapOf {n : ℕ} (ty : Fin n → D.what₂.FT) : ℝ :=
  if 0 < S.kapRatio ty then S.kapRatio ty ^ ((n : ℝ)⁻¹) else 1

/- English proof (translation)
Unfold `kapOf`. Use `split_ifs with h`. Conclude with `Real.rpow_pos_of_pos h _`. Conclude with `one_pos`.
-/
theorem kapOf_pos {n : ℕ} (ty : Fin n → D.what₂.FT) : 0 < S.kapOf ty := by
  unfold kapOf
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact one_pos

/- English proof (translation)
Take `⟨hbij, hk, ρ, hρ0, -, -, h⟩` from `h`. Use `set P : Fin n → ℝ := fun σ => ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) with hPdef`. Establish `hT : ∀ σ, S.iiStar (b σ) = ((kap * P σ : ℝ) : ℂ) • b σ`. Introduce `σ`. Use `h D.what₂.mu0 σ` as an intermediate fact.

Rewrite `this` using `[hρ0, mul_one]`. Conclude with `this`. Establish `hP : ∀ σ, P σ ≠ 0`. Introduce `σ h0`. Establish `hz : S.iotaQ D.what₂.mu0 (LinearMap.adjoint (S.iotaQ D.what₂.mu0) (b σ)) = 0`.

Use `hT σ` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify `this` using `[iiStar]`. Establish `h1 : LinearMap.adjoint (S.iotaQ D.what₂.mu0) (b σ) = 0`. Rewrite using `[← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_right, hz, inner_zero_left]`.

Take `⟨y, hy⟩` from `(hbij D.what₂.mu0).2 (b σ)`. Establish `h2 : inner ℂ (b σ) (b σ) = 0` using `by nth_rewrite 1 [← hy]`. Rewrite using `[← LinearMap.adjoint_inner_right, h1, inner_zero_right]`. Establish `h3 : b σ = 0` using `inner_self_eq_zero.1 h2`. Establish `h4` using `b.orthonormal.1 σ`.

Rewrite `h4` using `[h3, norm_zero]`. Conclude with `zero_ne_one h4`. Establish `hdet : LinearMap.det S.iiStar = ((kap ^ n * ∏ σ, P σ : ℝ) : ℂ)`. Rewrite using `[← LinearMap.det_toMatrix b.toBasis]`. Establish `hM : LinearMap.toMatrix b.toBasis b.toBasis S.iiStar = Matrix.diagonal (fun σ => ((kap * P σ : ℝ) : ℂ))`.

Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hT j, map_smul, Finsupp.smul_apply, ← OrthonormalBasis.coe_toBasis, Module.Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hij, if_neg (fun h => hij h.symm)]`. Simplify using the standard rewrite rules. Rewrite using `[hM, Matrix.det_diagonal, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hne : (∏ σ, P σ) ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun σ _ => hP σ)`. Establish `hr : S.kapRatio ty = kap ^ n`.

Unfold `kapRatio DV.lamProd`. Rewrite using `[hdet, Complex.ofReal_re]`. Conclude with `mul_div_cancel_right₀ _ hne`. Unfold `kapOf`. Rewrite using `[hr, if_pos (pow_pos hk n), Real.pow_rpow_inv_natCast hk.le hn.ne']`.
-/
theorem RowLatticeBoundForBasis.kap_eq {S : RowSide D EE} {n : ℕ} {b : OrthonormalBasis (Fin n) ℂ EE} {ty : Fin n → D.what₂.FT} {kap : ℝ}
    (h : S.RowLatticeBoundForBasis b ty kap) (hn : 0 < n) : kap = S.kapOf ty := by
  obtain ⟨hbij, hk, ρ, hρ0, -, -, h⟩ := h
  set P : Fin n → ℝ := fun σ => ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (ty σ) with hPdef
  have hT : ∀ σ, S.iiStar (b σ) = ((kap * P σ : ℝ) : ℂ) • b σ := by
    intro σ
    have := h D.what₂.mu0 σ
    rw [hρ0, mul_one] at this
    exact this
  have hP : ∀ σ, P σ ≠ 0 := by
    intro σ h0
    have hz : S.iotaQ D.what₂.mu0 (LinearMap.adjoint (S.iotaQ D.what₂.mu0) (b σ)) = 0 := by
      have := hT σ
      rw [h0] at this
      simpa [iiStar] using this
    have h1 : LinearMap.adjoint (S.iotaQ D.what₂.mu0) (b σ) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_right, hz, inner_zero_left]
    obtain ⟨y, hy⟩ := (hbij D.what₂.mu0).2 (b σ)
    have h2 : inner ℂ (b σ) (b σ) = 0 := by
      nth_rewrite 1 [← hy]
      rw [← LinearMap.adjoint_inner_right, h1, inner_zero_right]
    have h3 : b σ = 0 := inner_self_eq_zero.1 h2
    have h4 := b.orthonormal.1 σ
    rw [h3, norm_zero] at h4
    exact zero_ne_one h4
  have hdet : LinearMap.det S.iiStar = ((kap ^ n * ∏ σ, P σ : ℝ) : ℂ) := by
    rw [← LinearMap.det_toMatrix b.toBasis]
    have hM : LinearMap.toMatrix b.toBasis b.toBasis S.iiStar =
        Matrix.diagonal (fun σ => ((kap * P σ : ℝ) : ℂ)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hT j, map_smul, Finsupp.smul_apply,
        ← OrthonormalBasis.coe_toBasis, Module.Basis.repr_self, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : j = i
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij h.symm)]; simp
    rw [hM, Matrix.det_diagonal, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hne : (∏ σ, P σ) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun σ _ => hP σ)
  have hr : S.kapRatio ty = kap ^ n := by
    unfold kapRatio DV.lamProd
    rw [hdet, Complex.ofReal_re]
    exact mul_div_cancel_right₀ _ hne
  unfold kapOf
  rw [hr, if_pos (pow_pos hk n), Real.pow_rpow_inv_natCast hk.le hn.ne']

end RowSide

def kapSharp (D : D7) : ℝ := (RowSide.sharp D).kapOf D.what₂.ft

def BaseLevelRowSide.kap0 {D : D7} (X : BaseLevelRowSide D) : ℝ := X.s.kapOf D.what₂.ft0

def DV.KapRBase {D : D7} (X : DivX D) : Prop := X.kapR D.what₂.embLL = kapSharp D

def SharpLatticeBoundForNumber (D : D7) : Prop := SharpLatticeBound D (kapSharp D)

def BaseLevelRowSide.BaseLevelSideLevelOneCondition {D : D7} (X : BaseLevelRowSide D) : Prop := X.L1c0 X.kap0

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨_, h⟩ => by have := RowSide.RowLatticeBoundForBasis.kap_eq h hn; unfold SharpLatticeBoundForNumber kapSharp; rw [← this]; exact h, fun h => ⟨_, h⟩⟩`.
-/
theorem SharpLatticeBound.iff_def {D : D7} (hn : 0 < D.what₂.Drows) : (∃ kap, SharpLatticeBound D kap) ↔ SharpLatticeBoundForNumber D :=
  ⟨fun ⟨_, h⟩ => by have := RowSide.RowLatticeBoundForBasis.kap_eq h hn; unfold SharpLatticeBoundForNumber kapSharp; rw [← this]; exact h, fun h => ⟨_, h⟩⟩

end Formalism.BasicNotions

end
