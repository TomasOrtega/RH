import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDvdMulInvolutionAddOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhaseStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatEqui.Col

variable (D : D7) {N N' : ℕ}

/- English proof (translation)
Establish `h : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y)` using `fun y => D.host.conjE_apply D.host.φ₀ y`. Apply `(D.host.φ₀ : D.host.E →+* ℂ).injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `D.host.φ₀ _ = D.host.φ₀ _`. Rewrite using `[h, h, Complex.conj_conj]`.
-/
theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  have h : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y) := fun y =>
    D.host.conjE_apply D.host.φ₀ y
  apply (D.host.φ₀ : D.host.E →+* ℂ).injective
  change D.host.φ₀ _ = D.host.φ₀ _
  rw [h, h, Complex.conj_conj]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj, conj_conj]`.
-/
theorem adj_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (adj D M) = M := by
  ext i j; simp [adj, conj_conj]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[adj]`. Simplify using `[adj, Matrix.one_apply, h, Ne.symm h]`.
-/
theorem adj_one_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (1 - M) = 1 - adj D M := by
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.one_apply, h, Ne.symm h]

/- English proof (translation)
Unfold `adj`. Rewrite using `[Matrix.det_transpose]`. Conclude with `(RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm`.
-/
theorem det_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : (adj D M).det = D.host.conj M.det := by
  unfold adj
  rw [Matrix.det_transpose]
  exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[adj]`. Simplify using `[adj, Matrix.diagonal_apply, h, Ne.symm h]`.
-/
theorem adj_diagonal {n : ℕ} (d : Fin n → D.host.E) :
    adj D (Matrix.diagonal d) = Matrix.diagonal fun i => D.host.conj (d i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.diagonal_apply, h, Ne.symm h]

/- English proof (translation)
Take `⟨Lt, h1, -⟩` from `exists_lattice_of_adelic_point D N`. Establish `: L = Lt g` using `by ext x; rw [h x, (h1 g).1 x]`. Rewrite using `[this]`. Conclude with `(h1 g).2`.
-/
theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

/- English proof (translation)
Take `⟨Lt, h1, h2, -⟩` from `exists_lattice_of_adelic_point D N`. Rewrite using `[← h2]`. Conclude with `(h1 _).1`.
-/
theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

/- English proof (translation)
Unfold `IsRat`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Both sides reduce to the same expression.
-/
theorem isRat_one (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

def halfP (N : ℕ) : Matrix (Fin N) (Fin N) D.host.E := Matrix.diagonal fun i => if i < i.rev then 1 else 0

def revS (N : ℕ) : Matrix (Fin N) (Fin N) D.host.E := Matrix.of fun i j => if i = j.rev then 1 else 0

/- English proof (translation)
Unfold `halfP`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp`.
-/
theorem halfP_mul : halfP D N * halfP D N = halfP D N := by
  unfold halfP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

/- English proof (translation)
Unfold `halfP`. Rewrite using `[adj_diagonal]`. Apply the tactic sequence `congr 1; funext i; split_ifs <;> simp`.
-/
theorem adj_halfP : adj D (halfP D N) = halfP D N := by
  unfold halfP
  rw [adj_diagonal]
  congr 1; funext i; split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [revS, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single j.rev]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
theorem revS_mul : revS D N * revS D N = 1 := by
  ext i j
  simp only [revS, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [adj, revS, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]`. Distinguish the cases in `h : i = j.rev`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Establish `h' : ¬ j = i.rev` using `fun e => h (by rw [e, Fin.rev_rev])`. Simplify using `[h, h']`.
-/
theorem adj_revS : adj D (revS D N) = revS D N := by
  ext i j
  simp only [adj, revS, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  by_cases h : i = j.rev
  · subst h; simp
  · have h' : ¬ j = i.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [halfP, revS, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.of_apply]`. Distinguish the cases in `h : i = j.rev`. Substitute `h` using the available equality. Take `⟨k, hk⟩` from `hN`.

Establish `hj` using `j.2`. Simplify using `only [Fin.rev_rev, if_true, Fin.lt_def, Fin.val_rev]`. Use `split_ifs with h1 h2 h2`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[h]`.
-/
theorem halfP_revS (hN : Even N) : halfP D N * revS D N = revS D N - revS D N * halfP D N := by
  ext i j
  simp only [halfP, revS, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.of_apply]
  by_cases h : i = j.rev
  · subst h
    obtain ⟨k, hk⟩ := hN
    have hj := j.2
    simp only [Fin.rev_rev, if_true, Fin.lt_def, Fin.val_rev]
    split_ifs with h1 h2 h2
    · omega
    · simp
    · simp
    · omega
  · simp [h]

/- English proof (translation)
Use `split_ifs`. Conclude with `ha`. Conclude with `isIntegral_zero`.
-/
theorem int_ite (p : Prop) [Decidable p] {a : D.host.E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (if p then a else 0) := by
  split_ifs
  · exact ha
  · exact isIntegral_zero

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Express the relevant statement in the definitionally equal form `mulV D 1 _ x τ i j = -(x τ i j) + (M : ℂ) * (mulV D 1 _ x τ i j)`. Rewrite using `[mulV_apply, mulV_apply]`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal, Matrix.mul_diagonal]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulV_scalar_right (M : ℕ) (b : D.host.E) (x : VC D N N') :
    mulV D 1 (Matrix.diagonal fun _ => -1 + (M : D.host.E) * b) x =
      -x + (M : ℂ) • mulV D 1 (Matrix.diagonal fun _ => b) x := by
  funext τ i j
  change mulV D 1 _ x τ i j = -(x τ i j) + (M : ℂ) * (mulV D 1 _ x τ i j)
  rw [mulV_apply, mulV_apply]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul,
    Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp
  ring

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, add_mul, neg_mul, mul_assoc, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_neg_add_smul (T : Tor D) (c : ℂ) (x z y : VC D N N') :
    Hf D T (-x + c • z) y = -Hf D T x y + c * Hf D T z y := by
  simp only [Hf, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, add_mul, neg_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/- English proof (translation)
Rewrite using `[Hf_mulV, adj_adj, adj_adj]`.
-/
theorem Hf_mulV' (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T z (mulV D M' M w) = Hf D T (mulV D (adj D M') (adj D M) z) w := by
  rw [Hf_mulV, adj_adj, adj_adj]

/- English proof (translation)
Rewrite using `[norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : ((‖w i‖ : ℝ) : ℂ) ^ 2 = g i * w i ^ 2`. Rewrite using `[← Complex.mul_conj', h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[norm_pow, Complex.ofReal_pow, ← two_mul, pow_mul, pow_mul, h1, mul_pow, mul_div_cancel_right₀ _ (pow_ne_zero _ (pow_ne_zero _ (hw i)))]`.
-/
theorem norm_div_prod {ι : Type} [Fintype ι] (w g : ι → ℂ) (k : ℕ) (hw : ∀ i, w i ≠ 0)
    (h : ∀ i, (starRingEnd ℂ) (w i) = g i * w i) :
    ((‖∏ i, w i ^ (k + k)‖ : ℝ) : ℂ) / ∏ i, w i ^ (k + k) = ∏ i, g i ^ k := by
  rw [norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : ((‖w i‖ : ℝ) : ℂ) ^ 2 = g i * w i ^ 2 := by
    rw [← Complex.mul_conj', h]; ring
  rw [norm_pow, Complex.ofReal_pow, ← two_mul, pow_mul, pow_mul, h1, mul_pow,
    mul_div_cancel_right₀ _ (pow_ne_zero _ (pow_ne_zero _ (hw i)))]

end GlobalTheory.RatEqui.Col

open GlobalTheory.RatEqui.Col in

/- English proof (translation)
Introduce `D cc δ hc N N' hN hN' th hth γA γ L₁ hrat hdet hmov`. Establish `h1 : γ * adj D γ = 1` using `(mem_ratG_intG D N').2.2.2.1 γA γ hrat`. Establish `h2 : adj D γ * γ = 1` using `mul_eq_one_comm.1 h1`. Take `⟨st1, st2, st3⟩` from `GlobalTheory.T.rationalMatrixMul_thetaLattices D cc δ hc N N'`. Establish `k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N')` using `Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D (moves_one D N'), rfl⟩`.

Establish `k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) L₁)` using `Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D hmov, rfl⟩`. Set `u : VC D N N' ≃ₗ[ℂ] VC D N N'` to `LinearEquiv.ofLinear (mulV D γ 1) (mulV D (adj D γ) 1) (LinearMap.ext fun x => by simp [mulV_mulV, h1, mulV_one]) (LinearMap.ext fun x => by simp [mulV_mulV, h2, mulV_one])`. Establish `hu : ∀ x, u x = mulV D γ 1 x` using `fun x => rfl`. Establish `hu' : ∀ x, u.symm x = mulV D (adj D γ) 1 x` using `fun x => rfl`. Establish `hsub : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D (1 - adj D γ) 1` using `LinearMap.ext fun x => by`.

Rewrite using `[mulV_sub_left, mulV_one]`. Both sides reduce to the same expression. Establish `hd : (1 - adj D γ).det = D.host.conj (1 - γ).det` using `by rw [← adj_one_sub, det_adj]`. Establish `hd0 : (1 - adj D γ).det ≠ 0`. Rewrite using `[hd]`.

Conclude with `(map_ne_zero _).2 hdet`. Establish `hdV : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) = ∏ τ, embT D τ (1 - adj D γ).det ^ N`. Rewrite using `[hsub, GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings]`. Simplify using the standard rewrite rules. Establish `hw : ∀ τ, embT D τ (1 - adj D γ).det ≠ 0` using `fun τ => (map_ne_zero _).2 hd0`.

Establish `i1 : ∀ i j, IsIntegral ℤ ((1 : Matrix (Fin N') (Fin N') D.host.E) i j)` using `fun i j => by`. Rewrite using `[Matrix.one_apply]`. Conclude with `int_ite D _ isIntegral_one`. Establish `comm : ∀ (M : Matrix (Fin N) (Fin N) D.host.E) x, mulV D 1 M (u x) = u (mulV D 1 M x)` using `fun M x => by`. Simplify using `[hu, mulV_mulV]`.

Establish `key` using `GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase D cc δ hc N N' _ _ k0 k1 u (fun z w => by rw [hu, hu, Hf_mulV, mulV_mulV, h2, adj_one, mul_one, mulV_one]) (fun x => by`. Rewrite using `[st3 1 γA 1 γ _ _ (isRat_one D N) hrat (moves_one D N) hmov x, adj_one, hu])`. Use the proof step `(by rw [hdV]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ))`. Use the proof step `(by`. Take `⟨m, hm, hm'⟩` from `st2 (1 - adj D γ)⁻¹ 1`.

Establish `e : ∀ x : VC D N N', m • x = m • mulV D (1 - adj D γ)⁻¹ 1 x - u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x)`. Introduce `x`. Use `LinearMap.congr_fun hsub (m • mulV D (1 - adj D γ)⁻¹ 1 x)` as an intermediate fact. Rewrite `this` using `[map_nsmul (mulV D (1 - adj D γ) 1), mulV_mulV, Matrix.mul_nonsing_inv _ (Ne.isUnit hd0), mul_one, mulV_one]`. Conclude with `this.symm`.

Use `⟨m, hm, fun x hx => ⟨_, hm' x hx, ?_, e x⟩⟩` and prove the remaining obligations. Establish `: u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) = m • mulV D (1 - adj D γ)⁻¹ 1 x - m • x`. Rewrite using `[e x]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `sub_mem (hm' x hx) (nsmul_mem hx m))`. Use the proof step `(mulV D 1 (halfP D N)) (mulV D 1 (revS D N))`. Use the proof step `(fun x hx => ⟨st1 _ _ i1 (fun i j => by`. Rewrite using `[halfP, Matrix.diagonal_apply]`. Conclude with `int_ite D _ (int_ite D _ isIntegral_one)) x hx,`.

Use `st1 _ _ i1 (fun i j => int_ite D _ isIntegral_one) x hx⟩)`. Use the proof step `(fun x => by rw [mulV_mulV, halfP_mul, mul_one])`. Use the proof step `(fun x y => by rw [Hf_mulV, adj_one, adj_halfP])`. Use the proof step `(fun x => by rw [mulV_mulV, revS_mul, mul_one, mulV_one])`. Use the proof step `(fun x y => by rw [Hf_mulV, adj_one, adj_revS, mulV_mulV, revS_mul, mul_one, mulV_one])`.

Use the proof step `(fun x => by rw [mulV_mulV, mulV_mulV, mul_one, halfP_revS D hN, mulV_sub_right])`. Use the proof step `(comm _) (comm _)`. Use the proof step `(fun M hM => by`. Take `⟨l, b, hl⟩` from `GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM`. Establish `hb : D.host.conj (b : D.host.E) = b`.

Establish `h3` using `congrArg D.host.conj hl`. Rewrite `h3` using `[map_mul, conj_conj, mul_comm, hl, map_add, map_neg, map_one, map_mul, map_natCast]`. Conclude with `(mul_left_cancel₀ (Nat.cast_ne_zero.2 hM.ne') (add_left_cancel h3)).symm`. Establish `idg : ∀ a : 𝓞 D.host.E, ∀ i j : Fin N, IsIntegral ℤ (Matrix.diagonal (fun _ => (a : D.host.E)) i j)` using `fun a i j => by`. Rewrite using `[Matrix.diagonal_apply]`.

Conclude with `int_ite D _ a.2`. Use `⟨mulV D 1 (Matrix.diagonal fun _ => (l : D.host.E)), mulV D 1 (Matrix.diagonal fun _ => (b : D.host.E)), fun x hx => ⟨st1 _ _ i1 (idg l) x hx, st1 _ _ i1 (idg b) x hx⟩, comm _, comm _, fun x => ?_, fun x y => ?_, fun x y => ?_⟩` and prove the remaining obligations. Simplify using `only [mulV_mulV, halfP, Matrix.diagonal_mul_diagonal, mul_comm]`. Rewrite using `[Hf_mulV, adj_one, adj_diagonal, hb]`. Rewrite using `[Hf_mulV', adj_one, adj_diagonal, mulV_mulV, mul_one, Matrix.diagonal_mul_diagonal, hl, mulV_scalar_right, hf_neg_add_smul])`.

Use `th hth`. Rewrite using `[pull_eq]`. Use `key.trans ?_` and prove the remaining obligations. Use `congr 1`. Take `⟨k, hk⟩` from `hN`.

Establish `hk2 : N / 2 = k` using `by omega`. Rewrite using `[hdV, hk2]`. Establish `hconj : ∀ τ, (starRingEnd ℂ) (embT D τ (1 - adj D γ).det) = embT D τ γ.det * embT D τ (1 - adj D γ).det` using `fun τ => by`. Rewrite using `[← embT_conj, ← map_mul, ← Matrix.det_mul, mul_sub, h1, mul_one, hd, conj_conj, ← neg_sub γ 1, Matrix.det_neg, Fintype.card_fin, hN'.neg_one_pow, one_mul]`. Use `norm_div_prod _ _ k hw hconj` as an intermediate fact.

Rewrite `this` using `[← hk]`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.RatEqui.pull_right_eq_det_smul : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA' : GA D N') (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA' : GL (Fin N') (AE D)) γ' → (1 - γ').det ≠ 0 → Moves D (γA' : GL (Fin N') (AE D)) L₁' → pull D (tor0 D cc δ) 1 γ' th = (∏ τ, embT D τ γ'.det ^ (N / 2)) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) (stdL D N) L₁') th := by
  intro D cc δ hc N N' hN hN' th hth γA γ L₁ hrat hdet hmov
  have h1 : γ * adj D γ = 1 := (mem_ratG_intG D N').2.2.2.1 γA γ hrat
  have h2 : adj D γ * γ = 1 := mul_eq_one_comm.1 h1
  obtain ⟨st1, st2, st3⟩ := GlobalTheory.T.rationalMatrixMul_thetaLattices D cc δ hc N N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) L₁) :=
    Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D hmov, rfl⟩
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D γ 1) (mulV D (adj D γ) 1)
    (LinearMap.ext fun x => by simp [mulV_mulV, h1, mulV_one])
    (LinearMap.ext fun x => by simp [mulV_mulV, h2, mulV_one])
  have hu : ∀ x, u x = mulV D γ 1 x := fun x => rfl
  have hu' : ∀ x, u.symm x = mulV D (adj D γ) 1 x := fun x => rfl
  have hsub : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D (1 - adj D γ) 1 :=
    LinearMap.ext fun x => by
      rw [mulV_sub_left, mulV_one]; rfl
  have hd : (1 - adj D γ).det = D.host.conj (1 - γ).det := by rw [← adj_one_sub, det_adj]
  have hd0 : (1 - adj D γ).det ≠ 0 := by
    rw [hd]; exact (map_ne_zero _).2 hdet
  have hdV : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) =
      ∏ τ, embT D τ (1 - adj D γ).det ^ N := by
    rw [hsub, GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings]; simp
  have hw : ∀ τ, embT D τ (1 - adj D γ).det ≠ 0 := fun τ => (map_ne_zero _).2 hd0
  have i1 : ∀ i j, IsIntegral ℤ ((1 : Matrix (Fin N') (Fin N') D.host.E) i j) := fun i j => by
    rw [Matrix.one_apply]; exact int_ite D _ isIntegral_one
  have comm : ∀ (M : Matrix (Fin N) (Fin N) D.host.E) x, mulV D 1 M (u x) = u (mulV D 1 M x) := fun M x => by
    simp [hu, mulV_mulV]
  have key := GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase D cc δ hc N N' _ _ k0 k1 u
    (fun z w => by rw [hu, hu, Hf_mulV, mulV_mulV, h2, adj_one, mul_one, mulV_one])
    (fun x => by
      rw [st3 1 γA 1 γ _ _ (isRat_one D N) hrat (moves_one D N) hmov x, adj_one, hu])
    (by rw [hdV]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ))
    (by
      obtain ⟨m, hm, hm'⟩ := st2 (1 - adj D γ)⁻¹ 1
      have e : ∀ x : VC D N N', m • x = m • mulV D (1 - adj D γ)⁻¹ 1 x - u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) := by
        intro x
        have := LinearMap.congr_fun hsub (m • mulV D (1 - adj D γ)⁻¹ 1 x)
        rw [map_nsmul (mulV D (1 - adj D γ) 1), mulV_mulV, Matrix.mul_nonsing_inv _ (Ne.isUnit hd0), mul_one,
          mulV_one] at this
        exact this.symm
      refine ⟨m, hm, fun x hx => ⟨_, hm' x hx, ?_, e x⟩⟩
      have : u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) = m • mulV D (1 - adj D γ)⁻¹ 1 x - m • x := by
        rw [e x]; abel
      rw [this]
      exact sub_mem (hm' x hx) (nsmul_mem hx m))
    (mulV D 1 (halfP D N)) (mulV D 1 (revS D N))
    (fun x hx => ⟨st1 _ _ i1 (fun i j => by
        rw [halfP, Matrix.diagonal_apply]; exact int_ite D _ (int_ite D _ isIntegral_one)) x hx,
      st1 _ _ i1 (fun i j => int_ite D _ isIntegral_one) x hx⟩)
    (fun x => by rw [mulV_mulV, halfP_mul, mul_one])
    (fun x y => by rw [Hf_mulV, adj_one, adj_halfP])
    (fun x => by rw [mulV_mulV, revS_mul, mul_one, mulV_one])
    (fun x y => by rw [Hf_mulV, adj_one, adj_revS, mulV_mulV, revS_mul, mul_one, mulV_one])
    (fun x => by rw [mulV_mulV, mulV_mulV, mul_one, halfP_revS D hN, mulV_sub_right])
    (comm _) (comm _)
    (fun M hM => by
      obtain ⟨l, b, hl⟩ := GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM
      have hb : D.host.conj (b : D.host.E) = b := by
        have h3 := congrArg D.host.conj hl
        rw [map_mul, conj_conj, mul_comm, hl, map_add, map_neg, map_one, map_mul, map_natCast] at h3
        exact (mul_left_cancel₀ (Nat.cast_ne_zero.2 hM.ne') (add_left_cancel h3)).symm
      have idg : ∀ a : 𝓞 D.host.E, ∀ i j : Fin N,
          IsIntegral ℤ (Matrix.diagonal (fun _ => (a : D.host.E)) i j) := fun a i j => by
        rw [Matrix.diagonal_apply]; exact int_ite D _ a.2
      refine ⟨mulV D 1 (Matrix.diagonal fun _ => (l : D.host.E)), mulV D 1 (Matrix.diagonal fun _ => (b : D.host.E)),
        fun x hx => ⟨st1 _ _ i1 (idg l) x hx, st1 _ _ i1 (idg b) x hx⟩, comm _, comm _, fun x => ?_,
        fun x y => ?_, fun x y => ?_⟩
      · simp only [mulV_mulV, halfP, Matrix.diagonal_mul_diagonal, mul_comm]
      · rw [Hf_mulV, adj_one, adj_diagonal, hb]
      · rw [Hf_mulV', adj_one, adj_diagonal, mulV_mulV, mul_one, Matrix.diagonal_mul_diagonal, hl,
          mulV_scalar_right, hf_neg_add_smul])
    th hth
  rw [pull_eq]
  refine key.trans ?_
  congr 1
  obtain ⟨k, hk⟩ := hN
  have hk2 : N / 2 = k := by omega
  rw [hdV, hk2]
  have hconj : ∀ τ, (starRingEnd ℂ) (embT D τ (1 - adj D γ).det) =
      embT D τ γ.det * embT D τ (1 - adj D γ).det := fun τ => by
    rw [← embT_conj, ← map_mul, ← Matrix.det_mul, mul_sub, h1, mul_one, hd, conj_conj, ← neg_sub γ 1,
      Matrix.det_neg, Fintype.card_fin, hN'.neg_one_pow, one_mul]
  have := norm_div_prod _ _ k hw hconj
  rwa [← hk] at this
