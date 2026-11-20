import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IntegrandMono
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.MobJJDiag
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

open Complex MvPolynomial

/- English proof (translation)
Take `⟨Q, hQ, rfl⟩` from `h`. Use `⟨MvPolynomial.C c * Q, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(MvPolynomial.totalDegree_mul _ _).trans (by simp [hQ])`. Use function extensionality and compare the values at `u`. Simplify using `only [evX, map_mul, MvPolynomial.eval_C]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPG_smul {sg : ℤˣ} {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ} {f : (Fin m → Fin n → ℂ) → ℂ} (c : ℂ)
    (h : IsPG sg d Z f) : IsPG sg d Z (fun u => c * f u) := by
  obtain ⟨Q, hQ, rfl⟩ := h
  refine ⟨MvPolynomial.C c * Q, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [hQ])
  · funext u
    simp only [evX, map_mul, MvPolynomial.eval_C]
    ring

/- English proof (translation)
Establish `key : ∀ e ∈ Q.support, ∃ Q' : PX m n, Q'.totalDegree ≤ d ∧ ∀ u, ∫ v : Fin m → Fin n → ℂ, ker t u v * (evX (MvPolynomial.monomial e (Q.coeff e)) v * gZ sg (Matrix.diagonal z) v) = evX Q' u * gZ sg (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹) u`. Introduce `e he`. Take `⟨Q', hQ', h'⟩` from `four_mono sg t z hz e (Q.coeff e)`. Conclude with `⟨Q', hQ'.trans ((MvPolynomial.le_totalDegree he).trans hQ), h'⟩`. Use `choose! F hFd hF using key`.

Use `⟨∑ e ∈ Q.support, F e, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun e he => hFd e he)`. Use function extensionality and compare the values at `u`. Establish `hsplit : ∀ v, ker t u v * (evX Q v * gZ sg (Matrix.diagonal z) v) = ∑ e ∈ Q.support, ker t u v * (evX (MvPolynomial.monomial e (Q.coeff e)) v * gZ sg (Matrix.diagonal z) v)`. Introduce `v`.

Use `conv_lhs => rw [Q.as_sum]`. Simplify using `only [evX, map_sum, Finset.sum_mul, Finset.mul_sum]`. Repeatedly rewrite using `[hsplit]`. Rewrite using `[integral_finset_sum _ (fun e _ => intg_mono sg t z hz e (Q.coeff e) u)]`. Rewrite using `[Finset.sum_congr rfl (fun e he => hF e he u)]`.

Simplify using `only [evX, map_sum, Finset.sum_mul]`.
-/
theorem four_diag (sg : ℤˣ) (t : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    (d : ℕ) (Q : PX m n) (hQ : Q.totalDegree ≤ d) :
    IsPG sg d (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹)
      (fun u => ∫ v : Fin m → Fin n → ℂ, ker t u v * (evX Q v * gZ sg (Matrix.diagonal z) v)) := by
  classical
  have key : ∀ e ∈ Q.support, ∃ Q' : PX m n, Q'.totalDegree ≤ d ∧ ∀ u,
      ∫ v : Fin m → Fin n → ℂ, ker t u v * (evX (MvPolynomial.monomial e (Q.coeff e)) v * gZ sg (Matrix.diagonal z) v)
        = evX Q' u * gZ sg (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹) u := by
    intro e he
    obtain ⟨Q', hQ', h'⟩ := four_mono sg t z hz e (Q.coeff e)
    exact ⟨Q', hQ'.trans ((MvPolynomial.le_totalDegree he).trans hQ), h'⟩
  choose! F hFd hF using key
  refine ⟨∑ e ∈ Q.support, F e, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun e he => hFd e he)
  · funext u
    have hsplit : ∀ v, ker t u v * (evX Q v * gZ sg (Matrix.diagonal z) v)
        = ∑ e ∈ Q.support, ker t u v * (evX (MvPolynomial.monomial e (Q.coeff e)) v * gZ sg (Matrix.diagonal z) v) := by
      intro v
      conv_lhs => rw [Q.as_sum]
      simp only [evX, map_sum, Finset.sum_mul, Finset.mul_sum]
    simp_rw [hsplit]
    rw [integral_finset_sum _ (fun e _ => intg_mono sg t z hz e (Q.coeff e) u)]
    rw [Finset.sum_congr rfl (fun e he => hF e he u)]
    simp only [evX, map_sum, Finset.sum_mul]

/- English proof (translation)
Take `⟨Q, hQ, rfl⟩` from `hp`. Conclude with `isPG_smul C0 (four_diag sg t z hz d Q hQ)`.
-/
theorem pg_four (sg : ℤˣ) (t C0 : ℂ) (z : Fin n → ℂ) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im) {d : ℕ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hp : IsPG sg d (Matrix.diagonal z) f) :
    IsPG sg d (Matrix.diagonal fun j => -((normSq t : ℂ) / 4) * (z j)⁻¹)
      (fun u => C0 * ∫ v : Fin m → Fin n → ℂ, ker t u v * f v) := by
  obtain ⟨Q, hQ, rfl⟩ := hp
  exact isPG_smul C0 (four_diag sg t z hz d Q hQ)

/- English proof (translation)
Set `f : Fin m × Fin n × Bool → PX m n` to `fun k => if k.2.2 = true then ∑ l, MvPolynomial.X (k.1, l, true) * MvPolynomial.C (star (a l k.2.1)) else ∑ l, MvPolynomial.X (k.1, l, false) * MvPolynomial.C (a l k.2.1)`. Use `⟨MvPolynomial.bind₁ f Q, deg_bind_le f (fun k => ?_) Q, fun u => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `dsimp only [f] split_ifs <;>`. Use `(MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Simplify using `[MvPolynomial.totalDegree_X]`. Unfold `evX`. Express the relevant statement in the definitionally equal form `_ = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (MvPolynomial.bind₁ f Q)`. Rewrite using `[MvPolynomial.eval₂Hom_bind₁]`. Express the relevant statement in the definitionally equal form `MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q`.

Use `congrArg (fun g => MvPolynomial.eval₂Hom (RingHom.id ℂ) g Q) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Take `⟨i, j, b⟩` from `k`. Apply the tactic sequence `cases b <;> simp [f, Matrix.mul_apply, star_sum, star_mul']`.
-/
theorem evX_mulR (Q : PX m n) (a : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Q' : PX m n, Q'.totalDegree ≤ Q.totalDegree ∧ ∀ u : Fin m → Fin n → ℂ, evX Q (Matrix.of u * a) = evX Q' u := by
  classical
  let f : Fin m × Fin n × Bool → PX m n := fun k =>
    if k.2.2 = true then ∑ l, MvPolynomial.X (k.1, l, true) * MvPolynomial.C (star (a l k.2.1))
    else ∑ l, MvPolynomial.X (k.1, l, false) * MvPolynomial.C (a l k.2.1)
  refine ⟨MvPolynomial.bind₁ f Q, deg_bind_le f (fun k => ?_) Q, fun u => ?_⟩
  · dsimp only [f]
    split_ifs <;>
    · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      simp [MvPolynomial.totalDegree_X]
  · unfold evX
    change _ = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (MvPolynomial.bind₁ f Q)
    rw [MvPolynomial.eval₂Hom_bind₁]
    change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q = MvPolynomial.eval₂Hom (RingHom.id ℂ) _ Q
    refine congrArg (fun g => MvPolynomial.eval₂Hom (RingHom.id ℂ) g Q) ?_
    funext k
    obtain ⟨i, j, b⟩ := k
    cases b <;> simp [f, Matrix.mul_apply, star_sum, star_mul']

/- English proof (translation)
Unfold `gZ`. Establish `e : (Z * ((Matrix.of (Matrix.of u * a))ᴴ * Matrix.of (Matrix.of u * a))).trace = (a * Z * aᴴ * ((Matrix.of u)ᴴ * Matrix.of u)).trace`. Express the relevant statement in the definitionally equal form `(Z * ((Matrix.of u * a)ᴴ * (Matrix.of u * a))).trace = _`. Rewrite using `[Matrix.conjTranspose_mul]`. Rewrite using `[show Z * (aᴴ * (Matrix.of u)ᴴ * (Matrix.of u * a)) = (Z * aᴴ * ((Matrix.of u)ᴴ * Matrix.of u)) * a by simp only [Matrix.mul_assoc]]`.

Rewrite using `[Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e]`.
-/
theorem gZ_mulR (sg : ℤˣ) (Z a : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) :
    gZ sg Z (Matrix.of u * a) = gZ sg (a * Z * aᴴ) u := by
  unfold gZ
  have e : (Z * ((Matrix.of (Matrix.of u * a))ᴴ * Matrix.of (Matrix.of u * a))).trace
      = (a * Z * aᴴ * ((Matrix.of u)ᴴ * Matrix.of u)).trace := by
    change (Z * ((Matrix.of u * a)ᴴ * (Matrix.of u * a))).trace = _
    rw [Matrix.conjTranspose_mul]
    rw [show Z * (aᴴ * (Matrix.of u)ᴴ * (Matrix.of u * a))
        = (Z * aᴴ * ((Matrix.of u)ᴴ * Matrix.of u)) * a by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]

variable {sg : ℤˣ} {L : LOp m n}

/- English proof (translation)
Rewrite using `[mR_nG hb, mob_nU, h.nU _ b hb (mR_nG hb) f hf]`. Take `⟨Q, hQ, rfl⟩` from `hp`. Use `⟨Q, hQ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Simplify using `only [gZ, Matrix.add_mul, Matrix.trace_add, mul_add, Complex.exp_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pg_nG (h : LocHyp sg L) {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d Z f) :
    IsPG sg d (mob (mR (nG b)) Z) (L (nG b) f) := by
  rw [mR_nG hb, mob_nU, h.nU _ b hb (mR_nG hb) f hf]
  obtain ⟨Q, hQ, rfl⟩ := hp
  refine ⟨Q, hQ, ?_⟩
  funext u
  simp only [gZ, Matrix.add_mul, Matrix.trace_add, mul_add, Complex.exp_add]
  ring

/- English proof (translation)
Take `⟨k, hk⟩` from `h.mM`. Rewrite using `[hk (mG a) a ha (mR_mG ha) f hf, mR_mG ha, mob_mLc _ _ ha]`. Take `⟨Q, hQ, rfl⟩` from `hp`. Take `⟨Q', hQ', hQ'e⟩` from `evX_mulR Q a`. Use `⟨MvPolynomial.C ((a.det / ↑‖a.det‖) ^ k * ↑‖a.det‖ ^ m) * Q', ?_, ?_⟩` and prove the remaining obligations.

Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.totalDegree_C, zero_add]`. Conclude with `hQ'.trans hQ`. Use function extensionality and compare the values at `u show _ * (evX Q (Matrix.of u * a) * gZ sg Z (Matrix.of u * a)) = _`. Rewrite using `[hQ'e, gZ_mulR]`.

Simplify using `only [evX, map_mul, MvPolynomial.eval_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pg_mG (h : LocHyp sg L) {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) {d : ℕ}
    {Z : Matrix (Fin n) (Fin n) ℂ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d Z f) :
    IsPG sg d (mob (mR (mG a)) Z) (L (mG a) f) := by
  obtain ⟨k, hk⟩ := h.mM
  rw [hk (mG a) a ha (mR_mG ha) f hf, mR_mG ha, mob_mLc _ _ ha]
  obtain ⟨Q, hQ, rfl⟩ := hp
  obtain ⟨Q', hQ', hQ'e⟩ := evX_mulR Q a
  refine ⟨MvPolynomial.C ((a.det / ↑‖a.det‖) ^ k * ↑‖a.det‖ ^ m) * Q', ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hQ'.trans hQ
  · funext u
    show _ * (evX Q (Matrix.of u * a) * gZ sg Z (Matrix.of u * a)) = _
    rw [hQ'e, gZ_mulR]
    simp only [evX, map_mul, MvPolynomial.eval_C]
    ring

/- English proof (translation)
The claim follows from `isPG_smul c h`.
-/
theorem isPG_smul' {sg : ℤˣ} {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ} {f : (Fin m → Fin n → ℂ) → ℂ} (c : ℂ)
    (h : IsPG sg d Z f) : IsPG sg d Z (c • f) := isPG_smul c h

/- English proof (translation)
Establish `e : lFT C s f = fun u => C * ∫ v : Fin m → Fin n → ℂ, ker s u v * f v` using `rfl`. Establish `hn : (normSq s : ℂ) / 4 = 1`. Rewrite using `[Complex.normSq_eq_norm_sq, hs]`. Evaluate the numerical expressions. Use `pg_four sg s C z hz hp` as an intermediate fact.

Rewrite using `[e]`. Simplify `this` using `[hn]`.
-/
theorem pg_lFT {sg : ℤˣ} (C s : ℂ) (hs : ‖s‖ = 2) {z : Fin n → ℂ} (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im) {d : ℕ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hp : IsPG sg d (Matrix.diagonal z) f) :
    IsPG sg d (Matrix.diagonal fun j => -(z j)⁻¹) (lFT C s f) := by
  have e : lFT C s f = fun u => C * ∫ v : Fin m → Fin n → ℂ, ker s u v * f v := rfl
  have hn : (normSq s : ℂ) / 4 = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs]
    norm_num
  have := pg_four sg s C z hz hp
  rw [e]
  simpa [hn] using this

/- English proof (translation)
Take `⟨Q, hQ, rfl⟩` from `hp`. Use `⟨Q, hQ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Simplify using `only [chp, gZ, Matrix.add_mul, Matrix.trace_add, mul_add, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pg_chp {sg : ℤˣ} (x : Matrix (Fin n) (Fin n) ℂ) {d : ℕ} {Z : Matrix (Fin n) (Fin n) ℂ}
    {f : (Fin m → Fin n → ℂ) → ℂ} (hp : IsPG sg d Z f) : IsPG sg d (Z + x) (chp ((sg : ℤ) : ℂ) x f) := by
  obtain ⟨Q, hQ, rfl⟩ := hp
  refine ⟨Q, hQ, ?_⟩
  funext u
  simp only [chp, gZ, Matrix.add_mul, Matrix.trace_add, mul_add, Complex.exp_add]
  ring

/- English proof (translation)
Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hw`. Establish `hn : 0 < Complex.normSq w` using `Complex.normSq_pos.mpr hw0`. Establish `e : (-w⁻¹).im = w.im / Complex.normSq w`.

Simplify using `[Complex.inv_im, neg_div]`. Rewrite using `[e, ← mul_div_assoc]`. Conclude with `div_pos hw hn`.
-/
theorem im_neg_inv {sg : ℤˣ} {w : ℂ} (hw : 0 < ((sg : ℤ) : ℝ) * w.im) : 0 < ((sg : ℤ) : ℝ) * (-w⁻¹).im := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have e : (-w⁻¹).im = w.im / Complex.normSq w := by
    simp [Complex.inv_im, neg_div]
  rw [e, ← mul_div_assoc]
  exact div_pos hw hn

/- English proof (translation)
Rewrite using `[← Matrix.diagonal_one, Matrix.diagonal_add]`.
-/
theorem diag_add_one (w : Fin n → ℂ) : Matrix.diagonal w + 1 = Matrix.diagonal fun j => w j + 1 := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_add]

/- English proof (translation)
Conclude with `inG_nb hc`.
-/
theorem inG_nbLc {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (nbLc c) := by
  exact inG_nb hc

def nbH (c : Matrix (Fin n) (Fin n) ℂ) : GR n := if h : cᴴ = c then toGR _ (inG_nbLc h) else 1

/- English proof (translation)
Rewrite using `[nbH, dif_pos hc, mR_toGR]`.
-/
theorem mR_nbH {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : mR (nbH c) = nbLc c := by
  rw [nbH, dif_pos hc, mR_toGR]

/- English proof (translation)
Apply `mR_injective` to reduce the goal to its premises. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1` using `Matrix.conjTranspose_one`. Establish `hm1 : (-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -1` using `by simp`. Rewrite using `[mR_mul, mR_mul, mR_nG h1, mR_nbH hm1, mR_jG]`. Simplify using `[JJ, nU, nbLc, Matrix.fromBlocks_multiply]`.
-/
theorem jG_eq : jG n = nG 1 * nbH (-1) * nG 1 := by
  apply mR_injective
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hm1 : (-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -1 := by simp
  rw [mR_mul, mR_mul, mR_nG h1, mR_nbH hm1, mR_jG]
  simp [JJ, nU, nbLc, Matrix.fromBlocks_multiply]

/- English proof (translation)
Establish `hy : -(x + 1)⁻¹ + 1 = x / (x + 1)` using `by field_simp; ring`. Rewrite using `[hy]`. Simplify using `only [inv_neg, inv_inv, neg_neg, inv_div]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alg1 (x : ℂ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) : (-x)⁻¹ = -(-(-(-(x + 1)⁻¹ + 1)⁻¹)⁻¹)⁻¹ + 1 := by
  have hy : -(x + 1)⁻¹ + 1 = x / (x + 1) := by field_simp; ring
  rw [hy]
  simp only [inv_neg, inv_inv, neg_neg, inv_div]
  field_simp
  ring

/- English proof (translation)
Establish `hz0 : ∀ j, z j ≠ 0` using `fun j hj => by`. Use `hz j` as an intermediate fact. Rewrite `this` using `[hj]`. Simplify using `at this`. Establish `hz1' : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j + 1).im` using `fun j => by`.

Rewrite using `[Complex.add_im, Complex.one_im, add_zero]`. Conclude with `hz j`. Establish `hz1 : ∀ j, z j + 1 ≠ 0` using `fun j hj => by`. Use `hz1' j` as an intermediate fact. Rewrite `this` using `[hj]`.

Simplify using `at this`. Take `⟨C, s, κ, η, -, -, hs, hη, -, hnb⟩` from `h.nbar`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1` using `Matrix.conjTranspose_one`. Establish `hm1 : (-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -1` using `by simp`. Establish `hf1 : IsSw (L (nG 1) f)` using `h.sw _ _ hf`.

Establish `hf2 : IsSw (L (nbH (-1)) (L (nG 1) f))` using `h.sw _ _ hf1`. Establish `hL : L (jG n) f = L (nG 1) (L (nbH (-1)) (L (nG 1) f))`. Rewrite using `[jG_eq, h.mul _ _ _ hf, h.mul _ _ _ hf1]`. Rewrite using `[hL, mR_jG, mob_JJ_diag z hz0]`. Establish `p1 : IsPG sg d (Matrix.diagonal fun j => z j + 1) (L (nG 1) f)`.

Use `pg_nG h h1 hf hp` as an intermediate fact. Rewrite `this` using `[mR_nG h1, mob_nU, diag_add_one]`. Then use the resulting hypothesis. Establish `p2 : IsPG sg d (Matrix.diagonal fun j => -(z j + 1)⁻¹) (lFT C s (L (nG 1) f))` using `pg_lFT C s hs hz1' p1`. Establish `e1 : Matrix.diagonal (fun j => -(z j + 1)⁻¹) + η • (-1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal fun j => -(z j + 1)⁻¹ + 1`. Rewrite using `[hη, neg_smul, one_smul, neg_neg, diag_add_one]`.

Establish `p3 : IsPG sg d (Matrix.diagonal fun j => -(z j + 1)⁻¹ + 1) (chp ((sg : ℤ) : ℂ) (η • (-1 : Matrix (Fin n) (Fin n) ℂ)) (lFT C s (L (nG 1) f)))`. Use `pg_chp (η • (-1 : Matrix (Fin n) (Fin n) ℂ)) p2` as an intermediate fact. Rewrite `this` using `[e1]`. Conclude with `this`. Establish `hz2 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(z j + 1)⁻¹ + 1).im` using `fun j => by`.

Rewrite using `[Complex.add_im, Complex.one_im, add_zero]`. Conclude with `im_neg_inv (hz1' j)`. Establish `p4` using `pg_lFT C s hs hz2 p3`. Establish `hz3 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(-(z j + 1)⁻¹ + 1)⁻¹).im` using `fun j => im_neg_inv (hz2 j)`. Establish `p5` using `pg_lFT C s hs hz3 p4`.

Establish `hz4 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(-(-(z j + 1)⁻¹ + 1)⁻¹)⁻¹).im` using `fun j => im_neg_inv (hz3 j)`. Establish `p6` using `pg_lFT C s hs hz4 p5`. Establish `p7` using `isPG_smul' κ⁻¹ p6`. Rewrite `p7` using `[← hnb (nbH (-1)) (-1) hm1 (mR_nbH hm1) _ hf1]`. Establish `p8` using `pg_nG h h1 hf2 p7`.

Rewrite `p8` using `[mR_nG h1, mob_nU, diag_add_one]`. Establish `e : (fun j => (-z j)⁻¹) = fun j => -(-(-(-(z j + 1)⁻¹ + 1)⁻¹)⁻¹)⁻¹ + 1`. Use function extensionality and compare the values at `fun j => alg1 _ (hz0 j) (hz1 j)`. Rewrite using `[e]`. Conclude with `p8`.
-/
theorem pg_jG_diag (h : LocHyp sg L) {d : ℕ} {z : Fin n → ℂ} (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d (Matrix.diagonal z) f) :
    IsPG sg d (mob (mR (jG n)) (Matrix.diagonal z)) (L (jG n) f) := by
  have hz0 : ∀ j, z j ≠ 0 := fun j hj => by
    have := hz j
    rw [hj] at this
    simp at this
  have hz1' : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j + 1).im := fun j => by
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact hz j
  have hz1 : ∀ j, z j + 1 ≠ 0 := fun j hj => by
    have := hz1' j
    rw [hj] at this
    simp at this
  obtain ⟨C, s, κ, η, -, -, hs, hη, -, hnb⟩ := h.nbar
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hm1 : (-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ = -1 := by simp
  have hf1 : IsSw (L (nG 1) f) := h.sw _ _ hf
  have hf2 : IsSw (L (nbH (-1)) (L (nG 1) f)) := h.sw _ _ hf1
  have hL : L (jG n) f = L (nG 1) (L (nbH (-1)) (L (nG 1) f)) := by
    rw [jG_eq, h.mul _ _ _ hf, h.mul _ _ _ hf1]
  rw [hL, mR_jG, mob_JJ_diag z hz0]
  have p1 : IsPG sg d (Matrix.diagonal fun j => z j + 1) (L (nG 1) f) := by
    have := pg_nG h h1 hf hp
    rwa [mR_nG h1, mob_nU, diag_add_one] at this
  have p2 : IsPG sg d (Matrix.diagonal fun j => -(z j + 1)⁻¹) (lFT C s (L (nG 1) f)) :=
    pg_lFT C s hs hz1' p1
  have e1 : Matrix.diagonal (fun j => -(z j + 1)⁻¹) + η • (-1 : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal fun j => -(z j + 1)⁻¹ + 1 := by
    rw [hη, neg_smul, one_smul, neg_neg, diag_add_one]
  have p3 : IsPG sg d (Matrix.diagonal fun j => -(z j + 1)⁻¹ + 1)
      (chp ((sg : ℤ) : ℂ) (η • (-1 : Matrix (Fin n) (Fin n) ℂ)) (lFT C s (L (nG 1) f))) := by
    have := pg_chp (η • (-1 : Matrix (Fin n) (Fin n) ℂ)) p2
    rw [e1] at this
    exact this
  have hz2 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(z j + 1)⁻¹ + 1).im := fun j => by
    rw [Complex.add_im, Complex.one_im, add_zero]
    exact im_neg_inv (hz1' j)
  have p4 := pg_lFT C s hs hz2 p3
  have hz3 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(-(z j + 1)⁻¹ + 1)⁻¹).im := fun j => im_neg_inv (hz2 j)
  have p5 := pg_lFT C s hs hz3 p4
  have hz4 : ∀ j, 0 < ((sg : ℤ) : ℝ) * (-(-(-(z j + 1)⁻¹ + 1)⁻¹)⁻¹).im := fun j => im_neg_inv (hz3 j)
  have p6 := pg_lFT C s hs hz4 p5
  have p7 := isPG_smul' κ⁻¹ p6
  rw [← hnb (nbH (-1)) (-1) hm1 (mR_nbH hm1) _ hf1] at p7
  have p8 := pg_nG h h1 hf2 p7
  rw [mR_nG h1, mob_nU, diag_add_one] at p8
  have e : (fun j => (-z j)⁻¹) = fun j => -(-(-(-(z j + 1)⁻¹ + 1)⁻¹)⁻¹)⁻¹ + 1 :=
    funext fun j => alg1 _ (hz0 j) (hz1 j)
  rw [e]
  exact p8

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_left_inverse hU`.
-/
theorem unit_det_of_unitary {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) : IsUnit U.det :=
  Matrix.isUnit_det_of_left_inverse hU

/- English proof (translation)
Establish `h1 : IsUnit U.det` using `unit_det_of_unitary hU`. Establish `h2 : IsUnit (Uᴴ).det` using `unit_det_of_unitary (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')`. Apply `mR_injective` to reduce the goal to its premises. Rewrite using `[mR_mul, mR_mul, mR_mG h1, mR_mG h2, mR_jG]`. Establish `e1 : (Uᴴ)⁻¹ = U` using `Matrix.inv_eq_left_inv hU'`.

Establish `e2 : (Uᴴᴴ)⁻¹ = Uᴴ` using `by rw [Matrix.conjTranspose_conjTranspose]; exact Matrix.inv_eq_left_inv hU`. Simplify using `only [mLc, JJ, e1, e2, Matrix.fromBlocks_multiply]`. Simplify using `[hU', hU]`.
-/
theorem jG_conj {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    jG n = mG U * jG n * mG Uᴴ := by
  have h1 : IsUnit U.det := unit_det_of_unitary hU
  have h2 : IsUnit (Uᴴ).det := unit_det_of_unitary (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')
  apply mR_injective
  rw [mR_mul, mR_mul, mR_mG h1, mR_mG h2, mR_jG]
  have e1 : (Uᴴ)⁻¹ = U := Matrix.inv_eq_left_inv hU'
  have e2 : (Uᴴᴴ)⁻¹ = Uᴴ := by rw [Matrix.conjTranspose_conjTranspose]; exact Matrix.inv_eq_left_inv hU
  simp only [mLc, JJ, e1, e2, Matrix.fromBlocks_multiply]
  simp [hU', hU]

/- English proof (translation)
Establish `hZ' : Z = U * Matrix.diagonal z * Uᴴ`. Rewrite using `[← hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul, Matrix.mul_assoc, hU', Matrix.mul_one]`. Establish `hmob : mob (JJ n) Z = (-Z)⁻¹`. Simplify using `[mob, JJ]`. Rewrite using `[hmob]`.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hZ']`. Establish `e2 : U * Matrix.diagonal z * Uᴴ * (U * Matrix.diagonal (fun j => (-z j)⁻¹) * Uᴴ) = U * (Matrix.diagonal z * Matrix.diagonal (fun j => (-z j)⁻¹)) * Uᴴ`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]`.

Establish `hd : (fun j => z j * (-z j)⁻¹) = fun _ => (-1 : ℂ)`. Use function extensionality and compare the values at `j`. Rewrite using `[inv_neg, mul_neg, mul_inv_cancel₀ (hz0 j)]`. Establish `hd1 : Matrix.diagonal (fun _ : Fin n => (-1 : ℂ)) = -1`. Rewrite using `[← Matrix.diagonal_neg]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.neg_mul, e2, Matrix.diagonal_mul_diagonal, hd, hd1]`. Simplify using `[hU']`.
-/
theorem mob_JJ_conj {Z U : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hZ : Uᴴ * Z * U = Matrix.diagonal z) (hz0 : ∀ j, z j ≠ 0) :
    mob (JJ n) Z = U * (Matrix.diagonal fun j => (-z j)⁻¹) * Uᴴ := by
  have hZ' : Z = U * Matrix.diagonal z * Uᴴ := by
    rw [← hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul, Matrix.mul_assoc, hU', Matrix.mul_one]
  have hmob : mob (JJ n) Z = (-Z)⁻¹ := by
    simp [mob, JJ]
  rw [hmob]
  apply Matrix.inv_eq_right_inv
  rw [hZ']
  have e2 : U * Matrix.diagonal z * Uᴴ * (U * Matrix.diagonal (fun j => (-z j)⁻¹) * Uᴴ)
      = U * (Matrix.diagonal z * Matrix.diagonal (fun j => (-z j)⁻¹)) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  have hd : (fun j => z j * (-z j)⁻¹) = fun _ => (-1 : ℂ) := by
    funext j
    rw [inv_neg, mul_neg, mul_inv_cancel₀ (hz0 j)]
  have hd1 : Matrix.diagonal (fun _ : Fin n => (-1 : ℂ)) = -1 := by
    rw [← Matrix.diagonal_neg]
    rfl
  rw [Matrix.neg_mul, e2, Matrix.diagonal_mul_diagonal, hd, hd1]
  simp [hU']

/- English proof (translation)
Establish `hUd : IsUnit U.det` using `unit_det_of_unitary hU`. Establish `hUd' : IsUnit Uᴴ.det` using `unit_det_of_unitary (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')`. Establish `hz0 : ∀ j, z j ≠ 0` using `fun j hj => by`. Use `hz j` as an intermediate fact. Rewrite `this` using `[hj]`.

Simplify using `at this`. Rewrite using `[mR_jG, mob_JJ_conj hU hU' hZ hz0]`. Establish `hL : L (jG n) f = L (mG U) (L (jG n) (L (mG Uᴴ) f))` using `by conv_lhs => rw [jG_conj hU hU']`. Rewrite using `[h.mul _ _ _ hf, h.mul _ _ _ (h.sw _ _ hf)]`. Rewrite using `[hL]`.

Establish `p1 : IsPG sg d (Matrix.diagonal z) (L (mG Uᴴ) f)`. Use `pg_mG h hUd' hf hp` as an intermediate fact. Rewrite `this` using `[mR_mG hUd', mob_mLc _ _ hUd', Matrix.conjTranspose_conjTranspose, hZ]`. Then use the resulting hypothesis. Establish `hf1 : IsSw (L (mG Uᴴ) f)` using `h.sw _ _ hf`. Establish `p2` using `pg_jG_diag h hz hf1 p1`.

Rewrite `p2` using `[mR_jG, mob_JJ_diag z hz0]`. Establish `p3` using `pg_mG h hUd (h.sw _ _ hf1) p2`. Rewrite `p3` using `[mR_mG hUd, mob_mLc _ _ hUd]`. Then use the resulting hypothesis.
-/
theorem pg_jG (h : LocHyp sg L) {d : ℕ} {Z U : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (hZ : Uᴴ * Z * U = Matrix.diagonal z) (hz : ∀ j, 0 < ((sg : ℤ) : ℝ) * (z j).im)
    {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) (hp : IsPG sg d Z f) :
    IsPG sg d (mob (mR (jG n)) Z) (L (jG n) f) := by
  have hUd : IsUnit U.det := unit_det_of_unitary hU
  have hUd' : IsUnit Uᴴ.det := unit_det_of_unitary (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')
  have hz0 : ∀ j, z j ≠ 0 := fun j hj => by
    have := hz j
    rw [hj] at this
    simp at this
  rw [mR_jG, mob_JJ_conj hU hU' hZ hz0]
  have hL : L (jG n) f = L (mG U) (L (jG n) (L (mG Uᴴ) f)) := by
    conv_lhs => rw [jG_conj hU hU']
    rw [h.mul _ _ _ hf, h.mul _ _ _ (h.sw _ _ hf)]
  rw [hL]
  have p1 : IsPG sg d (Matrix.diagonal z) (L (mG Uᴴ) f) := by
    have := pg_mG h hUd' hf hp
    rwa [mR_mG hUd', mob_mLc _ _ hUd', Matrix.conjTranspose_conjTranspose, hZ] at this
  have hf1 : IsSw (L (mG Uᴴ) f) := h.sw _ _ hf
  have p2 := pg_jG_diag h hz hf1 p1
  rw [mR_jG, mob_JJ_diag z hz0] at p2
  have p3 := pg_mG h hUd (h.sw _ _ hf1) p2
  rwa [mR_mG hUd, mob_mLc _ _ hUd] at p3

end PositivityTheory.SiegelWeilFormula.KLI

end
