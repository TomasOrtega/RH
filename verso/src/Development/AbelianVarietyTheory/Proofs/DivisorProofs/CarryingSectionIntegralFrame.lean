import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovMult

open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum

section Places

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h0 : Ideal.absNorm la.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `la.ne_bot`. Establish `key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 K) ∈ la.asIdeal → ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal`. Introduce `n`.

Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => exact fun h => absurd rfl h`. Consider the case `one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top`. Consider the case `prime p hp => exact fun _ h => ⟨p, hp, h⟩`. Consider the case `mul a b ha hb`.

Introduce `h hm`. Rewrite `hm` using `[Nat.cast_mul]`. Conclude with `(la.isPrime.mem_or_mem hm).elim (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))`. Conclude with `key _ h0 (Ideal.absNorm_mem _)`.
-/
theorem exists_prime_mem (la : HeightOneSpectrum (𝓞 K)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
  have key : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 K) ∈ la.asIdeal → ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ la.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => exact fun h => absurd rfl h
    | one => exact fun _ h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) la.isPrime.ne_top
    | prime p hp => exact fun _ h => ⟨p, hp, h⟩
    | mul a b ha hb =>
      intro h hm
      rw [Nat.cast_mul] at hm
      exact (la.isPrime.mem_or_mem hm).elim (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  exact key _ h0 (Ideal.absNorm_mem _)

/- English proof (translation)
Use `vAdd_int_nonneg la (a := (n : 𝓞 K)) (by simpa using hn)` as an intermediate fact. Simplify `this` using `[vLa, Formalism.BasicNotions.vAdd]`.
-/
theorem vLa_nat_nonneg (la : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : 0 ≤ vLa la (n : K) := by
  have := vAdd_int_nonneg la (a := (n : 𝓞 K)) (by simpa using hn)
  simpa [vLa, Formalism.BasicNotions.vAdd] using this

/- English proof (translation)
Establish `h1 : la.valuation K (q : K) < 1`. Use `(la.valuation_lt_one_iff_mem (K := K) (q : 𝓞 K)).2 h` as an intermediate fact. Simplify using `using this`. Establish `h0 : la.valuation K (q : K) ≠ 0` using `(Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)`. Unfold `vLa`.

Rewrite `h1` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vLa_pos {la : HeightOneSpectrum (𝓞 K)} {q : ℕ} (hq : q ≠ 0) (h : (q : 𝓞 K) ∈ la.asIdeal) :
    0 < vLa la (q : K) := by
  have h1 : la.valuation K (q : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (q : 𝓞 K)).2 h
    simpa using this
  have h0 : la.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  unfold vLa
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

/- English proof (translation)
Take `⟨hp, h0, hS, hs⟩` from `h`. Establish `one : ∀ (q : ℕ), q ≠ 0 → ∀ (b : ℝ) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ), ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ, cost e' t = cost e t + b * Real.log q ∧ ∀ la, e' la = e la + (vLa la (q : K) : ℝ) * b`. Introduce `q hq b e`. Establish `hf` using `fin_mul (finite_vAdd (K := K) (a := q) (Nat.cast_ne_zero.2 hq)) fun _ => b`. Use `⟨e + Finsupp.ofSupportFinite _ hf, ?_, fun la => rfl⟩` and prove the remaining obligations.

Establish `h1` using `sum_vAdd_nat (K := K) hq`. Establish `h2 : ((Finsupp.ofSupportFinite _ hf).sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) / (Module.finrank ℚ K : ℝ) = b * Real.log q`. Rewrite using `[← h1, mul_finsum, Finsupp.sum, Finset.sum_div, finsum_eq_sum_of_support_subset (s := (Finsupp.ofSupportFinite _ hf).support)]`. Use `Finset.sum_congr rfl fun la _ => ?_` and prove the remaining obligations. Simplify using `only [Finsupp.ofSupportFinite_coe, lw]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `la hla`. Simplify using `only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]`. Introduce `h`. Apply `hla` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← mul_assoc, mul_comm b, h, zero_mul]`. Rewrite using `[cost, cost, Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _), ← h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `all : ∀ T : Finset ℕ, (∀ q ∈ T, q ≠ 0) → ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ, cost e' t = cost e t + ∑ q ∈ T, a q * Real.log q ∧ ∀ la, e' la = e la + ∑ q ∈ T, (vLa la (q : K) : ℝ) * a q`.

Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact fun _ => ⟨e, by simp, by simp⟩`. Consider the case `insert q T hq ih`. Introduce `hT`.

Take `⟨e₁, h1, h2⟩` from `ih fun r hr => hT r (Finset.mem_insert_of_mem hr)`. Take `⟨e₂, h3, h4⟩` from `one q (hT q (Finset.mem_insert_self _ _)) (a q) e₁`. Conclude with `⟨e₂, by rw [h3, h1, Finset.sum_insert hq]; ring, fun la => by rw [h4, h2, Finset.sum_insert hq]; ring⟩`. Take `⟨e', h1, h2⟩` from `all S fun q hq => (hp q hq).ne_zero`. Establish `hn : ∀ la, ∀ q ∈ S, 0 ≤ (vLa la (q : K) : ℝ) * a q` using `fun la q hq => mul_nonneg (by exact_mod_cast vLa_nat_nonneg la (hp q hq).ne_zero) (h0 q)`.

Use `⟨e', by linarith, fun la q => ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Distinguish the cases in `hq : q ∈ S`. Conclude with `add_le_add_right (Finset.single_le_sum (hn la) hq) _`. Rewrite using `[hS q hq, mul_zero]`.

Conclude with `add_le_add_right (Finset.sum_nonneg (hn la)) _`.
-/
theorem exists_spread {S : Finset ℕ} {a : ℕ → ℝ} {s : ℝ} (h : PrimeSum S a s) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ) : ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ, cost e' t ≤ cost e t + s ∧
      ∀ (la : HeightOneSpectrum (𝓞 K)) (q : ℕ), e la + (vLa la (q : K) : ℝ) * a q ≤ e' la := by
  classical
  obtain ⟨hp, h0, hS, hs⟩ := h
  have one : ∀ (q : ℕ), q ≠ 0 → ∀ (b : ℝ) (e : HeightOneSpectrum (𝓞 K) →₀ ℝ), ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + b * Real.log q ∧ ∀ la, e' la = e la + (vLa la (q : K) : ℝ) * b := by
    intro q hq b e
    have hf := fin_mul (finite_vAdd (K := K) (a := q) (Nat.cast_ne_zero.2 hq)) fun _ => b
    refine ⟨e + Finsupp.ofSupportFinite _ hf, ?_, fun la => rfl⟩
    have h1 := sum_vAdd_nat (K := K) hq
    have h2 : ((Finsupp.ofSupportFinite _ hf).sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) /
        (Module.finrank ℚ K : ℝ) = b * Real.log q := by
      rw [← h1, mul_finsum, Finsupp.sum, Finset.sum_div, finsum_eq_sum_of_support_subset (s := (Finsupp.ofSupportFinite _ hf).support)]
      · refine Finset.sum_congr rfl fun la _ => ?_
        simp only [Finsupp.ofSupportFinite_coe, lw]; ring
      · intro la hla
        simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
        intro h
        apply hla
        simp only
        rw [← mul_assoc, mul_comm b, h, zero_mul]
    rw [cost, cost, Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _), ← h2]
    ring
  have all : ∀ T : Finset ℕ, (∀ q ∈ T, q ≠ 0) → ∃ e' : HeightOneSpectrum (𝓞 K) →₀ ℝ,
      cost e' t = cost e t + ∑ q ∈ T, a q * Real.log q ∧ ∀ la, e' la = e la + ∑ q ∈ T, (vLa la (q : K) : ℝ) * a q := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨e, by simp, by simp⟩
    | insert q T hq ih =>
      intro hT
      obtain ⟨e₁, h1, h2⟩ := ih fun r hr => hT r (Finset.mem_insert_of_mem hr)
      obtain ⟨e₂, h3, h4⟩ := one q (hT q (Finset.mem_insert_self _ _)) (a q) e₁
      exact ⟨e₂, by rw [h3, h1, Finset.sum_insert hq]; ring, fun la => by rw [h4, h2, Finset.sum_insert hq]; ring⟩
  obtain ⟨e', h1, h2⟩ := all S fun q hq => (hp q hq).ne_zero
  have hn : ∀ la, ∀ q ∈ S, 0 ≤ (vLa la (q : K) : ℝ) * a q := fun la q hq =>
    mul_nonneg (by exact_mod_cast vLa_nat_nonneg la (hp q hq).ne_zero) (h0 q)
  refine ⟨e', by linarith, fun la q => ?_⟩
  rw [h2]
  by_cases hq : q ∈ S
  · exact add_le_add_right (Finset.single_le_sum (hn la) hq) _
  · rw [hS q hq, mul_zero]
    exact add_le_add_right (Finset.sum_nonneg (hn la)) _

end Places

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

/- English proof (translation)
Use `letI := io.toAlgebra`. Establish `hb` using `(refExp_vp_le_iff U).1 ha ⟨la, hla⟩ T io e ho y hy φ hφ`. Rewrite `hb` using `[← EReal.coe_add]`. Establish `hm` using `vLa_pos hq hla`. Establish `hv : vV T.V (q : T.Fr) = e * vLa la (q : c.F)` using `by rw [← ho.2, map_natCast]`.

Establish `hm' : (0 : ℝ) < vLa la (q : c.F)` using `by exact_mod_cast hm`. Establish `he : (0 : ℝ) < e` using `by exact_mod_cast ho.1`. Establish `hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * vLa la (q : c.F)`. Establish `: (((vV T.V (q : T.Fr)).toNat : ℕ) : ℤ) = e * vLa la (q : c.F)`. Rewrite using `[← hv, Int.toNat_of_nonneg (hv ▸ mul_nonneg (Nat.cast_nonneg _) hm.le)]`.

Conclude with `this` after adjusting the coercions. Use `le_of_forall_gt_imp_ge_of_dense fun b hb' => ?_` and prove the remaining obligations. Proceed by induction on `b using EReal.rec with`. Consider the case `bot => exact absurd hb' not_lt_bot`. Consider the case `top => exact le_top`.

Consider the case `coe b`. Establish `hb1` using `EReal.coe_lt_coe_iff.1 hb'`. Establish `hlt : depthAt_vp U G q y < ((b / vLa la (q : c.F) : ℝ) : EReal)`. Use `hb.trans_lt (EReal.coe_lt_coe_iff.2 ?_)` and prove the remaining obligations. Rewrite using `[lt_div_iff₀ hm', hv]`.

Use `lt_of_eq_of_lt ?_ hb1` and prove the remaining obligations. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Unfold `depthAt_vp depth_vw at hlt`. Take `⟨w, hw⟩` from `iInf_lt_iff.1 hlt`.

Take `⟨hwl, hw⟩` from `iInf_lt_iff.1 hw`. Establish `hne : evI y (w : Rul Xo c) ≠ 0` using `fun h0 => by`. Simplify using `only [h0, nval_zero] at hw`. Conclude with `not_top_lt hw`. Take `⟨g, hg, hgl⟩` from `GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z _ w`.

Establish `hev : evI y (g : Rul Xo c) = evI y (w : Rul Xo c)` using `hg T.Fr y.1 hZ`. Use `(iInf₂_le g (hgl hwl)).trans ?_` and prove the remaining obligations. Simplify using `only [nval_of_ne hne] at hw`. Use `beta_reduce`. Rewrite using `[hev, nval_of_ne hne, EReal.coe_le_coe_iff]`.

Establish `h2` using `EReal.coe_lt_coe_iff.1 hw`. Rewrite `h2` using `[hn, ← div_div, div_lt_div_iff_of_pos_right hm']`. Conclude with `h2.le`.
-/
theorem depthOn_le (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {cst a : ℝ} {G : WTZ E} {q : ℕ} (hq : q ≠ 0)
    (ha : refExp_vp U cst G q ≤ (a : EReal)) {la : HeightOneSpectrum (𝓞 c.F)} (hla : (q : 𝓞 c.F) ∈ la.asIdeal)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {y : IntFr Xo c T io} (hy : y.IsAlg)
    {φ : ℝ} (hφ : HasPhi y φ) {Z : Comp Xo c} (hZ : letI := io.toAlgebra; LiesOn Z y.1) :
    depthOn U Z G (fun f => nval T.V e (evI y f)) ≤ (((vLa la (q : c.F) : ℝ) * a + cst * φ / e : ℝ) : EReal) := by
  letI := io.toAlgebra
  have hb := (refExp_vp_le_iff U).1 ha ⟨la, hla⟩ T io e ho y hy φ hφ
  rw [← EReal.coe_add] at hb
  have hm := vLa_pos hq hla
  have hv : vV T.V (q : T.Fr) = e * vLa la (q : c.F) := by rw [← ho.2, map_natCast]
  have hm' : (0 : ℝ) < vLa la (q : c.F) := by exact_mod_cast hm
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * vLa la (q : c.F) := by
    have : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℤ) = e * vLa la (q : c.F) := by
      rw [← hv, Int.toNat_of_nonneg (hv ▸ mul_nonneg (Nat.cast_nonneg _) hm.le)]
    exact_mod_cast this
  refine le_of_forall_gt_imp_ge_of_dense fun b hb' => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb' not_lt_bot
  | top => exact le_top
  | coe b =>
    have hb1 := EReal.coe_lt_coe_iff.1 hb'
    have hlt : depthAt_vp U G q y < ((b / vLa la (q : c.F) : ℝ) : EReal) := by
      refine hb.trans_lt (EReal.coe_lt_coe_iff.2 ?_)
      rw [lt_div_iff₀ hm', hv]
      refine lt_of_eq_of_lt ?_ hb1
      push_cast; field_simp
    unfold depthAt_vp depth_vw at hlt
    obtain ⟨w, hw⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hwl, hw⟩ := iInf_lt_iff.1 hw
    have hne : evI y (w : Rul Xo c) ≠ 0 := fun h0 => by
      simp only [h0, nval_zero] at hw
      exact not_top_lt hw
    obtain ⟨g, hg, hgl⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z _ w
    have hev : evI y (g : Rul Xo c) = evI y (w : Rul Xo c) := hg T.Fr y.1 hZ
    refine (iInf₂_le g (hgl hwl)).trans ?_
    simp only [nval_of_ne hne] at hw
    beta_reduce
    rw [hev, nval_of_ne hne, EReal.coe_le_coe_iff]
    have h2 := EReal.coe_lt_coe_iff.1 hw
    rw [hn, ← div_div, div_lt_div_iff_of_pos_right hm'] at h2
    exact h2.le

/- English proof (translation)
Take `⟨⟨_, T, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩` from `hv`. Take `⟨T', i, e₁, y', φ, -, ho', hy', hφ, -, hv⟩` from `exists_ext_hasPhi ho y hy`. Take `⟨q, hq, hla⟩` from `exists_prime_mem la`. Establish `hf1 : evI y' f ≠ 0` using `fun h => hf0 (by show nval T.V e₀ (evI y f) = ⊤`. Rewrite using `[← (hv f hf.1.1.1).2, h, nval_zero])`.

Use `letI := (i.comp io).toAlgebra`. Establish `hZ : LiesOn Z y'.1`. Assume the negation of the conclusion as `h`. Conclude with `hf1 (hf.2 _ _ ((liesOff_iff Z y'.1).2 h))`. Use `⟨_, le_trans (le_of_eq ?_) (depthOn_le hU hq.ne_zero (ha q hq) hla ho' hy' hφ hZ), ?_⟩` and prove the remaining obligations.

Conclude with `iInf_congr fun g => iInf_congr fun _ => (hv g g.2.1.1.1).2.symm`. Use `le_trans (EReal.coe_le_coe_iff.2 ?_) ((hk la T' _ e₁ ho' y' hy' ⟨G', f, hf, hf1⟩ φ hφ).trans_eq (hv θ hθ.1).2)` and prove the remaining obligations. Use `he la q` as an intermediate fact. Establish `e2 : 8 / 2500 * φ / e₁ = 8 * (1 / 2500 * φ / e₁)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bound (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {a : ℕ → ℝ} {G : WTZ E}
    (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (a q : EReal)) {Z : Comp Xo c} {θ : Rul Xo c} {w : Ix Dw → ℤ}
    (hθ : θ ∈ secZ Xo c w) {e e' : HeightOneSpectrum (𝓞 c.F) →₀ ℝ}
    (he : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (q : ℕ), e la + (vLa la (q : c.F) : ℝ) * a q ≤ e' la)
    (hk : ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
      ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
        ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ))
    {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ (recVals Xo c).1 la) {G' : WTZ E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z G') (hf0 : v f ≠ ⊤) :
    ∃ B : ℝ, depthOn U Z G v ≤ (B : EReal) ∧ ((8 * B - 8 * e' la : ℝ) : EReal) ≤ v θ := by
  obtain ⟨⟨_, T, io, e₀, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  obtain ⟨T', i, e₁, y', φ, -, ho', hy', hφ, -, hv⟩ := exists_ext_hasPhi ho y hy
  obtain ⟨q, hq, hla⟩ := exists_prime_mem la
  have hf1 : evI y' f ≠ 0 := fun h => hf0 (by
    show nval T.V e₀ (evI y f) = ⊤
    rw [← (hv f hf.1.1.1).2, h, nval_zero])
  letI := (i.comp io).toAlgebra
  have hZ : LiesOn Z y'.1 := by
    by_contra h
    exact hf1 (hf.2 _ _ ((liesOff_iff Z y'.1).2 h))
  refine ⟨_, le_trans (le_of_eq ?_) (depthOn_le hU hq.ne_zero (ha q hq) hla ho' hy' hφ hZ), ?_⟩
  · exact iInf_congr fun g => iInf_congr fun _ => (hv g g.2.1.1.1).2.symm
  · refine le_trans (EReal.coe_le_coe_iff.2 ?_) ((hk la T' _ e₁ ho' y' hy' ⟨G', f, hf, hf1⟩ φ hφ).trans_eq (hv θ hθ.1).2)
    have := he la q
    have e2 : 8 / 2500 * φ / e₁ = 8 * (1 / 2500 * φ / e₁) := by ring
    linarith

/- English proof (translation)
Take `⟨θ, e, t, hC, hk, hI, hco⟩` from `hZ`. Take `⟨e', he', he⟩` from `exists_spread hS e t`. Establish `key` using `fun la v hv G' f hf hf0 => exists_bound hU ha hC.1 he hk (la := la) (v := v) hv (G' := G') (f := f) hf hf0`. Use `⟨fun la v hv G' f hf hf0 => ?_, θ, e', t, hC, fun la v hv ⟨w, _, hw⟩ => ?_, hI, by linarith⟩` and prove the remaining obligations. Take `⟨B, hB, -⟩` from `key la v hv G' f hf hf0`.

Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `EReal.coe_ne_top B (top_le_iff.1 ((le_iInf₂ fun w hw => (hn w hw).ge).trans hB))`. Take `⟨B, hB, hB'⟩` from `key la v hv _ w w.2 hw`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := add_le_add_left hB' _`.
-/
theorem mult_of (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
    {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r} {u u' : AllWt.Weight Dw} {S : Finset ℕ} {a : ℕ → ℝ} {s cc : ℝ}
    (hS : PrimeSum S a s) (ha : ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) (wtOf Dw u 0) q ≤ (a q : EReal)) {Z : Comp Xo c}
    (hZ : ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ), Carries U Z u u' θ ∧
      (∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ →
        ∀ y : IntFr Xo c T io, y.IsAlg → (∃ (G' : WTZ E), ∃ f ∈ cuspOn U Z G', evI y f ≠ 0) → ∀ φ : ℝ, HasPhi y φ →
          ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧
      InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc) :
    Mult U x V dict Z u u' (cc + s) := by
  obtain ⟨θ, e, t, hC, hk, hI, hco⟩ := hZ
  obtain ⟨e', he', he⟩ := exists_spread hS e t
  have key := fun la v hv G' f hf hf0 => exists_bound hU ha hC.1 he hk (la := la) (v := v) hv (G' := G') (f := f) hf hf0
  refine ⟨fun la v hv G' f hf hf0 => ?_, θ, e', t, hC, fun la v hv ⟨w, _, hw⟩ => ?_, hI, by linarith⟩
  · obtain ⟨B, hB, -⟩ := key la v hv G' f hf hf0
    by_contra hn
    push Not at hn
    exact EReal.coe_ne_top B (top_le_iff.1 ((le_iInf₂ fun w hw => (hn w hw).ge).trans hB))
  · obtain ⟨B, hB, hB'⟩ := key la v hv _ w w.2 hw
    calc _ ≤ ((8 : ℕ) : EReal) * (B : EReal) := mul_le_mul_of_nonneg_left hB (by exact_mod_cast Nat.zero_le 8)
      _ = ((8 * B - 8 * e' la : ℝ) : EReal) + ((((8 : ℕ) : ℝ) * e' la : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_natCast, ← EReal.coe_mul]; congr 1; push_cast; ring
      _ ≤ _ := add_le_add_left hB' _

/- English proof (translation)
Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem budget_add {T a b C₁ C₂ u : ℝ} (h₁ : T * b ≤ C₁ * u) (h₂ : T * a ≤ C₂ * u) : T * (a + b) ≤ (C₁ + C₂) * u := by
  linarith

/- English proof (translation)
Introduce `hR hK`. Use `Closed.imp (Closed.and hR hK) fun _ _ _ ⟨⟨C₁, h₁, hR⟩, C₂, h₂, hK⟩ => ⟨C₁ + C₂, add_nonneg h₁ h₂, ?_⟩` and prove the remaining obligations. Use `(hR.and hK).imp fun _ h x hx hle ι p hp i hi Y hY u1 hu => ?_` and prove the remaining obligations. Take `⟨hR, hK⟩` from `h x hx hle ι p hp`. Take `⟨S, a, s, hS, hs, ha⟩` from `hR i hi Y hY u1 hu`.

Take `⟨cc, hc0, hc, hZ⟩` from `hK i hi Y hY u1 hu`. Establish `hs0 : 0 ≤ s` using `(Finset.sum_nonneg fun q _ => mul_nonneg (hS.2.1 q) (Real.log_natCast_nonneg q)).trans hS.2.2.2`. Conclude with `⟨cc + s, add_nonneg hc0 hs0, budget_add hs hc, fun Z => mult_of hY.1.unf hS ha (hZ Z)⟩`.
-/
theorem multC_of_refW : GlobalTheory.RefSum.RefW → (Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → MultC := by
  intro hR hK
  refine Closed.imp (Closed.and hR hK) fun _ _ _ ⟨⟨C₁, h₁, hR⟩, C₂, h₂, hK⟩ => ⟨C₁ + C₂, add_nonneg h₁ h₂, ?_⟩
  refine (hR.and hK).imp fun _ h x hx hle ι p hp i hi Y hY u1 hu => ?_
  obtain ⟨hR, hK⟩ := h x hx hle ι p hp
  obtain ⟨S, a, s, hS, hs, ha⟩ := hR i hi Y hY u1 hu
  obtain ⟨cc, hc0, hc, hZ⟩ := hK i hi Y hY u1 hu
  have hs0 : 0 ≤ s := (Finset.sum_nonneg fun q _ => mul_nonneg (hS.2.1 q) (Real.log_natCast_nonneg q)).trans hS.2.2.2
  exact ⟨cc + s, add_nonneg hc0 hs0, budget_add hs hc, fun Z => mult_of hY.1.unf hS ha (hZ Z)⟩

end GlobalTheory.CovMult

end
