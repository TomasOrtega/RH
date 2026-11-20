import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpUConstMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoords
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.ThetaDecomp

def okGroup (d : ℕ) : AddSubgroup ℂ where
  carrier := {z | InOK d z}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
    exact ⟨u + u', v + v', by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨u, v, rfl⟩
    exact ⟨-u, -v, by push_cast; ring⟩

/- English proof (translation)
Take `⟨u, v, rfl⟩` from `h`. Conclude with `⟨n * u, n * v, by push_cast; ring⟩`.
-/
theorem inOK_natCast_mul {d : ℕ} (n : ℕ) {z : ℂ} (h : InOK d z) : InOK d ((n : ℂ) * z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

/- English proof (translation)
Simplify using `[wK]`.
-/
theorem wK_re (d : ℕ) : (wK d).re = 1 / 2 := by simp [wK]

/- English proof (translation)
Simplify using `[wK]`.
-/
theorem wK_im (d : ℕ) : (wK d).im = Real.sqrt d / 2 := by simp [wK]

/- English proof (translation)
Take `⟨u, v, rfl⟩` from `hx`. Take `⟨u', v', rfl⟩` from `hy`. Establish `hs : Real.sqrt d ≠ 0` using `by positivity`. Use `⟨v * u' - u * v', ?_⟩` and prove the remaining obligations. Rewrite using `[h1, Complex.im_ofReal_mul]`.

Simplify using `[wK_re, wK_im]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeHermitianForm_im_int_of_mem_order {d : ℕ} (hd : 0 < d) {x y : ℂ} (hx : InOK d x) (hy : InOK d y) : ∃ k : ℤ, (h1 d x y).im = k := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  have hs : Real.sqrt d ≠ 0 := by positivity
  refine ⟨v * u' - u * v', ?_⟩
  rw [h1, Complex.im_ofReal_mul]
  simp [wK_re, wK_im]
  field_simp
  ring

/- English proof (translation)
Establish `hs : Real.sqrt d ≠ 0` using `by positivity`. Rewrite `h`, `h'` using `[h1, Complex.im_ofReal_mul]`. Simplify using `only [Complex.mul_im, Complex.conj_re, Complex.conj_im, wK_re, wK_im, map_one, Complex.one_re, Complex.one_im] at h h'`. Establish `e : Real.sqrt d * (2 / Real.sqrt d) = 2` using `by field_simp`. Use `⟨-l, k, Complex.ext ?_ ?_⟩` and prove the remaining obligations.

Simplify using `[wK_re, wK_im]`. Take the linear combination `(-1) * h' + (1 / 2) * h - z.re / 2 * e`. Simplify using `[wK_re, wK_im]`. Take the linear combination `(Real.sqrt d / 2) * h - z.im / 2 * e`.
-/
theorem inOK_of_im {d : ℕ} (hd : 0 < d) {z : ℂ} {k l : ℤ} (h : (h1 d z 1).im = k) (h' : (h1 d z (wK d)).im = l) :
    InOK d z := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  rw [h1, Complex.im_ofReal_mul] at h h'
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, wK_re, wK_im, map_one, Complex.one_re,
    Complex.one_im] at h h'
  have e : Real.sqrt d * (2 / Real.sqrt d) = 2 := by field_simp
  refine ⟨-l, k, Complex.ext ?_ ?_⟩
  · simp [wK_re, wK_im]
    linear_combination (-1) * h' + (1 / 2) * h - z.re / 2 * e
  · simp [wK_re, wK_im]
    linear_combination (Real.sqrt d / 2) * h - z.im / 2 * e

/- English proof (translation)
Rewrite using `[mem_algebraicClosure_iff]`. Use `IsAlgebraic.of_pow (n := 2 * r.den) (by have := r.den_pos; omega) ?_` and prove the remaining obligations. Establish `: Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) ^ (2 * r.den) = 1`. Rewrite using `[← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`. Use `⟨r.num, ?_⟩` and prove the remaining obligations.

Establish `: (r.num : ℂ) = r * r.den` using `by exact_mod_cast (Rat.mul_den_eq_num r).symm`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `isAlgebraic_one`.
-/
theorem exp_rat_mem (r : ℚ) : Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * r.den) (by have := r.den_pos; omega) ?_
  have : Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) ^ (2 * r.den) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have : (r.num : ℂ) = r * r.den := by exact_mod_cast (Rat.mul_den_eq_num r).symm
    rw [this]; push_cast; ring
  rw [this]; exact isAlgebraic_one

/- English proof (translation)
Rewrite using `[kap, Complex.exp_eq_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Use `⟨-n, ?_⟩` and prove the remaining obligations. Establish `h2 : (((hf Hm x y).im : ℝ) : ℂ) = ((-n : ℤ) : ℝ)`.

Apply `mul_left_cancel₀ Complex.two_pi_I_ne_zero` to reduce the goal to its premises. Use `push_cast`. Take the linear combination `-hn`. Conclude with `h2` after adjusting the coercions. Introduce and unpack `⟨k, hk⟩`.

Conclude with `⟨-k, by rw [hk]; push_cast; ring⟩`.
-/
theorem kap_eq_one_iff {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    kap Hm x y = 1 ↔ ∃ k : ℤ, (hf Hm x y).im = k := by
  rw [kap, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have h2 : (((hf Hm x y).im : ℝ) : ℂ) = ((-n : ℤ) : ℝ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      push_cast
      linear_combination -hn
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    exact ⟨-k, by rw [hk]; push_cast; ring⟩

noncomputable def betaL {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun v := beta d Hm v y
  map_add' v w := by simp only [beta, hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    simp only [beta, hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem natCast_mul_im (n : ℕ) (z : ℂ) : ((n : ℂ) * z).im = n * z.im := by simp

/- English proof (translation)
Simplify using `only [h1, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cmLatticeHermitianForm_natCast_mul_right (d n : ℕ) (z w : ℂ) : h1 d z ((n : ℂ) * w) = n * h1 d z w := by
  simp only [h1, map_mul, map_natCast]; ring

/- English proof (translation)
Take `⟨h1, -, h3, -⟩` from `GlobalTheory.HeisOps.heisenberg g S.d S.Hm hS.1.pos hS.2.2.1.1`. Establish `hW : ∀ (l l' : S.La) F, opW S.d S.Hm l (opW S.d S.Hm l' F) = opW S.d S.Hm (l + l' : S.La) F` using `fun l l' F => (h1 l l' F).2.2 (hS.2.2.2.2.2.2.1 l l.2 l' l'.2)`. Establish `hq : ∀ l l' : S.La, (l : S.La ⧸ A) = l' → opW S.d S.Hm l G = opW S.d S.Hm l' G`. Introduce `l l' h`. Use `hW l (-l + l') G` as an intermediate fact.

Rewrite `this` using `[hA _ (QuotientAddGroup.eq.1 h), add_neg_cancel_left]`. Conclude with `this`. Use `⟨ContDiff.sum fun c _ => (h3 _ G hG).2, fun y hy => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[← Equiv.sum_comp (Equiv.addLeft ((⟨y, hy⟩ : S.La) : S.La ⧸ A))]`.

Establish `: opW S.d S.Hm y (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) G z) z = ∑ c : S.La ⧸ A, opW S.d S.Hm y (opW S.d S.Hm (c.out : S.La) G) z`. Simplify using `only [opW.eq_1 S.d S.Hm y, opU.eq_1 S.Hm y, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hW ⟨y, hy⟩, hq]`.

Simplify using the standard rewrite rules.
-/
theorem isTheta_sum {g : ℕ} (S : Setup g) (hS : S.Ok) (A : AddSubgroup S.La) [Fintype (S.La ⧸ A)]
    (G : (Fin g → ℂ) → ℂ) (hG : ContDiff ℂ ⊤ G) (hA : ∀ l ∈ A, opW S.d S.Hm l G = G) :
    S.IsTheta (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) G z) := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hS.1.pos hS.2.2.1.1
  have hW : ∀ (l l' : S.La) F, opW S.d S.Hm l (opW S.d S.Hm l' F) = opW S.d S.Hm (l + l' : S.La) F :=
    fun l l' F => (h1 l l' F).2.2 (hS.2.2.2.2.2.2.1 l l.2 l' l'.2)
  have hq : ∀ l l' : S.La, (l : S.La ⧸ A) = l' → opW S.d S.Hm l G = opW S.d S.Hm l' G := by
    intro l l' h
    have := hW l (-l + l') G
    rw [hA _ (QuotientAddGroup.eq.1 h), add_neg_cancel_left] at this
    exact this
  refine ⟨ContDiff.sum fun c _ => (h3 _ G hG).2, fun y hy => ?_⟩
  funext z
  rw [← Equiv.sum_comp (Equiv.addLeft ((⟨y, hy⟩ : S.La) : S.La ⧸ A))]
  have : opW S.d S.Hm y (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) G z) z =
      ∑ c : S.La ⧸ A, opW S.d S.Hm y (opW S.d S.Hm (c.out : S.La) G) z := by
    simp only [opW.eq_1 S.d S.Hm y, opU.eq_1 S.Hm y, Finset.mul_sum, Finset.sum_mul]
  rw [this]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hW ⟨y, hy⟩, hq]
  simp

end GlobalTheory.MomOne.ThetaDecomp

namespace GlobalTheory.MomOne
open ThetaDecomp

/- English proof (translation)
Introduce `q g S x a θ _ hS hx hβ ha hθ`. Establish `hd : 0 < S.d` using `hS.1.pos`. Take `⟨c1, c2, c3, -⟩` from `GlobalTheory.MomOne.Frame.coord g S x a hd hβ fun i => (ha i).1`. Take `⟨e1, -, e3, -, -, e6⟩` from `GlobalTheory.HeisOps.heisenberg g S.d S.Hm hd hS.2.2.1.1`. Establish `ha0 : ∀ i, (a i : ℂ) ≠ 0` using `fun i => by exact_mod_cast (ha i).1.ne'`.

Take `⟨ψ, hψ⟩ : ∃ ψ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v i, ψ v i = beta S.d S.Hm v (x i) / (a i : ℂ)` from `⟨LinearMap.pi fun i => (a i : ℂ)⁻¹ • betaL S.d S.Hm (x i), fun v i => by`. Rewrite using `[div_eq_inv_mul]`. Use the proof step `rfl⟩`. Establish `hφψ : ∀ v, ∑ i, ψ v i • x i = v` using `fun v => by simp only [hψ]; exact (c1 v).symm`. Establish `hψφ : ∀ z : Fin g → ℂ, ψ (∑ i, z i • x i) = z` using `fun z => by`.

Use function extensionality and compare the values at `i`. Rewrite using `[map_sum, Finset.sum_apply]`. Simplify using `only [map_smul]`. Simplify using `only [Pi.smul_apply, hψ, hβ, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single i (fun j _ h => by simp [h]) (by simp)]`.

Simplify using `[ha0 i]`. Establish `hH : ∀ v w, (hf S.Hm v w).im = ∑ i, (a i : ℝ) * (h1 S.d (ψ v i) (ψ w i)).im` using `fun v w => by`. Use `c2 (ψ v) (ψ w)` as an intermediate fact. Rewrite `this` using `[hφψ, hφψ]`. Rewrite using `[this, Complex.im_sum]`.

Simplify using the standard rewrite rules. Take `⟨F, hFd⟩ : ∃ F : (Fin g → ℂ) → ℂ, F = fun v => ∏ i, θ (ψ v i) ^ a i` from `⟨_, rfl⟩`. Establish `hF : ∀ z : Fin g → ℂ, F (∑ i, z i • x i) = ∑ _j : Fin 1, 1 * ∏ i, θ (z i) ^ a i` using `fun z => by`. Simplify using `[hFd, hψφ]`. Establish `hFc : ContDiff ℂ ⊤ F`.

Rewrite using `[hFd]`. Use `contDiff_prod fun i _ => ContDiff.pow (hθ.1.contDiff.comp ?_) _` and prove the remaining obligations. Conclude with `(LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp ψ)).contDiff`. Establish `hF0 : F 0 = 1` using `by simp [hFd, hθ.2.1]`. Establish `hU : ∀ v z : Fin g → ℂ, opU S.Hm v F (∑ i, z i • x i) = ∏ i, U1 S.d (ψ v i) θ (z i) ^ a i` using `fun v z => by`.

Use `(c3 1 (fun _ => 1) (fun _ _ => θ) F hF (ψ v) z).1` as an intermediate fact. Rewrite `this` using `[hφψ]`. Simplify using `using this`. Establish `hW : ∀ v : Fin g → ℂ, (∀ i, InOK S.d (ψ v i)) → opW S.d S.Hm v F = F` using `fun v hv => by`. Use function extensionality and compare the values at `w`.

Use `(c3 1 (fun _ => 1) (fun _ _ => θ) F hF (ψ v) (ψ w)).2` as an intermediate fact. Rewrite `this` using `[hφψ, hφψ]`. Rewrite using `[this]`. Simplify using `[hFd, hθ.2.2.2.1 _ (hv _)]`. Take `⟨D, hD⟩ : ∃ D : AddSubgroup (Fin g → ℂ), ∀ v, v ∈ D ↔ ∀ i, InOK S.d ((a i : ℂ) * ψ v i)` from `⟨⨅ i, (okGroup S.d).comap ((betaL S.d S.Hm (x i)).toAddMonoidHom), fun v => by`.

Simplify using `only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap, hψ, mul_div_cancel₀ _ (ha0 _)]`. Use the proof step `rfl⟩`. Establish `hLD : ∀ l ∈ S.La, l ∈ D` using `fun l hl => (hD l).2 fun i => by`. Rewrite using `[hψ, mul_div_cancel₀ _ (ha0 _)]`. Conclude with `hS.2.2.2.2.2.2.1 l hl _ (hx i)`.

Take `⟨A, hA⟩ : ∃ A : AddSubgroup S.La, ∀ l : S.La, l ∈ A ↔ ∀ i, InOK S.d (ψ l i)` from `⟨⨅ i, (okGroup S.d).comap (((LinearMap.proj i).comp ψ : (Fin g → ℂ) →ₗ[ℂ] ℂ).toAddMonoidHom.comp S.La.subtype.toAddMonoidHom), fun l => by`. Simplify using `only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]`. Use the proof step `rfl⟩`. Establish `hN : ∀ v ∈ D, ∀ i, InOK S.d (ψ ((∏ j, a j) • v) i)` using `fun v hv i => by`. Use `inOK_natCast_mul (∏ j ∈ Finset.univ.erase i, a j) ((hD v).1 hv i)` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Rewrite using `[map_nsmul, Pi.smul_apply, nsmul_eq_mul]` and apply the resulting hypothesis. Establish `hN0 : ∏ j, a j ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => (ha i).1.ne'`. Establish `hint : ∀ v, (∀ i, InOK S.d (ψ v i)) → ∀ w ∈ D, ∃ k : ℤ, (hf S.Hm v w).im = k` using `fun v hv w hw => by choose k hk using fun i => cmLatticeHermitianForm_im_int_of_mem_order hd (hv i) ((hD w).1 hw i)`. Use `⟨∑ i, k i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hH]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hk, cmLatticeHermitianForm_natCast_mul_right]`. Simplify using the standard rewrite rules.

Establish `hrat : ∀ v ∈ D, ∀ w ∈ D, ∃ r : ℚ, (hf S.Hm v w).im = r` using `fun v hv w hw => by`. Take `⟨k, hk⟩` from `hint _ (hN v hv) w hw`. Use `⟨k / (∏ j, a j : ℕ), ?_⟩` and prove the remaining obligations. Establish `h0 : ((∏ j, a j : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast hN0`. Rewrite using `[Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff h0, ← hk, hH, hH, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, Pi.smul_apply, nsmul_eq_mul, Basic.cmLatticeHermitianForm_mul_left, natCast_mul_im]`. Expand and normalize the polynomial expressions, which then agree. Use `hS.2.2.2.1` as an intermediate fact. Establish `: Module.Finite ℤ S.La` using `inferInstance`.

Establish `: AddGroup.FG S.La` using `Module.Finite.iff_addGroup_fg.1 inferInstance`. Use `AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg S.La hN0` as an intermediate fact. Establish `: A.FiniteIndex` using `AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom (∏ j, a j)).range) (by`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `(hA _).2 (hN l (hLD l l.2)))`.

Establish `: Fintype (S.La ⧸ A)` using `Fintype.ofFinite _`. Establish `hcomm : ∀ (l w : Fin g → ℂ) z, opW S.d S.Hm l (opU S.Hm w F) z = kap S.Hm l w * opU S.Hm w (opW S.d S.Hm l F) z`. Introduce `l w z`. Rewrite using `[opW, (e1 l w F).2.1]`. Simplify using `only [opU.eq_1 S.Hm w, opW]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hk0 : ∀ l w : Fin g → ℂ, kap S.Hm l w ≠ 0` using `fun l w => Complex.exp_ne_zero _`. Take `⟨χ, hχd⟩ : ∃ χ : S.La ⧸ A → Multiplicative D →* ℂ, ∀ c w hw, χ c (Multiplicative.ofAdd ⟨w, hw⟩) = kap S.Hm (c.out : S.La) w` from `⟨fun c => { toFun := fun w => kap S.Hm (c.out : S.La) (Multiplicative.toAdd w : D) map_one' := by simp [kap, hf] map_mul' := fun w w' => (e6 _ _ _).1 }, fun _ _ _ => rfl⟩`. Establish `hχ : Function.Injective χ`. Introduce `c c' h`.

Rewrite using `[← c.out_eq, ← c'.out_eq]`. Use `QuotientAddGroup.eq.2 ((hA _).2 fun i => ?_)` and prove the remaining obligations. Establish `key : ∀ s, InOK S.d s → ∃ k : ℤ, (h1 S.d (ψ (-c.out + c'.out : S.La) i) s).im = k`. Introduce `s hs`. Take `⟨w, hψs⟩ : ∃ w, ψ w = Pi.single i (s / a i)` from `⟨_, hψφ _⟩`.

Establish `hw : w ∈ D` using `(hD w).2 fun j => by`. Rewrite using `[hψs]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify `hs` using `[mul_div_cancel₀ _ (ha0 _)]`.

Conclude with `⟨0, 0, by simp [hj]⟩`. Establish `h1' : kap S.Hm (c.out : S.La) w = kap S.Hm (c'.out : S.La) w`. Rewrite using `[← hχd c w hw, ← hχd c' w hw, h]`. Establish `h2` using `(e6 (c.out : S.La) (-c.out + c'.out : S.La) w).2`. Rewrite `h2` using `[← Submodule.coe_add, add_neg_cancel_left, ← h1']`.

Take `⟨k, hk⟩` from `(kap_eq_one_iff _ _ _).1 ((mul_eq_left₀ (hk0 _ _)).1 h2.symm)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, hH, hψs, Finset.sum_eq_single i (fun j _ h => by simp [h, h1]) (by simp), ← natCast_mul_im, ← cmLatticeHermitianForm_natCast_mul_right]`. Simplify using `[mul_div_cancel₀ _ (ha0 _)]`. Take `⟨k, hk⟩` from `key 1 ⟨1, 0, by simp⟩`.

Take `⟨l, hl⟩` from `key (wK S.d) ⟨0, 1, by simp⟩`. Conclude with `inOK_of_im hd hk hl`. Establish `hli` using `(linearIndependent_monoidHom (Multiplicative D) ℂ).comp χ hχ`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ, hne⟩ : ∃ σ ∈ D, (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) (opU S.Hm σ F) z) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `h` using `Fintype.linearIndependent_iff.1 hli (fun c => opW S.d S.Hm (c.out : S.La) F 0) (by`. Use function extensionality and compare the values at `w`. Rewrite using `[Finset.sum_apply, Pi.zero_apply]`. Take `⟨σ, hσ⟩` from `w`.

Establish `h` using `congrFun (hcon σ hσ) (-σ)`. Simplify using `only [hcomm, opU.eq_1 S.Hm σ, neg_add_cancel, ← mul_assoc, ← Finset.sum_mul, Pi.zero_apply] at h`. Establish `h` using `(mul_eq_zero.1 h).resolve_right (Complex.exp_ne_zero _)`. Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [← hχd c σ hσ]; exact mul_comm _ _) 0`.

Establish `h0 : (0 : S.La ⧸ A).out ∈ A` using `(QuotientAddGroup.eq_zero_iff _).1 (Quotient.out_eq _)`. Simplify using `only [hW _ ((hA _).1 h0), hF0] at h`. Conclude with `one_ne_zero h`. Use `clear c1 c2 c3`. Establish `hth` using `isTheta_sum S hS A (opU S.Hm σ F) (e3 σ F hFc).1 fun l hl => by`.

Use function extensionality and compare the values at `z`. Rewrite using `[hcomm, hW _ ((hA l).1 hl), (kap_eq_one_iff _ _ _).2 (hint _ ((hA l).1 hl) σ hσ), one_mul]`. Set `e` to `(Fintype.equivFin (S.La ⧸ A)).symm`. Use `⟨_, fun j => Complex.exp ((Real.pi : ℂ) * Complex.I * ((beta S.d S.Hm ((e j).out : S.La) ((e j).out : S.La)).re : ℂ)) * Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf S.Hm ((e j).out : S.La) σ).im : ℝ) : ℂ)), fun j => ψ (((e j).out : S.La) + σ), _, hth, hne, fun j => mul_mem ?_ …` and prove the remaining obligations. Take `⟨u, v, h⟩` from `hS.2.2.2.2.2.2.1 _ (e j).out.2 _ (e j).out.2`.

Establish `h' : (w0 S.d).re = 1 / 2` using `wK_re S.d`. Use `exp_rat_mem (u + v / 2) using 3` and compare the differences between its conclusion and the goal. Rewrite using `[h]`. Simplify using `[h']`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨r, hr⟩` from `hrat _ (hLD _ (e j).out.2) σ hσ`. Use `exp_rat_mem (-r) using 2` and compare the differences between its conclusion and the goal. Rewrite using `[hr]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨a i, (ha i).1, (ha i).2, (hD _).1 (D.add_mem (hLD _ (e j).out.2) hσ) i⟩`. Rewrite using `[← Equiv.sum_comp e]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[opW, (e1 _ σ F).1, ← hU]`. Conclude with `(mul_assoc _ _ _).symm`.
-/
theorem exists_theta_eq_sum_prod : ∀ (q : ℕ) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (θ : ℂ → ℂ), q.Prime → S.Ok → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → IsTh S.d θ → ∃ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → Fin g → ℂ) (Θ : (Fin g → ℂ) → ℂ), S.IsTheta Θ ∧ Θ ≠ 0 ∧ (∀ j, r j ∈ Qbar) ∧ (∀ j i, PrimeTo S.d q (t j i)) ∧ ∀ z : Fin g → ℂ, Θ (∑ i, z i • x i) = ∑ j, r j * ∏ i, U1 S.d (t j i) θ (z i) ^ a i := by
  classical
  intro q g S x a θ _ hS hx hβ ha hθ
  have hd : 0 < S.d := hS.1.pos
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.MomOne.Frame.coord g S x a hd hβ fun i => (ha i).1
  obtain ⟨e1, -, e3, -, -, e6⟩ := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hd hS.2.2.1.1
  have ha0 : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).1.ne'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v i, ψ v i = beta S.d S.Hm v (x i) / (a i : ℂ) :=
    ⟨LinearMap.pi fun i => (a i : ℂ)⁻¹ • betaL S.d S.Hm (x i), fun v i => by
      rw [div_eq_inv_mul]; rfl⟩
  have hφψ : ∀ v, ∑ i, ψ v i • x i = v := fun v => by simp only [hψ]; exact (c1 v).symm
  have hψφ : ∀ z : Fin g → ℂ, ψ (∑ i, z i • x i) = z := fun z => by
    funext i
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul]
    simp only [Pi.smul_apply, hψ, hβ, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j _ h => by simp [h]) (by simp)]
    simp [ha0 i]
  have hH : ∀ v w, (hf S.Hm v w).im = ∑ i, (a i : ℝ) * (h1 S.d (ψ v i) (ψ w i)).im := fun v w => by
    have := c2 (ψ v) (ψ w)
    rw [hφψ, hφψ] at this
    rw [this, Complex.im_sum]
    simp
  obtain ⟨F, hFd⟩ : ∃ F : (Fin g → ℂ) → ℂ, F = fun v => ∏ i, θ (ψ v i) ^ a i := ⟨_, rfl⟩
  have hF : ∀ z : Fin g → ℂ, F (∑ i, z i • x i) = ∑ _j : Fin 1, 1 * ∏ i, θ (z i) ^ a i := fun z => by
    simp [hFd, hψφ]
  have hFc : ContDiff ℂ ⊤ F := by
    rw [hFd]
    refine contDiff_prod fun i _ => ContDiff.pow (hθ.1.contDiff.comp ?_) _
    exact (LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp ψ)).contDiff
  have hF0 : F 0 = 1 := by simp [hFd, hθ.2.1]
  have hU : ∀ v z : Fin g → ℂ, opU S.Hm v F (∑ i, z i • x i) = ∏ i, U1 S.d (ψ v i) θ (z i) ^ a i := fun v z => by
    have := (c3 1 (fun _ => 1) (fun _ _ => θ) F hF (ψ v) z).1
    rw [hφψ] at this
    simpa using this
  have hW : ∀ v : Fin g → ℂ, (∀ i, InOK S.d (ψ v i)) → opW S.d S.Hm v F = F := fun v hv => by
    funext w
    have := (c3 1 (fun _ => 1) (fun _ _ => θ) F hF (ψ v) (ψ w)).2
    rw [hφψ, hφψ] at this
    rw [this]
    simp [hFd, hθ.2.2.2.1 _ (hv _)]
  obtain ⟨D, hD⟩ : ∃ D : AddSubgroup (Fin g → ℂ), ∀ v, v ∈ D ↔ ∀ i, InOK S.d ((a i : ℂ) * ψ v i) :=
    ⟨⨅ i, (okGroup S.d).comap ((betaL S.d S.Hm (x i)).toAddMonoidHom), fun v => by
      simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap, hψ, mul_div_cancel₀ _ (ha0 _)]
      rfl⟩
  have hLD : ∀ l ∈ S.La, l ∈ D := fun l hl => (hD l).2 fun i => by
    rw [hψ, mul_div_cancel₀ _ (ha0 _)]
    exact hS.2.2.2.2.2.2.1 l hl _ (hx i)
  obtain ⟨A, hA⟩ : ∃ A : AddSubgroup S.La, ∀ l : S.La, l ∈ A ↔ ∀ i, InOK S.d (ψ l i) :=
    ⟨⨅ i, (okGroup S.d).comap
      (((LinearMap.proj i).comp ψ : (Fin g → ℂ) →ₗ[ℂ] ℂ).toAddMonoidHom.comp S.La.subtype.toAddMonoidHom), fun l => by
      simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
      rfl⟩
  have hN : ∀ v ∈ D, ∀ i, InOK S.d (ψ ((∏ j, a j) • v) i) := fun v hv i => by
    have := inOK_natCast_mul (∏ j ∈ Finset.univ.erase i, a j) ((hD v).1 hv i)
    rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at this
    rwa [map_nsmul, Pi.smul_apply, nsmul_eq_mul]
  have hN0 : ∏ j, a j ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (ha i).1.ne'
  have hint : ∀ v, (∀ i, InOK S.d (ψ v i)) → ∀ w ∈ D, ∃ k : ℤ, (hf S.Hm v w).im = k := fun v hv w hw => by
    choose k hk using fun i => cmLatticeHermitianForm_im_int_of_mem_order hd (hv i) ((hD w).1 hw i)
    refine ⟨∑ i, k i, ?_⟩
    rw [hH]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hk, cmLatticeHermitianForm_natCast_mul_right]; simp
  have hrat : ∀ v ∈ D, ∀ w ∈ D, ∃ r : ℚ, (hf S.Hm v w).im = r := fun v hv w hw => by
    obtain ⟨k, hk⟩ := hint _ (hN v hv) w hw
    refine ⟨k / (∏ j, a j : ℕ), ?_⟩
    have h0 : ((∏ j, a j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff h0, ← hk, hH, hH, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Basic.cmLatticeHermitianForm_mul_left, natCast_mul_im]
    ring
  have := hS.2.2.2.1
  have : Module.Finite ℤ S.La := inferInstance
  have : AddGroup.FG S.La := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg S.La hN0
  have : A.FiniteIndex := AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom (∏ j, a j)).range) (by
    rintro _ ⟨l, rfl⟩
    exact (hA _).2 (hN l (hLD l l.2)))
  have : Fintype (S.La ⧸ A) := Fintype.ofFinite _
  have hcomm : ∀ (l w : Fin g → ℂ) z, opW S.d S.Hm l (opU S.Hm w F) z = kap S.Hm l w * opU S.Hm w (opW S.d S.Hm l F) z := by
    intro l w z
    rw [opW, (e1 l w F).2.1]
    simp only [opU.eq_1 S.Hm w, opW]
    ring
  have hk0 : ∀ l w : Fin g → ℂ, kap S.Hm l w ≠ 0 := fun l w => Complex.exp_ne_zero _
  obtain ⟨χ, hχd⟩ : ∃ χ : S.La ⧸ A → Multiplicative D →* ℂ, ∀ c w hw,
      χ c (Multiplicative.ofAdd ⟨w, hw⟩) = kap S.Hm (c.out : S.La) w :=
    ⟨fun c =>
      { toFun := fun w => kap S.Hm (c.out : S.La) (Multiplicative.toAdd w : D)
        map_one' := by simp [kap, hf]
        map_mul' := fun w w' => (e6 _ _ _).1 }, fun _ _ _ => rfl⟩
  have hχ : Function.Injective χ := by
    intro c c' h
    rw [← c.out_eq, ← c'.out_eq]
    refine QuotientAddGroup.eq.2 ((hA _).2 fun i => ?_)
    have key : ∀ s, InOK S.d s → ∃ k : ℤ, (h1 S.d (ψ (-c.out + c'.out : S.La) i) s).im = k := by
      intro s hs
      obtain ⟨w, hψs⟩ : ∃ w, ψ w = Pi.single i (s / a i) := ⟨_, hψφ _⟩
      have hw : w ∈ D := (hD w).2 fun j => by
        rw [hψs]
        by_cases hj : j = i
        · subst hj; simpa [mul_div_cancel₀ _ (ha0 _)] using hs
        · exact ⟨0, 0, by simp [hj]⟩
      have h1' : kap S.Hm (c.out : S.La) w = kap S.Hm (c'.out : S.La) w := by
        rw [← hχd c w hw, ← hχd c' w hw, h]
      have h2 := (e6 (c.out : S.La) (-c.out + c'.out : S.La) w).2
      rw [← Submodule.coe_add, add_neg_cancel_left, ← h1'] at h2
      obtain ⟨k, hk⟩ := (kap_eq_one_iff _ _ _).1 ((mul_eq_left₀ (hk0 _ _)).1 h2.symm)
      refine ⟨k, ?_⟩
      rw [← hk, hH, hψs, Finset.sum_eq_single i (fun j _ h => by simp [h, h1]) (by simp), ← natCast_mul_im,
        ← cmLatticeHermitianForm_natCast_mul_right]
      simp [mul_div_cancel₀ _ (ha0 _)]
    obtain ⟨k, hk⟩ := key 1 ⟨1, 0, by simp⟩
    obtain ⟨l, hl⟩ := key (wK S.d) ⟨0, 1, by simp⟩
    exact inOK_of_im hd hk hl
  have hli := (linearIndependent_monoidHom (Multiplicative D) ℂ).comp χ hχ
  obtain ⟨σ, hσ, hne⟩ : ∃ σ ∈ D, (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) (opU S.Hm σ F) z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := Fintype.linearIndependent_iff.1 hli (fun c => opW S.d S.Hm (c.out : S.La) F 0) (by
      funext w
      rw [Finset.sum_apply, Pi.zero_apply]
      obtain ⟨σ, hσ⟩ := w
      have h := congrFun (hcon σ hσ) (-σ)
      simp only [hcomm, opU.eq_1 S.Hm σ, neg_add_cancel, ← mul_assoc, ← Finset.sum_mul, Pi.zero_apply] at h
      have h := (mul_eq_zero.1 h).resolve_right (Complex.exp_ne_zero _)
      rw [← h]
      exact Finset.sum_congr rfl fun c _ => by rw [← hχd c σ hσ]; exact mul_comm _ _) 0
    have h0 : (0 : S.La ⧸ A).out ∈ A := (QuotientAddGroup.eq_zero_iff _).1 (Quotient.out_eq _)
    simp only [hW _ ((hA _).1 h0), hF0] at h
    exact one_ne_zero h
  clear c1 c2 c3
  have hth := isTheta_sum S hS A (opU S.Hm σ F) (e3 σ F hFc).1 fun l hl => by
    funext z
    rw [hcomm, hW _ ((hA l).1 hl), (kap_eq_one_iff _ _ _).2 (hint _ ((hA l).1 hl) σ hσ), one_mul]
  let e := (Fintype.equivFin (S.La ⧸ A)).symm
  refine ⟨_, fun j => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((beta S.d S.Hm ((e j).out : S.La) ((e j).out : S.La)).re : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf S.Hm ((e j).out : S.La) σ).im : ℝ) : ℂ)),
    fun j => ψ (((e j).out : S.La) + σ), _, hth, hne, fun j => mul_mem ?_ ?_, fun j i => ?_, fun z => ?_⟩
  · obtain ⟨u, v, h⟩ := hS.2.2.2.2.2.2.1 _ (e j).out.2 _ (e j).out.2
    have h' : (w0 S.d).re = 1 / 2 := wK_re S.d
    convert exp_rat_mem (u + v / 2) using 3
    rw [h]; simp [h']; ring
  · obtain ⟨r, hr⟩ := hrat _ (hLD _ (e j).out.2) σ hσ
    convert exp_rat_mem (-r) using 2
    rw [hr]; push_cast; ring
  · exact ⟨a i, (ha i).1, (ha i).2, (hD _).1 (D.add_mem (hLD _ (e j).out.2) hσ) i⟩
  · rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [opW, (e1 _ σ F).1, ← hU]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.MomOne
