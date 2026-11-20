import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompat

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplPerf

section Generic

variable {U E R : Type} [CommRing U] [CommRing E] [CommRing R] (p : ℕ) (τ : U →* R)
  (φ : R →+* R) (io : E →+* R) (ψ : E → E)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact h`. Consider the case `succ k ih`. Take `⟨e, r, h⟩` from `ih`. Use `⟨ψ e, φ r, ?_⟩` and prove the remaining obligations.

Rewrite using `[← add_assoc, Function.iterate_succ_apply', h, map_add, map_mul, map_natCast, hψ]`.
-/
theorem persist (hψ : ∀ e, io (ψ e) = φ (io e)) {x : R} {n : ℕ}
    (h : ∃ e r, φ^[n] x = io e + (p : R) * r) (k : ℕ) :
    ∃ e r, φ^[n + k] x = io e + (p : R) * r := by
  induction k with
  | zero => exact h
  | succ k ih =>
    obtain ⟨e, r, h⟩ := ih
    refine ⟨ψ e, φ r, ?_⟩
    rw [← add_assoc, Function.iterate_succ_apply', h, map_add, map_mul, map_natCast, hψ]

/- English proof (translation)
Introduce `u hu`. Proceed by induction on `hu using Subring.closure_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero => exact ⟨0, 0, 0, by simp [h0]⟩`. Consider the case `one => exact ⟨0, 1, 0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`. Take `⟨e, r, h⟩` from `persist p φ io ψ hψ hn m`. Take `⟨e', r', h'⟩` from `persist p φ io ψ hψ hm n`.

Take `⟨c, hc⟩` from `hadd x y`. Rewrite `h'` using `[add_comm m n]`. Rewrite `h`, `h'` using `[← RingHom.coe_pow]`. Use `⟨n + m, e + e', r + r' + (φ ^ (n + m)) c, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.coe_pow, hc, map_add, map_add, map_mul, map_natCast, h, h', map_add]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x _ hx`. Take `⟨n, e, r, h⟩` from `hx`. Take `⟨c, hc⟩` from `hneg x`. Rewrite `h` using `[← RingHom.coe_pow]`.

Use `⟨n, -e, -r + (φ ^ n) c, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.coe_pow, hc, map_add, map_neg, map_mul, map_natCast, h, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`.

Take `⟨m, hm⟩` from `hy`. Take `⟨e, r, h⟩` from `persist p φ io ψ hψ hn m`. Take `⟨e', r', h'⟩` from `persist p φ io ψ hψ hm n`. Rewrite `h'` using `[add_comm m n]`. Rewrite `h`, `h'` using `[← RingHom.coe_pow]`.

Use `⟨n + m, e * e', io e * r' + r * (io e' + p * r'), ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.coe_pow, map_mul, map_mul, h, h', map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem closure_perf (hψ : ∀ e, io (ψ e) = φ (io e)) (h0 : τ 0 = 0)
    (hadd : ∀ x y, ∃ r, τ (x + y) = τ x + τ y + (p : R) * r)
    (hneg : ∀ x, ∃ r, τ (-x) = -τ x + (p : R) * r) (S : Set U)
    (hS : ∀ u ∈ S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r) :
    ∀ u ∈ Subring.closure S, ∃ n e r, φ^[n] (τ u) = io e + (p : R) * r := by
  intro u hu
  induction hu using Subring.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, 0, 0, by simp [h0]⟩
  | one => exact ⟨0, 1, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    obtain ⟨c, hc⟩ := hadd x y
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e + e', r + r' + (φ ^ (n + m)) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add, map_add, map_mul, map_natCast, h, h', map_add]
    ring
  | neg x _ hx =>
    obtain ⟨n, e, r, h⟩ := hx
    obtain ⟨c, hc⟩ := hneg x
    rw [← RingHom.coe_pow] at h
    refine ⟨n, -e, -r + (φ ^ n) c, ?_⟩
    rw [← RingHom.coe_pow, hc, map_add, map_neg, map_mul, map_natCast, h, map_neg]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    obtain ⟨e, r, h⟩ := persist p φ io ψ hψ hn m
    obtain ⟨e', r', h'⟩ := persist p φ io ψ hψ hm n
    rw [add_comm m n] at h'
    rw [← RingHom.coe_pow] at h h'
    refine ⟨n + m, e * e', io e * r' + r * (io e' + p * r'), ?_⟩
    rw [← RingHom.coe_pow, map_mul, map_mul, h, h', map_mul]
    ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, pow_succ]`.
-/
theorem iterate_τ (hφ : ∀ u, φ (τ u) = τ (u ^ p)) (n : ℕ) (u : U) :
    φ^[n] (τ u) = τ (u ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, pow_succ]

end Generic

variable {l : ℕ} [Fact l.Prime]

def teichW (l : ℕ) [Fact l.Prime] : OCb l →* WCb l :=
  (inclW l : Ainf l →* WCb l).comp (WittVector.teichmuller l)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem teichW_apply (u : OCb l) : teichW l u = inclW l (WittVector.teichmuller l u) := rfl

/- English proof (translation)
Rewrite using `[teichW_apply, coeff_inclW, WittVector.teichmuller_coeff_zero]`.
-/
theorem teichW_coeff (u : OCb l) : (teichW l u).coeff 0 = algebraMap (OCb l) (Cb l) u := by
  rw [teichW_apply, coeff_inclW, WittVector.teichmuller_coeff_zero]

/- English proof (translation)
Take `⟨r, hr⟩` from `(coeff_zero_eq_zero_iff (teichW l (x + y) - teichW l x - teichW l y)).1 (by`. Rewrite using `[sub_coeff_zero, sub_coeff_zero, teichW_coeff, teichW_coeff, teichW_coeff, map_add]`. Use the proof step `ring)`. Conclude with `⟨r, by linear_combination hr⟩`.
-/
theorem teichW_add (x y : OCb l) :
    ∃ r, teichW l (x + y) = teichW l x + teichW l y + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := (coeff_zero_eq_zero_iff (teichW l (x + y) - teichW l x - teichW l y)).1 (by
    rw [sub_coeff_zero, sub_coeff_zero, teichW_coeff, teichW_coeff, teichW_coeff, map_add]
    ring)
  exact ⟨r, by linear_combination hr⟩

/- English proof (translation)
Rewrite using `[teichW_apply, WittVector.teichmuller_zero, map_zero]`.
-/
theorem teichW_zero : teichW l 0 = 0 := by
  rw [teichW_apply, WittVector.teichmuller_zero, map_zero]

/- English proof (translation)
Take `⟨r, hr⟩` from `teichW_add x (-x)`. Rewrite `hr` using `[add_neg_cancel, teichW_zero]`. Conclude with `⟨-r, by linear_combination -hr⟩`.
-/
theorem teichW_neg (x : OCb l) : ∃ r, teichW l (-x) = -teichW l x + (l : WCb l) * r := by
  obtain ⟨r, hr⟩ := teichW_add x (-x)
  rw [add_neg_cancel, teichW_zero] at hr
  exact ⟨-r, by linear_combination -hr⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `WittVector.map (frobenius (Cb l) l) (teichW l u) = _`. Rewrite using `[teichW_apply, teichW_apply, inclW, WittVector.map_teichmuller, WittVector.map_teichmuller, WittVector.map_teichmuller, frobenius_def, ← map_pow]`.
-/
theorem frobW_teichW (u : OCb l) : frobW l (teichW l u) = teichW l (u ^ l) := by
  change WittVector.map (frobenius (Cb l) l) (teichW l u) = _
  rw [teichW_apply, teichW_apply, inclW, WittVector.map_teichmuller, WittVector.map_teichmuller,
    WittVector.map_teichmuller, frobenius_def, ← map_pow]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [LocAinf.εroot]`. Consider the case `succ k ih`. Rewrite using `[LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]`. Conclude with `ih`.
-/
theorem εroot_pow {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) : AI.εroot k ^ l ^ k = AI.ε := by
  induction k with
  | zero => simp [LocAinf.εroot]
  | succ k ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

def rightW (LL : FinExt l) : WCb l →+* RW LL :=
  (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] RW LL).toRingHom

def teichR (LL : FinExt l) : OCb l →* RW LL := (rightW LL : WCb l →* RW LL).comp (teichW l)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem teichR_apply (LL : FinExt l) (u : OCb l) : teichR LL u = rightW LL (teichW l u) := rfl

/- English proof (translation)
The claim follows from `congrArg (rightW LL) (frobW_teichW u)`.
-/
theorem φRW_teichR (LL : FinExt l) (u : OCb l) :
    (φRW LL : RW LL →+* RW LL) (teichR LL u) = teichR LL (u ^ l) :=
  congrArg (rightW LL) (frobW_teichW u)

/- English proof (translation)
Establish `h : teichW l (AI.εroot s) = inclW l (piW AI s) + 1`. Rewrite using `[piW, map_sub, map_one, sub_add_cancel, teichW_apply]`. Rewrite using `[teichR_apply, h, map_add, map_one]`. Both sides reduce to the same expression.
-/
theorem teichR_εroot {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) :
    teichR LL (AI.εroot s) = piR AI LL s + 1 := by
  have h : teichW l (AI.εroot s) = inclW l (piW AI s) + 1 := by
    rw [piW, map_sub, map_one, sub_add_cancel, teichW_apply]
  rw [teichR_apply, h, map_add, map_one]
  rfl

/- English proof (translation)
The claim follows from `IsIntegral.of_pow hm (hx ▸ isIntegral_one)`.
-/
theorem isIntegral_of_pow_eq_one {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {x : B}
    {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : IsIntegral A x :=
  IsIntegral.of_pow hm (hx ▸ isIntegral_one)

/- English proof (translation)
Rewrite using `[map_pow, map_add, map_one, ha, mul_zero, add_zero]`.
-/
theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero {E R : Type} [CommRing E] [CommRing R] (io : E →+* R) (p : ℕ) (a : E) (t : R)
    (ha : io a = t) (k : ℕ) : (t + 1) ^ k = io ((a + 1) ^ k) + (p : R) * 0 := by
  rw [map_pow, map_add, map_one, ha, mul_zero, add_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, a, 0, by simp [ha]⟩`.
-/
theorem gen_aux₀ {E R : Type} [CommRing E] [CommRing R] (φ : R →+* R) (io : E →+* R) (p : ℕ)
    (a : E) (t : R) (ha : io a = t) : ∃ n e r, φ^[n] t = io e + (p : R) * r :=
  ⟨0, a, 0, by simp [ha]⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `l _ P AI K s LL h W E`. Take `⟨h1, -, h3, -⟩` from `GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E`. Use `closure_perf l (teichR LL) (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL) W.φE h1 ?_ ?_ ?_ _ ?_` and prove the remaining obligations. Rewrite using `[teichR_apply, teichW_zero]`. Conclude with `(rightW LL).map_zero`.

Introduce `x y`. Take `⟨r, hr⟩` from `teichW_add x y`. Use `⟨rightW LL r, ?_⟩` and prove the remaining obligations. Rewrite using `[teichR_apply, teichR_apply, teichR_apply, hr, (rightW LL).map_add, (rightW LL).map_add, (rightW LL).map_mul, map_natCast (rightW LL)]`. Introduce `x`.

Take `⟨r, hr⟩` from `teichW_neg x`. Use `⟨rightW LL r, ?_⟩` and prove the remaining obligations. Rewrite using `[teichR_apply, teichR_apply, hr, (rightW LL).map_add, (rightW LL).map_neg, (rightW LL).map_mul, map_natCast (rightW LL)]`. Introduce and unpack `u (⟨k, rfl⟩ | ⟨c, hc, m, hm, hlm, hcm, hxb⟩)`. Use `⟨k, (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ + 1) ^ l ^ s, 0, ?_⟩` and prove the remaining obligations.

Establish `e1` using `iterate_τ l (teichR LL) (φRW LL : RW LL →+* RW LL) (φRW_teichR LL) k (AI.εroot k)`. Establish `e2 : teichR LL (AI.εroot k ^ l ^ k) = teichR LL (AI.εroot s) ^ l ^ s`. Rewrite using `[εroot_pow, ← εroot_pow AI s]`. Conclude with `(teichR LL).map_pow _ _`. Rewrite `e2` using `[teichR_εroot]`.

Conclude with `(e1.trans e2).trans (add_one_pow_eq_ringHom_image_add_prime_mul_zero (E.tie.ioE : W.EE →+* RW LL) l _ _ h3 _)`. Establish `hc' : (⟨c, hc⟩ : ↥(K0 K)) ^ m = 1` using `Subtype.ext hcm`. Establish `hint : ∀ i, IsIntegral ℤ_[l] (W.emb i ⟨c, hc⟩)` using `fun i => isIntegral_of_pow_eq_one hm (by rw [← map_pow, hc', map_one])`. Establish `e1` using `E.inertia_action_on_roots ⟨c, hc⟩ m hm hlm hcm u hxb (fun i => ⟨W.emb i ⟨c, hc⟩, hint i⟩) (fun i => rfl)`. Establish `e2` using `(E.tie.ioE_ext _).trans (congrArg (inclR LL) e1)`.

Conclude with `gen_aux₀ (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL) l _ _ e2`.
-/
theorem teich_mem_perfection : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), ∀ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ (n : ℕ) (e : W.EE) (r : RW LL), (φRW LL)^[n] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l u)) = E.tie.ioE e + (l : RW LL) * r := by
  intro l _ P AI K s LL h W E
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Decompl.ioE_compat l P AI K s LL h W E
  refine closure_perf l (teichR LL) (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL)
    W.φE h1 ?_ ?_ ?_ _ ?_
  · rw [teichR_apply, teichW_zero]; exact (rightW LL).map_zero
  · intro x y
    obtain ⟨r, hr⟩ := teichW_add x y
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, teichR_apply, hr, (rightW LL).map_add, (rightW LL).map_add,
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · intro x
    obtain ⟨r, hr⟩ := teichW_neg x
    refine ⟨rightW LL r, ?_⟩
    rw [teichR_apply, teichR_apply, hr, (rightW LL).map_add, (rightW LL).map_neg,
      (rightW LL).map_mul, map_natCast (rightW LL)]
  · rintro u (⟨k, rfl⟩ | ⟨c, hc, m, hm, hlm, hcm, hxb⟩)
    · refine ⟨k, (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ + 1) ^ l ^ s,
        0, ?_⟩
      have e1 := iterate_τ l (teichR LL) (φRW LL : RW LL →+* RW LL) (φRW_teichR LL) k (AI.εroot k)
      have e2 : teichR LL (AI.εroot k ^ l ^ k) = teichR LL (AI.εroot s) ^ l ^ s := by
        rw [εroot_pow, ← εroot_pow AI s]
        exact (teichR LL).map_pow _ _
      rw [teichR_εroot] at e2
      exact (e1.trans e2).trans (add_one_pow_eq_ringHom_image_add_prime_mul_zero (E.tie.ioE : W.EE →+* RW LL) l _ _ h3 _)
    · have hc' : (⟨c, hc⟩ : ↥(K0 K)) ^ m = 1 := Subtype.ext hcm
      have hint : ∀ i, IsIntegral ℤ_[l] (W.emb i ⟨c, hc⟩) := fun i =>
        isIntegral_of_pow_eq_one hm (by rw [← map_pow, hc', map_one])
      have e1 := E.inertia_action_on_roots ⟨c, hc⟩ m hm hlm hcm u hxb (fun i => ⟨W.emb i ⟨c, hc⟩, hint i⟩)
        (fun i => rfl)
      have e2 := (E.tie.ioE_ext _).trans (congrArg (inclR LL) e1)
      exact gen_aux₀ (φRW LL : RW LL →+* RW LL) (E.tie.ioE : W.EE →+* RW LL) l _ _ e2

end GlobalTheory.DecomplPerf
