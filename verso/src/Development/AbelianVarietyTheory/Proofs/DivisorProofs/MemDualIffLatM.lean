import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors
open NumberField Complex GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.RealMult GlobalTheory.LatJet

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

def pairAct (a b c d : F) (p : F × F) : F × F := (p.2 * b + p.1 * d, p.2 * a + p.1 * c)

def pairInv (a b c d : F) (q : F × F) : F × F := (q.1 * a - q.2 * b, q.2 * d - q.1 * c)

/- English proof (translation)
Use `ext`. Simplify using `only [pairInv, pairAct]`. Take the linear combination `p.1 * h`. Simplify using `only [pairInv, pairAct]`. Take the linear combination `p.2 * h`.
-/
theorem pairInv_act (a b c d : F) (h : a * d - b * c = 1) (p : F × F) :
    pairInv a b c d (pairAct a b c d p) = p := by
  ext
  · simp only [pairInv, pairAct]; linear_combination p.1 * h
  · simp only [pairInv, pairAct]; linear_combination p.2 * h

/- English proof (translation)
Use `ext`. Simplify using `only [pairInv, pairAct]`. Take the linear combination `q.1 * h`. Simplify using `only [pairInv, pairAct]`. Take the linear combination `q.2 * h`.
-/
theorem pairAct_inv (a b c d : F) (h : a * d - b * c = 1) (q : F × F) :
    pairAct a b c d (pairInv a b c d q) = q := by
  ext
  · simp only [pairInv, pairAct]; linear_combination q.1 * h
  · simp only [pairInv, pairAct]; linear_combination q.2 * h

/- English proof (translation)
Establish `h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ x * I ≤ I`. Rewrite using `[FractionalIdeal.mul_le]`. Introduce `i hi j hj`. Take `⟨r, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hi`. Rewrite using `[smul_mul_assoc]`.

Conclude with `(I : Submodule (𝓞 F) F).smul_mem r (h j hj)`. Establish `h2` using `mul_le_mul_left h1 I⁻¹`. Simplify using `only [mul_assoc, mul_inv_cancel₀ hI, mul_one] at h2`. Establish `h3 : x ∈ (1 : FractionalIdeal (𝓞 F)⁰ F)` using `h2 (FractionalIdeal.mem_spanSingleton_self _ x)`. Conclude with `(FractionalIdeal.mem_one_iff _).1 h3`.
-/
theorem int_of_mul_mem (I : FractionalIdeal (𝓞 F)⁰ F) (hI : I ≠ 0) (x : F) (h : ∀ y ∈ I, x * y ∈ I) :
    ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = x := by
  have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ x * I ≤ I := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact (I : Submodule (𝓞 F) F).smul_mem r (h j hj)
  have h2 := mul_le_mul_left h1 I⁻¹
  simp only [mul_assoc, mul_inv_cancel₀ hI, mul_one] at h2
  have h3 : x ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := h2 (FractionalIdeal.mem_spanSingleton_self _ x)
  exact (FractionalIdeal.mem_one_iff _).1 h3

/- English proof (translation)
Take `⟨r, rfl⟩` from `hx`. Rewrite using `[← Algebra.smul_def]`. Conclude with `(I : Submodule (𝓞 F) F).smul_mem r hy`.
-/
theorem mul_mem_of_int (I : FractionalIdeal (𝓞 F)⁰ F) {x y : F} (hx : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = x)
    (hy : y ∈ I) : x * y ∈ I := by
  obtain ⟨r, rfl⟩ := hx
  rw [← Algebra.smul_def]
  exact (I : Submodule (𝓞 F) F).smul_mem r hy

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[latM_eq_dual]`. Both sides reduce to the same expression.
-/
theorem mem_dual_iff_latM (𝔞 : Frac F) (x : F) : x ∈ dualLat 𝔞 ↔ x ∈ latM 𝔞 := by
  rw [latM_eq_dual]; rfl

/- English proof (translation)
Rewrite using `[dualLat, ← latM_eq_dual, latM]`. Use `mul_ne_zero (inv_ne_zero ?_) (Units.ne_zero _)` and prove the remaining obligations. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]`. Conclude with `inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)`.
-/
theorem dualLat_ne_zero (𝔞 : Frac F) : dualLat 𝔞 ≠ 0 := by
  rw [dualLat, ← latM_eq_dual, latM]
  refine mul_ne_zero (inv_ne_zero ?_) (Units.ne_zero _)
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

variable {𝔞 𝔟 : Frac F} {a b c d : F}

/- English proof (translation)
The claim follows from `int_of_mul_mem (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (Units.ne_zero _) a fun y hy ↦ by have := (h.2 y hy 0 (dualLat 𝔞 : Submodule (𝓞 F) F).zero_mem).1 simpa [mul_comm] using this`.
-/
theorem a_int (h : InModularGroup 𝔞 𝔟 a b c d) : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = a :=
  int_of_mul_mem (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (Units.ne_zero _) a fun y hy ↦ by
    have := (h.2 y hy 0 (dualLat 𝔞 : Submodule (𝓞 F) F).zero_mem).1
    simpa [mul_comm] using this

/- English proof (translation)
The claim follows from `int_of_mul_mem (dualLat 𝔞) (dualLat_ne_zero 𝔞) d fun y hy ↦ by have := (h.2 0 (zero_mem _) y hy).2 simpa [mul_comm] using this`.
-/
theorem d_int (h : InModularGroup 𝔞 𝔟 a b c d) : ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = d :=
  int_of_mul_mem (dualLat 𝔞) (dualLat_ne_zero 𝔞) d fun y hy ↦ by
    have := (h.2 0 (zero_mem _) y hy).2
    simpa [mul_comm] using this

def latEquiv (h : InModularGroup 𝔞 𝔟 a b c d) : LatPair 𝔞 𝔟 ≃ LatPair 𝔞 𝔟 where
  toFun p := ⟨pairAct a b c d p.1, by
    obtain ⟨h1, h2⟩ := h.2 p.1.2 p.2.2.1 p.1.1 ((mem_dual_iff_latM 𝔞 _).2 p.2.1)
    refine ⟨(mem_dual_iff_latM 𝔞 _).1 h2, h1, fun h0 ↦ p.2.2.2 ?_⟩
    rw [← pairInv_act a b c d h.1 p.1, h0]; simp [pairInv]⟩
  invFun q := ⟨pairInv a b c d q.1, by
    have hm := (mem_dual_iff_latM 𝔞 _).2 q.2.1
    have hb := q.2.2.1
    refine ⟨(mem_dual_iff_latM 𝔞 _).1 ?_, ?_, fun h0 ↦ q.2.2.2 ?_⟩
    · refine (dualLat 𝔞 : Submodule (𝓞 F) F).sub_mem (mul_comm a q.1.1 ▸ mul_mem_of_int _ (a_int h) hm) ?_
      simpa using (h.2 q.1.2 hb 0 (dualLat 𝔞 : Submodule (𝓞 F) F).zero_mem).2
    · refine (𝔟 : Submodule (𝓞 F) F).sub_mem (mul_comm d q.1.2 ▸ mul_mem_of_int (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (d_int h) hb) ?_
      simpa using (h.2 0 (zero_mem _) q.1.1 hm).1
    · rw [← pairAct_inv a b c d h.1 q.1, h0]; simp [pairAct]⟩
  left_inv p := Subtype.ext (pairInv_act a b c d h.1 p.1)
  right_inv q := Subtype.ext (pairAct_inv a b c d h.1 q.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem latEquiv_apply (h : InModularGroup 𝔞 𝔟 a b c d) (p : LatPair 𝔞 𝔟) :
    (latEquiv h p).1 = pairAct a b c d p.1 := rfl

def clsEquiv (h : InModularGroup 𝔞 𝔟 a b c d) : Quotient (latRel 𝔞 𝔟) ≃ Quotient (latRel 𝔞 𝔟) :=
  Quotient.congr (latEquiv h) fun p q ↦ by
    show (∃ ε : (𝓞 F)ˣ, _) ↔ (∃ ε : (𝓞 F)ˣ, _)
    simp only [latEquiv_apply, pairAct]
    constructor
    · rintro ⟨ε, h1, h2⟩
      exact ⟨ε, by rw [h1, h2]; ring, by rw [h1, h2]; ring⟩
    · rintro ⟨ε, h1, h2⟩
      have hd := h.1
      exact ⟨ε, by linear_combination a * h1 - b * h2 + (((ε : 𝓞 F) : F) * p.1.1 - q.1.1) * hd,
        by linear_combination d * h2 - c * h1 + (((ε : 𝓞 F) : F) * p.1.2 - q.1.2) * hd⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem clsEquiv_mk (h : InModularGroup 𝔞 𝔟 a b c d) (p : LatPair 𝔞 𝔟) :
    clsEquiv h (Quotient.mk _ p) = Quotient.mk _ (latEquiv h p) := rfl

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

variable {F : Type} [Field F] [NumberField F]

def moeb (a b c d : F) (z : Emb F → ℂ) : Emb F → ℂ :=
  fun τ ↦ ((τ a : ℂ) * z τ + (τ b : ℂ)) / ((τ c : ℂ) * z τ + (τ d : ℂ))

def den (c d : F) (z : Emb F → ℂ) (τ : Emb F) : ℂ := (τ c : ℂ) * z τ + (τ d : ℂ)

/- English proof (translation)
Rewrite using `[← map_mul, ← map_mul, ← map_sub, h, map_one]`.
-/
theorem det_emb {a b c d : F} (h : a * d - b * c = 1) (τ : Emb F) : τ a * τ d - τ b * τ c = 1 := by
  rw [← map_mul, ← map_mul, ← map_sub, h, map_one]

/- English proof (translation)
Introduce `h0`. Establish `him : τ c * (z τ).im = 0`. Use `congrArg Complex.im h0` as an intermediate fact. Simplify `this` using `[den]`. Establish `hc : τ c = 0`.

Break down `mul_eq_zero.1 him with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 (hz τ).ne'`. Establish `hc' : c = 0` using `(map_eq_zero τ).1 hc`. Establish `hd : (τ d : ℂ) = 0` using `by simpa [den, hc] using h0`.

Establish `hd' : d = 0` using `(map_eq_zero τ).1 (by exact_mod_cast hd)`. Rewrite `h` using `[hc', hd']`. Simplify using `at h`.
-/
theorem den_ne {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) (τ : Emb F) :
    den c d z τ ≠ 0 := by
  intro h0
  have him : τ c * (z τ).im = 0 := by
    have := congrArg Complex.im h0
    simpa [den] using this
  have hc : τ c = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact h1
    · exact absurd h1 (hz τ).ne'
  have hc' : c = 0 := (map_eq_zero τ).1 hc
  have hd : (τ d : ℂ) = 0 := by simpa [den, hc] using h0
  have hd' : d = 0 := (map_eq_zero τ).1 (by exact_mod_cast hd)
  rw [hc', hd'] at h
  simp at h

/- English proof (translation)
Introduce `τ`. Establish `hn` using `Complex.normSq_pos.2 (den_ne h hz τ)`. Establish `hdet` using `det_emb h τ`. Simplify using `only [den] at hn`. Simplify using `only [moeb, Complex.div_im]`.

Rewrite using `[← sub_div]`. Use `div_pos ?_ hn` and prove the remaining obligations. Establish `: ((τ a : ℂ) * z τ + (τ b : ℂ)).im * ((τ c : ℂ) * z τ + (τ d : ℂ)).re - ((τ a : ℂ) * z τ + (τ b : ℂ)).re * ((τ c : ℂ) * z τ + (τ d : ℂ)).im = (z τ).im * (τ a * τ d - τ b * τ c)`. Simplify using `only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, hdet, mul_one]`. Conclude with `hz τ`.
-/
theorem moeb_mem {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) :
    moeb a b c d z ∈ halfSpace F := by
  intro τ
  have hn := Complex.normSq_pos.2 (den_ne h hz τ)
  have hdet := det_emb h τ
  simp only [den] at hn
  simp only [moeb, Complex.div_im]
  rw [← sub_div]
  refine div_pos ?_ hn
  have : ((τ a : ℂ) * z τ + (τ b : ℂ)).im * ((τ c : ℂ) * z τ + (τ d : ℂ)).re -
      ((τ a : ℂ) * z τ + (τ b : ℂ)).re * ((τ c : ℂ) * z τ + (τ d : ℂ)).im =
      (z τ).im * (τ a * τ d - τ b * τ c) := by
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this, hdet, mul_one]
  exact hz τ

/- English proof (translation)
Establish `hne` using `den_ne h hz τ`. Simplify using `only [den] at hne`. Establish `hne' : z τ * (τ c : ℂ) + (τ d : ℂ) ≠ 0` using `by rw [mul_comm]; exact hne`. Simplify using `only [latPt, moeb, pairAct, den, map_add, map_mul, Complex.ofReal_add, Complex.ofReal_mul]`. Rewrite using `[eq_div_iff hne]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latPt_moeb {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) (p : F × F)
    (τ : Emb F) : latPt (moeb a b c d z) p τ = latPt z (pairAct a b c d p) τ / den c d z τ := by
  have hne := den_ne h hz τ
  simp only [den] at hne
  have hne' : z τ * (τ c : ℂ) + (τ d : ℂ) ≠ 0 := by rw [mul_comm]; exact hne
  simp only [latPt, moeb, pairAct, den, map_add, map_mul, Complex.ofReal_add, Complex.ofReal_mul]
  rw [eq_div_iff hne]
  field_simp
  ring

/- English proof (translation)
Establish `hprod : ∏ τ, latPt (moeb a b c d z) p τ = (∏ τ, latPt z (pairAct a b c d p) τ) / ∏ τ, den c d z τ`. Repeatedly rewrite using `[latPt_moeb h hz p]`. Rewrite using `[Finset.prod_div_distrib]`. Unfold `eisTerm`. Rewrite using `[hprod]`.

Generalize the expression as in `∏ τ, latPt z (pairAct a b c d p) τ = P`. Generalize the expression as in `∏ τ, den c d z τ = Q`. Establish `harg : ((‖Q‖ : ℝ) : ℂ).arg ≠ Real.pi`. Rewrite using `[Complex.arg_ofReal_of_nonneg (norm_nonneg _)]`. Conclude with `Real.pi_pos.ne`.

Establish `hQ : (((‖Q‖⁻¹ : ℝ)) : ℂ) ^ (-2 * σ) = ((‖Q‖ : ℝ) : ℂ) ^ (2 * σ)`. Rewrite using `[Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, neg_mul, neg_neg]`. Establish `hN : ((‖P / Q‖ : ℝ) : ℂ) ^ (-2 * σ) = ((‖P‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖Q‖ : ℝ) : ℂ) ^ (2 * σ)`. Rewrite using `[norm_div, div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (inv_nonneg.2 (norm_nonneg _)), hQ]`. Rewrite using `[hN, inv_div, div_eq_mul_inv, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eisTerm_moeb {a b c d : F} (h : a * d - b * c = 1) {z : Emb F → ℂ} (hz : z ∈ halfSpace F) (k : ℕ)
    (σ : ℂ) (p : F × F) :
    eisTerm k σ (moeb a b c d z) p =
      (∏ τ, den c d z τ) ^ k * ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ^ (2 * σ) * eisTerm k σ z (pairAct a b c d p) := by
  have hprod : ∏ τ, latPt (moeb a b c d z) p τ = (∏ τ, latPt z (pairAct a b c d p) τ) / ∏ τ, den c d z τ := by
    simp_rw [latPt_moeb h hz p]
    rw [Finset.prod_div_distrib]
  unfold eisTerm
  rw [hprod]
  generalize ∏ τ, latPt z (pairAct a b c d p) τ = P
  generalize ∏ τ, den c d z τ = Q
  have harg : ((‖Q‖ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (norm_nonneg _)]; exact Real.pi_pos.ne
  have hQ : (((‖Q‖⁻¹ : ℝ)) : ℂ) ^ (-2 * σ) = ((‖Q‖ : ℝ) : ℂ) ^ (2 * σ) := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, neg_mul, neg_neg]
  have hN : ((‖P / Q‖ : ℝ) : ℂ) ^ (-2 * σ) = ((‖P‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖Q‖ : ℝ) : ℂ) ^ (2 * σ) := by
    rw [norm_div, div_eq_mul_inv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (inv_nonneg.2 (norm_nonneg _)), hQ]
  rw [hN, inv_div, div_eq_mul_inv, mul_pow]
  ring

/- English proof (translation)
Proceed by induction on `x using Quotient.inductionOn with`. Consider the case `h p`. Rewrite using `[clsEquiv_mk, eisClass_mk _ _ hk, eisClass_mk _ _ hk, latEquiv_apply]`. Conclude with `eisTerm_moeb h.1 hz k σ p.1`.
-/
theorem eisClass_moeb [IsTotallyReal F] {𝔞 𝔟 : Frac F} {a b c d : F} (h : InModularGroup 𝔞 𝔟 a b c d)
    {z : Emb F → ℂ} (hz : z ∈ halfSpace F) {k : ℕ} (hk : Even k) (σ : ℂ) (x : Quotient (latRel 𝔞 𝔟)) :
    eisClass 𝔞 𝔟 k σ (moeb a b c d z) x =
      (∏ τ, den c d z τ) ^ k * ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ^ (2 * σ) * eisClass 𝔞 𝔟 k σ z (clsEquiv h x) := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [clsEquiv_mk, eisClass_mk _ _ hk, eisClass_mk _ _ hk, latEquiv_apply]
    exact eisTerm_moeb h.1 hz k σ p.1

end GlobalTheory.EisModular

namespace GlobalTheory.EisModular

/- English proof (translation)
Introduce `F _ _ _ 𝔞 𝔟 s hs G hG hdiff`. Use `⟨hdiff, ?_⟩` and prove the remaining obligations. Introduce `a b c d hγ z hz`. Establish `hw` using `moeb_mem hγ.1 hz`. Establish `hQ : (∏ τ, den c d z τ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ ↦ den_ne hγ.1 hz τ`.

Express the relevant statement in the definitionally equal form `G (moeb a b c d z) = (∏ τ, den c d z τ) ^ (2 * s) * G z`. Establish `hk : Even (2 * s)` using `even_two_mul s`. Distinguish the cases in `h2 : 2 * s = 2`. Take `⟨H, hH, rfl⟩` from `hG.2 h2`. Rewrite using `[h2]`.

Use `set K : ℂ → ℂ := fun σ ↦ (∏ τ, den c d z τ) ^ 2 * ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ^ (2 * σ) * H σ z with hK`. Establish `heq : ∀ σ : ℂ, 0 < σ.re → H σ (moeb a b c d z) = K σ`. Introduce `σ hσ`. Rewrite using `[(hH.1 σ hσ _ hw).2, hK]`. Simplify using `only`.

Rewrite using `[(hH.1 σ hσ z hz).2, eisSum, eisSum]`. Repeatedly rewrite using `[eisClass_moeb hγ hz even_two σ]`. Rewrite using `[tsum_mul_left, Equiv.tsum_eq]`. Establish `hU : IsOpen halfPlane` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hf : AnalyticOnNhd ℂ (fun σ ↦ H σ (moeb a b c d z)) halfPlane` using `(hH.2.2 [] _ hw).analyticOnNhd hU`.

Establish `hnQ : ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ≠ 0`. Rewrite using `[Complex.ofReal_ne_zero]`. Conclude with `norm_ne_zero_iff.2 hQ`. Establish `hg : AnalyticOnNhd ℂ K halfPlane`. Use `DifferentiableOn.analyticOnNhd ?_ hU` and prove the remaining obligations.

Use `DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_const _) ?_) (hH.2.2 [] z hz)` and prove the remaining obligations. Conclude with `(Differentiable.const_cpow (differentiable_id.const_mul 2) (Or.inl hnQ)).differentiableOn`. Establish `hpc : IsPreconnected halfPlane` using `(convex_halfSpace_re_gt _).isPreconnected`. Establish `h1 : (1 : ℂ) ∈ halfPlane` using `by show -1 / 2 < (1 : ℂ).re; norm_num`. Establish `hev : (fun σ ↦ H σ (moeb a b c d z)) =ᶠ[nhds 1] K` using `by filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with σ hσ using heq σ hσ`.

Use `hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h1 hev (show (0 : ℂ) ∈ halfPlane by show -1 / 2 < (0 : ℂ).re; norm_num)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Simplify using `[hK]`. Establish `h1` using `hG.1 h2 _ hw`. Establish `h0` using `hG.1 h2 z hz`.

Establish `h3 : HasSum (fun x ↦ (∏ τ, den c d z τ) ^ (2 * s) * eisClass 𝔞 𝔟 (2 * s) 0 z (clsEquiv hγ x)) ((∏ τ, den c d z τ) ^ (2 * s) * G z)` using `(Equiv.hasSum_iff (clsEquiv hγ) (f := fun x ↦ (∏ τ, den c d z τ) ^ (2 * s) * eisClass 𝔞 𝔟 (2 * s) 0 z x)).2 (h0.mul_left _)`. Use `h1.unique ?_` and prove the remaining obligations. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Rewrite using `[eisClass_moeb hγ hz hk]`.

Simplify using the standard rewrite rules.
-/
theorem eisMod : EisMod := by
  intro F _ _ _ 𝔞 𝔟 s hs G hG hdiff
  refine ⟨hdiff, ?_⟩
  intro a b c d hγ z hz
  have hw := moeb_mem hγ.1 hz
  have hQ : (∏ τ, den c d z τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ ↦ den_ne hγ.1 hz τ
  change G (moeb a b c d z) = (∏ τ, den c d z τ) ^ (2 * s) * G z
  have hk : Even (2 * s) := even_two_mul s
  by_cases h2 : 2 * s = 2
  · obtain ⟨H, hH, rfl⟩ := hG.2 h2
    rw [h2]
    set K : ℂ → ℂ := fun σ ↦
      (∏ τ, den c d z τ) ^ 2 * ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ^ (2 * σ) * H σ z with hK
    have heq : ∀ σ : ℂ, 0 < σ.re → H σ (moeb a b c d z) = K σ := by
      intro σ hσ
      rw [(hH.1 σ hσ _ hw).2, hK]
      simp only
      rw [(hH.1 σ hσ z hz).2, eisSum, eisSum]
      simp_rw [eisClass_moeb hγ hz even_two σ]
      rw [tsum_mul_left, Equiv.tsum_eq]
    have hU : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
    have hf : AnalyticOnNhd ℂ (fun σ ↦ H σ (moeb a b c d z)) halfPlane :=
      (hH.2.2 [] _ hw).analyticOnNhd hU
    have hnQ : ((‖∏ τ, den c d z τ‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.2 hQ
    have hg : AnalyticOnNhd ℂ K halfPlane := by
      refine DifferentiableOn.analyticOnNhd ?_ hU
      refine DifferentiableOn.mul (DifferentiableOn.mul (differentiableOn_const _) ?_) (hH.2.2 [] z hz)
      exact (Differentiable.const_cpow (differentiable_id.const_mul 2) (Or.inl hnQ)).differentiableOn
    have hpc : IsPreconnected halfPlane := (convex_halfSpace_re_gt _).isPreconnected
    have h1 : (1 : ℂ) ∈ halfPlane := by show -1 / 2 < (1 : ℂ).re; norm_num
    have hev : (fun σ ↦ H σ (moeb a b c d z)) =ᶠ[nhds 1] K := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by norm_num)] with σ hσ using heq σ hσ
    have := hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h1 hev
      (show (0 : ℂ) ∈ halfPlane by show -1 / 2 < (0 : ℂ).re; norm_num)
    refine this.trans ?_
    simp [hK]
  · have h1 := hG.1 h2 _ hw
    have h0 := hG.1 h2 z hz
    have h3 : HasSum (fun x ↦ (∏ τ, den c d z τ) ^ (2 * s) * eisClass 𝔞 𝔟 (2 * s) 0 z (clsEquiv hγ x))
        ((∏ τ, den c d z τ) ^ (2 * s) * G z) :=
      (Equiv.hasSum_iff (clsEquiv hγ) (f := fun x ↦ (∏ τ, den c d z τ) ^ (2 * s) * eisClass 𝔞 𝔟 (2 * s) 0 z x)).2
        (h0.mul_left _)
    refine h1.unique ?_
    convert h3 using 1
    funext x
    rw [eisClass_moeb hγ hz hk]
    simp

end GlobalTheory.EisModular
