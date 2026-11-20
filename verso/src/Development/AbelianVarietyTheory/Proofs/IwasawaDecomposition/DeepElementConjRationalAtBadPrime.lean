import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumberFieldGLDenseInCompletionGLTwoSidedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesCongruentOneOfSameBadPlaceComponents
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.DeepElt

open WithZero

section Val

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ}

def Cg (N : ℕ) (X : GL (Fin n) K) : Prop :=
  ∀ r s, Valued.v (((X : Matrix (Fin n) (Fin n) K) - 1) r s) ≤ exp (-(N : ℤ))

/- English proof (translation)
Introduce `r s`. Use `NearCong.mul_cong (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) N X.1 Y.1 hX hY r s` as an intermediate fact. Simplify `this` using `only [Units.val_mul]`.
-/
theorem cg_mul {N : ℕ} {X Y : GL (Fin n) K} (hX : Cg N X) (hY : Cg N Y) : Cg N (X * Y) := by
  intro r s
  have := NearCong.mul_cong (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) N X.1 Y.1 hX hY r s
  simpa only [Units.val_mul] using this

/- English proof (translation)
Introduce `r s` and use `(hX r s).trans (by rw [exp_le_exp]; omega)`.
-/
theorem cg_mono {M N : ℕ} (h : M ≤ N) {X : GL (Fin n) K} (hX : Cg N X) : Cg M X :=
  fun r s => (hX r s).trans (by rw [exp_le_exp]; omega)

/- English proof (translation)
Rewrite using `[map_mul, map_inv₀, hπ]`. Establish `h0 : (exp (-(N : ℤ)) : WithZero (Multiplicative ℤ)) ≠ 0` using `exp_ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, mul_inv_cancel₀ h0, one_mul]`. Use `_ ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' le_rfl h`. Use `_ = _ := mul_one _`. Introduce `h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_le_iff (π m : K) {N : ℕ} (hπ : Valued.v π = exp (-(N : ℤ))) :
    Valued.v (π⁻¹ * m) ≤ 1 ↔ Valued.v m ≤ exp (-(N : ℤ)) := by
  rw [map_mul, map_inv₀, hπ]
  have h0 : (exp (-(N : ℤ)) : WithZero (Multiplicative ℤ)) ≠ 0 := exp_ne_zero
  constructor
  · intro h
    calc Valued.v m = exp (-(N : ℤ)) * ((exp (-(N : ℤ)))⁻¹ * Valued.v m) := by
          rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]
      _ ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' le_rfl h
      _ = _ := mul_one _
  · intro h
    calc (exp (-(N : ℤ)))⁻¹ * Valued.v m ≤ (exp (-(N : ℤ)))⁻¹ * exp (-(N : ℤ)) := mul_le_mul' le_rfl h
      _ = 1 := inv_mul_cancel₀ h0

/- English proof (translation)
Establish `hπ0 : π ≠ 0`. Introduce `h`. Rewrite `hπ` using `[h, map_zero]`. Conclude with `exp_ne_zero hπ.symm`. Establish `hπ1 : Valued.v π < 1`.

Rewrite using `[hπ, ← exp_zero, exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : ∀ i j, Valued.v (π⁻¹ * ((X : Matrix (Fin n) (Fin n) K) - 1) i j) ≤ 1` using `fun i j => (val_le_iff π _ hπ).2 (hX i j)`. Establish `h2 : ∀ i j, Valued.v (π⁻¹ * (((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) i j) ≤ 1` using `fun i j => by simp`. Establish `h3` using `GlobalTheory.FrameAgree.inv_mul_cong π hπ0 hπ1 X 1 h1 h2`.

Simplify using `only [mul_one] at h3`. Introduce `r s`. Conclude with `(val_le_iff π _ hπ).1 (h3 r s)`.
-/
theorem cg_inv {N : ℕ} (hN : 1 ≤ N) (π : K) (hπ : Valued.v π = exp (-(N : ℤ))) {X : GL (Fin n) K} (hX : Cg N X) :
    Cg N X⁻¹ := by
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hπ1 : Valued.v π < 1 := by
    rw [hπ, ← exp_zero, exp_lt_exp]; omega
  have h1 : ∀ i j, Valued.v (π⁻¹ * ((X : Matrix (Fin n) (Fin n) K) - 1) i j) ≤ 1 :=
    fun i j => (val_le_iff π _ hπ).2 (hX i j)
  have h2 : ∀ i j, Valued.v (π⁻¹ * (((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) i j) ≤ 1 :=
    fun i j => by simp
  have h3 := GlobalTheory.FrameAgree.inv_mul_cong π hπ0 hπ1 X 1 h1 h2
  simp only [mul_one] at h3
  intro r s
  exact (val_le_iff π _ hπ).1 (h3 r s)

/- English proof (translation)
Introduce `r s`. Establish `hinv : ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (G : Matrix (Fin n) (Fin n) K) = 1` using `Units.inv_mul G`. Establish `e : ((G⁻¹ * X * G : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 = ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1) * (G : Matrix (Fin n) (Fin n) K)`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv, Units.val_mul, Units.val_mul]`. Establish `hin : ∀ m, Valued.v ((((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1)) r m) ≤ exp (-(N : ℤ))` using `fun m => by`.

Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, Matrix.mul_apply]`.

Use `Valuation.map_sum_le _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cg_conj {N : ℕ} (G : GL (Fin n) K) (hG : ∀ r s, Valued.v ((G : Matrix (Fin n) (Fin n) K) r s) ≤ 1)
    (hGi : ∀ r s, Valued.v (((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) r s) ≤ 1)
    {X : GL (Fin n) K} (hX : Cg N X) : Cg N (G⁻¹ * X * G) := by
  intro r s
  have hinv : ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (G : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul G
  have e : ((G⁻¹ * X * G : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      ((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1) * (G : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv, Units.val_mul, Units.val_mul]
  have hin : ∀ m, Valued.v ((((G⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1)) r m) ≤
      exp (-(N : ℤ)) := fun m => by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * exp (-(N : ℤ)) := mul_le_mul' (hGi r l) (hX l m)
      _ = _ := one_mul _
  rw [e, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun m _ => ?_
  rw [map_mul]
  calc _ ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' (hin m) (hG m s)
    _ = _ := mul_one _

/- English proof (translation)
Establish `hb : ∀ w : WithZero (Multiplicative ℤ), ∃ c : ℕ, w ≤ exp (c : ℤ)`. Introduce `w`. Distinguish the cases in `hw : w = 0`. Conclude with `⟨0, by rw [hw]; exact zero_le'⟩`. Use `⟨(WithZero.log w).toNat, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `choose c hc using hb`. Use `set f : Fin n × Fin n → ℕ := fun p => c (Valued.v ((k : Matrix (Fin n) (Fin n) K) p.1 p.2)) + c (Valued.v (((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1 p.2)) with hf`. Use `set C : ℕ := Finset.univ.sup f with hC`. Establish `hle : ∀ r s, f (r, s) ≤ C` using `fun r s => Finset.le_sup (f := f) (Finset.mem_univ (r, s))`.

Establish `hk : ∀ r s, Valued.v ((k : Matrix (Fin n) (Fin n) K) r s) ≤ exp (C : ℤ)` using `fun r s => by`. Use `(hc _).trans (exp_le_exp.2 ?_)` and prove the remaining obligations. Use `hle r s` as an intermediate fact. Simplify using `only [hf] at this`. Use linear arithmetic over natural numbers and integers.

Establish `hki : ∀ r s, Valued.v (((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) r s) ≤ exp (C : ℤ)` using `fun r s => by`. Use `(hc _).trans (exp_le_exp.2 ?_)` and prove the remaining obligations. Use `hle r s` as an intermediate fact. Simplify using `only [hf] at this`. Use linear arithmetic over natural numbers and integers.

Use `⟨N + 2 * C, fun X hX r s => ?_⟩` and prove the remaining obligations. Establish `hinv : (k : Matrix (Fin n) (Fin n) K) * ((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1` using `Units.mul_inv k`. Establish `e : ((k * X * k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 = (k : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1) * ((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv, Units.val_mul, Units.val_mul]`. Establish `hin : ∀ m, Valued.v (((k : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1)) r m) ≤ exp (C : ℤ) * exp (-((N + 2 * C : ℕ) : ℤ))` using `fun m => by`.

Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hk r l) (hX l m)`. Rewrite using `[e, Matrix.mul_apply]`.

Use `Valuation.map_sum_le _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← exp_add, ← exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cg_conj_bound (k : GL (Fin n) K) (N : ℕ) : ∃ N' : ℕ, ∀ X : GL (Fin n) K, Cg N' X → Cg N (k * X * k⁻¹) := by
  have hb : ∀ w : WithZero (Multiplicative ℤ), ∃ c : ℕ, w ≤ exp (c : ℤ) := by
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by rw [hw]; exact zero_le'⟩
    · refine ⟨(WithZero.log w).toNat, ?_⟩
      calc w = exp (WithZero.log w) := (WithZero.exp_log hw).symm
        _ ≤ exp ((WithZero.log w).toNat : ℤ) := exp_le_exp.2 (Int.self_le_toNat _)
  choose c hc using hb
  set f : Fin n × Fin n → ℕ := fun p => c (Valued.v ((k : Matrix (Fin n) (Fin n) K) p.1 p.2)) +
    c (Valued.v (((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1 p.2)) with hf
  set C : ℕ := Finset.univ.sup f with hC
  have hle : ∀ r s, f (r, s) ≤ C := fun r s => Finset.le_sup (f := f) (Finset.mem_univ (r, s))
  have hk : ∀ r s, Valued.v ((k : Matrix (Fin n) (Fin n) K) r s) ≤ exp (C : ℤ) := fun r s => by
    refine (hc _).trans (exp_le_exp.2 ?_)
    have := hle r s
    simp only [hf] at this
    omega
  have hki : ∀ r s, Valued.v (((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) r s) ≤ exp (C : ℤ) := fun r s => by
    refine (hc _).trans (exp_le_exp.2 ?_)
    have := hle r s
    simp only [hf] at this
    omega
  refine ⟨N + 2 * C, fun X hX r s => ?_⟩
  have hinv : (k : Matrix (Fin n) (Fin n) K) * ((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := Units.mul_inv k
  have e : ((k * X * k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      (k : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1) * ((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv, Units.val_mul, Units.val_mul]
  have hin : ∀ m, Valued.v (((k : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1)) r m) ≤
      exp (C : ℤ) * exp (-((N + 2 * C : ℕ) : ℤ)) := fun m => by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hk r l) (hX l m)
  rw [e, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun m _ => ?_
  rw [map_mul]
  calc _ ≤ exp (C : ℤ) * exp (-((N + 2 * C : ℕ) : ℤ)) * exp (C : ℤ) := mul_le_mul' (hin m) (hki m s)
    _ = exp (-(N : ℤ)) := by
      rw [← exp_add, ← exp_add]
      congr 1
      push_cast
      ring

end Val

end GlobalTheory.Mem.Col2.AdT.DeepElt

namespace GlobalTheory.Mem.Col2.AdT.DeepElt

open WithZero

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Rewrite using `[hG, LinearMap.toMatrix'_apply]`. Establish `hs : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P`. Rewrite using `[GlobalTheory.Mem.ColAd.mem_stdAt_val]`. Introduce `l`. Rewrite using `[Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hm` using `(hh (Pi.single s 1)).2 hs`. Rewrite `hm` using `[GlobalTheory.Mem.ColAd.mem_stdAt_val]`. Conclude with `hm r`.
-/
theorem val_entry_le (P : HeightOneSpectrum (𝓞 E)) (G : (Sp E n ≃ₗ[E] Sp E n) →* GL (Fin n) E)
    (hG : ∀ h r s, (G h : Matrix (Fin n) (Fin n) E) r s = LinearMap.toMatrix' h.toLinearMap r s)
    (h : Sp E n ≃ₗ[E] Sp E n) (hh : h ∈ Formalism.L2.Col.GLint E n P) (r s : Fin n) :
    Valued.v (algebraMap E (P.adicCompletion E) ((G h : Matrix (Fin n) (Fin n) E) r s)) ≤ 1 := by
  rw [hG, LinearMap.toMatrix'_apply]
  have hs : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    rw [GlobalTheory.Mem.ColAd.mem_stdAt_val]
    intro l
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hm := (hh (Pi.single s 1)).2 hs
  rw [GlobalTheory.Mem.ColAd.mem_stdAt_val] at hm
  exact hm r

/- English proof (translation)
Use `set loc : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) := GlobalTheory.FrameAgree.locM P with hloc`. Use `set ra : GL (Fin n) E →* GL (Fin n) (P.adicCompletion E) := bc (algebraMap E (P.adicCompletion E)) with hra`. Establish `hlr : ∀ M, loc (GlobalTheory.TwU.ratA F M) = ra M` using `fun M => Units.ext (Matrix.ext fun r s => AdTieNear.adAt_ratA P M r s)`. Establish `hC : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔ Cg N (loc z)` using `fun N z => hiff N z`. Establish `hπ : Valued.v (((qOf P : ℕ) : P.adicCompletion E) ^ D) = exp (-(D : ℤ))`.

Rewrite using `[map_pow, hq, ← WithZero.exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `hGP : ∀ r s, Valued.v (((ra (G g)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ 1` using `fun r s => val_entry_le P G hG g hg r s`. Establish `hGPi : ∀ r s, Valued.v ((((ra (G g))⁻¹ : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ 1`.

Introduce `r s`. Rewrite using `[← map_inv, ← map_inv]`. Conclude with `val_entry_le P G hG g⁻¹ (inv_mem hg) r s`. Establish `c1 : Cg D ((loc kk)⁻¹ * ra f)`. Use `(hC D _).1 h1` as an intermediate fact.

Rewrite `this` using `[map_mul, map_inv, hlr]`. Then use the resulting hypothesis. Establish `c2 : Cg D ((ra f)⁻¹ * loc kk)`. Use `(hC D _).1 h2` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv, hlr]`. Then use the resulting hypothesis. Establish `c3 : Cg D (((ra f)⁻¹ * loc κ * ra f)⁻¹ * ra (G g))`.

Use `(hC D _).1 h3` as an intermediate fact. Simplify `this` using `only [map_mul, map_inv, hlr]`. Use `set AP : GL (Fin n) (P.adicCompletion E) := (loc kk)⁻¹ * loc κ * loc kk with hAP`. Establish `s1 : Cg D (AP⁻¹ * ra (G g))`. Establish `e : AP⁻¹ * ra (G g) = ((loc kk)⁻¹ * ra f) * (((ra f)⁻¹ * loc κ * ra f)⁻¹ * ra (G g)) * ((ra (G g))⁻¹ * ((ra f)⁻¹ * loc kk) * ra (G g))`.

Rewrite using `[hAP]`. Use `group`. Rewrite using `[e]`. Conclude with `cg_mul (cg_mul c1 c3) (cg_conj _ hGP hGPi c2)`. Establish `s2 : Cg D ((ra (G g))⁻¹ * AP)`.

Establish `e : (ra (G g))⁻¹ * AP = ((ra (G g))⁻¹ * ((loc kk)⁻¹ * ra f) * ra (G g)) * (((ra f)⁻¹ * loc κ * ra f)⁻¹ * ra (G g))⁻¹ * ((ra f)⁻¹ * loc kk)`. Rewrite using `[hAP]`. Use `group`. Rewrite using `[e]`. Conclude with `cg_mul (cg_mul (cg_conj _ hGP hGPi c1) (cg_inv hD _ hπ c3)) c2`.

Take `⟨N0, hN0⟩` from `cg_conj_bound (loc kk) N`. Take `⟨γ, hγ⟩` from `GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided E P n (max D N0) AP`. Establish `d1 : Cg (max D N0) (AP⁻¹ * ra γ)` using `fun r s => (hγ r s).1`. Establish `d2 : Cg (max D N0) ((ra γ)⁻¹ * AP)` using `fun r s => (hγ r s).2`. Use `set g' : Sp E n ≃ₗ[E] Sp E n := LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E) (Matrix.GeneralLinearGroup.toLin γ) with hg'`.

Establish `hg'γ : G g' = γ`. Use extensionality with `r s`. Rewrite using `[hG]`. Simplify using `[hg']`. Establish `hmv : ∀ h w, (G h : Matrix (Fin n) (Fin n) E) *ᵥ w = h w` using `fun h w => by`.

Establish `e : (G h : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' h.toLinearMap` using `Matrix.ext (hG h)`. Rewrite using `[e, LinearMap.toMatrix'_mulVec]`. Both sides reduce to the same expression. Establish `hy : ∀ r s, Valued.v (adAt F P (((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(D : ℤ))`. Establish `e : loc ((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g)) = AP⁻¹ * ra (G g)`.

Simplify using `only [map_mul, map_inv, hlr, hAP]`. Use `s1` as an intermediate fact. Rewrite `this` using `[← e]`. Conclude with `this`. Establish `hy' : ∀ r s, Valued.v (adAt F P (((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g') : GL (Fin n) (AfE F E)) r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(D : ℤ))`.

Establish `e : loc ((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g')) = AP⁻¹ * ra γ`. Simplify using `only [map_mul, map_inv, hlr, hAP, hg'γ]`. Use `cg_mono (le_max_left D N0) d1` as an intermediate fact. Rewrite `this` using `[← e]`. Conclude with `this`.

Establish `hCE : CongE P D g g'` using `(AdTieNear.congE_of_near P D D hD le_rfl (kk⁻¹ * κ * kk) g g' (G g) (G g') (hmv g) (hmv g') hg hq hy hy').symm`. Establish `toIntAt : ∀ H : GL (Fin n) E, Cg D (ra H) → ∀ a b, IntAt P ((((qOf P : ℕ) : E) ^ D)⁻¹ * ((H : Matrix (Fin n) (Fin n) E) a b - (1 : Matrix (Fin n) (Fin n) E) a b))`. Introduce `H hH a b`. Apply `GlobalTheory.FrameAgree.intAt_of_val` to reduce the goal to its premises. Rewrite using `[map_pow, map_natCast]`.

Establish `e1 : algebraMap E (P.adicCompletion E) ((1 : Matrix (Fin n) (Fin n) E) a b) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) a b`. Apply the tactic sequence `rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp`. Rewrite using `[e1]`. Conclude with `(val_le_iff _ _ hπ).2 (hH a b)`. Use `set h : Sp E n ≃ₗ[E] Sp E n := g⁻¹ * g' with hh`.

Establish `e1 : Cg D (ra (G h))`. Establish `e : ra (G h) = ((ra (G g))⁻¹ * AP) * (AP⁻¹ * ra γ)`. Rewrite using `[hh, map_mul, map_mul, map_inv, map_inv, hg'γ]`. Use `group`. Rewrite using `[e]`.

Conclude with `cg_mul s2 (cg_mono (le_max_left D N0) d1)`. Establish `e2 : Cg D (ra (G h⁻¹))`. Establish `e : ra (G h⁻¹) = ((ra γ)⁻¹ * AP) * (AP⁻¹ * ra (G g))`. Rewrite using `[hh, map_inv, map_inv, map_mul, map_mul, map_inv, map_inv, hg'γ]`. Use `group`.

Rewrite using `[e]`. Conclude with `cg_mul (cg_mono (le_max_left D N0) d2) s1`. Establish `hhm : h ∈ Formalism.L2.Col.GLint E n P`. Use `(GlobalTheory.FrameAgree.glint_of_cong P D h (fun a b => ?_) (fun a b => ?_)).1` and prove the remaining obligations. Rewrite using `[← hG]`.

Conclude with `toIntAt _ e1 a b`. Use `toIntAt _ e2 a b` as an intermediate fact. Rewrite `this` using `[hG]`. Conclude with `this`. Establish `hg'm : g' ∈ Formalism.L2.Col.GLint E n P`.

Use `mul_mem hg hhm` as an intermediate fact. Rewrite `this` using `[hh, mul_inv_cancel_left]`. Then use the resulting hypothesis. Take `⟨z, hzU, hzOff, hzP⟩` from `hlift ((loc x)⁻¹ * loc kk * ra γ * (loc kk)⁻¹)`. Establish `hlz : loc z = (loc x)⁻¹ * loc kk * ra γ * (loc kk)⁻¹` using `Units.ext (Matrix.ext fun r s => hzP r s)`. Use `⟨z, hzU, hzOff, (hC N z).2 ?_, g', hg'm, hCE, fun r s => ?_⟩` and prove the remaining obligations.

Rewrite using `[hlz, hx]`. Establish `e : (loc κ)⁻¹ * loc kk * ra γ * (loc kk)⁻¹ = loc kk * (AP⁻¹ * ra γ) * (loc kk)⁻¹`. Rewrite using `[hAP]`. Use `group`. Rewrite using `[e]`.

Conclude with `hN0 _ (cg_mono (le_max_right D N0) d1)`. Establish `e : loc (kk⁻¹ * (x * z) * kk) = ra γ`. Rewrite using `[map_mul, map_mul, map_mul, map_inv, hlz]`. Use `group`. Use `congrArg (fun X : GL (Fin n) (P.adicCompletion E) => (X : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) e` as an intermediate fact.

Rewrite using `[hg'γ]`. Conclude with `this`.
-/
theorem core (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = exp (-1 : ℤ))
    (hiff : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔
      ∀ r s, Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(N : ℤ)))
    (G : (Sp E n ≃ₗ[E] Sp E n) →* GL (Fin n) E)
    (hG : ∀ h r s, (G h : Matrix (Fin n) (Fin n) E) r s = LinearMap.toMatrix' h.toLinearMap r s)
    (U : Subgroup (GL (Fin n) (AfE F E))) (Off : GL (Fin n) (AfE F E) → Prop)
    (hlift : ∀ A : GL (Fin n) (P.adicCompletion E), ∃ z ∈ U, Off z ∧ ∀ r s, adAt F P (z.1 r s) = A.1 r s)
    (D : ℕ) (hD : 1 ≤ D) (kk : GL (Fin n) (AfE F E)) (f : GL (Fin n) E)
    (h1 : GlobalTheory.TwU.CongAt P D (kk⁻¹ * GlobalTheory.TwU.ratA F f)) (h2 : GlobalTheory.TwU.CongAt P D ((GlobalTheory.TwU.ratA F f)⁻¹ * kk))
    (κ : GL (Fin n) (AfE F E)) (g : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h3 : GlobalTheory.TwU.CongAt P D (((GlobalTheory.TwU.ratA F f)⁻¹ * κ * GlobalTheory.TwU.ratA F f)⁻¹ * GlobalTheory.TwU.ratA F (G g)))
    (x : GL (Fin n) (AfE F E)) (hx : GlobalTheory.FrameAgree.locM P x = GlobalTheory.FrameAgree.locM P κ) (N : ℕ) :
    ∃ z ∈ U, Off z ∧ GlobalTheory.TwU.CongAt P N z ∧ ∃ g' ∈ Formalism.L2.Col.GLint E n P, CongE P D g g' ∧
      ∀ r s, adAt F P ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap E (P.adicCompletion E) ((G g').1 r s) := by
  set loc : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) := GlobalTheory.FrameAgree.locM P with hloc
  set ra : GL (Fin n) E →* GL (Fin n) (P.adicCompletion E) := bc (algebraMap E (P.adicCompletion E)) with hra
  have hlr : ∀ M, loc (GlobalTheory.TwU.ratA F M) = ra M := fun M =>
    Units.ext (Matrix.ext fun r s => AdTieNear.adAt_ratA P M r s)
  have hC : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔ Cg N (loc z) := fun N z => hiff N z

  have hπ : Valued.v (((qOf P : ℕ) : P.adicCompletion E) ^ D) = exp (-(D : ℤ)) := by
    rw [map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp

  have hGP : ∀ r s, Valued.v (((ra (G g)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ 1 :=
    fun r s => val_entry_le P G hG g hg r s
  have hGPi : ∀ r s, Valued.v ((((ra (G g))⁻¹ : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ 1 := by
    intro r s
    rw [← map_inv, ← map_inv]
    exact val_entry_le P G hG g⁻¹ (inv_mem hg) r s

  have c1 : Cg D ((loc kk)⁻¹ * ra f) := by
    have := (hC D _).1 h1
    rwa [map_mul, map_inv, hlr] at this
  have c2 : Cg D ((ra f)⁻¹ * loc kk) := by
    have := (hC D _).1 h2
    rwa [map_mul, map_inv, hlr] at this
  have c3 : Cg D (((ra f)⁻¹ * loc κ * ra f)⁻¹ * ra (G g)) := by
    have := (hC D _).1 h3
    simpa only [map_mul, map_inv, hlr] using this
  set AP : GL (Fin n) (P.adicCompletion E) := (loc kk)⁻¹ * loc κ * loc kk with hAP
  have s1 : Cg D (AP⁻¹ * ra (G g)) := by
    have e : AP⁻¹ * ra (G g) = ((loc kk)⁻¹ * ra f) * (((ra f)⁻¹ * loc κ * ra f)⁻¹ * ra (G g)) *
        ((ra (G g))⁻¹ * ((ra f)⁻¹ * loc kk) * ra (G g)) := by
      rw [hAP]; group
    rw [e]
    exact cg_mul (cg_mul c1 c3) (cg_conj _ hGP hGPi c2)
  have s2 : Cg D ((ra (G g))⁻¹ * AP) := by
    have e : (ra (G g))⁻¹ * AP = ((ra (G g))⁻¹ * ((loc kk)⁻¹ * ra f) * ra (G g)) *
        (((ra f)⁻¹ * loc κ * ra f)⁻¹ * ra (G g))⁻¹ * ((ra f)⁻¹ * loc kk) := by
      rw [hAP]; group
    rw [e]
    exact cg_mul (cg_mul (cg_conj _ hGP hGPi c1) (cg_inv hD _ hπ c3)) c2

  obtain ⟨N0, hN0⟩ := cg_conj_bound (loc kk) N
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided E P n (max D N0) AP
  have d1 : Cg (max D N0) (AP⁻¹ * ra γ) := fun r s => (hγ r s).1
  have d2 : Cg (max D N0) ((ra γ)⁻¹ * AP) := fun r s => (hγ r s).2
  set g' : Sp E n ≃ₗ[E] Sp E n :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E) (Matrix.GeneralLinearGroup.toLin γ) with hg'
  have hg'γ : G g' = γ := by
    ext r s
    rw [hG]
    simp [hg']
  have hmv : ∀ h w, (G h : Matrix (Fin n) (Fin n) E) *ᵥ w = h w := fun h w => by
    have e : (G h : Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix' h.toLinearMap := Matrix.ext (hG h)
    rw [e, LinearMap.toMatrix'_mulVec]
    rfl

  have hy : ∀ r s, Valued.v (adAt F P (((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) r s) -
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(D : ℤ)) := by
    have e : loc ((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g)) = AP⁻¹ * ra (G g) := by
      simp only [map_mul, map_inv, hlr, hAP]
    have := s1
    rw [← e] at this
    exact this
  have hy' : ∀ r s, Valued.v (adAt F P (((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g') : GL (Fin n) (AfE F E)) r s) -
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(D : ℤ)) := by
    have e : loc ((kk⁻¹ * κ * kk)⁻¹ * GlobalTheory.TwU.ratA F (G g')) = AP⁻¹ * ra γ := by
      simp only [map_mul, map_inv, hlr, hAP, hg'γ]
    have := cg_mono (le_max_left D N0) d1
    rw [← e] at this
    exact this
  have hCE : CongE P D g g' :=
    (AdTieNear.congE_of_near P D D hD le_rfl (kk⁻¹ * κ * kk) g g' (G g) (G g') (hmv g) (hmv g') hg hq hy hy').symm

  have toIntAt : ∀ H : GL (Fin n) E, Cg D (ra H) →
      ∀ a b, IntAt P ((((qOf P : ℕ) : E) ^ D)⁻¹ * ((H : Matrix (Fin n) (Fin n) E) a b - (1 : Matrix (Fin n) (Fin n) E) a b)) := by
    intro H hH a b
    apply GlobalTheory.FrameAgree.intAt_of_val
    rw [map_pow, map_natCast]
    have e1 : algebraMap E (P.adicCompletion E) ((1 : Matrix (Fin n) (Fin n) E) a b) =
        (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [e1]
    exact (val_le_iff _ _ hπ).2 (hH a b)
  set h : Sp E n ≃ₗ[E] Sp E n := g⁻¹ * g' with hh
  have e1 : Cg D (ra (G h)) := by
    have e : ra (G h) = ((ra (G g))⁻¹ * AP) * (AP⁻¹ * ra γ) := by
      rw [hh, map_mul, map_mul, map_inv, map_inv, hg'γ]; group
    rw [e]
    exact cg_mul s2 (cg_mono (le_max_left D N0) d1)
  have e2 : Cg D (ra (G h⁻¹)) := by
    have e : ra (G h⁻¹) = ((ra γ)⁻¹ * AP) * (AP⁻¹ * ra (G g)) := by
      rw [hh, map_inv, map_inv, map_mul, map_mul, map_inv, map_inv, hg'γ]; group
    rw [e]
    exact cg_mul (cg_mono (le_max_left D N0) d2) s1
  have hhm : h ∈ Formalism.L2.Col.GLint E n P := by
    refine (GlobalTheory.FrameAgree.glint_of_cong P D h (fun a b => ?_) (fun a b => ?_)).1
    · rw [← hG]; exact toIntAt _ e1 a b
    · have := toIntAt _ e2 a b
      rw [hG] at this
      exact this
  have hg'm : g' ∈ Formalism.L2.Col.GLint E n P := by
    have := mul_mem hg hhm
    rwa [hh, mul_inv_cancel_left] at this

  obtain ⟨z, hzU, hzOff, hzP⟩ := hlift ((loc x)⁻¹ * loc kk * ra γ * (loc kk)⁻¹)
  have hlz : loc z = (loc x)⁻¹ * loc kk * ra γ * (loc kk)⁻¹ := Units.ext (Matrix.ext fun r s => hzP r s)
  refine ⟨z, hzU, hzOff, (hC N z).2 ?_, g', hg'm, hCE, fun r s => ?_⟩
  · rw [hlz, hx]
    have e : (loc κ)⁻¹ * loc kk * ra γ * (loc kk)⁻¹ = loc kk * (AP⁻¹ * ra γ) * (loc kk)⁻¹ := by
      rw [hAP]; group
    rw [e]
    exact hN0 _ (cg_mono (le_max_right D N0) d1)
  · have e : loc (kk⁻¹ * (x * z) * kk) = ra γ := by
      rw [map_mul, map_mul, map_mul, map_inv, hlz]; group
    have := congrArg (fun X : GL (Fin n) (P.adicCompletion E) => (X : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) e
    rw [hg'γ]
    exact this

end Core

end GlobalTheory.Mem.Col2.AdT.DeepElt

namespace GlobalTheory.Mem.Col2.AdT.DeepElt

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `B X I hOk hPins l Z a i hi kk fb hFr P v hv κ hκ g hg hIn x hx hxv N`. Establish `hlift` using `GlobalTheory.T.exists_unitaryAdelic_supported_at_bad_prime_place I hOk hPins l Z a i hi P v hv`. Take `⟨hseam, hq, -⟩` from `GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a 0 0 P 1`. Establish `hiff` using `fun N z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) N P z).2.2`. Take `⟨f1, f2⟩` from `hFr P`.

Unfold `GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn`. Establish `hvP : (GlobalTheory.TwU.seamP (sm I l Z) P.1).under (𝓞 (I.rec7 l Z).host.F) = v` using `by ext1`. Conclude with `hv.symm`. Establish `hloc : GlobalTheory.FrameAgree.locM (GlobalTheory.TwU.seamP (sm I l Z) P.1) x = GlobalTheory.FrameAgree.locM (GlobalTheory.TwU.seamP (sm I l Z) P.1) κ`. Apply `GlobalTheory.FrameAgree.loc_agree` to reduce the goal to its premises.

Rewrite using `[hvP]`. Conclude with `hxv`. Rewrite `hiff`, `hIn`, `f1`, `f2`, `hloc`, the goal using `[hseam]`. Establish `i1 : NumberField ↥(I.rec7 l Z).host.F` using `inferInstance`. Establish `i2 : NumberField (I.rec7 l Z).host.E` using `inferInstance`.

Conclude with `@core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) _ _ hlift ((I.cst a).D P) (((hOk.idx_ok a).cst_ok).D_pos P) kk (fb P) f1 f2 κ g hg hIn x hloc N`.
-/
theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a kk fb → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), ∀ g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ g → ∀ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) x = bc (prV (E := (I.rec7 l Z).host.E) v) κ → ∀ N : ℕ, ∃ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ∧ ∃ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' ∧ ∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * (x * z) * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s) := by
  intro B X I hOk hPins l Z a i hi kk fb hFr P v hv κ hκ g hg hIn x hx hxv N
  have hlift := GlobalTheory.T.exists_unitaryAdelic_supported_at_bad_prime_place I hOk hPins l Z a i hi P v hv
  obtain ⟨hseam, hq, -⟩ := GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a 0 0 P 1
  have hiff := fun N z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) N P z).2.2
  obtain ⟨f1, f2⟩ := hFr P
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn
  have hvP : (GlobalTheory.TwU.seamP (sm I l Z) P.1).under (𝓞 (I.rec7 l Z).host.F) = v := by
    ext1
    exact hv.symm
  have hloc : GlobalTheory.FrameAgree.locM (GlobalTheory.TwU.seamP (sm I l Z) P.1) x = GlobalTheory.FrameAgree.locM (GlobalTheory.TwU.seamP (sm I l Z) P.1) κ := by
    apply GlobalTheory.FrameAgree.loc_agree
    rw [hvP]
    exact hxv
  rw [hseam] at hiff hIn f1 f2 hloc ⊢
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact @core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) _ _ hlift ((I.cst a).D P)
    (((hOk.idx_ok a).cst_ok).D_pos P) kk (fb P) f1 f2 κ g hg hIn x hloc N

end GlobalTheory.Mem.Col2.AdT.DeepElt
