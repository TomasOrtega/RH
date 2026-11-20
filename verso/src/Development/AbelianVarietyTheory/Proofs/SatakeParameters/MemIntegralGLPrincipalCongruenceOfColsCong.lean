import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.CongOne

open GlobalTheory.TopStep GlobalTheory.BlockDecompositionK1

/- English proof (translation)
Establish `hq : ((qOf P : ℕ) : E) ≠ 0` using `qOf_ne_zero`. Establish `hqD : ((qOf P : E) ^ D) ≠ 0` using `pow_ne_zero _ hq`. Establish `hsingle : ∀ s l, IntAt P ((Pi.single s (1 : E) : Sp E n) l)` using `fun s l => mem_stdAt.1 (single_mem_stdAt (P := P) s) l`. Establish `hent : ∀ l s, IntAt P (k (Pi.single s (1 : E)) l)` using `fun l s => by`. Establish `e : k (Pi.single s (1 : E)) l = (qOf P : E) ^ D * (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) + (Pi.single s (1 : E) : Sp E n) l`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `((intAt_pow (intAt_nat (qOf P)) D).mul (h s l)).add (hsingle s l)`. Set `A : Matrix (Fin n) (Fin n) E` to `Matrix.of fun l s => k (Pi.single s (1 : E)) l`.

Establish `hA : ∀ l s, IntAt P (A l s)` using `hent`. Establish `hAx : ∀ x, A.mulVec x = k x` using `fun x => by`. Use function extensionality and compare the values at `l`. Use `Eq.trans ?_ (apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l).symm` and prove the remaining obligations. Use `show ∑ s, A l s * x s = _`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Establish `hred : A.map (redP P) = 1`. Use extensionality with `l s`.

Rewrite using `[Matrix.map_apply]`. Establish `h0 : redP P (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l) = 0`. Take `⟨c, rfl⟩ : ∃ c, D = c + 1` from `⟨D - 1, by omega⟩`. Conclude with `reduction_eq_zero_of_integral_absNorm_pow_inv_mul (h s l)`. Rewrite `h0` using `[reduction_sub (hent l s) (hsingle s l), sub_eq_zero]`.

Use `show redP P (k (Pi.single s (1 : E)) l) = _`. Rewrite using `[h0, Matrix.one_apply, Pi.single_apply]`. Use `split_ifs`. Conclude with `reduction_one₂`. Conclude with `reduction_zero`.

Establish `hdet : IsUnit (redP P A.det)`. Rewrite using `[(det_int hA).2, hred, Matrix.det_one]`. Conclude with `isUnit_one`. Take `⟨j, hj⟩` from `exists_glint_of_matrix A hA hdet`. Establish `hjk : j.1 = k` using `LinearEquiv.ext fun x => (hj x).trans (hAx x)`.

Establish `hk : k ∈ GLint E n P` using `hjk ▸ j.2`. Use `⟨hk, fun x hx => ?_⟩` and prove the remaining obligations. Use `mem_stdAt.2 fun l => ?_` and prove the remaining obligations. Establish `e1` using `apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l`. Establish `e2` using `apply_eq_sum (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l`.

Establish `e : (((qOf P : E) ^ D)⁻¹ • (k x - x)) l = ∑ s, x s * (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))`. Rewrite using `[Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Express the relevant statement in the definitionally equal form `((qOf P : E) ^ D)⁻¹ * ((k : Sp E n →ₗ[E] Sp E n) x l - (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l) = _`. Rewrite using `[e1, e2, ← Finset.sum_sub_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.id_apply, LinearEquiv.coe_coe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `intAt_sum _ fun s _ => (mem_stdAt.1 hx s).mul (h s l)`.
-/
theorem mem_glint_prinCong_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
    {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n) (hD : 1 ≤ D)
    (h : ∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) :
    ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  classical
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hqD : ((qOf P : E) ^ D) ≠ 0 := pow_ne_zero _ hq
  have hsingle : ∀ s l, IntAt P ((Pi.single s (1 : E) : Sp E n) l) := fun s l =>
    mem_stdAt.1 (single_mem_stdAt (P := P) s) l
  have hent : ∀ l s, IntAt P (k (Pi.single s (1 : E)) l) := fun l s => by
    have e : k (Pi.single s (1 : E)) l = (qOf P : E) ^ D * (((qOf P : E) ^ D)⁻¹ *
        (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) + (Pi.single s (1 : E) : Sp E n) l := by
      field_simp
      ring
    rw [e]
    exact ((intAt_pow (intAt_nat (qOf P)) D).mul (h s l)).add (hsingle s l)
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun l s => k (Pi.single s (1 : E)) l
  have hA : ∀ l s, IntAt P (A l s) := hent
  have hAx : ∀ x, A.mulVec x = k x := fun x => by
    funext l
    refine Eq.trans ?_ (apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l).symm
    show ∑ s, A l s * x s = _
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm]
    rfl
  have hred : A.map (redP P) = 1 := by
    ext l s
    rw [Matrix.map_apply]
    have h0 : redP P (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l) = 0 := by
      obtain ⟨c, rfl⟩ : ∃ c, D = c + 1 := ⟨D - 1, by omega⟩
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (h s l)
    rw [reduction_sub (hent l s) (hsingle s l), sub_eq_zero] at h0
    show redP P (k (Pi.single s (1 : E)) l) = _
    rw [h0, Matrix.one_apply, Pi.single_apply]
    split_ifs
    · exact reduction_one₂
    · exact reduction_zero
  have hdet : IsUnit (redP P A.det) := by
    rw [(det_int hA).2, hred, Matrix.det_one]
    exact isUnit_one
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hA hdet
  have hjk : j.1 = k := LinearEquiv.ext fun x => (hj x).trans (hAx x)
  have hk : k ∈ GLint E n P := hjk ▸ j.2
  refine ⟨hk, fun x hx => ?_⟩
  refine mem_stdAt.2 fun l => ?_
  have e1 := apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l
  have e2 := apply_eq_sum (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l
  have e : (((qOf P : E) ^ D)⁻¹ • (k x - x)) l = ∑ s, x s * (((qOf P : E) ^ D)⁻¹ *
      (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) := by
    rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    change ((qOf P : E) ^ D)⁻¹ * ((k : Sp E n →ₗ[E] Sp E n) x l - (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l) = _
    rw [e1, e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [LinearMap.id_apply, LinearEquiv.coe_coe]
    ring
  rw [e]
  exact intAt_sum _ fun s _ => (mem_stdAt.1 hx s).mul (h s l)

end GlobalTheory.CongOne
