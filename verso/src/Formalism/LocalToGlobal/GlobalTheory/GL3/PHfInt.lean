import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfArith
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrdUnimod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicAevalEqZero

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

open Polynomial NumberField Matrix

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.IntegralTrace.isIntegral_trace .. | (apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (intros; apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | ( …`.
-/
theorem trace_isIntegral {E : Type*} [Field E] [NumberField E] (φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M *ᵥ x ∈ L) : IsIntegral ℤ M.trace := by
  first | exact GlobalTheory.IntegralTrace.isIntegral_trace .. | (apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (intros; apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (intros; apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> first | assumption | infer_instance) | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp M hM | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp M | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› | exact @GlobalTheory.IntegralTrace.isIntegral_trace E

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits Matrix

variable (D : D7)

def sE {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) : D.host.E :=
  ∑ i, ∑ j, A i j * D.host.conj (B i j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hYY_eq {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D A B = Algebra.trace D.host.K D.host.E (sE D A B) := rfl

/- English proof (translation)
The claim follows from `o.isIntegral_coe.map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).toRingHom.toIntAlgHom`.
-/
theorem conj_int (o : 𝓞 D.host.E) : IsIntegral ℤ (D.host.conj (o : D.host.E)) :=
  o.isIntegral_coe.map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).toRingHom.toIntAlgHom

def cO (o : 𝓞 D.host.E) : 𝓞 D.host.E := ⟨D.host.conj (o : D.host.E), conj_int D o⟩

/- English proof (translation)
Rewrite using `[Matrix.smul_apply, Algebra.smul_def]`.
-/
theorem smul_entry {N N' : ℕ} (o : 𝓞 D.host.E) (A : Matrix (Fin N') (Fin N) D.host.E) (i j) :
    (o • A) i j = (o : D.host.E) * A i j := by
  rw [Matrix.smul_apply, Algebra.smul_def]

/- English proof (translation)
Simplify using `only [sE, Matrix.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem sE_add_left {N N' : ℕ} (A A' B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (A + A') B = sE D A B + sE D A' B := by
  simp only [sE, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [sE, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem sE_add_right {N N' : ℕ} (A B B' : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (B + B') = sE D A B + sE D A B' := by
  simp only [sE, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[sE]`.
-/
theorem sE_zero_left {N N' : ℕ} (B : Matrix (Fin N') (Fin N) D.host.E) : sE D 0 B = 0 := by
  simp [sE]

/- English proof (translation)
Simplify using `[sE]`.
-/
theorem sE_zero_right {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) : sE D A 0 = 0 := by
  simp [sE]

/- English proof (translation)
Simplify using `only [sE, smul_entry, Finset.mul_sum, mul_assoc]`.
-/
theorem sE_smul_left {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (o • A) B = (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [sE, smul_entry, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sE_smul_right {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (o • B) = D.host.conj (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [sE, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem sE_esmul_left {N N' : ℕ} (a : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (a • A) B = a * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [sE, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sE_esmul_right {N N' : ℕ} (b : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (b • B) = D.host.conj b * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Set `_` to `D.host.cmStar`. Use `set Bs : Matrix (Fin N) (Fin N') D.host.E := Matrix.of fun j i => D.host.conj (B i j) with hBs`. Establish `hBs_mem : ∀ y ∈ L', Bs *ᵥ y ∈ L`. Introduce `y hy`. Rewrite using `[hL.2.2]`.

Introduce `x hx`. Establish `h1 : stdH D.host.E N x (Bs *ᵥ y) = stdH D.host.E N' (B *ᵥ x) y`. Simplify using `only [stdH, CU.star_conj D, Matrix.mulVec, dotProduct, hBs, Matrix.of_apply, map_sum, map_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Conclude with `(hL'.2.2 y).1 hy _ (hB x hx)`.

Establish `hM : ∀ x ∈ L, (Bs * A) *ᵥ x ∈ L`. Introduce `x hx`. Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `hBs_mem _ (hA x hx)`. Establish `h` using `trace_isIntegral D.host.φ₀ L hL.1 hL.2.1 (Bs * A) hM`.

Establish `htr : (Bs * A).trace = sE D A B`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sE, hBs, Matrix.of_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h` using `[htr]`. Then use the resulting hypothesis.
-/
theorem sE_hom_gen {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E)
    (hA : ∀ x ∈ L, A *ᵥ x ∈ L') (hB : ∀ x ∈ L, B *ᵥ x ∈ L') : IsIntegral ℤ (sE D A B) := by
  let _ := D.host.cmStar
  set Bs : Matrix (Fin N) (Fin N') D.host.E := Matrix.of fun j i => D.host.conj (B i j) with hBs
  have hBs_mem : ∀ y ∈ L', Bs *ᵥ y ∈ L := by
    intro y hy
    rw [hL.2.2]
    intro x hx
    have h1 : stdH D.host.E N x (Bs *ᵥ y) = stdH D.host.E N' (B *ᵥ x) y := by
      simp only [stdH, CU.star_conj D, Matrix.mulVec, dotProduct, hBs, Matrix.of_apply, map_sum,
        map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    exact (hL'.2.2 y).1 hy _ (hB x hx)
  have hM : ∀ x ∈ L, (Bs * A) *ᵥ x ∈ L := by
    intro x hx
    rw [← Matrix.mulVec_mulVec]
    exact hBs_mem _ (hA x hx)
  have h := trace_isIntegral D.host.φ₀ L hL.1 hL.2.1 (Bs * A) hM
  have htr : (Bs * A).trace = sE D A B := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sE, hBs, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rwa [htr] at h

/- English proof (translation)
Establish `h1 : ∀ A ∈ homL D L L', ∀ B, (∀ x ∈ L, B *ᵥ x ∈ L') → IsIntegral ℤ (sE D A B)`. Introduce `A hA B hB`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA => exact sE_hom_gen D L L' hL hL' A B hA hB`. Consider the case `zero => rw [sE_zero_left]`.

Conclude with `isIntegral_zero`. Consider the case `add A A' _ _ h1 h2 => rw [sE_add_left]`. Conclude with `h1.add h2`. Consider the case `smul o A _ h1 => rw [sE_smul_left]`. Conclude with `o.isIntegral_coe.mul h1`.

Proceed by induction on `hB using Submodule.span_induction with`. Consider the case `mem B hB => exact h1 A hA B hB`. Consider the case `zero => rw [sE_zero_right]`. Conclude with `isIntegral_zero`. Consider the case `add B B' _ _ h2 h3 => rw [sE_add_right]`.

Conclude with `h2.add h3`. Consider the case `smul o B _ h2 => rw [sE_smul_right]`. Conclude with `(conj_int D o).mul h2`.
-/
theorem sE_hom {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    IsIntegral ℤ (sE D A B) := by
  have h1 : ∀ A ∈ homL D L L', ∀ B, (∀ x ∈ L, B *ᵥ x ∈ L') → IsIntegral ℤ (sE D A B) := by
    intro A hA B hB
    induction hA using Submodule.span_induction with
    | mem A hA => exact sE_hom_gen D L L' hL hL' A B hA hB
    | zero => rw [sE_zero_left]; exact isIntegral_zero
    | add A A' _ _ h1 h2 => rw [sE_add_left]; exact h1.add h2
    | smul o A _ h1 => rw [sE_smul_left]; exact o.isIntegral_coe.mul h1
  induction hB using Submodule.span_induction with
  | mem B hB => exact h1 A hA B hB
  | zero => rw [sE_zero_right]; exact isIntegral_zero
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact h2.add h3
  | smul o B _ h2 => rw [sE_smul_right]; exact (conj_int D o).mul h2

def TrOK (z : D.host.E) : Prop :=
  ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace D.host.K D.host.E ((o : D.host.E) * z))

/- English proof (translation)
Introduce `o` and use `by rw [mul_zero, map_zero]; exact isIntegral_zero`.
-/
theorem trOK_zero : TrOK D 0 := fun o => by rw [mul_zero, map_zero]; exact isIntegral_zero

/- English proof (translation)
Introduce `o` and use `by rw [mul_add, map_add]; exact (hz o).add (hw o)`.
-/
theorem trOK_add {z w : D.host.E} (hz : TrOK D z) (hw : TrOK D w) : TrOK D (z + w) :=
  fun o => by rw [mul_add, map_add]; exact (hz o).add (hw o)

/- English proof (translation)
Introduce `o` and use `by have := hz (o * o') rwa [show ((o * o' : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * o' from rfl, mul_assoc] at this`.
-/
theorem trOK_mul {z : D.host.E} (hz : TrOK D z) (o' : 𝓞 D.host.E) : TrOK D ((o' : D.host.E) * z) :=
  fun o => by
    have := hz (o * o')
    rwa [show ((o * o' : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * o' from rfl, mul_assoc] at this

/- English proof (translation)
Establish `h` using `((D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 a).1 ha) b hb`. Take `⟨r, hr⟩` from `h`. Rewrite using `[← hr]`. Conclude with `r.isIntegral_coe`.
-/
theorem trace_conj_integral (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    IsIntegral ℤ (Algebra.trace D.host.K D.host.E (a * D.host.conj b)) := by
  have h := ((D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 a).1 ha) b hb
  obtain ⟨r, hr⟩ := h
  rw [← hr]
  exact r.isIntegral_coe

/- English proof (translation)
Introduce `o`. Establish `hot : ((o * t : 𝓞 D.host.E) : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)`. Use `(D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem (o * t) ha` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis. Use `trace_conj_integral D _ b hot hb` as an intermediate fact.

Rewrite `this` using `[show ((o * t : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * t from rfl]`. Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trOK_gen (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) (t : 𝓞 D.host.E) :
    TrOK D (a * D.host.conj b * t) := by
  intro o
  have hot : ((o * t : 𝓞 D.host.E) : D.host.E) * a ∈
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem (o * t) ha
    rwa [Algebra.smul_def] at this
  have := trace_conj_integral D _ b hot hb
  rw [show ((o * t : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * t from rfl] at this
  convert this using 2
  ring

/- English proof (translation)
Establish `hgen : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ A₀ ∈ homL D L L', ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ B₀ ∈ homL D L L', TrOK D (sE D (a • A₀) (b • B₀))`. Introduce `a ha A₀ hA₀ b hb B₀ hB₀`. Rewrite using `[sE_esmul_left, sE_esmul_right, ← mul_assoc]`. Conclude with `trOK_gen D a b ha hb ⟨sE D A₀ B₀, sE_hom D L L' hL hL' A₀ B₀ hA₀ hB₀⟩`. Establish `h1 : ∀ A ∈ YYl D L L', ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ B₀ ∈ homL D L L', TrOK D (sE D A (b • B₀))`.

Introduce `A hA b hb B₀ hB₀`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA`. Take `⟨a, ha, A₀, hA₀, rfl⟩` from `hA`. Conclude with `hgen a ha A₀ hA₀ b hb B₀ hB₀`.

Consider the case `zero => rw [sE_zero_left]`. Conclude with `trOK_zero D`. Consider the case `add A A' _ _ h2 h3 => rw [sE_add_left]`. Conclude with `trOK_add D h2 h3`. Consider the case `smul o A _ h2 => rw [sE_smul_left]`.

Conclude with `trOK_mul D h2 o`. Proceed by induction on `hB using Submodule.span_induction with`. Consider the case `mem B hB`. Take `⟨b, hb, B₀, hB₀, rfl⟩` from `hB`. Conclude with `h1 A hA b hb B₀ hB₀`.

Consider the case `zero => rw [sE_zero_right]`. Conclude with `trOK_zero D`. Consider the case `add B B' _ _ h2 h3 => rw [sE_add_right]`. Conclude with `trOK_add D h2 h3`. Consider the case `smul o B _ h2 => rw [sE_smul_right]`.

Conclude with `trOK_mul D h2 (cO D o)`.
-/
theorem trOK_YY {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ YYl D L L') (hB : B ∈ YYl D L L') :
    TrOK D (sE D A B) := by

  have hgen : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ A₀ ∈ homL D L L',
      ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ B₀ ∈ homL D L L',
      TrOK D (sE D (a • A₀) (b • B₀)) := by
    intro a ha A₀ hA₀ b hb B₀ hB₀
    rw [sE_esmul_left, sE_esmul_right, ← mul_assoc]
    exact trOK_gen D a b ha hb ⟨sE D A₀ B₀, sE_hom D L L' hL hL' A₀ B₀ hA₀ hB₀⟩
  have h1 : ∀ A ∈ YYl D L L', ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ B₀ ∈ homL D L L', TrOK D (sE D A (b • B₀)) := by
    intro A hA b hb B₀ hB₀
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hA
      exact hgen a ha A₀ hA₀ b hb B₀ hB₀
    | zero => rw [sE_zero_left]; exact trOK_zero D
    | add A A' _ _ h2 h3 => rw [sE_add_left]; exact trOK_add D h2 h3
    | smul o A _ h2 => rw [sE_smul_left]; exact trOK_mul D h2 o
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨b, hb, B₀, hB₀, rfl⟩ := hB
    exact h1 A hA b hb B₀ hB₀
  | zero => rw [sE_zero_right]; exact trOK_zero D
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact trOK_add D h2 h3
  | smul o B _ h2 => rw [sE_smul_right]; exact trOK_mul D h2 (cO D o)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

/- English proof (translation)
Introduce `D N N' L L' hA A hA' B hB'`. Establish `h` using `trOK_YY D L L' hA.2.2.1 hA.2.2.2 A B hA' hB' 1`. Rewrite using `[hYY_eq]`. Simplify using `using h`.
-/
theorem hermitian_pairing_integral : AR.HYYIntRec := by
  intro D N N' L L' hA A hA' B hB'
  have h := trOK_YY D L L' hA.2.2.1 hA.2.2.2 A B hA' hB' 1
  rw [hYY_eq]
  simpa using h

/- English proof (translation)
The claim follows from `HfArithRec_of_int hermitian_pairing_integral`.
-/
theorem arithmetic_hermitian_form : HfArithRec := HfArithRec_of_int hermitian_pairing_integral

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
