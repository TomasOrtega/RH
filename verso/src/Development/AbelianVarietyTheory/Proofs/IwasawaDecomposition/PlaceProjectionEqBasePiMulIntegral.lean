import Mathlib
import Formalism.LocalToGlobal.Columns.RecLevelLocK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.PiDiv

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0]`. Conclude with `zero_le'`. Rewrite `h`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ST : Finset (Pl E)} {π : 𝓞 E}

/- English proof (translation)
Introduce `hπ`. Establish `hle : ST.inf (fun P : Pl E => P.asIdeal) ≤ w.asIdeal`. Introduce `x hx`. Establish `hx' : ∀ P ∈ ST, x ∈ P.asIdeal` using `fun P hP => (Finset.inf_le hP : ST.inf (fun P : Pl E => P.asIdeal) ≤ P.asIdeal) hx`. Take `⟨c, rfl⟩` from `(h.dvd x).1 hx'`.

Conclude with `Ideal.mul_mem_right _ _ hπ`. Take `⟨P, hP, hPw⟩` from `(Ideal.IsPrime.inf_le' w.isPrime).1 hle`. Establish `e : P.asIdeal = w.asIdeal` using `P.isMaximal.eq_of_le w.isPrime.ne_top hPw`. Conclude with `hw (HeightOneSpectrum.ext e ▸ hP)`.
-/
theorem notMem_of_notMem (h : BasePi ST π) {w : Pl E} (hw : w ∉ ST) : π ∉ w.asIdeal := by
  intro hπ
  have hle : ST.inf (fun P : Pl E => P.asIdeal) ≤ w.asIdeal := by
    intro x hx
    have hx' : ∀ P ∈ ST, x ∈ P.asIdeal := fun P hP => (Finset.inf_le hP : ST.inf (fun P : Pl E => P.asIdeal) ≤ P.asIdeal) hx
    obtain ⟨c, rfl⟩ := (h.dvd x).1 hx'
    exact Ideal.mul_mem_right _ _ hπ
  obtain ⟨P, hP, hPw⟩ := (Ideal.IsPrime.inf_le' w.isPrime).1 hle
  have e : P.asIdeal = w.asIdeal := P.isMaximal.eq_of_le w.isPrime.ne_top hPw
  exact hw (HeightOneSpectrum.ext e ▸ hP)

/- English proof (translation)
Take `⟨b, hb⟩` from `w.intValuation_exists_uniformizer`. Take `⟨a, ha⟩` from `crtPl ST (fun P => if P = w then 1 else 0)`. Establish `haw : a ∉ w.asIdeal`. Introduce `haw`. Establish `h1` using `ha w hw`.

Rewrite `h1` using `[if_pos rfl]`. Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ haw h1))`. Establish `hbw : b ∈ w.asIdeal` using `(w.intValuation_lt_one_iff_mem b).1 (by rw [hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)`. Establish `hab : ∀ P ∈ ST, a * b ∈ P.asIdeal`. Introduce `P hP`.

Distinguish the cases in `hPw : P = w`. Substitute `hPw` using the available equality. Conclude with `Ideal.mul_mem_left _ _ hbw`. Establish `h1` using `ha P hP`. Rewrite `h1` using `[if_neg hPw, sub_zero]`.

Conclude with `Ideal.mul_mem_right _ _ h1`. Take `⟨c, hc⟩` from `(h.dvd _).1 hab`. Establish `hv : w.intValuation (a * b) = WithZero.exp (-1)`. Rewrite using `[map_mul, hb, HeightOneSpectrum.intValuation_eq_one_iff.2 haw, one_mul]`. Rewrite using `[← hv, hc, map_mul]`.

Conclude with `mul_le_of_le_one_right' (w.intValuation_le_one c)`.
-/
theorem exp_neg_one_le (h : BasePi ST π) {w : Pl E} (hw : w ∈ ST) : WithZero.exp (-1) ≤ w.intValuation π := by
  classical
  obtain ⟨b, hb⟩ := w.intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := crtPl ST (fun P => if P = w then 1 else 0)
  have haw : a ∉ w.asIdeal := by
    intro haw
    have h1 := ha w hw
    rw [if_pos rfl] at h1
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ haw h1))
  have hbw : b ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem b).1 (by rw [hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
  have hab : ∀ P ∈ ST, a * b ∈ P.asIdeal := by
    intro P hP
    by_cases hPw : P = w
    · subst hPw; exact Ideal.mul_mem_left _ _ hbw
    · have h1 := ha P hP
      rw [if_neg hPw, sub_zero] at h1
      exact Ideal.mul_mem_right _ _ h1
  obtain ⟨c, hc⟩ := (h.dvd _).1 hab
  have hv : w.intValuation (a * b) = WithZero.exp (-1) := by
    rw [map_mul, hb, HeightOneSpectrum.intValuation_eq_one_iff.2 haw, one_mul]
  rw [← hv, hc, map_mul]
  exact mul_le_of_le_one_right' (w.intValuation_le_one c)

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

/- English proof (translation)
Simplify using `[prV, inclE, Algebra.TensorProduct.map_tmul]`.
-/
theorem prV_inclE (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) x) = inclE (F := F) (v.adicCompletion F) x := by
  simp [prV, inclE, Algebra.TensorProduct.map_tmul]

end GlobalTheory.Mem.Col2.PiDiv

open GlobalTheory.Mem.Col2.PiDiv in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ ST π hπ v z hz hP`. Use `set e : E := algebraMap (𝓞 E) E π with he_def`. Establish `he : e ≠ 0` using `hπ.coe_ne_zero`. Establish `hzR : z ∈ RInt F E` using `hz`. Use `⟨prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e⁻¹ * z), ?_, ?_⟩` and prove the remaining obligations.

Use `(GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).2.2 fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, adAt_inclE, map_mul, valued_algebraMap, map_inv₀]`. Establish `hz1 : Valued.v (adAt F w z) ≤ 1` using `by rw [adAt_apply]; exact (mem_rInt_iff F E z).1 hzR w`. Establish `hv0 : 0 < w.valuation E e`. Rewrite using `[zero_lt_iff]`.

Conclude with `(Valuation.ne_zero_iff _).2 he`. Rewrite using `[inv_mul_le_one₀ hv0]`. Establish `hve : w.valuation E e = w.intValuation π` using `HeightOneSpectrum.valuation_of_algebraMap w π`. Distinguish the cases in `hw : w ∈ ST`. Conclude with `(le_exp_neg_one_of_lt_one (hP w hw)).trans (hve ▸ exp_neg_one_le hπ hw)`.

Rewrite using `[hve, HeightOneSpectrum.intValuation_eq_one_iff.2 (notMem_of_notMem hπ hw)]`. Conclude with `hz1`. Rewrite using `[map_mul, prV_inclE, ← mul_assoc, ← map_mul, mul_inv_cancel₀ he, map_one, one_mul]`.
-/
theorem GlobalTheory.Mem.Col2.prV_eq_pi_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  intro F E _ _ _ _ _ _ ST π hπ v z hz hP
  set e : E := algebraMap (𝓞 E) E π with he_def
  have he : e ≠ 0 := hπ.coe_ne_zero
  have hzR : z ∈ RInt F E := hz
  refine ⟨prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e⁻¹ * z), ?_, ?_⟩
  · refine (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).2.2 fun w _ => ?_
    rw [map_mul, adAt_inclE, map_mul, valued_algebraMap, map_inv₀]
    have hz1 : Valued.v (adAt F w z) ≤ 1 := by rw [adAt_apply]; exact (mem_rInt_iff F E z).1 hzR w
    have hv0 : 0 < w.valuation E e := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 he
    rw [inv_mul_le_one₀ hv0]
    have hve : w.valuation E e = w.intValuation π := HeightOneSpectrum.valuation_of_algebraMap w π
    by_cases hw : w ∈ ST
    · exact (le_exp_neg_one_of_lt_one (hP w hw)).trans (hve ▸ exp_neg_one_le hπ hw)
    · rw [hve, HeightOneSpectrum.intValuation_eq_one_iff.2 (notMem_of_notMem hπ hw)]
      exact hz1
  · rw [map_mul, prV_inclE, ← mul_assoc, ← map_mul, mul_inv_cancel₀ he, map_one, one_mul]
