import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.UnitaryFactor

section Glue

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def glue (e : A) (X Y : Matrix n n A) : Matrix n n A := e • X + (1 - e) • Y

/- English proof (translation)
Simplify using `[glue, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem glue_apply (e : A) (X Y : Matrix n n A) (i j : n) :
    glue e X Y i j = e * X i j + (1 - e) * Y i j := by
  simp [glue, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[glue, ← add_smul]`. Simplify using the standard rewrite rules.
-/
theorem glue_self (e : A) (X : Matrix n n A) : glue e X X = X := by
  rw [glue, ← add_smul]; simp

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `by linear_combination he`. Simplify using `only [glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, smul_add]`.
-/
theorem glue_mul {e : A} (he : e * e = e) (X Y X' Y' : Matrix n n A) :
    glue e X Y * glue e X' Y' = glue e (X * X') (Y * Y') := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  simp only [glue, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add, smul_add]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[glue_apply, Matrix.map_apply]`.
-/
theorem glue_map (f : A →+* A) (e : A) (X Y : Matrix n n A) :
    (glue e X Y).map f = glue (f e) (X.map f) (Y.map f) := by
  ext i j; simp [glue_apply, Matrix.map_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[glue_apply]`.
-/
theorem glue_transpose (e : A) (X Y : Matrix n n A) : (glue e X Y).transpose = glue e X.transpose Y.transpose := by
  ext i j; simp [glue_apply]

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj, ih]`. Take the linear combination `(f j * ∏ i ∈ s, f i - g j * ∏ i ∈ s, f i - f j * ∏ i ∈ s, g i + g j * ∏ i ∈ s, g i) * he`.
-/
theorem prod_glue {e : A} (he : e * e = e) (s : Finset n) (f g : n → A) :
    ∏ i ∈ s, (e * f i + (1 - e) * g i) = e * ∏ i ∈ s, f i + (1 - e) * ∏ i ∈ s, g i := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j s hj ih
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj, ih]
    linear_combination (f j * ∏ i ∈ s, f i - g j * ∏ i ∈ s, f i - f j * ∏ i ∈ s, g i + g j * ∏ i ∈ s, g i) * he

/- English proof (translation)
Rewrite using `[Matrix.det_apply', Matrix.det_apply', Matrix.det_apply', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [glue_apply]`. Rewrite using `[prod_glue he]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_glue {e : A} (he : e * e = e) (X Y : Matrix n n A) :
    (glue e X Y).det = e * X.det + (1 - e) * Y.det := by
  rw [Matrix.det_apply', Matrix.det_apply', Matrix.det_apply', Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [glue_apply]
  rw [prod_glue he]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨glue e (g : Matrix n n A) 1, glue e ((g⁻¹ : GL n A) : Matrix n n A) 1, by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self], by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩`.
-/
theorem exists_glue_left {e : A} (he : e * e = e) (g : GL n A) :
    ∃ U : GL n A, (U : Matrix n n A) = glue e (g : Matrix n n A) 1 ∧
      ((U⁻¹ : GL n A) : Matrix n n A) = glue e ((g⁻¹ : GL n A) : Matrix n n A) 1 :=
  ⟨⟨glue e (g : Matrix n n A) 1, glue e ((g⁻¹ : GL n A) : Matrix n n A) 1,
    by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self],
    by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨glue e 1 (g : Matrix n n A), glue e 1 ((g⁻¹ : GL n A) : Matrix n n A), by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self], by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩`.
-/
theorem exists_glue_right {e : A} (he : e * e = e) (g : GL n A) :
    ∃ U : GL n A, (U : Matrix n n A) = glue e 1 (g : Matrix n n A) ∧
      ((U⁻¹ : GL n A) : Matrix n n A) = glue e 1 ((g⁻¹ : GL n A) : Matrix n n A) :=
  ⟨⟨glue e 1 (g : Matrix n n A), glue e 1 ((g⁻¹ : GL n A) : Matrix n n A),
    by rw [glue_mul he, Units.mul_inv, Matrix.one_mul, glue_self],
    by rw [glue_mul he, Units.inv_mul, Matrix.one_mul, glue_self]⟩, rfl, rfl⟩

/- English proof (translation)
Rewrite using `[glue_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem glue_left_sub (e : A) (X : Matrix n n A) (i j : n) :
    glue e X 1 i j - (1 : Matrix n n A) i j = e * (X i j - (1 : Matrix n n A) i j) := by
  rw [glue_apply]; ring

/- English proof (translation)
Rewrite using `[glue_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem glue_right_sub (e : A) (X : Matrix n n A) (i j : n) :
    glue e 1 X i j - (1 : Matrix n n A) i j = (1 - e) * (X i j - (1 : Matrix n n A) i j) := by
  rw [glue_apply]; ring

/- English proof (translation)
Take the linear combination `(1 - u) * (h2 + h1')`.
-/
theorem alg_sub_one {ε η u : A} (h2 : ε * η = 0) (h1' : η * η = η) :
    (1 - η) + η * u - 1 = (ε + η) * (η * (u - 1)) := by
  linear_combination (1 - u) * (h2 + h1')

/- English proof (translation)
Take the linear combination `(-(1 - u - v + u * v)) * (h1 + h2) - ε * hu`.
-/
theorem alg_norm {ε η u v : A} (h1 : ε * ε = ε) (h2 : ε * η = 0) (hu : u * v = 1) :
    (1 - η) + η * u = ((1 - (ε + η)) + (ε + η) * u) * ((1 - ε) + ε * v) := by
  linear_combination (-(1 - u - v + u * v)) * (h1 + h2) - ε * hu

/- English proof (translation)
Take the linear combination `(1 - u - v + u * v) * h1' + η * hu`.
-/
theorem alg_inv {η u v : A} (h1' : η * η = η) (hu : u * v = 1) :
    ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
  linear_combination (1 - u - v + u * v) * h1' + η * hu

end Glue

end GlobalTheory.UnitaryFactor

namespace GlobalTheory.UnitaryFactor

/- English proof (translation)
Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.
-/
theorem one_mem_ohE (D : D7) {a : ℕ} (i j : Fin a) : (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D a k hk`. Establish `hkI : IntG D (k : GL (Fin a) (AE D))` using `(GlobalTheory.NormSum.mem_intG k).1 hk`. Establish `hgu : (((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)).map (sgA D)).transpose * ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = 1` using `(GlobalTheory.NormSum.PtsMem.mem_GA D _).1 k.2`. Establish `hu : ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) * sgA D ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) = 1` using `GlobalTheory.NormSum.VacMove.det_norm D k`. Establish `hum` using `GlobalTheory.NormSum.VacMove.det_int D _ hkI`.

Generalize the expression as in `hg : (k : GL (Fin a) (AE D)) = g at hkI hgu hu hum ⊢`. Establish `hdg : ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = (g : Matrix (Fin a) (Fin a) (AE D)).det` using `Matrix.GeneralLinearGroup.val_det_apply g`. Generalize the expression as in `((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = u at hu hum hdg ⊢`. Take `⟨ε, hε, h1, h2, h3⟩` from `GlobalTheory.NormSum.VacMove.exists_half_idem D`. Establish `hηε : sgA D (sgA D ε) = ε` using `GlobalTheory.NormSum.VacMove.sgA_sgA D ε`.

Establish `hηm : sgA D ε ∈ OhE D` using `GlobalTheory.NormSum.VacMove.sgA_mem D hε`. Establish `h1' : sgA D ε * sgA D ε = sgA D ε` using `by rw [← map_mul, h1]`. Generalize the expression as in `hη : sgA D ε = η at hηε hηm h1' h2 h3 ⊢`. Establish `hPP : (ε + η) * (ε + η) = ε + η` using `by linear_combination h1 + h1' + 2 * h2`. Establish `hPs : sgA D (ε + η) = ε + η` using `by rw [map_add, hη, hηε, add_comm]`.

Establish `hPm : ε + η ∈ OhE D` using `add_mem hε hηm`. Establish `h1m : (1 : Matrix (Fin a) (Fin a) (AE D)).map (sgA D) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Take `⟨ks, hks1, hks2⟩` from `exists_glue_left hPP g`. Take `⟨ki, hki1, hki2⟩` from `exists_glue_right hPP g`. Establish `hksG : ks ∈ GA D a`.

Rewrite using `[GlobalTheory.NormSum.PtsMem.mem_GA, hks1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu, Matrix.one_mul, glue_self]`. Establish `hkiG : ki ∈ GA D a`. Rewrite using `[GlobalTheory.NormSum.PtsMem.mem_GA, hki1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu, Matrix.one_mul, glue_self]`. Establish `hdet : ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) = (1 - (ε + η)) + (ε + η) * u`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hks1, det_glue hPP, Matrix.det_one, hdg]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hx : ((1 - η) + η * u) * ((1 - η) + η * sgA D u) = 1`. Conclude with `alg_inv h1' hu`. Take `⟨x, hx1, hx2⟩ : ∃ x : (AE D)ˣ, (x : AE D) = (1 - η) + η * u ∧ ((x⁻¹ : (AE D)ˣ) : AE D) = (1 - η) + η * sgA D u` from `⟨⟨_, _, hx, by rw [mul_comm, hx]⟩, rfl, rfl⟩`. Use `⟨⟨ks, hksG⟩, ⟨ki, hkiG⟩, x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext show ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = (ks : Matrix (Fin a) (Fin a) (AE D)) * ki` to reduce the goal to its premises. Rewrite using `[hg, hks1, hki1, glue_mul hPP, Matrix.mul_one, Matrix.one_mul, glue_self]`. Conclude with `(GlobalTheory.NormSum.mem_intG _).2 fun i j => ⟨by rw [hks1, glue_apply]`. Conclude with `add_mem (mul_mem hPm (hkI i j).1) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j)),`.

Use `by rw [hks2, glue_apply]`. Conclude with `add_mem (mul_mem hPm (hkI i j).2) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j))⟩`. Conclude with `(GlobalTheory.NormSum.mem_intG _).2 fun i j => ⟨by rw [hki1, glue_apply]`. Conclude with `add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).1),`. Use `by rw [hki2, glue_apply]`.

Conclude with `add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).2)⟩`. Introduce `q hq hi i j show ZeroAt D q ((ks : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)`. Rewrite using `[hks1, glue_left_sub]`. Conclude with `GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _`. Introduce `q hq hi i j show ZeroAt D q ((ki : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)`.

Rewrite using `[hki1, glue_right_sub]`. Conclude with `GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) _`. Introduce `q hq hi`. Establish `e : ((x : (AE D)ˣ) : AE D) - 1 = (ε + η) * (η * (u - 1))`. Rewrite using `[hx1]`.

Conclude with `alg_sub_one h2 h1'`. Rewrite using `[e]`. Conclude with `GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _`. Apply `Units.ext show (x : AE D) = ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) * sgA D (x : AE D)` to reduce the goal to its premises. Establish `hs : sgA D ((1 - η) + η * u) = (1 - ε) + ε * sgA D u`.

Rewrite using `[map_add (sgA D), map_sub (sgA D), map_one (sgA D), map_mul (sgA D), hηε]`. Rewrite using `[hdet, hx1, hs]`. Conclude with `alg_norm h1 h2 hu`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx1]`.

Conclude with `add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm hum)`. Rewrite using `[hx2]`. Conclude with `add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm (GlobalTheory.NormSum.VacMove.sgA_mem D hum))`. Use `⟨η, hηm, ?_⟩` and prove the remaining obligations. Rewrite using `[hx1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_split_inert_factor : ∀ (D : D7) {a : ℕ} (k : GA D a), k ∈ intG D a → ∃ (ks ki : GA D a) (x : (AE D)ˣ), k = ks * ki ∧ ks ∈ intG D a ∧ ki ∈ intG D a ∧ SuppSplit D (ks : GL (Fin a) (AE D)) ∧ SuppInert D (ki : GL (Fin a) (AE D)) ∧ (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) ∧ x = Matrix.GeneralLinearGroup.det (ks : GL (Fin a) (AE D)) * sgU D x ∧ IntU D x ∧ ∃ η ∈ OhE D, (x : AE D) - 1 = η * (((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1) := by
  intro D a k hk
  have hkI : IntG D (k : GL (Fin a) (AE D)) := (GlobalTheory.NormSum.mem_intG k).1 hk
  have hgu : (((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)).map (sgA D)).transpose *
      ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = 1 :=
    (GlobalTheory.NormSum.PtsMem.mem_GA D _).1 k.2
  have hu : ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) *
      sgA D ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) = 1 :=
    GlobalTheory.NormSum.VacMove.det_norm D k
  have hum := GlobalTheory.NormSum.VacMove.det_int D _ hkI
  generalize hg : (k : GL (Fin a) (AE D)) = g at hkI hgu hu hum ⊢
  have hdg : ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = (g : Matrix (Fin a) (Fin a) (AE D)).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  generalize ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) = u at hu hum hdg ⊢
  obtain ⟨ε, hε, h1, h2, h3⟩ := GlobalTheory.NormSum.VacMove.exists_half_idem D
  have hηε : sgA D (sgA D ε) = ε := GlobalTheory.NormSum.VacMove.sgA_sgA D ε
  have hηm : sgA D ε ∈ OhE D := GlobalTheory.NormSum.VacMove.sgA_mem D hε
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  generalize hη : sgA D ε = η at hηε hηm h1' h2 h3 ⊢
  have hPP : (ε + η) * (ε + η) = ε + η := by linear_combination h1 + h1' + 2 * h2
  have hPs : sgA D (ε + η) = ε + η := by rw [map_add, hη, hηε, add_comm]
  have hPm : ε + η ∈ OhE D := add_mem hε hηm
  have h1m : (1 : Matrix (Fin a) (Fin a) (AE D)).map (sgA D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨ks, hks1, hks2⟩ := exists_glue_left hPP g
  obtain ⟨ki, hki1, hki2⟩ := exists_glue_right hPP g
  have hksG : ks ∈ GA D a := by
    rw [GlobalTheory.NormSum.PtsMem.mem_GA, hks1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu,
      Matrix.one_mul, glue_self]
  have hkiG : ki ∈ GA D a := by
    rw [GlobalTheory.NormSum.PtsMem.mem_GA, hki1, glue_map, hPs, h1m, glue_transpose, Matrix.transpose_one, glue_mul hPP, hgu,
      Matrix.one_mul, glue_self]
  have hdet : ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) = (1 - (ε + η)) + (ε + η) * u := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hks1, det_glue hPP, Matrix.det_one, hdg]
    ring
  have hx : ((1 - η) + η * u) * ((1 - η) + η * sgA D u) = 1 := by
    exact alg_inv h1' hu
  obtain ⟨x, hx1, hx2⟩ : ∃ x : (AE D)ˣ, (x : AE D) = (1 - η) + η * u ∧
      ((x⁻¹ : (AE D)ˣ) : AE D) = (1 - η) + η * sgA D u :=
    ⟨⟨_, _, hx, by rw [mul_comm, hx]⟩, rfl, rfl⟩
  refine ⟨⟨ks, hksG⟩, ⟨ki, hkiG⟩, x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((k : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = (ks : Matrix (Fin a) (Fin a) (AE D)) * ki
    rw [hg, hks1, hki1, glue_mul hPP, Matrix.mul_one, Matrix.one_mul, glue_self]
  · exact (GlobalTheory.NormSum.mem_intG _).2 fun i j =>
      ⟨by rw [hks1, glue_apply]
          exact add_mem (mul_mem hPm (hkI i j).1) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j)),
       by rw [hks2, glue_apply]
          exact add_mem (mul_mem hPm (hkI i j).2) (mul_mem (sub_mem (one_mem _) hPm) (one_mem_ohE D i j))⟩
  · exact (GlobalTheory.NormSum.mem_intG _).2 fun i j =>
      ⟨by rw [hki1, glue_apply]
          exact add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).1),
       by rw [hki2, glue_apply]
          exact add_mem (mul_mem hPm (one_mem_ohE D i j)) (mul_mem (sub_mem (one_mem _) hPm) (hkI i j).2)⟩
  · intro q hq hi i j
    show ZeroAt D q ((ks : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)
    rw [hks1, glue_left_sub]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
  · intro q hq hi i j
    show ZeroAt D q ((ki : Matrix (Fin a) (Fin a) (AE D)) i j - (1 : Matrix (Fin a) (Fin a) (AE D)) i j)
    rw [hki1, glue_right_sub]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) _
  · intro q hq hi
    have e : ((x : (AE D)ˣ) : AE D) - 1 = (ε + η) * (η * (u - 1)) := by
      rw [hx1]; exact alg_sub_one h2 h1'
    rw [e]
    exact GlobalTheory.NormSum.VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
  · apply Units.ext
    show (x : AE D) = ((Matrix.GeneralLinearGroup.det ks : (AE D)ˣ) : AE D) * sgA D (x : AE D)
    have hs : sgA D ((1 - η) + η * u) = (1 - ε) + ε * sgA D u := by
      rw [map_add (sgA D), map_sub (sgA D), map_one (sgA D), map_mul (sgA D), hηε]
    rw [hdet, hx1, hs]
    exact alg_norm h1 h2 hu
  · refine ⟨?_, ?_⟩
    · rw [hx1]; exact add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm hum)
    · rw [hx2]; exact add_mem (sub_mem (one_mem _) hηm) (mul_mem hηm (GlobalTheory.NormSum.VacMove.sgA_mem D hum))
  · refine ⟨η, hηm, ?_⟩
    rw [hx1]
    ring

end GlobalTheory.UnitaryFactor
