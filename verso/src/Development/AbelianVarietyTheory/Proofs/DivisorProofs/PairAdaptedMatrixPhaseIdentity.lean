import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelIsotr

section General

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `conv_lhs => enter [2, k]`.

Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_eq_sum {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    GlobalTheory.WeilM.hTens c JA JB x y = ∑ j, ∑ l, (xᵀ * JA * y.map c) j l * JB j l := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

def col {α : Type} (w : α → S) : Matrix α Unit S := Matrix.of fun i _ => w i

def row {α : Type} (w : α → S) : Matrix Unit α S := Matrix.of fun _ j => w j

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[col, row, Matrix.mul_apply, Matrix.vecMulVec_apply]`.
-/
theorem vecMulVec_eq_col_mul_row {α β : Type} (w : α → S) (v : β → S) :
    Matrix.vecMulVec w v = col w * row v := by
  ext i j
  simp [col, row, Matrix.mul_apply, Matrix.vecMulVec_apply]

/- English proof (translation)
Simplify using `[GlobalTheory.WeilM.diagCols, GlobalTheory.WeilM.dbl, Matrix.transpose_fromRows, Matrix.fromRows_mul, Matrix.mul_fromCols, Fintype.sum_sum_type, Finset.sum_neg_distrib]`.
-/
theorem sum_diag_dbl {n : Type} [Fintype n] [DecidableEq n] (N J : Matrix n n S) :
    ∑ j, ∑ l, ((GlobalTheory.WeilM.diagCols n : Matrix (n ⊕ n) n S) * N * (GlobalTheory.WeilM.diagCols n : Matrix (n ⊕ n) n S)ᵀ) j l *
      GlobalTheory.WeilM.dbl J j l = 0 := by
  simp [GlobalTheory.WeilM.diagCols, GlobalTheory.WeilM.dbl, Matrix.transpose_fromRows, Matrix.fromRows_mul, Matrix.mul_fromCols,
    Fintype.sum_sum_type, Finset.sum_neg_distrib]

/- English proof (translation)
Use `set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) S := GlobalTheory.WeilM.diagCols (Fin n) with hΔdef`. Establish `hmul : ∀ {a b e : Type} [Fintype b] (P : Matrix a b S) (Q : Matrix b e S), (P * Q).map c = P.map c * Q.map c` using `fun P Q => Matrix.map_mul (f := (c : S →+* S))`. Establish `hadd : ∀ {a b : Type} (P Q : Matrix a b S), (P + Q).map c = P.map c + Q.map c` using `fun P Q => Matrix.map_add c (map_add c) P Q`. Establish `h1m : (1 : Matrix (Fin n) (Fin n) S).map c = 1` using `Matrix.map_one _ (map_zero c) (map_one c)`. Establish `hΔ : Δᵀ.map c = Δᵀ`.

Rewrite using `[Matrix.transpose_map, hΔdef, GlobalTheory.WeilM.diagCols, Matrix.fromRows_map, h1m]`. Establish `h1' : ∀ {e : Type} (T : Matrix Unit e S), ιᵀ * (JA * ((col w).map c * T)) = 0` using `fun T => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.zero_mul]`. Establish `h2' : ∀ {e : Type} (T : Matrix (Fin d₁) e S), (col w)ᵀ * (JA * (ι.map c * T)) = 0` using `fun T => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.zero_mul]`.

Establish `h3' : ∀ {e : Type} (T : Matrix Unit e S), (col w)ᵀ * (JA * ((col w).map c * T)) = 0` using `fun T => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h3, Matrix.zero_mul]`. Establish `key : (ι * (Z * Δᵀ) + Matrix.vecMulVec w Y)ᵀ * JA * (ι * (Z' * Δᵀ) + Matrix.vecMulVec w Y').map c = Δ * (Zᵀ * (ιᵀ * JA * ι.map c) * Z'.map c) * Δᵀ`. Rewrite using `[vecMulVec_eq_col_mul_row, vecMulVec_eq_col_mul_row, hadd, hmul, hmul, hmul, hΔ]`. Simplify using `only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h1', h2', h3', Matrix.mul_zero, add_zero]`.

Rewrite using `[hTens_eq_sum, key]`. Conclude with `sum_diag_dbl _ _`.
-/
theorem hTens_isotr {d d₁ n : ℕ} (JA : Matrix (Fin d) (Fin d) S) (J : Matrix (Fin n) (Fin n) S)
    (ι : Matrix (Fin d) (Fin d₁) S) (w : Fin d → S)
    (h1 : ιᵀ * JA * (col w).map c = 0) (h2 : (col w)ᵀ * JA * ι.map c = 0) (h3 : (col w)ᵀ * JA * (col w).map c = 0)
    (Z Z' : Matrix (Fin d₁) (Fin n) S) (Y Y' : Fin n ⊕ Fin n → S) :
    GlobalTheory.WeilM.hTens c JA (GlobalTheory.WeilM.dbl J)
      (ι * (Z * (GlobalTheory.WeilM.diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) S)ᵀ) + Matrix.vecMulVec w Y)
      (ι * (Z' * (GlobalTheory.WeilM.diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) S)ᵀ) + Matrix.vecMulVec w Y') = 0 := by
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) S := GlobalTheory.WeilM.diagCols (Fin n) with hΔdef
  have hmul : ∀ {a b e : Type} [Fintype b] (P : Matrix a b S) (Q : Matrix b e S), (P * Q).map c = P.map c * Q.map c :=
    fun P Q => Matrix.map_mul (f := (c : S →+* S))
  have hadd : ∀ {a b : Type} (P Q : Matrix a b S), (P + Q).map c = P.map c + Q.map c :=
    fun P Q => Matrix.map_add c (map_add c) P Q
  have h1m : (1 : Matrix (Fin n) (Fin n) S).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have hΔ : Δᵀ.map c = Δᵀ := by
    rw [Matrix.transpose_map, hΔdef, GlobalTheory.WeilM.diagCols, Matrix.fromRows_map, h1m]
  have h1' : ∀ {e : Type} (T : Matrix Unit e S), ιᵀ * (JA * ((col w).map c * T)) = 0 := fun T => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have h2' : ∀ {e : Type} (T : Matrix (Fin d₁) e S), (col w)ᵀ * (JA * (ι.map c * T)) = 0 := fun T => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.zero_mul]
  have h3' : ∀ {e : Type} (T : Matrix Unit e S), (col w)ᵀ * (JA * ((col w).map c * T)) = 0 := fun T => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h3, Matrix.zero_mul]
  have key : (ι * (Z * Δᵀ) + Matrix.vecMulVec w Y)ᵀ * JA * (ι * (Z' * Δᵀ) + Matrix.vecMulVec w Y').map c =
      Δ * (Zᵀ * (ιᵀ * JA * ι.map c) * Z'.map c) * Δᵀ := by
    rw [vecMulVec_eq_col_mul_row, vecMulVec_eq_col_mul_row, hadd, hmul, hmul, hmul, hΔ]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, h1', h2', h3', Matrix.mul_zero, add_zero]
  rw [hTens_eq_sum, key]
  exact sum_diag_dbl _ _

end General

section Specific

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2 τ, h.2.2.2 τ, star_star]`.
-/
theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, col, Matrix.of_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem transpose_mul_col_apply {d k : Type} [Fintype d] (A : Matrix d k E) (J : Matrix d d E) (v : d → E) (m : k) (u : Unit) :
    (Aᵀ * J * col v) m u = (fun i => A i m) ⬝ᵥ (J *ᵥ v) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, col, Matrix.of_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end Specific

section Adapted

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}

/- English proof (translation)
Use extensionality with `m u`. Rewrite using `[transpose_mul_col_apply, Matrix.zero_apply]`. Establish `hv : (fun i => H'.ι i m) = H'.ι *ᵥ Pi.single m 1`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.

Rewrite using `[hv]`. Conclude with `(h.orth (Pi.single m 1)).1`.
-/
theorem adapted_iota_x (h : H'.IsAdapted σ B W W₁ i₀ i₁) : H'.ιᵀ * W.J * col (fun i => σ (H'.x i)) = 0 := by
  ext m u
  rw [transpose_mul_col_apply, Matrix.zero_apply]
  have hv : (fun i => H'.ι i m) = H'.ι *ᵥ Pi.single m 1 := by
    ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hv]
  exact (h.orth (Pi.single m 1)).1

/- English proof (translation)
Use extensionality with `m u`. Rewrite using `[transpose_mul_col_apply, Matrix.zero_apply]`. Conclude with `h.xx`.
-/
theorem adapted_x_x (h : H'.IsAdapted σ B W W₁ i₀ i₁) : (col H'.x)ᵀ * W.J * col (fun i => σ (H'.x i)) = 0 := by
  ext m u
  rw [transpose_mul_col_apply, Matrix.zero_apply]
  exact h.xx

/- English proof (translation)
Establish `hmul : ∀ {a b e : Type} [Fintype b] (P : Matrix a b E) (Q : Matrix b e E), (P * Q).map σ = P.map σ * Q.map σ` using `fun P Q => Matrix.map_mul (f := (σ : E →+* E))`. Establish `hJ : (W.J.map σ)ᵀ = -W.J`. Use extensionality with `i j`. Simplify using `[hskew]`. Establish `hx : (col (fun i => σ (H'.x i))).map σ = col H'.x`.

Use extensionality with `i u`. Simplify using `[col, sigma_sigma hcm]`. Establish `e1 : ((H'.ιᵀ * W.J * col (fun i => σ (H'.x i))).map σ)ᵀ = -((col H'.x)ᵀ * W.J * H'.ι.map σ)`. Rewrite using `[hmul, hmul, hx, Matrix.transpose_mul, Matrix.transpose_mul, hJ, ← Matrix.transpose_map, Matrix.transpose_transpose]`. Simplify using `[Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`.

Establish `e2` using `e1`. Rewrite `e2` using `[adapted_iota_x h]`. Simplify using `using e2.symm`.
-/
theorem adapted_x_iota (h : H'.IsAdapted σ B W W₁ i₀ i₁) (hcm : IsCMExt F E σ) (hskew : ∀ i j, σ (W.J j i) = -W.J i j) :
    (col H'.x)ᵀ * W.J * H'.ι.map σ = 0 := by
  have hmul : ∀ {a b e : Type} [Fintype b] (P : Matrix a b E) (Q : Matrix b e E), (P * Q).map σ = P.map σ * Q.map σ :=
    fun P Q => Matrix.map_mul (f := (σ : E →+* E))
  have hJ : (W.J.map σ)ᵀ = -W.J := by
    ext i j; simp [hskew]
  have hx : (col (fun i => σ (H'.x i))).map σ = col H'.x := by
    ext i u; simp [col, sigma_sigma hcm]
  have e1 : ((H'.ιᵀ * W.J * col (fun i => σ (H'.x i))).map σ)ᵀ = -((col H'.x)ᵀ * W.J * H'.ι.map σ) := by
    rw [hmul, hmul, hx, Matrix.transpose_mul, Matrix.transpose_mul, hJ, ← Matrix.transpose_map, Matrix.transpose_transpose]
    simp [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have e2 := e1
  rw [adapted_iota_x h] at e2
  simpa using e2.symm

end Adapted

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, cA_inclR]`.
-/
theorem incM_map_cA {a b : Type} (P : Matrix a b E) : (incM F P).map (cA σ) = incM F (P.map σ) := by
  ext i j; simp [incM, cA_inclR]

/- English proof (translation)
The claim follows from `(Matrix.map_mul (f := inclR (F := F) (AF F))).symm`.
-/
theorem incM_mul {a b e : Type} [Fintype b] (P : Matrix a b E) (Q : Matrix b e E) :
    incM F P * incM F Q = incM F (P * Q) :=
  (Matrix.map_mul (f := inclR (F := F) (AF F))).symm

/- English proof (translation)
The claim follows from `(Matrix.transpose_map).symm`.
-/
theorem incM_transpose {a b : Type} (P : Matrix a b E) : (incM F P)ᵀ = incM F Pᵀ :=
  (Matrix.transpose_map).symm

/- English proof (translation)
Use extensionality with `i u`. Both sides reduce to the same expression.
-/
theorem col_incV {a : ℕ} (v : Fin a → E) : col (incV F v) = incM F (col v) := by
  ext i u; rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM]`.
-/
theorem incM_zero {a b : Type} : incM F (0 : Matrix a b E) = 0 := by
  ext i j; simp [incM]

/- English proof (translation)
Use extensionality with `i u`. Both sides reduce to the same expression.
-/
theorem col_map {a : Type} (v : a → E) : (col v).map σ = col (fun i => σ (v i)) := by
  ext i u; rfl

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}

/- English proof (translation)
Rewrite using `[col_incV, incM_map_cA, col_map, incM_transpose, incM_mul, incM_mul, adapted_iota_x h, incM_zero]`.
-/
theorem adelic_iota_x (h : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (incM F H'.ι)ᵀ * incM F W.J * (col (incV F H'.x)).map (cA σ) = 0 := by
  rw [col_incV, incM_map_cA, col_map, incM_transpose, incM_mul, incM_mul, adapted_iota_x h, incM_zero]

/- English proof (translation)
Rewrite using `[col_incV, incM_map_cA, col_map, incM_transpose, incM_mul, incM_mul, adapted_x_x h, incM_zero]`.
-/
theorem adelic_x_x (h : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (col (incV F H'.x))ᵀ * incM F W.J * (col (incV F H'.x)).map (cA σ) = 0 := by
  rw [col_incV, incM_map_cA, col_map, incM_transpose, incM_mul, incM_mul, adapted_x_x h, incM_zero]

/- English proof (translation)
Rewrite using `[col_incV, incM_map_cA, incM_transpose, incM_mul, incM_mul, adapted_x_iota h hcm hskew, incM_zero]`.
-/
theorem adelic_x_iota (h : H'.IsAdapted σ B W W₁ i₀ i₁) (hcm : IsCMExt F E σ) (hskew : ∀ i j, σ (W.J j i) = -W.J i j) :
    (col (incV F H'.x))ᵀ * incM F W.J * (incM F H'.ι).map (cA σ) = 0 := by
  rw [col_incV, incM_map_cA, incM_transpose, incM_mul, incM_mul, adapted_x_iota h hcm hskew, incM_zero]

end Adelic

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH Z Z' Y Y'`. Unfold `GlobalTheory.WeilM.symp`. Rewrite using `[hTens_isotr (cA σ) _ _ _ _ (adelic_iota_x hH) (adelic_x_iota hH hP.base.cm hP.skew.skew) (adelic_x_x hH)]`. Simplify using the standard rewrite rules.
-/
theorem isotropic_mixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (Z Z' : Matrix (Fin d₁) (Fin n) (AE F E)) (Y Y' : Fin n ⊕ Fin n → AE F E),
      symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))
        (incM F H'.ι * (Z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y)
        (incM F H'.ι * (Z' * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) + Matrix.vecMulVec (incV F H'.x) Y') = 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH Z Z' Y Y'
  unfold GlobalTheory.WeilM.symp
  rw [hTens_isotr (cA σ) _ _ _ _ (adelic_iota_x hH) (adelic_x_iota hH hP.base.cm hP.skew.skew) (adelic_x_x hH)]
  simp

end GlobalTheory.SiegelIsotr

end
