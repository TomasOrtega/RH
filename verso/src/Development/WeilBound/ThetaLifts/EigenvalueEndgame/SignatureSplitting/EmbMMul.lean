import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open Matrix GlobalTheory.WeilM

variable {S R d k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]

structure Dual (c : R →ₐ[S] R) (J : Matrix d d R) (X Y : Matrix d k R) : Prop where
  cc : ∀ a, c (c a) = a
  skew : (J.map c)ᵀ = -J
  xx : Xᵀ * J * X.map c = 0
  yy : Yᵀ * J * Y.map c = 0
  xy : Xᵀ * J * Y.map c = 1

def embM (c : R →ₐ[S] R) (J : Matrix d d R) (X Y : Matrix d k R) (g g' : Matrix k k R) : Matrix d d R :=
  1 + X * (g - 1) * (J * Y.map c)ᵀ - Y * (g' - 1) * (J * X.map c)ᵀ

variable {c : R →ₐ[S] R} {J : Matrix d d R} {X Y : Matrix d k R}

/- English proof (translation)
Conclude with `Matrix.map_mul (f := c.toRingHom)`.
-/
theorem mapc_mul {a b e : Type} [Fintype b] (A : Matrix a b R) (B : Matrix b e R) : (A * B).map c = A.map c * B.map c := by
  exact Matrix.map_mul (f := c.toRingHom)

/- English proof (translation)
Conclude with `Matrix.map_one _ (map_zero c) (map_one c)`.
-/
theorem mapc_one {a : Type} [DecidableEq a] : (1 : Matrix a a R).map c = 1 := by
  exact Matrix.map_one _ (map_zero c) (map_one c)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Conclude with `h.cc _`.
-/
theorem Dual.mcc (h : Dual c J X Y) {a b : Type} (A : Matrix a b R) : (A.map c).map c = A := by
  ext i j
  simp only [Matrix.map_apply]
  exact h.cc _

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
private theorem mapc_transpose {a b : Type} (A : Matrix a b R) : (Aᵀ.map c) = (A.map c)ᵀ := by
  ext i j
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
private theorem mapc_add' {a b : Type} (A B : Matrix a b R) : (A + B).map c = A.map c + B.map c := by
  ext i j
  simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
private theorem mapc_sub' {a b : Type} (A B : Matrix a b R) : (A - B).map c = A.map c - B.map c := by
  ext i j
  simp

/- English proof (translation)
Establish `e : ((Xᵀ * J * Y.map c).map c)ᵀ = (1 : Matrix k k R)`. Rewrite using `[h.xy, mapc_one, transpose_one]`. Rewrite `e` using `[mapc_mul, mapc_mul, h.mcc, transpose_mul, transpose_mul, h.skew, mapc_transpose, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]`. Conclude with `neg_eq_iff_eq_neg.mp e`.
-/
theorem Dual.yx (h : Dual c J X Y) : Yᵀ * J * X.map c = -1 := by
  have e : ((Xᵀ * J * Y.map c).map c)ᵀ = (1 : Matrix k k R) := by
    rw [h.xy, mapc_one, transpose_one]
  rw [mapc_mul, mapc_mul, h.mcc, transpose_mul, transpose_mul, h.skew, mapc_transpose, transpose_transpose,
    Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc] at e
  exact neg_eq_iff_eq_neg.mp e

/- English proof (translation)
Simplify using `only [transpose_mul, transpose_transpose, Matrix.mul_assoc]`.
-/
theorem tr_mul {e : Type} (Z : Matrix d k R) (T : Matrix d e R) : (J * Z.map c)ᵀ * T = (Tᵀ * J * Z.map c)ᵀ := by
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [embM, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, tr_mul]`.
-/
theorem embM_mul {e : Type} (g g' : Matrix k k R) (T : Matrix d e R) :
    embM c J X Y g g' * T = T + X * (g - 1) * (Tᵀ * J * Y.map c)ᵀ - Y * (g' - 1) * (Tᵀ * J * X.map c)ᵀ := by
  simp only [embM, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, tr_mul]

/- English proof (translation)
Rewrite using `[embM_mul, h.xy, h.xx]`. Simplify using `only [transpose_one, transpose_zero, Matrix.mul_one, Matrix.mul_zero, sub_zero, Matrix.mul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem Dual.embX (h : Dual c J X Y) (g g' : Matrix k k R) : embM c J X Y g g' * X = X * g := by
  rw [embM_mul, h.xy, h.xx]
  simp only [transpose_one, transpose_zero, Matrix.mul_one, Matrix.mul_zero, sub_zero, Matrix.mul_sub]
  abel

/- English proof (translation)
Rewrite using `[embM_mul, h.yy, h.yx]`. Simplify using `only [transpose_zero, transpose_neg, transpose_one, Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, add_zero, sub_neg_eq_add, Matrix.mul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem Dual.embY (h : Dual c J X Y) (g g' : Matrix k k R) : embM c J X Y g g' * Y = Y * g' := by
  rw [embM_mul, h.yy, h.yx]
  simp only [transpose_zero, transpose_neg, transpose_one, Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, add_zero,
    sub_neg_eq_add, Matrix.mul_sub]
  abel

/- English proof (translation)
Establish `hAX : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (X * M) = M`. Introduce `e M`. Rewrite using `[← Matrix.mul_assoc, tr_mul, h.xy, transpose_one, Matrix.one_mul]`. Establish `hAY : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (Y * M) = 0`. Introduce `e M`.

Rewrite using `[← Matrix.mul_assoc, tr_mul, h.yy, transpose_zero, Matrix.zero_mul]`. Establish `hBX : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (X * M) = 0`. Introduce `e M`. Rewrite using `[← Matrix.mul_assoc, tr_mul, h.xx, transpose_zero, Matrix.zero_mul]`. Establish `hBY : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (Y * M) = -M`.

Introduce `e M`. Rewrite using `[← Matrix.mul_assoc, tr_mul, h.yx, transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul]`. Establish `hAX1 : (J * Y.map c)ᵀ * X = 1` using `by rw [tr_mul, h.xy, transpose_one]`. Establish `hAY1 : (J * Y.map c)ᵀ * Y = 0` using `by rw [tr_mul, h.yy, transpose_zero]`. Establish `hBX1 : (J * X.map c)ᵀ * X = 0` using `by rw [tr_mul, h.xx, transpose_zero]`.

Establish `hBY1 : (J * X.map c)ᵀ * Y = -1` using `by rw [tr_mul, h.yx, transpose_neg, transpose_one]`. Simplify using `only [embM, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hAX, hAY, hBX, hBY, hAX1, hAY1, hBX1, hBY1, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul, sub_zero, zero_sub, add_zero, zero_add, sub_ …`. Normalize the expressions using the abelian group laws.
-/
theorem Dual.emb_mul (h : Dual c J X Y) (g g' f f' : Matrix k k R) :
    embM c J X Y g g' * embM c J X Y f f' = embM c J X Y (g * f) (g' * f') := by
  have hAX : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (X * M) = M := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.xy, transpose_one, Matrix.one_mul]
  have hAY : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (Y * M) = 0 := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.yy, transpose_zero, Matrix.zero_mul]
  have hBX : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (X * M) = 0 := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.xx, transpose_zero, Matrix.zero_mul]
  have hBY : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (Y * M) = -M := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.yx, transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul]
  have hAX1 : (J * Y.map c)ᵀ * X = 1 := by rw [tr_mul, h.xy, transpose_one]
  have hAY1 : (J * Y.map c)ᵀ * Y = 0 := by rw [tr_mul, h.yy, transpose_zero]
  have hBX1 : (J * X.map c)ᵀ * X = 0 := by rw [tr_mul, h.xx, transpose_zero]
  have hBY1 : (J * X.map c)ᵀ * Y = -1 := by rw [tr_mul, h.yx, transpose_neg, transpose_one]
  simp only [embM, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, hAX, hAY, hBX, hBY, hAX1, hAY1, hBX1, hBY1, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg,
    Matrix.neg_mul, sub_zero, zero_sub, add_zero, zero_add, sub_neg_eq_add, neg_neg]
  abel

/- English proof (translation)
Simplify using `only [embM, transpose_add, transpose_sub, transpose_one, transpose_mul, transpose_transpose, mapc_add', mapc_sub', mapc_mul, mapc_one, mapc_transpose, h.mcc, h.skew, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Ma …`. Normalize the expressions using the abelian group laws.
-/
theorem Dual.emb_tr (h : Dual c J X Y) (g f : Matrix k k R) :
    (embM c J X Y g (f.map c)ᵀ)ᵀ * J = J * (embM c J X Y f (g.map c)ᵀ).map c := by
  simp only [embM, transpose_add, transpose_sub, transpose_one, transpose_mul, transpose_transpose, mapc_add',
    mapc_sub', mapc_mul, mapc_one, mapc_transpose, h.mcc, h.skew, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

/- English proof (translation)
Rewrite using `[_root_.mul_inv_rev, Units.val_mul, mapc_mul, transpose_mul]`.
-/
theorem star_mul (g f : GL k R) : ((((g * f)⁻¹).1).map c)ᵀ = ((g⁻¹).1.map c)ᵀ * ((f⁻¹).1.map c)ᵀ := by
  rw [_root_.mul_inv_rev, Units.val_mul, mapc_mul, transpose_mul]

/- English proof (translation)
Rewrite using `[h.emb_mul, ← star_mul]`. Simplify using `[embM, mapc_one]`.
-/
theorem Dual.emb_inv (h : Dual c J X Y) (g : GL k R) :
    embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ * embM c J X Y (g⁻¹).1 ((g⁻¹⁻¹).1.map c)ᵀ = 1 := by
  rw [h.emb_mul, ← star_mul]
  simp [embM, mapc_one]

def Dual.emb (h : Dual c J X Y) : GL k R →* UG c J where
  toFun g := ⟨⟨embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ, embM c J X Y (g⁻¹).1 ((g⁻¹⁻¹).1.map c)ᵀ, h.emb_inv g,
    mul_eq_one_comm.1 (h.emb_inv g)⟩, by
      change (embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ)ᵀ * J * (embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ).map c = J
      have := mul_eq_one_comm.1 (h.emb_inv g)
      rw [inv_inv] at this
      rw [h.emb_tr, Matrix.mul_assoc, ← mapc_mul, this, mapc_one, Matrix.mul_one]⟩
  map_one' := Subtype.ext (Units.ext (by simp [embM]))
  map_mul' g f := Subtype.ext (Units.ext (by
    change embM c J X Y (g.1 * f.1) _ = embM c J X Y g.1 _ * embM c J X Y f.1 _
    rw [h.emb_mul, ← star_mul]))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Dual.emb_val (h : Dual c J X Y) (g : GL k R) : (h.emb g).1.1 = embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ := rfl

/- English proof (translation)
Establish `hE : ∀ {a b : GL k R → Matrix k k R}, Continuous a → Continuous b → Continuous fun g => embM c J X Y (a g) (b g)`. Introduce `a b ha hb`. Simplify using `only [embM]`. Use `fun_prop`. Establish `hv : Continuous fun g : GL k R => (g : Matrix k k R)` using `Units.continuous_val`.

Establish `hi : Continuous fun g : GL k R => ((g⁻¹ : GL k R) : Matrix k k R)` using `Units.continuous_coe_inv`. Establish `hii : Continuous fun g : GL k R => ((g⁻¹⁻¹ : GL k R) : Matrix k k R)`. Simplify `hv` using `only [inv_inv]`. Rewrite using `[continuous_induced_rng]`. Use `Units.continuous_iff.mpr ⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `(hE hv ((hi.matrix_map hc).matrix_transpose)).congr fun g => (h.emb_val g).symm`. Conclude with `(hE hi ((hii.matrix_map hc).matrix_transpose)).congr fun g => rfl`.
-/
theorem Dual.emb_cont [TopologicalSpace R] [IsTopologicalRing R] (h : Dual c J X Y) (hc : Continuous c) : Continuous h.emb := by
  have hE : ∀ {a b : GL k R → Matrix k k R}, Continuous a → Continuous b →
      Continuous fun g => embM c J X Y (a g) (b g) := by
    intro a b ha hb
    simp only [embM]
    fun_prop
  have hv : Continuous fun g : GL k R => (g : Matrix k k R) := Units.continuous_val
  have hi : Continuous fun g : GL k R => ((g⁻¹ : GL k R) : Matrix k k R) := Units.continuous_coe_inv
  have hii : Continuous fun g : GL k R => ((g⁻¹⁻¹ : GL k R) : Matrix k k R) := by
    simpa only [inv_inv] using hv
  rw [continuous_induced_rng]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (hE hv ((hi.matrix_map hc).matrix_transpose)).congr fun g => (h.emb_val g).symm
  · exact (hE hi ((hii.matrix_map hc).matrix_transpose)).congr fun g => rfl

/- English proof (translation)
Establish `hfc : (f : R → R') ∘ c = c' ∘ f` using `funext hf`. Simplify using `only [embM, Matrix.map_sub f (map_sub f), Matrix.map_add f (map_add f), Matrix.map_mul, Matrix.map_one f (map_zero f) (map_one f), Matrix.transpose_map, Matrix.map_map, hfc]`.
-/
theorem embM_map {S' R' : Type} [CommRing S'] [CommRing R'] [Algebra S' R'] {c' : R' →ₐ[S'] R'} (f : R →+* R')
    (hf : ∀ a, f (c a) = c' (f a)) (g g' : Matrix k k R) :
    (embM c J X Y g g').map f = embM c' (J.map f) (X.map f) (Y.map f) (g.map f) (g'.map f) := by
  have hfc : (f : R → R') ∘ c = c' ∘ f := funext hf
  simp only [embM, Matrix.map_sub f (map_sub f), Matrix.map_add f (map_add f), Matrix.map_mul,
    Matrix.map_one f (map_zero f) (map_one f), Matrix.transpose_map, Matrix.map_map, hfc]

/- English proof (translation)
Establish `hfc : (f : R → R') ∘ c = c' ∘ f` using `funext hf`. Use `⟨hc, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun M => Matrix.map M f) h.skew`. Simplify using `only [Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_neg f (map_neg f)] at e`. Simplify `e` using `only [Matrix.transpose_map, Matrix.map_map]`.

Establish `e` using `congrArg (fun M => Matrix.map M f) h.xx`. Simplify using `only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e`. Simplify `e` using `only [Matrix.transpose_map, Matrix.map_map]`. Establish `e` using `congrArg (fun M => Matrix.map M f) h.yy`. Simplify using `only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e`.

Simplify `e` using `only [Matrix.transpose_map, Matrix.map_map]`. Establish `e` using `congrArg (fun M => Matrix.map M f) h.xy`. Simplify using `only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_one f (map_zero f) (map_one f)] at e`. Simplify `e` using `only [Matrix.transpose_map, Matrix.map_map]`.
-/
theorem Dual.map (h : Dual c J X Y) {S' R' : Type} [CommRing S'] [CommRing R'] [Algebra S' R'] {c' : R' →ₐ[S'] R'} (f : R →+* R')
    (hf : ∀ a, f (c a) = c' (f a)) (hc : ∀ a, c' (c' a) = a) : Dual c' (J.map f) (X.map f) (Y.map f) := by
  have hfc : (f : R → R') ∘ c = c' ∘ f := funext hf
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · have e := congrArg (fun M => Matrix.map M f) h.skew
    simp only [Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_neg f (map_neg f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.xx
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.yy
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.xy
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_one f (map_zero f) (map_one f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e

end PositivityTheory.ThKEnd.Two

end
