import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelHaar
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrictStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongrStatement

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Set Matrix
open Formalism.UG (cT cT_mul cT_one)
open scoped NNReal ENNReal Pointwise

namespace CompanionTheory.ThKR.Sieg

variable {R : Type} [CommRing R] {s : R →+* R} {n k : ℕ} {J : Matrix (Fin n) (Fin n) R} {X Y : Matrix (Fin n) (Fin k) R}

section Alg

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => map_add s _ _`.
-/
theorem cT_add {a b : Type} (P Q : Matrix a b R) : cT s (P + Q) = cT s P + cT s Q := Matrix.ext fun _ _ => map_add s _ _

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => map_sub s _ _`.
-/
theorem cT_sub {a b : Type} (P Q : Matrix a b R) : cT s (P - Q) = cT s P - cT s Q := Matrix.ext fun _ _ => map_sub s _ _

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => map_neg s _`.
-/
theorem cT_neg {a b : Type} (P : Matrix a b R) : cT s (-P) = -cT s P := Matrix.ext fun _ _ => map_neg s _

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => map_zero s`.
-/
theorem cT_zero {a b : Type} : cT s (0 : Matrix a b R) = 0 := Matrix.ext fun _ _ => map_zero s

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => map_mul s _ _`.
-/
theorem cT_smul {a b : Type} (c : R) (P : Matrix a b R) : cT s (c • P) = s c • cT s P :=
  Matrix.ext fun _ _ => map_mul s _ _

variable (s J X Y) in

structure Fr : Prop where
  ss : ∀ x, s (s x) = x
  herm : cT s J = J
  xx : cT s X * J * X = 0
  yy : cT s Y * J * Y = 0
  xy : cT s X * J * Y = 1

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => h.ss _`.
-/
theorem Fr.cc (h : Fr s J X Y) {a b : Type} (P : Matrix a b R) : cT s (cT s P) = P := Matrix.ext fun _ _ => h.ss _

/- English proof (translation)
Rewrite using `[cT_mul, cT_mul, h.cc, h.herm, Matrix.mul_assoc]`.
-/
theorem Fr.swap (h : Fr s J X Y) {a b : Type} (P : Matrix (Fin n) a R) (Q : Matrix (Fin n) b R) :
    cT s (cT s P * J * Q) = cT s Q * J * P := by
  rw [cT_mul, cT_mul, h.cc, h.herm, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[← h.swap, h.xy, cT_one]`.
-/
theorem Fr.yx (h : Fr s J X Y) : cT s Y * J * X = 1 := by rw [← h.swap, h.xy, cT_one]

/- English proof (translation)
Rewrite using `[← h.swap, e, cT_zero]`.
-/
theorem Fr.zero (h : Fr s J X Y) {a b : Type} {P : Matrix (Fin n) a R} {Q : Matrix (Fin n) b R}
    (e : cT s P * J * Q = 0) : cT s Q * J * P = 0 := by rw [← h.swap, e, cT_zero]

/- English proof (translation)
Use `conv_rhs => rw [← hg]`. Simplify using `only [cT_mul, Matrix.mul_assoc]`.
-/
theorem gram_unitary {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * J * g = J) {a b : Type} (P : Matrix (Fin n) a R)
    (Q : Matrix (Fin n) b R) : cT s (g * P) * J * (g * Q) = cT s P * J * Q := by
  conv_rhs => rw [← hg]
  simp only [cT_mul, Matrix.mul_assoc]

/- English proof (translation)
Establish `h1 : cT s B * (cT s X * J * g) = cT s X * J`. Use `gram_unitary hg X (1 : Matrix (Fin n) (Fin n) R)` as an intermediate fact. Rewrite `this` using `[hB, cT_mul, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s X)]`. Then use the resulting hypothesis. Establish `h2 : cT s B * (cT s X * J * (g * Y)) = 1`. Rewrite using `[← Matrix.mul_assoc (cT s X * J), ← Matrix.mul_assoc, h1, h.xy]`.

Establish `h3` using `mul_eq_one_comm.1 h2`. Use `⟨by rw [hB, ← Matrix.mul_assoc, h.yx, Matrix.one_mul], h2, h3, ?_⟩` and prove the remaining obligations. Use `conv_rhs => enter [2]`. Rewrite using `[← h1]`. Rewrite using `[← Matrix.mul_assoc _ (cT s B), h3, Matrix.one_mul]`.
-/
theorem Fr.par (h : Fr s J X Y) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * J * g = J) {B : Matrix (Fin k) (Fin k) R}
    (hB : g * X = X * B) : cT s Y * J * (g * X) = B ∧ cT s B * (cT s X * J * (g * Y)) = 1 ∧
      cT s X * J * (g * Y) * cT s B = 1 ∧ cT s X * J * g = cT s X * J * (g * Y) * (cT s X * J) := by
  have h1 : cT s B * (cT s X * J * g) = cT s X * J := by
    have := gram_unitary hg X (1 : Matrix (Fin n) (Fin n) R)
    rwa [hB, cT_mul, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s X)] at this
  have h2 : cT s B * (cT s X * J * (g * Y)) = 1 := by
    rw [← Matrix.mul_assoc (cT s X * J), ← Matrix.mul_assoc, h1, h.xy]
  have h3 := mul_eq_one_comm.1 h2
  refine ⟨by rw [hB, ← Matrix.mul_assoc, h.yx, Matrix.one_mul], h2, h3, ?_⟩
  conv_rhs => enter [2]; rw [← h1]
  rw [← Matrix.mul_assoc _ (cT s B), h3, Matrix.one_mul]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.ss, h.herm, h.yy, h.xx, h.yx⟩`.
-/
theorem Fr.symm (h : Fr s J X Y) : Fr s J Y X := ⟨h.ss, h.herm, h.yy, h.xx, h.yx⟩

/- English proof (translation)
Use `h3 (1 - X * (cT s Y * J) - Y * (cT s X * J)) (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xx, h.xy]; simp) (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx]; simp)` as an intermediate fact. Simplify `this` using `only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h1, h2, Matrix.mul_one, sub_left_inj]`.
-/
theorem Fr.ext (h : Fr s J X Y) {g g' : Matrix (Fin n) (Fin n) R} (h1 : g * X = g' * X) (h2 : g * Y = g' * Y)
    (h3 : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → cT s Y * J * Z = 0 → g * Z = g' * Z) : g = g' := by
  have := h3 (1 - X * (cT s Y * J) - Y * (cT s X * J))
    (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xx, h.xy]; simp)
    (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx]; simp)
  simpa only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h1, h2, Matrix.mul_one, sub_left_inj]
    using this

/- English proof (translation)
Use `h.ext ?_ ?_ fun Z h1 h2 => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hB', Matrix.mul_assoc l, hB', ← Matrix.mul_assoc l, hB, Matrix.mul_assoc, Matrix.mul_assoc, e1]`. Rewrite using `[Matrix.mul_assoc, hD, ← Matrix.mul_assoc, hD', Matrix.mul_assoc l, hD', ← Matrix.mul_assoc l, hD, Matrix.mul_assoc, Matrix.mul_assoc, e2]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hb Z h1 h2, hb]`. Rewrite using `[← Matrix.mul_assoc, (h.par hl hB).2.2.2, Matrix.mul_assoc, h1, Matrix.mul_zero]`.

Rewrite using `[← Matrix.mul_assoc, (h.symm.par hl hD).2.2.2, Matrix.mul_assoc, h2, Matrix.mul_zero]`.
-/
theorem Fr.comm (h : Fr s J X Y) {l b : Matrix (Fin n) (Fin n) R} (hl : cT s l * J * l = J)
    {B D B' D' : Matrix (Fin k) (Fin k) R} (hB : l * X = X * B) (hD : l * Y = Y * D) (hB' : b * X = X * B')
    (hD' : b * Y = Y * D') (e1 : B * B' = B' * B) (e2 : D * D' = D' * D)
    (hb : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → cT s Y * J * Z = 0 → b * Z = Z) : b * l = l * b := by
  refine h.ext ?_ ?_ fun Z h1 h2 => ?_
  · rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hB', Matrix.mul_assoc l, hB', ← Matrix.mul_assoc l, hB,
      Matrix.mul_assoc, Matrix.mul_assoc, e1]
  · rw [Matrix.mul_assoc, hD, ← Matrix.mul_assoc, hD', Matrix.mul_assoc l, hD', ← Matrix.mul_assoc l, hD,
      Matrix.mul_assoc, Matrix.mul_assoc, e2]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hb Z h1 h2, hb]
    · rw [← Matrix.mul_assoc, (h.par hl hB).2.2.2, Matrix.mul_assoc, h1, Matrix.mul_zero]
    · rw [← Matrix.mul_assoc, (h.symm.par hl hD).2.2.2, Matrix.mul_assoc, h2, Matrix.mul_zero]

variable (s J X) in

def eich (Z : Matrix (Fin n) (Fin k) R) (c : Matrix (Fin k) (Fin k) R) : Matrix (Fin n) (Fin n) R :=
  1 + Z * (cT s X * J) - X * (cT s Z * J) + X * c * (cT s X * J)

/- English proof (translation)
Simplify using `only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), hU, Matrix.mul_assoc X (cT s Z * J)]`. Simplify using the standard rewrite rules.
-/
theorem Fr.eich_mul_of (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (c : Matrix (Fin k) (Fin k) R) {a : Type}
    {U : Matrix (Fin n) a R} (hU : cT s X * J * U = 0) : eich s J X Z c * U = U - X * (cT s Z * J * U) := by
  simp only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), hU, Matrix.mul_assoc X (cT s Z * J)]
  simp

/- English proof (translation)
Rewrite using `[h.eich_mul_of c h.xx, h.zero hZ]`. Simplify using the standard rewrite rules.
-/
theorem Fr.eich_X (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s X * J * Z = 0) (c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z c * X = X := by rw [h.eich_mul_of c h.xx, h.zero hZ]; simp

/- English proof (translation)
Simplify using `only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), h.xy, Matrix.mul_assoc X (cT s Z * J), h.zero hZ]`. Simplify using the standard rewrite rules.
-/
theorem Fr.eich_Y (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s Y * J * Z = 0) (c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z c * Y = Y + Z + X * c := by
  simp only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), h.xy, Matrix.mul_assoc X (cT s Z * J),
    h.zero hZ]
  simp

/- English proof (translation)
Use `conv_lhs => rw [show eich s J X Z c = 1 + _ - _ + _ from rfl]`. Simplify using `only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc (eich s J X Z₀ c₀), Matrix.mul_assoc X c, h.eich_X h₀, h.eich_mul_of c₀ hZ]`. Simplify using `only [eich, cT_add, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem Fr.eich_mul (h : Fr s J X Y) {Z₀ Z : Matrix (Fin n) (Fin k) R} (h₀ : cT s X * J * Z₀ = 0) (hZ : cT s X * J * Z = 0)
    (c₀ c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z₀ c₀ * eich s J X Z c = eich s J X (Z₀ + Z) (c₀ + c - cT s Z₀ * J * Z) := by
  conv_lhs => rw [show eich s J X Z c = 1 + _ - _ + _ from rfl]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc (eich s J X Z₀ c₀), Matrix.mul_assoc X c,
    h.eich_X h₀, h.eich_mul_of c₀ hZ]
  simp only [eich, cT_add, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/- English proof (translation)
Simplify using `[eich, cT_zero]`.
-/
theorem eich_zero : eich s J X 0 0 = 1 := by simp [eich, cT_zero]

/- English proof (translation)
Establish `e : cT s (eich s J X Z c) * J = J * eich s J X (-Z) (cT s c)`. Simplify using `only [eich, cT_add, cT_sub, cT_mul, cT_one, cT_neg, h.cc, h.herm, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.mul_assoc, h.eich_mul (by rw [Matrix.mul_neg, hZ, neg_zero]) hZ, cT_neg, Matrix.neg_mul, Matrix.neg_mul, sub_neg_eq_add, hc, neg_add_cancel, eich_zero, Matrix.mul_one]`.
-/
theorem Fr.eich_unitary (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s X * J * Z = 0)
    {c : Matrix (Fin k) (Fin k) R} (hc : cT s c + c + cT s Z * J * Z = 0) :
    cT s (eich s J X Z c) * J * eich s J X Z c = J := by
  have e : cT s (eich s J X Z c) * J = J * eich s J X (-Z) (cT s c) := by
    simp only [eich, cT_add, cT_sub, cT_mul, cT_one, cT_neg, h.cc, h.herm, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul,
      Matrix.sub_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e, Matrix.mul_assoc, h.eich_mul (by rw [Matrix.mul_neg, hZ, neg_zero]) hZ, cT_neg, Matrix.neg_mul, Matrix.neg_mul,
    sub_neg_eq_add, hc, neg_add_cancel, eich_zero, Matrix.mul_one]

variable (s J X Y) in

def W1 : AddSubgroup (Matrix (Fin n) (Fin k) R) where
  carrier := {Z | cT s X * J * Z = 0 ∧ cT s Y * J * Z = 0}
  zero_mem' := by simp
  add_mem' ha hb := ⟨by rw [Matrix.mul_add, ha.1, hb.1, add_zero], by rw [Matrix.mul_add, ha.2, hb.2, add_zero]⟩
  neg_mem' ha := ⟨by rw [Matrix.mul_neg, ha.1, neg_zero], by rw [Matrix.mul_neg, ha.2, neg_zero]⟩

variable (s k) in

def W2 : AddSubgroup (Matrix (Fin k) (Fin k) R) where
  carrier := {c | cT s c = -c}
  zero_mem' := by simp [cT_zero]
  add_mem' {a b} (ha : cT s a = -a) (hb : cT s b = -b) := show cT s _ = _ by rw [cT_add, ha, hb, neg_add]
  neg_mem' {a} (ha : cT s a = -a) := show cT s _ = _ by rw [cT_neg, ha]

variable [Invertible (2 : R)]

/- English proof (translation)
Establish `: s ⅟2 * 2 = 1`. Use `congrArg s (invOf_mul_self (2 : R))` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, map_ofNat]`. Then use the resulting hypothesis. Conclude with `(invOf_eq_left_inv this).symm`.
-/
theorem s_half : s ⅟2 = ⅟2 := by
  have : s ⅟2 * 2 = 1 := by
    have := congrArg s (invOf_mul_self (2 : R))
    rwa [map_mul, map_one, map_ofNat] at this
  exact (invOf_eq_left_inv this).symm

/- English proof (translation)
Rewrite using `[← add_smul, invOf_two_add_invOf_two, one_smul]`.
-/
theorem half_add {a b : Type} (P : Matrix a b R) : (⅟2 : R) • P + (⅟2 : R) • P = P := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

def Fr.β (h : Fr s J X Y) : W1 s J X Y →+ W1 s J X Y →+ W2 s k :=
  AddMonoidHom.mk' (fun Z₀ => AddMonoidHom.mk' (fun Z =>
    ⟨(⅟2 : R) • (cT s Z.1 * J * Z₀.1 - cT s Z₀.1 * J * Z.1), show cT s _ = _ by
      rw [cT_smul, s_half, cT_sub, h.swap, h.swap, ← smul_neg, neg_sub]⟩)
    fun a b => Subtype.ext (by
      simp only [AddSubgroup.coe_add, cT_add, Matrix.add_mul, Matrix.mul_add, smul_add, smul_sub]; abel))
    fun a b => AddMonoidHom.ext fun c => Subtype.ext (by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, AddSubgroup.coe_add, cT_add, Matrix.add_mul,
        Matrix.mul_add, smul_add, smul_sub]; abel)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Fr.β_val (h : Fr s J X Y) (Z₀ Z : W1 s J X Y) :
    (h.β Z₀ Z).1 = (⅟2 : R) • (cT s Z.1 * J * Z₀.1 - cT s Z₀.1 * J * Z.1) := rfl

def Fr.nMat (h : Fr s J X Y) : Heis h.β →* Matrix (Fin n) (Fin n) R where
  toFun x := eich s J X x.1.1 (x.2.1 - (⅟2 : R) • (cT s x.1.1 * J * x.1.1))
  map_one' := by
    change eich s J X 0 (0 - (⅟2 : R) • (cT s (0 : Matrix (Fin n) (Fin k) R) * J * 0)) = 1
    simp [eich_zero]
  map_mul' x y := by
    have key : ∀ (Z₀ Z : Matrix (Fin n) (Fin k) R) (c₀ c : Matrix (Fin k) (Fin k) R),
        c₀ + c + (⅟2 : R) • (cT s Z * J * Z₀ - cT s Z₀ * J * Z) - (⅟2 : R) • (cT s (Z₀ + Z) * J * (Z₀ + Z)) =
          c₀ - (⅟2 : R) • (cT s Z₀ * J * Z₀) + (c - (⅟2 : R) • (cT s Z * J * Z)) - cT s Z₀ * J * Z := fun Z₀ Z c₀ c => by
      simp only [cT_add, Matrix.add_mul, Matrix.mul_add, smul_add, smul_sub]
      have := half_add (cT s Z₀ * J * Z)
      generalize (⅟2 : R) • (cT s Z₀ * J * Z) = m at this ⊢
      rw [← this]
      abel
    rw [h.eich_mul x.1.2.1 y.1.2.1]
    exact congrArg (eich s J X (x.1.1 + y.1.1)) (key x.1.1 y.1.1 x.2.1 y.2.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Fr.nMat_apply (h : Fr s J X Y) (x : Heis h.β) :
    h.nMat x = eich s J X x.1.1 (x.2.1 - (⅟2 : R) • (cT s x.1.1 * J * x.1.1)) := rfl

/- English proof (translation)
The claim follows from `h.eich_unitary x.1.2.1 (by rw [cT_sub, cT_smul, s_half, h.swap, show cT s x.2.1 = -x.2.1 from x.2.2] conv_lhs => enter [2]; rw [← half_add (cT s x.1.1 * J * x.1.1)] abel)`.
-/
theorem Fr.nMat_unitary (h : Fr s J X Y) (x : Heis h.β) : cT s (h.nMat x) * J * h.nMat x = J :=
  h.eich_unitary x.1.2.1 (by
    rw [cT_sub, cT_smul, s_half, h.swap, show cT s x.2.1 = -x.2.1 from x.2.2]
    conv_lhs => enter [2]; rw [← half_add (cT s x.1.1 * J * x.1.1)]
    abel)

/- English proof (translation)
Establish `e1` using `congrArg (cT s Y * J * ·) e`. Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc _ X, h.yx, hZ, hZ', Matrix.one_mul] at e1`. Take `rfl` from `add_left_cancel e1`. Conclude with `⟨by simpa using e, rfl⟩`.
-/
theorem Fr.decomp_inj (h : Fr s J X Y) {Z Z' : Matrix (Fin n) (Fin k) R} (hZ : cT s Y * J * Z = 0) (hZ' : cT s Y * J * Z' = 0)
    {c c' : Matrix (Fin k) (Fin k) R} (e : Y + Z + X * c = Y + Z' + X * c') : Z = Z' ∧ c = c' := by
  have e1 := congrArg (cT s Y * J * ·) e
  simp only [Matrix.mul_add, ← Matrix.mul_assoc _ X, h.yx, hZ, hZ', Matrix.one_mul] at e1
  obtain rfl := add_left_cancel e1
  exact ⟨by simpa using e, rfl⟩

/- English proof (translation)
Rewrite `e` using `[h.nMat_apply, h.nMat_apply, h.eich_Y x.1.2.2, h.eich_Y y.1.2.2]`. Take `⟨e1, e2⟩` from `h.decomp_inj x.1.2.2 y.1.2.2 e`. Rewrite `e2` using `[e1, sub_left_inj]`. Conclude with `Prod.ext (Subtype.ext e1) (Subtype.ext e2)`.
-/
theorem Fr.nMat_inj (h : Fr s J X Y) {x y : Heis h.β} (e : h.nMat x * Y = h.nMat y * Y) : x = y := by
  rw [h.nMat_apply, h.nMat_apply, h.eich_Y x.1.2.2, h.eich_Y y.1.2.2] at e
  obtain ⟨e1, e2⟩ := h.decomp_inj x.1.2.2 y.1.2.2 e
  rw [e1, sub_left_inj] at e2
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

def Fr.pt (h : Fr s J X Y) (W : Matrix (Fin n) (Fin k) R) (h1 : cT s X * J * W = 1) (h2 : cT s W * J * W = 0) : Heis h.β :=
  (⟨W - Y - X * (cT s Y * J * W),
    by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, h1, h.xy, h.xx]; simp,
    by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, h.yy, h.yx]; simp⟩,
   ⟨(⅟2 : R) • (cT s Y * J * W - cT s W * J * Y), show cT s _ = _ by
      rw [cT_smul, s_half, cT_sub, h.swap, h.swap, ← smul_neg, neg_sub]⟩)

/- English proof (translation)
Rewrite using `[h.nMat_apply, h.eich_Y (h.pt W h1 h2).1.2.2]`. Establish `h3 : cT s W * J * X = 1` using `by rw [← h.swap, h1, cT_one]`. Establish `e : cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)) = -(cT s Y * J * W) - cT s W * J * Y`. Rewrite using `[cT_sub, cT_sub, cT_mul, h.swap]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc (cT s W * J * Y), ← Matrix.mul_assoc _ X, h1, h2, h3, h.xx, h.xy, h.yx, h.yy]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `Y + (W - Y - X * (cT s Y * J * W)) + X * ((⅟2 : R) • (cT s Y * J * W - cT s W * J * Y) - (⅟2 : R) • (cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)))) = W`. Rewrite using `[e, ← smul_sub, show cT s Y * J * W - cT s W * J * Y - (-(cT s Y * J * W) - cT s W * J * Y) = cT s Y * J * W + cT s Y * J * W by abel, smul_add, half_add]`. Normalize the expressions using the abelian group laws.
-/
theorem Fr.nMat_pt (h : Fr s J X Y) (W : Matrix (Fin n) (Fin k) R) (h1 : cT s X * J * W = 1) (h2 : cT s W * J * W = 0) :
    h.nMat (h.pt W h1 h2) * Y = W := by
  rw [h.nMat_apply, h.eich_Y (h.pt W h1 h2).1.2.2]
  have h3 : cT s W * J * X = 1 := by rw [← h.swap, h1, cT_one]
  have e : cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)) =
      -(cT s Y * J * W) - cT s W * J * Y := by
    rw [cT_sub, cT_sub, cT_mul, h.swap]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc (cT s W * J * Y), ← Matrix.mul_assoc _ X, h1, h2, h3,
      h.xx, h.xy, h.yx, h.yy]
    simp
  change Y + (W - Y - X * (cT s Y * J * W)) + X * ((⅟2 : R) • (cT s Y * J * W - cT s W * J * Y) -
    (⅟2 : R) • (cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)))) = W
  rw [e, ← smul_sub, show cT s Y * J * W - cT s W * J * Y - (-(cT s Y * J * W) - cT s W * J * Y) =
    cT s Y * J * W + cT s Y * J * W by abel, smul_add, half_add]
  abel

end Alg

section Top

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]

instance lcMat (a b : ℕ) : LocallyCompactSpace (Matrix (Fin a) (Fin b) R) :=
  inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → R))

instance scMat (a b : ℕ) : SecondCountableTopology (Matrix (Fin a) (Fin b) R) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → R))

instance scSub {a b : ℕ} (W : AddSubgroup (Matrix (Fin a) (Fin b) R)) : SecondCountableTopology W :=
  TopologicalSpace.Subtype.secondCountableTopology (W : Set (Matrix (Fin a) (Fin b) R))

omit [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
/- English proof (translation)
The claim follows from `(hf.matrix_map hs).matrix_transpose`.
-/
theorem continuous_cT (hs : Continuous s) {a b T : Type} [TopologicalSpace T] {f : T → Matrix a b R} (hf : Continuous f) :
    Continuous fun x => cT s (f x) := (hf.matrix_map hs).matrix_transpose

omit [LocallyCompactSpace R] [SecondCountableTopology R] in
/- English proof (translation)
The claim follows from `(isClosed_eq (continuous_const.matrix_mul continuous_id) continuous_const).inter (isClosed_eq (continuous_const.matrix_mul continuous_id) continuous_const)`.
-/
theorem isClosed_frame_annihilator : IsClosed (W1 s J X Y : Set (Matrix (Fin n) (Fin k) R)) :=
  (isClosed_eq (continuous_const.matrix_mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_const.matrix_mul continuous_id) continuous_const)

omit [LocallyCompactSpace R] [SecondCountableTopology R] in
/- English proof (translation)
The claim follows from `isClosed_eq (continuous_cT hs continuous_id) continuous_neg`.
-/
theorem isClosed_skew_hermitian (hs : Continuous s) : IsClosed (W2 s k : Set (Matrix (Fin k) (Fin k) R)) :=
  isClosed_eq (continuous_cT hs continuous_id) continuous_neg

def scal {a b : ℕ} (W : AddSubgroup (Matrix (Fin a) (Fin b) R)) (u : Rˣ) (h : ∀ x ∈ W, u.1 • x ∈ W)
    (h' : ∀ x ∈ W, u⁻¹.1 • x ∈ W) : W ≃ₜ+ W where
  toFun x := ⟨u.1 • x.1, h _ x.2⟩
  invFun x := ⟨u⁻¹.1 • x.1, h' _ x.2⟩
  left_inv x := Subtype.ext (by simp [smul_smul])
  right_inv x := Subtype.ext (by simp [smul_smul])
  map_add' x y := Subtype.ext (smul_add _ _ _)
  continuous_toFun := (continuous_subtype_val.const_smul u.1).subtype_mk _
  continuous_invFun := (continuous_subtype_val.const_smul u⁻¹.1).subtype_mk _

def scalM (a b : ℕ) (u : Rˣ) : Matrix (Fin a) (Fin b) R ≃ₜ+ Matrix (Fin a) (Fin b) R where
  toFun x := u.1 • x
  invFun x := u⁻¹.1 • x
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]
  map_add' x y := smul_add _ _ _
  continuous_toFun := continuous_id.const_smul u.1
  continuous_invFun := continuous_id.const_smul u⁻¹.1

@[reducible] def msMat (a b : ℕ) : MeasurableSpace (Matrix (Fin a) (Fin b) R) := borel _

attribute [local instance] msMat

local instance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) R) := ⟨rfl⟩

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [Matrix.mul_smul, hx.1, smul_zero], by rw [Matrix.mul_smul, hx.2, smul_zero]⟩`.
-/
theorem smul_mem_frame_annihilator (c : R) (x) (hx : x ∈ W1 s J X Y) : c • x ∈ W1 s J X Y :=
  ⟨by rw [Matrix.mul_smul, hx.1, smul_zero], by rw [Matrix.mul_smul, hx.2, smul_zero]⟩

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
/- English proof (translation)
The claim follows from `show cT s _ = _ by rw [cT_smul, hc, show cT s x = -x from hx, smul_neg]`.
-/
theorem smul_mem_skew_hermitian {c : R} (hc : s c = c) (x) (hx : x ∈ W2 s k) : c • x ∈ W2 s k :=
  show cT s _ = _ by rw [cT_smul, hc, show cT s x = -x from hx, smul_neg]

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
/- English proof (translation)
The claim follows from `(Units.inv_eq_of_mul_eq_one_right (by rw [← hu, ← map_mul, Units.mul_inv, map_one])).symm`.
-/
theorem s_inv {u : Rˣ} (hu : s u = u) : s u⁻¹.1 = u⁻¹.1 :=
  (Units.inv_eq_of_mul_eq_one_right (by rw [← hu, ← map_mul, Units.mul_inv, map_one])).symm

/- English proof (translation)
Rewrite using `[← GlobalTheory.T.addEquivAddHaarChar_prodCongr, ← GlobalTheory.T.addEquivAddHaarChar_prodCongr]`. Set `e : (W1 s J X Y × Matrix (Fin k) (Fin k) R × Matrix (Fin k) (Fin k) R) ≃ₜ+ Matrix (Fin n) (Fin k) R` to `{ toFun := fun p => p.1.1 + X * p.2.1 + Y * p.2.2 invFun := fun U => (⟨U - X * (cT s Y * J * U) - Y * (cT s X * J * U), by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xy, h.xx]; simp, by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix. …`. Establish `e1 : cT s Y * J * (p.1.1 + X * p.2.1 + Y * p.2.2) = p.2.1`. Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx, p.1.2.2]`. Simplify using the standard rewrite rules.

Establish `e2 : cT s X * J * (p.1.1 + X * p.2.1 + Y * p.2.2) = p.2.2`. Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xy, h.xx, p.1.2.1]`. Simplify using the standard rewrite rules. Use `Prod.ext (Subtype.ext ?_) (Prod.ext e1 e2)` and prove the remaining obligations. Simplify using `only [e1, e2]`.

Normalize the expressions using the abelian group laws. Use `right_inv := fun U => by simp only; abel`. Use the proof step `map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, Matrix.mul_add]; abel`. Use `continuous_toFun := ((continuous_subtype_val.comp continuous_fst).add (continuous_const.matrix_mul continuous_snd.fst)).add (continuous_const.matrix_mul continuous_snd.snd)`. Use `continuous_invFun := (((continuous_id.sub (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id))).sub (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id))).subtype_mk _).prodMk ((continuous_const.matrix_mul continuous_id).prodMk (continuous …`.

Use `GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ e.toAddMonoidHom e.toHomeomorph.isOpenEmbedding _ _ fun p => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 • (p.1.1 + X * p.2.1 + Y * p.2.2) = u.1 • p.1.1 + X * (u.1 • p.2.1) + Y * (u.1 • p.2.2)`. Simplify using `only [smul_add, Matrix.mul_smul]`.
-/
theorem haar_character_frame_annihilator (h : Fr s J X Y) [LocallyCompactSpace (W1 s J X Y)] (u : Rˣ) :
    addEquivAddHaarChar (scalM n k u) = addEquivAddHaarChar (scal (W1 s J X Y) u (smul_mem_frame_annihilator _) (smul_mem_frame_annihilator _)) *
      (addEquivAddHaarChar (scalM k k u) * addEquivAddHaarChar (scalM k k u)) := by
  rw [← GlobalTheory.T.addEquivAddHaarChar_prodCongr, ← GlobalTheory.T.addEquivAddHaarChar_prodCongr]
  let e : (W1 s J X Y × Matrix (Fin k) (Fin k) R × Matrix (Fin k) (Fin k) R) ≃ₜ+ Matrix (Fin n) (Fin k) R :=
    { toFun := fun p => p.1.1 + X * p.2.1 + Y * p.2.2
      invFun := fun U => (⟨U - X * (cT s Y * J * U) - Y * (cT s X * J * U),
        by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xy, h.xx]; simp,
        by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx]; simp⟩,
        cT s Y * J * U, cT s X * J * U)
      left_inv := fun p => by
        have e1 : cT s Y * J * (p.1.1 + X * p.2.1 + Y * p.2.2) = p.2.1 := by
          simp only [Matrix.mul_add, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx, p.1.2.2]; simp
        have e2 : cT s X * J * (p.1.1 + X * p.2.1 + Y * p.2.2) = p.2.2 := by
          simp only [Matrix.mul_add, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xy, h.xx, p.1.2.1]; simp
        refine Prod.ext (Subtype.ext ?_) (Prod.ext e1 e2)
        simp only [e1, e2]
        abel
      right_inv := fun U => by simp only; abel
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, Matrix.mul_add]; abel
      continuous_toFun := ((continuous_subtype_val.comp continuous_fst).add
        (continuous_const.matrix_mul continuous_snd.fst)).add (continuous_const.matrix_mul continuous_snd.snd)
      continuous_invFun := (((continuous_id.sub (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id))).sub
        (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id))).subtype_mk _).prodMk
        ((continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id)) }
  refine GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ e.toAddMonoidHom e.toHomeomorph.isOpenEmbedding _ _ fun p => ?_
  change u.1 • (p.1.1 + X * p.2.1 + Y * p.2.2) = u.1 • p.1.1 + X * (u.1 • p.2.1) + Y * (u.1 • p.2.2)
  simp only [smul_add, Matrix.mul_smul]

/- English proof (translation)
Rewrite using `[← GlobalTheory.T.addEquivAddHaarChar_prodCongr]`. Establish `cc : ∀ P : Matrix (Fin k) (Fin k) R, cT s (cT s P) = P` using `fun P => Matrix.ext fun _ _ => hss _`. Establish `hω' : s ω⁻¹.1 = -ω⁻¹.1`. Establish `: s ω⁻¹.1 * ω = -1` using `by rw [← neg_neg ω.1, ← hω, mul_neg, ← map_mul, Units.inv_mul, map_one]`. Rewrite using `[← mul_one (s _), ← ω.mul_inv, ← mul_assoc, this, neg_one_mul]`.

Set `e : (W2 s k × W2 s k) ≃ₜ+ Matrix (Fin k) (Fin k) R` to `{ toFun := fun p => p.1.1 + ω.1 • p.2.1 invFun := fun U => (⟨(⅟2 : R) • (U - cT s U), show cT s _ = _ by`. Rewrite using `[cT_smul, s_half, cT_sub, cc, ← smul_neg, neg_sub]⟩,`. Use the proof step `⟨ω⁻¹.1 • (⅟2 : R) • (U + cT s U), show cT s _ = _ by`. Rewrite using `[cT_smul, cT_smul, s_half, cT_add, cc, hω', neg_smul, add_comm]⟩)`. Use `left_inv := fun p => by`.

Establish `e1 : cT s (p.1.1 + ω.1 • p.2.1) = -p.1.1 + ω.1 • p.2.1`. Rewrite using `[cT_add, cT_smul, hω, show cT s p.1.1 = -p.1.1 from p.1.2, show cT s p.2.1 = -p.2.1 from p.2.2, neg_smul_neg]`. Use `Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `only [e1]`. Rewrite using `[show p.1.1 + ω.1 • p.2.1 - (-p.1.1 + ω.1 • p.2.1) = p.1.1 + p.1.1 by abel, smul_add, half_add]`.

Simplify using `only [e1]`. Rewrite using `[show p.1.1 + ω.1 • p.2.1 + (-p.1.1 + ω.1 • p.2.1) = ω.1 • p.2.1 + ω.1 • p.2.1 by abel, smul_add, half_add, smul_smul, Units.inv_mul, one_smul]`. Use `right_inv := fun U => by`. Simplify using `only [smul_smul ω.1, Units.mul_inv, one_smul, ← smul_add]`. Rewrite using `[show U - cT s U + (U + cT s U) = U + U by abel, smul_add, half_add]`.

Use the proof step `map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]; abel`. Use `continuous_toFun := (continuous_subtype_val.comp continuous_fst).add ((continuous_subtype_val.comp continuous_snd).const_smul ω.1)`. Use `continuous_invFun := (((continuous_id.sub (continuous_cT hs continuous_id)).const_smul (⅟2 : R)).subtype_mk _).prodMk ((((continuous_id.add (continuous_cT hs continuous_id)).const_smul (⅟2 : R)).const_smul ω⁻¹.1).subtype_mk _) }`. Use `GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ e.toAddMonoidHom e.toHomeomorph.isOpenEmbedding _ _ fun p => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 • (p.1.1 + ω.1 • p.2.1) = u.1 • p.1.1 + ω.1 • u.1 • p.2.1`.

Rewrite using `[smul_add, smul_comm]`.
-/
theorem haar_character_skew_hermitian [Invertible (2 : R)] (hs : Continuous s) (hss : ∀ x, s (s x) = x) [LocallyCompactSpace (W2 s k)]
    (ω : Rˣ) (hω : s ω = -ω) {u : Rˣ} (hu : s u = u) :
    addEquivAddHaarChar (scalM k k u) = addEquivAddHaarChar (scal (W2 s k) u (smul_mem_skew_hermitian hu) (smul_mem_skew_hermitian (s_inv hu))) *
      addEquivAddHaarChar (scal (W2 s k) u (smul_mem_skew_hermitian hu) (smul_mem_skew_hermitian (s_inv hu))) := by
  rw [← GlobalTheory.T.addEquivAddHaarChar_prodCongr]
  have cc : ∀ P : Matrix (Fin k) (Fin k) R, cT s (cT s P) = P := fun P => Matrix.ext fun _ _ => hss _
  have hω' : s ω⁻¹.1 = -ω⁻¹.1 := by
    have : s ω⁻¹.1 * ω = -1 := by rw [← neg_neg ω.1, ← hω, mul_neg, ← map_mul, Units.inv_mul, map_one]
    rw [← mul_one (s _), ← ω.mul_inv, ← mul_assoc, this, neg_one_mul]
  let e : (W2 s k × W2 s k) ≃ₜ+ Matrix (Fin k) (Fin k) R :=
    { toFun := fun p => p.1.1 + ω.1 • p.2.1
      invFun := fun U => (⟨(⅟2 : R) • (U - cT s U), show cT s _ = _ by
          rw [cT_smul, s_half, cT_sub, cc, ← smul_neg, neg_sub]⟩,
        ⟨ω⁻¹.1 • (⅟2 : R) • (U + cT s U), show cT s _ = _ by
          rw [cT_smul, cT_smul, s_half, cT_add, cc, hω', neg_smul, add_comm]⟩)
      left_inv := fun p => by
        have e1 : cT s (p.1.1 + ω.1 • p.2.1) = -p.1.1 + ω.1 • p.2.1 := by
          rw [cT_add, cT_smul, hω, show cT s p.1.1 = -p.1.1 from p.1.2, show cT s p.2.1 = -p.2.1 from p.2.2, neg_smul_neg]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [e1]
          rw [show p.1.1 + ω.1 • p.2.1 - (-p.1.1 + ω.1 • p.2.1) = p.1.1 + p.1.1 by abel, smul_add, half_add]
        · simp only [e1]
          rw [show p.1.1 + ω.1 • p.2.1 + (-p.1.1 + ω.1 • p.2.1) = ω.1 • p.2.1 + ω.1 • p.2.1 by abel, smul_add, half_add,
            smul_smul, Units.inv_mul, one_smul]
      right_inv := fun U => by
        simp only [smul_smul ω.1, Units.mul_inv, one_smul, ← smul_add]
        rw [show U - cT s U + (U + cT s U) = U + U by abel, smul_add, half_add]
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]; abel
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).add
        ((continuous_subtype_val.comp continuous_snd).const_smul ω.1)
      continuous_invFun := (((continuous_id.sub (continuous_cT hs continuous_id)).const_smul (⅟2 : R)).subtype_mk _).prodMk
        ((((continuous_id.add (continuous_cT hs continuous_id)).const_smul (⅟2 : R)).const_smul ω⁻¹.1).subtype_mk _) }
  refine GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ e.toAddMonoidHom e.toHomeomorph.isOpenEmbedding _ _ fun p => ?_
  change u.1 • (p.1.1 + ω.1 • p.2.1) = u.1 • p.1.1 + ω.1 • u.1 • p.2.1
  rw [smul_add, smul_comm]

/- English proof (translation)
Establish `: LocallyCompactSpace (W1 s J X Y)` using `isClosed_frame_annihilator.locallyCompactSpace`. Establish `: LocallyCompactSpace (W2 s k)` using `(isClosed_skew_hermitian hs).locallyCompactSpace`. Establish `c1 : Continuous fun Z : W1 s J X Y => Z.1` using `continuous_subtype_val`. Establish `hβ : Continuous fun p : W1 s J X Y × W1 s J X Y => h.β p.1 p.2` using `(((((continuous_cT hs (c1.comp continuous_snd)).matrix_mul continuous_const).matrix_mul (c1.comp continuous_fst)).sub (((continuous_cT hs (c1.comp continuous_fst)).matrix_mul continuous_const).matrix_mul (c1.comp continuous_snd))).const_smul (⅟2 : R)).subtype_mk fun p => (h.β p.1 …`. Use `Heis.isTopologicalGroup h.β hβ` as an intermediate fact.

Establish `hu2 : s (u * u).1 = (u * u).1` using `by rw [Units.val_mul, map_mul, hu]`. Set `θ₁` to `scal (W1 s J X Y) u (smul_mem_frame_annihilator _) (smul_mem_frame_annihilator _)`. Set `θ` to `scal (W2 s k) u (smul_mem_skew_hermitian hu) (smul_mem_skew_hermitian (s_inv hu))`. Set `θ₂` to `θ.trans θ`. Set `ψ : Heis h.β ≃ₜ* Heis h.β` to `{ toFun := fun x => (θ₁ x.1, θ₂ x.2) invFun := fun x => (θ₁.symm x.1, θ₂.symm x.2) left_inv := fun x => Prod.ext (θ₁.symm_apply_apply _) (θ₂.symm_apply_apply _) right_inv := fun x => Prod.ext (θ₁.apply_symm_apply _) (θ₂.apply_symm_apply _) map_mul' := fun x y => Prod.ext (map_add …`.

Express the relevant statement in the definitionally equal form `u.1 • u.1 • (x.2.1 + y.2.1 + (h.β x.1 y.1).1) = u.1 • u.1 • x.2.1 + u.1 • u.1 • y.2.1 + (h.β (θ₁ x.1) (θ₁ y.1)).1`. Rewrite using `[h.β_val, h.β_val]`. Express the relevant statement in the definitionally equal form `_ = _ + (⅟2 : R) • (cT s (u.1 • y.1.1) * J * (u.1 • x.1.1) - cT s (u.1 • x.1.1) * J * (u.1 • y.1.1))`. Simplify using `only [cT_smul, hu, Matrix.smul_mul, Matrix.mul_smul, smul_add, ← smul_sub, smul_comm (⅟2 : R) u.1]))`. Use `continuous_toFun := θ₁.continuous.prodMap θ₂.continuous`.

Use `continuous_invFun := θ₁.symm.continuous.prodMap θ₂.symm.continuous }`. Use `choose ι₀ hι₀ using hN`. Establish `jinj : ∀ {p q}, (j p).1 = (j q).1 → p = q` using `fun e => hj.injective (Units.ext e)`. Set `ι : Heis h.β →* H` to `MonoidHom.mk' ι₀ fun x y => jinj (by rw [map_mul, Units.val_mul, hι₀, hι₀, hι₀, map_mul])`. Establish `hι : ∀ x, (j (ι x)).1 = h.nMat x` using `hι₀`.

Establish `cn : Continuous h.nMat`. Establish `d1 : Continuous fun x : Heis h.β => x.1.1` using `c1.comp continuous_fst`. Establish `d2 : Continuous fun x : Heis h.β => x.2.1` using `continuous_subtype_val.comp continuous_snd`. Conclude with `((continuous_const.add (d1.matrix_mul continuous_const)).sub (continuous_const.matrix_mul ((continuous_cT hs d1).matrix_mul continuous_const))).add ((continuous_const.matrix_mul (d2.sub ((((continuous_cT hs d1).matrix_mul continuous_const).matrix_mul d1).const_smul (⅟2 : R)))).ma …`. Establish `cι : Continuous ι` using `hj.continuous_iff.2 (Units.continuous_iff.2 ⟨cn.congr fun x => (hι x).symm, (cn.comp continuous_inv).congr fun x => by`.

Rewrite using `[Function.comp, Function.comp, ← map_inv, ← map_inv, hι]⟩)`. Establish `cj : Continuous fun p => (j p).1` using `Units.continuous_val.comp hj.continuous`. Set `B : H → Matrix (Fin k) (Fin k) R` to `fun p => cT s Y * J * ((j p).1 * X)`. Establish `hB : ∀ p, (j p).1 * X = X * B p` using `fun p => by`. Take `⟨B', e⟩` from `hP p`.

Rewrite using `[show B p = B' from (h.par (hU p) e).1, e]`. Set `W : H → Matrix (Fin n) (Fin k) R` to `fun p => (j p).1 * Y * cT s (B p)`. Establish `cW : Continuous W` using `(cj.matrix_mul continuous_const).matrix_mul (continuous_cT hs (continuous_const.matrix_mul (cj.matrix_mul continuous_const)))`. Establish `W1' : ∀ p, cT s X * J * W p = 1` using `fun p => by rw [← Matrix.mul_assoc, (h.par (hU p) (hB p)).2.2.1]`. Establish `W2' : ∀ p, cT s (W p) * J * W p = 0` using `fun p => by`.

Simplify using `only [W]`. Rewrite using `[Matrix.mul_assoc (j p).1, gram_unitary (hU p), cT_mul, Matrix.mul_assoc _ (cT s Y), ← Matrix.mul_assoc, Matrix.mul_assoc _ _ Y, h.yy]`. Simplify using the standard rewrite rules. Set `π : H → Heis h.β` to `fun p => h.pt (W p) (W1' p) (W2' p)`. Establish `hπ : ∀ p, h.nMat (π p) * Y = W p` using `fun p => h.nMat_pt _ _ _`.

Establish `cπ : Continuous π` using `(((cW.sub continuous_const).sub (continuous_const.matrix_mul (continuous_const.matrix_mul cW))).subtype_mk _).prodMk ((((continuous_const.matrix_mul cW).sub (((continuous_cT hs cW).matrix_mul continuous_const).matrix_mul continuous_const)).const_smul (⅟2 : R)).subtype_mk _)`. Establish `nX : ∀ x, h.nMat x * X = X` using `fun x => h.eich_X x.1.2.1 _`. Establish `Beq : ∀ p B', (j p).1 * X = X * B' → B p = B'` using `fun p B' e => (h.par (hU p) e).1`. Establish `bb : (j b).1 * (j b⁻¹).1 = 1` using `by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`. Establish `bb' : (j b⁻¹).1 * (j b).1 = 1` using `mul_eq_one_comm.1 bb`.

Establish `bX' : (j b⁻¹).1 * X = u⁻¹.1 • X`. Use `congrArg (fun M => u⁻¹.1 • (j b⁻¹).1 * M) bX` as an intermediate fact. Simplify `this.symm` using `[← Matrix.mul_assoc, bb', smul_smul]`. Establish `bY' : (j b⁻¹).1 * Y = u.1 • Y`. Use `congrArg (fun M => u.1 • (j b⁻¹).1 * M) bY` as an intermediate fact.

Simplify `this.symm` using `[← Matrix.mul_assoc, bb', smul_smul]`. Establish `bJ : ∀ Z : Matrix (Fin n) (Fin k) R, cT s Z * J * (j b⁻¹).1 = cT s ((j b).1 * Z) * J` using `fun Z => by`. Rewrite using `[← gram_unitary (hU b) Z, bb, Matrix.mul_one]`. Establish `hφι : ∀ x, φ (ι x) = ι (ψ x)` using `fun x => jinj (by`. Rewrite using `[hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, hι, hι, h.nMat_apply, h.nMat_apply]`.

Express the relevant statement in the definitionally equal form `_ = eich s J X (u.1 • x.1.1) (u.1 • u.1 • x.2.1 - (⅟2 : R) • (cT s (u.1 • x.1.1) * J * (u.1 • x.1.1)))`. Simplify using `only [eich, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub (j b).1, Matrix.sub_mul _ _ (j b⁻¹).1, Matrix.mul_one, bb, ← Matrix.mul_assoc (j b).1, bX, bZ _ _ x.1.2.1 x.1.2.2, cT_smul, hu, Matrix.smul_mul, Matrix.mul_smul, smul_comm (⅟2 : R) u.1, ← smul_sub]`. Establish `e1 : cT s X * J * (j b⁻¹).1 = u.1 • (cT s X * J)` using `by rw [bJ, bX, cT_smul, hu, Matrix.smul_mul]`. Establish `e2 : cT s x.1.1 * J * (j b⁻¹).1 = cT s x.1.1 * J` using `by rw [bJ, bZ _ _ x.1.2.1 x.1.2.2]`. Rewrite using `[Matrix.mul_assoc x.1.1 (cT s X * J), Matrix.mul_assoc X (cT s x.1.1 * J), Matrix.mul_assoc _ (cT s X * J) (j b⁻¹).1, e1, e2]`.

Simplify using `only [Matrix.mul_smul])`. Establish `h1 : ∀ p, π (φ p) = ψ (π p)` using `fun p => h.nMat_inj (by`. Establish `e : B (φ p) = B p` using `Beq _ _ (by`. Rewrite using `[hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, bX', Matrix.mul_smul, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, bX, Matrix.smul_mul, smul_smul, Units.inv_mul, one_smul])`. Rewrite using `[hπ, ← hι, ← hφι, hφ (ι _), map_mul, map_mul, Units.val_mul, Units.val_mul, hι, Matrix.mul_assoc, bY', Matrix.mul_smul, Matrix.mul_assoc, hπ]`.

Simplify using `only [W]`. Rewrite using `[e, hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc _ _ Y, bY']`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc])`. Establish `key` using `char_eq_of_retract ι cι π cπ (fun x p => h.nMat_inj (by`. Establish `e : B (ι x * p) = B p` using `Beq _ _ (by`.

Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hι, nX])`. Rewrite using `[hπ, map_mul, Matrix.mul_assoc, hπ]`. Simplify using `only [W]`. Rewrite using `[e, map_mul, Units.val_mul, hι]`. Simplify using `only [Matrix.mul_assoc])) φ ψ h1 (fun p => by`.

Rewrite using `[h1, ← hφι, ← map_inv φ, ← map_mul φ, hφ, mul_inv_eq_iff_eq_mul]`. Apply `jinj` to reduce the goal to its premises. Rewrite using `[map_mul j b, map_mul j _ b, Units.val_mul, Units.val_mul]`. Use `h.comm (hU _) (hB _) (D := cT s X * J * ((j p).1 * Y)) ?_ (B' := u.1 • 1) (D' := u⁻¹.1 • 1) (by simp [bX]) (by simp [bY]) (by simp) (by simp) (bZ n)` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc, ← map_inv, hι]`.

Establish `e : (j p).1 * Y = h.nMat (π p) * Y * (cT s X * J * ((j p).1 * Y))`. Rewrite using `[hπ, Matrix.mul_assoc, (h.par (hU p) (hB p)).2.1, Matrix.mul_one]`. Use `conv_lhs => rw [e]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc _ (h.nMat _) Y, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul])`. Rewrite using `[key, Heis.char_eq h.β hβ ψ θ₁ θ₂ fun _ => rfl, haar_character_frame_annihilator h u, addEquivAddHaarChar_trans, ← haar_character_skew_hermitian hs h.ss ω hω hu, mul_assoc]`.
-/
theorem char_conj [Invertible (2 : R)] (h : Fr s J X Y) (hs : Continuous s) (ω : Rˣ) (hω : s ω = -ω) {u : Rˣ} (hu : s u = u)
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (j : H →* GL (Fin n) R)
    (hj : IsEmbedding j) (hU : ∀ p, cT s (j p).1 * J * (j p).1 = J) (hP : ∀ p, ∃ B : Matrix (Fin k) (Fin k) R, (j p).1 * X = X * B)
    (hN : ∀ x, ∃ p, (j p).1 = h.nMat x) (b : H) (bX : (j b).1 * X = u.1 • X) (bY : (j b).1 * Y = u⁻¹.1 • Y)
    (bZ : ∀ (m : ℕ) (Z : Matrix (Fin n) (Fin m) R), cT s X * J * Z = 0 → cT s Y * J * Z = 0 → (j b).1 * Z = Z)
    (φ : H ≃ₜ* H) (hφ : ∀ p, φ p = b * p * b⁻¹) :
    mulEquivHaarChar φ * addEquivAddHaarChar (scalM k k u) = addEquivAddHaarChar (scalM n k u) := by
  have : LocallyCompactSpace (W1 s J X Y) := isClosed_frame_annihilator.locallyCompactSpace
  have : LocallyCompactSpace (W2 s k) := (isClosed_skew_hermitian hs).locallyCompactSpace
  have c1 : Continuous fun Z : W1 s J X Y => Z.1 := continuous_subtype_val
  have hβ : Continuous fun p : W1 s J X Y × W1 s J X Y => h.β p.1 p.2 :=
    (((((continuous_cT hs (c1.comp continuous_snd)).matrix_mul continuous_const).matrix_mul (c1.comp continuous_fst)).sub
      (((continuous_cT hs (c1.comp continuous_fst)).matrix_mul continuous_const).matrix_mul
        (c1.comp continuous_snd))).const_smul (⅟2 : R)).subtype_mk fun p => (h.β p.1 p.2).2
  have := Heis.isTopologicalGroup h.β hβ
  have hu2 : s (u * u).1 = (u * u).1 := by rw [Units.val_mul, map_mul, hu]
  let θ₁ := scal (W1 s J X Y) u (smul_mem_frame_annihilator _) (smul_mem_frame_annihilator _)
  let θ := scal (W2 s k) u (smul_mem_skew_hermitian hu) (smul_mem_skew_hermitian (s_inv hu))
  let θ₂ := θ.trans θ
  let ψ : Heis h.β ≃ₜ* Heis h.β :=
    { toFun := fun x => (θ₁ x.1, θ₂ x.2)
      invFun := fun x => (θ₁.symm x.1, θ₂.symm x.2)
      left_inv := fun x => Prod.ext (θ₁.symm_apply_apply _) (θ₂.symm_apply_apply _)
      right_inv := fun x => Prod.ext (θ₁.apply_symm_apply _) (θ₂.apply_symm_apply _)
      map_mul' := fun x y => Prod.ext (map_add θ₁ _ _) (Subtype.ext (by
        change u.1 • u.1 • (x.2.1 + y.2.1 + (h.β x.1 y.1).1) =
          u.1 • u.1 • x.2.1 + u.1 • u.1 • y.2.1 + (h.β (θ₁ x.1) (θ₁ y.1)).1
        rw [h.β_val, h.β_val]
        change _ = _ + (⅟2 : R) • (cT s (u.1 • y.1.1) * J * (u.1 • x.1.1) - cT s (u.1 • x.1.1) * J * (u.1 • y.1.1))
        simp only [cT_smul, hu, Matrix.smul_mul, Matrix.mul_smul, smul_add, ← smul_sub, smul_comm (⅟2 : R) u.1]))
      continuous_toFun := θ₁.continuous.prodMap θ₂.continuous
      continuous_invFun := θ₁.symm.continuous.prodMap θ₂.symm.continuous }
  choose ι₀ hι₀ using hN
  have jinj : ∀ {p q}, (j p).1 = (j q).1 → p = q := fun e => hj.injective (Units.ext e)
  let ι : Heis h.β →* H := MonoidHom.mk' ι₀ fun x y => jinj (by rw [map_mul, Units.val_mul, hι₀, hι₀, hι₀, map_mul])
  have hι : ∀ x, (j (ι x)).1 = h.nMat x := hι₀
  have cn : Continuous h.nMat := by
    have d1 : Continuous fun x : Heis h.β => x.1.1 := c1.comp continuous_fst
    have d2 : Continuous fun x : Heis h.β => x.2.1 := continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.add (d1.matrix_mul continuous_const)).sub
      (continuous_const.matrix_mul ((continuous_cT hs d1).matrix_mul continuous_const))).add
      ((continuous_const.matrix_mul (d2.sub ((((continuous_cT hs d1).matrix_mul continuous_const).matrix_mul d1).const_smul
        (⅟2 : R)))).matrix_mul continuous_const)
  have cι : Continuous ι := hj.continuous_iff.2 (Units.continuous_iff.2
    ⟨cn.congr fun x => (hι x).symm, (cn.comp continuous_inv).congr fun x => by
      rw [Function.comp, Function.comp, ← map_inv, ← map_inv, hι]⟩)
  have cj : Continuous fun p => (j p).1 := Units.continuous_val.comp hj.continuous
  let B : H → Matrix (Fin k) (Fin k) R := fun p => cT s Y * J * ((j p).1 * X)
  have hB : ∀ p, (j p).1 * X = X * B p := fun p => by
    obtain ⟨B', e⟩ := hP p
    rw [show B p = B' from (h.par (hU p) e).1, e]
  let W : H → Matrix (Fin n) (Fin k) R := fun p => (j p).1 * Y * cT s (B p)
  have cW : Continuous W := (cj.matrix_mul continuous_const).matrix_mul
    (continuous_cT hs (continuous_const.matrix_mul (cj.matrix_mul continuous_const)))
  have W1' : ∀ p, cT s X * J * W p = 1 := fun p => by rw [← Matrix.mul_assoc, (h.par (hU p) (hB p)).2.2.1]
  have W2' : ∀ p, cT s (W p) * J * W p = 0 := fun p => by
    simp only [W]
    rw [Matrix.mul_assoc (j p).1, gram_unitary (hU p), cT_mul, Matrix.mul_assoc _ (cT s Y), ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ Y, h.yy]
    simp
  let π : H → Heis h.β := fun p => h.pt (W p) (W1' p) (W2' p)
  have hπ : ∀ p, h.nMat (π p) * Y = W p := fun p => h.nMat_pt _ _ _
  have cπ : Continuous π :=
    (((cW.sub continuous_const).sub (continuous_const.matrix_mul (continuous_const.matrix_mul cW))).subtype_mk _).prodMk
      ((((continuous_const.matrix_mul cW).sub (((continuous_cT hs cW).matrix_mul continuous_const).matrix_mul
        continuous_const)).const_smul (⅟2 : R)).subtype_mk _)
  have nX : ∀ x, h.nMat x * X = X := fun x => h.eich_X x.1.2.1 _
  have Beq : ∀ p B', (j p).1 * X = X * B' → B p = B' := fun p B' e => (h.par (hU p) e).1
  have bb : (j b).1 * (j b⁻¹).1 = 1 := by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have bb' : (j b⁻¹).1 * (j b).1 = 1 := mul_eq_one_comm.1 bb
  have bX' : (j b⁻¹).1 * X = u⁻¹.1 • X := by
    have := congrArg (fun M => u⁻¹.1 • (j b⁻¹).1 * M) bX
    simpa [← Matrix.mul_assoc, bb', smul_smul] using this.symm
  have bY' : (j b⁻¹).1 * Y = u.1 • Y := by
    have := congrArg (fun M => u.1 • (j b⁻¹).1 * M) bY
    simpa [← Matrix.mul_assoc, bb', smul_smul] using this.symm
  have bJ : ∀ Z : Matrix (Fin n) (Fin k) R, cT s Z * J * (j b⁻¹).1 = cT s ((j b).1 * Z) * J := fun Z => by
    rw [← gram_unitary (hU b) Z, bb, Matrix.mul_one]
  have hφι : ∀ x, φ (ι x) = ι (ψ x) := fun x => jinj (by
    rw [hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, hι, hι, h.nMat_apply, h.nMat_apply]
    change _ = eich s J X (u.1 • x.1.1) (u.1 • u.1 • x.2.1 - (⅟2 : R) • (cT s (u.1 • x.1.1) * J * (u.1 • x.1.1)))
    simp only [eich, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub (j b).1, Matrix.sub_mul _ _ (j b⁻¹).1, Matrix.mul_one, bb,
      ← Matrix.mul_assoc (j b).1, bX, bZ _ _ x.1.2.1 x.1.2.2, cT_smul, hu,
      Matrix.smul_mul, Matrix.mul_smul, smul_comm (⅟2 : R) u.1, ← smul_sub]
    have e1 : cT s X * J * (j b⁻¹).1 = u.1 • (cT s X * J) := by rw [bJ, bX, cT_smul, hu, Matrix.smul_mul]
    have e2 : cT s x.1.1 * J * (j b⁻¹).1 = cT s x.1.1 * J := by rw [bJ, bZ _ _ x.1.2.1 x.1.2.2]
    rw [Matrix.mul_assoc x.1.1 (cT s X * J), Matrix.mul_assoc X (cT s x.1.1 * J),
      Matrix.mul_assoc _ (cT s X * J) (j b⁻¹).1, e1, e2]
    simp only [Matrix.mul_smul])
  have h1 : ∀ p, π (φ p) = ψ (π p) := fun p => h.nMat_inj (by
    have e : B (φ p) = B p := Beq _ _ (by
      rw [hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, bX', Matrix.mul_smul, Matrix.mul_assoc, hB,
        ← Matrix.mul_assoc, bX, Matrix.smul_mul, smul_smul, Units.inv_mul, one_smul])
    rw [hπ, ← hι, ← hφι, hφ (ι _), map_mul, map_mul, Units.val_mul, Units.val_mul, hι, Matrix.mul_assoc, bY', Matrix.mul_smul,
      Matrix.mul_assoc, hπ]
    simp only [W]
    rw [e, hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc _ _ Y, bY']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc])
  have key := char_eq_of_retract ι cι π cπ (fun x p => h.nMat_inj (by
    have e : B (ι x * p) = B p := Beq _ _ (by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hι, nX])
    rw [hπ, map_mul, Matrix.mul_assoc, hπ]
    simp only [W]
    rw [e, map_mul, Units.val_mul, hι]
    simp only [Matrix.mul_assoc])) φ ψ h1 (fun p => by
    rw [h1, ← hφι, ← map_inv φ, ← map_mul φ, hφ, mul_inv_eq_iff_eq_mul]
    apply jinj
    rw [map_mul j b, map_mul j _ b, Units.val_mul, Units.val_mul]
    refine h.comm (hU _) (hB _) (D := cT s X * J * ((j p).1 * Y)) ?_ (B' := u.1 • 1) (D' := u⁻¹.1 • 1) (by simp [bX])
      (by simp [bY]) (by simp) (by simp) (bZ n)
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, ← map_inv, hι]
    have e : (j p).1 * Y = h.nMat (π p) * Y * (cT s X * J * ((j p).1 * Y)) := by
      rw [hπ, Matrix.mul_assoc, (h.par (hU p) (hB p)).2.1, Matrix.mul_one]
    conv_lhs => rw [e]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc _ (h.nMat _) Y, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul])
  rw [key, Heis.char_eq h.β hβ ψ θ₁ θ₂ fun _ => rfl, haar_character_frame_annihilator h u, addEquivAddHaarChar_trans, ← haar_character_skew_hermitian hs h.ss ω hω hu,
    mul_assoc]

end Top

end CompanionTheory.ThKR.Sieg

end
