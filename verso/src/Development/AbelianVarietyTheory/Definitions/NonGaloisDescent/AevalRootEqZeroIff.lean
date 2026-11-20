import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UTr

variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'}

def IsCsr (P : B[X]) : Prop := P.Monic ∧ C (s (P.coeff 0)) * P = (P.map s).reflect P.natDegree

variable {s}

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in

/- English proof (translation)
Establish `h0` using `congrArg (fun Q => Q.coeff 0) h.2`. Simplify using `only [coeff_C_mul, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, coeff_map, coeff_natDegree, h.1.leadingCoeff, map_one] at h0`. Conclude with `h0`.
-/
theorem _root_.GlobalTheory.UTr.IsCsr.conj_mul_coeff_zero {P : B[X]}
    (h : _root_.GlobalTheory.UTr.IsCsr s P) : s (P.coeff 0) * P.coeff 0 = 1 := by
  have h0 := congrArg (fun Q => Q.coeff 0) h.2
  simp only [coeff_C_mul, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, coeff_map,
    coeff_natDegree, h.1.leadingCoeff, map_one] at h0
  exact h0

/- English proof (translation)
Use `⟨fun h => by simpa using h.conj_mul_coeff_zero, fun h => ⟨monic_X_sub_C u, ?_⟩⟩` and prove the remaining obligations. Establish `e : reflect 1 (X : B[X]) = 1` using `by simpa using reflect_monomial (R := B) 1 1`. Establish `e' : C (s u) * C u = (1 : B[X])` using `by rw [← C_mul, h, C_1]`. Rewrite using `[natDegree_X_sub_C, Polynomial.map_sub, map_X, map_C, reflect_sub, e, reflect_C]`. Simplify using `only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg]`.

Take the linear combination `e'`.
-/
theorem isCsr_X_sub_C [Nontrivial B] {u : B} : IsCsr s (X - C u) ↔ s u * u = 1 := by
  refine ⟨fun h => by simpa using h.conj_mul_coeff_zero, fun h => ⟨monic_X_sub_C u, ?_⟩⟩
  have e : reflect 1 (X : B[X]) = 1 := by simpa using reflect_monomial (R := B) 1 1
  have e' : C (s u) * C u = (1 : B[X]) := by rw [← C_mul, h, C_1]
  rw [natDegree_X_sub_C, Polynomial.map_sub, map_X, map_C, reflect_sub, e, reflect_C]
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg]
  linear_combination e'

/- English proof (translation)
Use `⟨hP.1.mul hQ.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hP.1.natDegree_mul hQ.1, Polynomial.map_mul, reflect_mul _ _ natDegree_map_le natDegree_map_le, ← hP.2, ← hQ.2, mul_coeff_zero, map_mul, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsCsr.mul {P Q : B[X]} (hP : IsCsr s P) (hQ : IsCsr s Q) : IsCsr s (P * Q) := by
  refine ⟨hP.1.mul hQ.1, ?_⟩
  rw [hP.1.natDegree_mul hQ.1, Polynomial.map_mul, reflect_mul _ _ natDegree_map_le natDegree_map_le, ← hP.2, ← hQ.2,
    mul_coeff_zero, map_mul, C_mul]
  ring

/- English proof (translation)
Use `⟨hP.1.map φ, ?_⟩` and prove the remaining obligations. Use `nontriviality B'`. Establish `e : s'.comp φ = φ.comp s` using `RingHom.ext fun b => (hφ b).symm`. Rewrite using `[hP.1.natDegree_map, Polynomial.map_map, e, ← Polynomial.map_map, reflect_map, ← hP.2, Polynomial.map_mul, map_C, coeff_map, hφ]`.
-/
theorem IsCsr.map {P : B[X]} (hP : IsCsr s P) (φ : B →+* B') (hφ : ∀ b, φ (s b) = s' (φ b)) :
    IsCsr s' (P.map φ) := by
  refine ⟨hP.1.map φ, ?_⟩
  nontriviality B'
  have e : s'.comp φ = φ.comp s := RingHom.ext fun b => (hφ b).symm
  rw [hP.1.natDegree_map, Polynomial.map_map, e, ← Polynomial.map_map, reflect_map, ← hP.2, Polynomial.map_mul, map_C, coeff_map, hφ]

variable (s) in

abbrev Csr : Type := {P : B[X] // IsCsr s P}

def Csr.mul (P Q : Csr s) : Csr s := ⟨P.1 * Q.1, P.2.mul Q.2⟩

def Csr.map (P : Csr s) (φ : B →+* B') (hφ : ∀ b, φ (s b) = s' (φ b)) : Csr s' := ⟨P.1.map φ, P.2.map φ hφ⟩

abbrev Csr.Factorisation (P : Csr s) : Type := {p : Csr s × Csr s // p.1.1 * p.2.1 = P.1}

def Csr.mulFactorisation (P₁ P₂ : Csr s) : (P₁.mul P₂).Factorisation := ⟨(P₁, P₂), rfl⟩

def Csr.Factorisation.map {P : Csr s} (p : P.Factorisation) (φ : B →+* B') (hφ : ∀ b, φ (s b) = s' (φ b)) :
    (P.map φ hφ).Factorisation :=
  ⟨(p.1.1.map φ hφ, p.1.2.map φ hφ), (Polynomial.map_mul φ).symm.trans (congrArg (Polynomial.map φ) p.2)⟩

def Csr.Factorisation.res {P : Csr s} (p : P.Factorisation) : B := resultant p.1.1.1 p.1.2.1

def Alg (P : Csr s) : Type := AdjoinRoot P.1

variable (P : Csr s)

instance : CommRing (Alg P) := inferInstanceAs (CommRing (AdjoinRoot P.1))
instance {S : Type} [CommSemiring S] [Algebra S B] : Algebra S (Alg P) := inferInstanceAs (Algebra S (AdjoinRoot P.1))
instance {S : Type} [CommSemiring S] [Algebra S B] : IsScalarTower S B (Alg P) :=
  inferInstanceAs (IsScalarTower S B (AdjoinRoot P.1))

def root : Alg P := AdjoinRoot.root P.1

def powBasis : Module.Basis (Fin P.1.natDegree) B (Alg P) := (AdjoinRoot.powerBasis' P.2.1).basis

instance : Module.Free B (Alg P) := .of_basis (powBasis P)
instance : Module.Finite B (Alg P) := .of_basis (powBasis P)

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `aeval (AdjoinRoot.root P.1) q = 0 ↔ _`. Rewrite using `[AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]`.
-/
theorem _root_.GlobalTheory.UTr.aeval_root_eq_zero_iff {q : B[X]} :
    aeval (_root_.GlobalTheory.UTr.root P) q = 0 ↔ P.1 ∣ q := by
  change aeval (AdjoinRoot.root P.1) q = 0 ↔ _
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.UTr.aeval_root_eq_zero_iff P).2 dvd_rfl`.
-/
theorem _root_.GlobalTheory.UTr.aeval_root :
    aeval (_root_.GlobalTheory.UTr.root P) P.1 = 0 :=
  (_root_.GlobalTheory.UTr.aeval_root_eq_zero_iff P).2 dvd_rfl

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
Take `⟨q, hq⟩ : ∃ q, AdjoinRoot.mk P.1 q = z` from `AdjoinRoot.mk_surjective z`. Conclude with `⟨q, (AdjoinRoot.aeval_eq q).trans hq⟩`.
-/
theorem _root_.GlobalTheory.UTr.exists_aeval_root (z : _root_.GlobalTheory.UTr.Alg P) :
    ∃ q : B[X], aeval (_root_.GlobalTheory.UTr.root P) q = z := by
  obtain ⟨q, hq⟩ : ∃ q, AdjoinRoot.mk P.1 q = z := AdjoinRoot.mk_surjective z
  exact ⟨q, (AdjoinRoot.aeval_eq q).trans hq⟩

variable {P} in

/- English proof (translation)
Take `⟨q, rfl⟩` from `exists_aeval_root P z`. Proceed by induction on `q using Polynomial.induction_on with`. Consider the case `C a => simpa using hC a`. Consider the case `add a b ha hb => simpa using hadd _ _ ha hb`. Consider the case `monomial n a h => rw [pow_succ, ← mul_assoc, map_mul, aeval_X]`.

Conclude with `hmul _ _ h hr`.
-/
theorem Alg.induction {p : Alg P → Prop} (hC : ∀ b, p (algebraMap B _ b)) (hr : p (root P))
    (hadd : ∀ y z, p y → p z → p (y + z)) (hmul : ∀ y z, p y → p z → p (y * z)) (z : Alg P) : p z := by
  obtain ⟨q, rfl⟩ := exists_aeval_root P z
  induction q using Polynomial.induction_on with
  | C a => simpa using hC a
  | add a b ha hb => simpa using hadd _ _ ha hb
  | monomial n a h => rw [pow_succ, ← mul_assoc, map_mul, aeval_X]; exact hmul _ _ h hr

variable {P} in

/- English proof (translation)
The claim follows from `RingHom.ext (Alg.induction hC hr (fun y z hy hz => by rw [map_add, map_add, hy, hz]) fun y z hy hz => by rw [map_mul, map_mul, hy, hz])`.
-/
theorem Alg.ringHom_ext {S : Type} [Ring S] {f g : Alg P →+* S} (hC : ∀ b, f (algebraMap B _ b) = g (algebraMap B _ b))
    (hr : f (root P) = g (root P)) : f = g :=
  RingHom.ext (Alg.induction hC hr (fun y z hy hz => by rw [map_add, map_add, hy, hz])
    fun y z hy hz => by rw [map_mul, map_mul, hy, hz])

def gamma : (Alg P)ˣ :=
  Units.mkOfMulEqOne (root P) (-(algebraMap B _ (s (P.1.coeff 0)) * aeval (root P) P.1.divX)) (by
    have h := aeval_root P
    rw [← X_mul_divX_add P.1, map_add, map_mul, aeval_X, aeval_C] at h
    have h1 := congrArg (algebraMap B (Alg P)) P.2.conj_mul_coeff_zero
    rw [map_mul, map_one] at h1
    linear_combination (-algebraMap B (Alg P) (s (P.1.coeff 0))) * h + h1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem val_gamma : (gamma P : Alg P) = root P := rfl

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
Use `letI := (_root_.GlobalTheory.UTr.gamma P)⁻¹.invertible`. Establish `key` using `eval₂_reflect_mul_pow (algebraMap B (_root_.GlobalTheory.UTr.Alg P)) (((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) P.1.natDegree (P.1.map s) (natDegree_map_le)`. Establish `hroot : ⅟(((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = _root_.GlobalTheory.UTr.root P` using `rfl`. Rewrite using `[← eval₂_map, ← key, ← P.2.2, hroot, ← aeval_def, map_mul, _root_.GlobalTheory.UTr.aeval_root, mul_zero, zero_mul]`.
-/
theorem _root_.GlobalTheory.UTr.eval₂_gamma_inv :
    P.1.eval₂ ((algebraMap B (_root_.GlobalTheory.UTr.Alg P)).comp s)
      ((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) = 0 := by
  letI := (_root_.GlobalTheory.UTr.gamma P)⁻¹.invertible
  have key := eval₂_reflect_mul_pow (algebraMap B (_root_.GlobalTheory.UTr.Alg P))
    (((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) :
      _root_.GlobalTheory.UTr.Alg P) P.1.natDegree (P.1.map s) (natDegree_map_le)
  have hroot : ⅟(((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) :
      _root_.GlobalTheory.UTr.Alg P) = _root_.GlobalTheory.UTr.root P := rfl
  rw [← eval₂_map, ← key, ← P.2.2, hroot, ← aeval_def, map_mul, _root_.GlobalTheory.UTr.aeval_root, mul_zero, zero_mul]

def conj : Alg P →+* Alg P := AdjoinRoot.lift _ _ (eval₂_gamma_inv P)

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
The claim follows from `AdjoinRoot.lift_of _`.
-/
@[simp] theorem _root_.GlobalTheory.UTr.conj_algebraMap (b : B) :
    _root_.GlobalTheory.UTr.conj P (algebraMap B _ b) = algebraMap B _ (s b) :=
  AdjoinRoot.lift_of _

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
The claim follows from `AdjoinRoot.lift_root _`.
-/
@[simp] theorem _root_.GlobalTheory.UTr.conj_root :
    _root_.GlobalTheory.UTr.conj P (_root_.GlobalTheory.UTr.root P) =
      ((_root_.GlobalTheory.UTr.gamma P)⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) :=
  AdjoinRoot.lift_root _

/- English proof (translation)
Rewrite using `[conj_root]`. Conclude with `(gamma P).mul_inv`.
-/
theorem root_mul_conj_root : root P * conj P (root P) = 1 := by rw [conj_root]; exact (gamma P).mul_inv

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, conj_algebraMap]`.
-/
theorem conj_smul (b : B) (z : Alg P) : conj P (b • z) = s b • conj P z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, conj_algebraMap]

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
Use `set σ := _root_.GlobalTheory.UTr.conj P`. Use `set γ := _root_.GlobalTheory.UTr.gamma P`. Establish `hγ : ((γ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = _root_.GlobalTheory.UTr.root P` using `rfl`. Establish `hinv : σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = _root_.GlobalTheory.UTr.root P`. Establish `e : ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = σ γ` using `(_root_.GlobalTheory.UTr.conj_root P).symm`.

Establish `h1 : σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) * ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = 1`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.inv_mul, mul_one]`. Use `_ = γ := by rw [← mul_assoc, h1, one_mul]`.

Use `_ = _root_.GlobalTheory.UTr.root P := hγ`. Take `⟨q, rfl⟩` from `_root_.GlobalTheory.UTr.exists_aeval_root P z`. Proceed by induction on `q using Polynomial.induction_on with`. Consider the case `C a => simp [σ, hs]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `monomial k a ih`. Rewrite using `[pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, ih, aeval_X, _root_.GlobalTheory.UTr.conj_root, hinv]`.
-/
theorem _root_.GlobalTheory.UTr.conj_conj (hs : ∀ b, s (s b) = b)
    (z : _root_.GlobalTheory.UTr.Alg P) :
    _root_.GlobalTheory.UTr.conj P (_root_.GlobalTheory.UTr.conj P z) = z := by
  set σ := _root_.GlobalTheory.UTr.conj P
  set γ := _root_.GlobalTheory.UTr.gamma P
  have hγ : ((γ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
      _root_.GlobalTheory.UTr.root P := rfl
  have hinv : σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
      _root_.GlobalTheory.UTr.root P := by
    have e : ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
        σ γ := (_root_.GlobalTheory.UTr.conj_root P).symm
    have h1 : σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) *
        ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = 1 := by
      calc _ = σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) *
            σ γ := by rw [← e]
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    calc σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)
        = σ ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) *
          (((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) * γ) := by
          rw [Units.inv_mul, mul_one]
      _ = γ := by rw [← mul_assoc, h1, one_mul]
      _ = _root_.GlobalTheory.UTr.root P := hγ
  obtain ⟨q, rfl⟩ := _root_.GlobalTheory.UTr.exists_aeval_root P z
  induction q using Polynomial.induction_on with
  | C a => simp [σ, hs]
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, map_mul, ih, aeval_X,
      _root_.GlobalTheory.UTr.conj_root, hinv]

def normU : (Alg P)ˣ →* (Alg P)ˣ := MonoidHom.id _ * Units.map (conj P : Alg P →* Alg P)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem val_normU (z : (Alg P)ˣ) : (normU P z : Alg P) = z * conj P z := rfl

def tor : Subgroup (Alg P)ˣ := (normU P).ker

variable {P} in

/- English proof (translation)
The claim follows from `Units.ext_iff`.
-/
theorem mem_tor {z : (Alg P)ˣ} : z ∈ tor P ↔ (z : Alg P) * conj P z = 1 := Units.ext_iff

/- English proof (translation)
The claim follows from `mem_tor.2 (root_mul_conj_root P)`.
-/
theorem gamma_mem_tor : gamma P ∈ tor P := mem_tor.2 (root_mul_conj_root P)

def plus : Subgroup (Alg P)ˣ := (Units.map (conj P : Alg P →* Alg P)).eqLocus (MonoidHom.id _)

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in
variable {P} in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Units.map _ x = x ↔ _`. Rewrite using `[Units.ext_iff]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.UTr.mem_plus {x : (_root_.GlobalTheory.UTr.Alg P)ˣ} :
    x ∈ _root_.GlobalTheory.UTr.plus P ↔ _root_.GlobalTheory.UTr.conj P x = x := by
  change Units.map _ x = x ↔ _
  rw [Units.ext_iff]
  rfl

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in

/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.UTr.mem_plus, _root_.GlobalTheory.UTr.val_normU, map_mul, _root_.GlobalTheory.UTr.conj_conj P hs, mul_comm]`.
-/
theorem _root_.GlobalTheory.UTr.normU_mem_plus (hs : ∀ b, s (s b) = b)
    (z : (_root_.GlobalTheory.UTr.Alg P)ˣ) :
    _root_.GlobalTheory.UTr.normU P z ∈ _root_.GlobalTheory.UTr.plus P := by
  rw [_root_.GlobalTheory.UTr.mem_plus, _root_.GlobalTheory.UTr.val_normU,
    map_mul, _root_.GlobalTheory.UTr.conj_conj P hs, mul_comm]

def norms : Subgroup (plus P) := (normU P).range.subgroupOf (plus P)

abbrev Cls : Type := plus P ⧸ norms P

variable {P} in

def Cls.rep (c : Cls P) : Alg P := ((Quotient.out c : plus P) : (Alg P)ˣ)

def torInt (O : Subring B) : Subgroup (tor P) := (UnitLemma.intUnits O (Alg P)).subgroupOf (tor P)

section Map

variable {P} {Q : Csr s'} (φ : B →+* B') (h : Q.1 ∣ P.1.map φ)

def algMap : Alg P →+* Alg Q :=
  AdjoinRoot.lift ((algebraMap B' (Alg Q)).comp φ) (root Q) (by
    rw [← eval₂_map]; exact (aeval_root_eq_zero_iff Q).2 h)

/- English proof (translation)
The claim follows from `AdjoinRoot.lift_of _`.
-/
@[simp] theorem algMap_algebraMap (b : B) : algMap φ h (algebraMap B _ b) = algebraMap B' _ (φ b) :=
  AdjoinRoot.lift_of _

/- English proof (translation)
The claim follows from `AdjoinRoot.lift_root _`.
-/
@[simp] theorem algMap_root : algMap φ h (root P) = root Q := AdjoinRoot.lift_root _

variable (hφ : ∀ b, φ (s b) = s' (φ b))
include hφ

/- English proof (translation)
Use `RingHom.congr_fun (Alg.ringHom_ext (f := (algMap φ h).comp (conj P)) (g := (conj Q).comp (algMap φ h)) (fun b => by simp [hφ]) ?_) z` and prove the remaining obligations. Establish `h1` using `congrArg (algMap φ h) (root_mul_conj_root P)`. Rewrite `h1` using `[map_mul, map_one, algMap_root]`. Express the relevant statement in the definitionally equal form `algMap φ h (conj P (root P)) = conj Q (algMap φ h (root P))`. Rewrite using `[algMap_root, conj_root Q]`.

Conclude with `Units.eq_inv_of_mul_eq_one_left h1`.
-/
theorem algMap_conj (z : Alg P) : algMap φ h (conj P z) = conj Q (algMap φ h z) := by
  refine RingHom.congr_fun (Alg.ringHom_ext (f := (algMap φ h).comp (conj P)) (g := (conj Q).comp (algMap φ h))
    (fun b => by simp [hφ]) ?_) z
  have h1 := congrArg (algMap φ h) (root_mul_conj_root P)
  rw [map_mul, map_one, algMap_root] at h1
  change algMap φ h (conj P (root P)) = conj Q (algMap φ h (root P))
  rw [algMap_root, conj_root Q]
  exact Units.eq_inv_of_mul_eq_one_left h1

def torMap : tor P →* tor Q :=
  ((Units.map (algMap φ h : Alg P →* Alg Q)).comp (tor P).subtype).codRestrict _ fun z => mem_tor.2 (by
    change algMap φ h (z.1 : Alg P) * conj Q (algMap φ h (z.1 : Alg P)) = 1
    rw [← algMap_conj φ h hφ, ← map_mul, mem_tor.1 z.2, map_one])

def plusMap : plus P →* plus Q :=
  ((Units.map (algMap φ h : Alg P →* Alg Q)).comp (plus P).subtype).codRestrict _ fun z => mem_plus.2 (by
    change conj Q (algMap φ h (z.1 : Alg P)) = algMap φ h (z.1 : Alg P)
    rw [← algMap_conj φ h hφ, mem_plus.1 z.2])

def clsMap : Cls P →* Cls Q :=
  QuotientGroup.map _ _ (plusMap φ h hφ) (by
    rintro x ⟨u, hu⟩
    refine ⟨Units.map (algMap φ h : Alg P →* Alg Q) u, Units.ext ?_⟩
    change algMap φ h (u : Alg P) * conj Q (algMap φ h (u : Alg P)) = algMap φ h (x.1 : Alg P)
    rw [← algMap_conj φ h hφ, ← map_mul, ← val_normU, hu]; rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_torMap (z : tor P) : ((torMap φ h hφ z).1 : Alg Q) = algMap φ h (z.1 : Alg P) := rfl

end Map

variable {P} in

def Csr.Factorisation.fst (p : P.Factorisation) : Alg P →+* Alg p.1.1 :=
  algMap (RingHom.id B) (by rw [Polynomial.map_id]; exact Dvd.intro _ p.2)

variable {P} in

def Csr.Factorisation.snd (p : P.Factorisation) : Alg P →+* Alg p.1.2 :=
  algMap (RingHom.id B) (by rw [Polynomial.map_id]; exact Dvd.intro_left _ p.2)

def herm (x y z : Alg P) : B := Algebra.trace B _ (x * y * conj P z)

/- English proof (translation)
Rewrite using `[herm, herm, map_mul (conj P)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_mul_mul (x u y z : Alg P) : herm P x (u * y) (u * z) = herm P (x * (u * conj P u)) y z := by
  rw [herm, herm, map_mul (conj P)]; congr 1; ring

def gram (x : Alg P) : Matrix (Fin P.1.natDegree) (Fin P.1.natDegree) B :=
  Matrix.of fun i j => herm P x (powBasis P j) (powBasis P i)

open Classical in
variable (s) in

def normSign (d : B) : ℤˣ := if ∃ u : Bˣ, d = u * s u then 1 else -1

def etaDet (x : Alg P) : ℤˣ := normSign s (gram P x).det

variable {n : Type} [Fintype n] [DecidableEq n]

def evalMat (g : Matrix n n B) (hg : aeval g P.1 = 0) : Alg P →ₐ[B] Matrix n n B :=
  Ideal.Quotient.liftₐ (Ideal.span {P.1}) (aeval g) fun q hq => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hq
    rw [map_mul, hg, zero_mul]

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in
variable {n : Type} [Fintype n] [DecidableEq n] in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Ideal.Quotient.liftₐ _ _ _ (Ideal.Quotient.mk _ X) = g`. Conclude with `aeval_X g`.
-/
@[simp] theorem _root_.GlobalTheory.UTr.evalMat_root (g : Matrix n n B) (hg : aeval g P.1 = 0) :
    _root_.GlobalTheory.UTr.evalMat P g hg (_root_.GlobalTheory.UTr.root P) = g := by
  change Ideal.Quotient.liftₐ _ _ _ (Ideal.Quotient.mk _ X) = g
  exact aeval_X g

variable {P} in

/- English proof (translation)
The claim follows from `RingHom.congr_fun (Alg.ringHom_ext (f := f.toRingHom) (g := (evalMat P g hg).toRingHom) (fun b => (f.commutes b).trans ((evalMat P g hg).commutes b).symm) (hf.trans (evalMat_root P g hg).symm)) z`.
-/
theorem eq_evalMat {g : Matrix n n B} (hg : aeval g P.1 = 0) (f : Alg P →ₐ[B] Matrix n n B) (hf : f (root P) = g)
    (z : Alg P) : f z = evalMat P g hg z :=
  RingHom.congr_fun (Alg.ringHom_ext (f := f.toRingHom) (g := (evalMat P g hg).toRingHom)
    (fun b => (f.commutes b).trans ((evalMat P g hg).commutes b).symm) (hf.trans (evalMat_root P g hg).symm)) z

variable {J : Matrix n n B}

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable {J : Matrix n n B} in

/- English proof (translation)
Use `set E := _root_.GlobalTheory.UTr.evalMat P _ hg`. Use `set γ := _root_.GlobalTheory.UTr.gamma P`. Establish `hγ : ((γ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = _root_.GlobalTheory.UTr.root P` using `rfl`. Establish `hgU : _root_.Formalism.UG.cT s g.1.1 * J * g.1.1 = J` using `g.2`. Establish `hroot : E (_root_.GlobalTheory.UTr.root P) = g.1.1` using `_root_.GlobalTheory.UTr.evalMat_root P _ hg`.

Establish `hgγ : g.1.1 * E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hroot]`. Use `_ = 1 := by rw [← map_mul, ← hγ, Units.mul_inv, map_one]`. Establish `hside : _root_.Formalism.UG.cT s g.1.1 * J = J * E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hgγ, mul_one]`. Use `_ = _ := by rw [← mul_assoc, hgU]`. Establish `hcT_alg : ∀ a : B, _root_.Formalism.UG.cT s (algebraMap B (Matrix n n B) a) = algebraMap B (Matrix n n B) (s a)`. Introduce `a`.

Unfold `_root_.Formalism.UG.cT`. Use extensionality with `i j`. Simplify using `[algebraMap_matrix_apply, apply_ite s, eq_comm]`. Establish `hcT_add : ∀ M N : Matrix n n B, _root_.Formalism.UG.cT s (M + N) = _root_.Formalism.UG.cT s M + _root_.Formalism.UG.cT s N`. Introduce `M N`.

Unfold `_root_.Formalism.UG.cT`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Take `⟨q, rfl⟩` from `_root_.GlobalTheory.UTr.exists_aeval_root P z`. Proceed by induction on `q using Polynomial.induction_on with`.

Consider the case `C a`. Rewrite using `[aeval_C, AlgHom.commutes, _root_.GlobalTheory.UTr.conj_algebraMap, AlgHom.commutes, hcT_alg]`. Conclude with `Algebra.commutes _ _`. Consider the case `add p q hp hq`. Rewrite using `[map_add, map_add, map_add, map_add, hcT_add, add_mul, hp, hq, mul_add]`.

Consider the case `monomial k a ih`. Rewrite using `[pow_succ, ← mul_assoc, map_mul (aeval _) (C a * X ^ k) X, aeval_X]`. Generalize the expression as in `aeval (_root_.GlobalTheory.UTr.root P) (C a * X ^ k) = w at ih ⊢`. Simplify using `only [map_mul]`. Rewrite using `[_root_.Formalism.UG.cT_mul, hroot, _root_.GlobalTheory.UTr.conj_root, mul_assoc, ih, ← mul_assoc, hside, mul_assoc, ← map_mul, ← map_mul, mul_comm ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)]`.
-/
theorem _root_.GlobalTheory.UTr.cT_evalMat (g : _root_.Formalism.UG.UJ s J)
    (hg : aeval g.1.1 P.1 = 0) (z : _root_.GlobalTheory.UTr.Alg P) :
    _root_.Formalism.UG.cT s (_root_.GlobalTheory.UTr.evalMat P _ hg z) * J =
      J * _root_.GlobalTheory.UTr.evalMat P _ hg (_root_.GlobalTheory.UTr.conj P z) := by
  set E := _root_.GlobalTheory.UTr.evalMat P _ hg
  set γ := _root_.GlobalTheory.UTr.gamma P
  have hγ : ((γ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) =
      _root_.GlobalTheory.UTr.root P := rfl
  have hgU : _root_.Formalism.UG.cT s g.1.1 * J * g.1.1 = J := g.2
  have hroot : E (_root_.GlobalTheory.UTr.root P) = g.1.1 :=
    _root_.GlobalTheory.UTr.evalMat_root P _ hg
  have hgγ : g.1.1 * E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)
      = 1 := by
    calc _ = E (_root_.GlobalTheory.UTr.root P) *
          E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) := by
          rw [hroot]
      _ = 1 := by rw [← map_mul, ← hγ, Units.mul_inv, map_one]
  have hside : _root_.Formalism.UG.cT s g.1.1 * J =
      J * E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P) := by
    calc _ = _root_.Formalism.UG.cT s g.1.1 * J * (g.1.1 *
          E ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)) := by
          rw [hgγ, mul_one]
      _ = _ := by rw [← mul_assoc, hgU]
  have hcT_alg : ∀ a : B, _root_.Formalism.UG.cT s (algebraMap B (Matrix n n B) a) =
      algebraMap B (Matrix n n B) (s a) := by
    intro a
    unfold _root_.Formalism.UG.cT
    ext i j
    simp [algebraMap_matrix_apply, apply_ite s, eq_comm]
  have hcT_add : ∀ M N : Matrix n n B, _root_.Formalism.UG.cT s (M + N) = _root_.Formalism.UG.cT s M + _root_.Formalism.UG.cT s N := by
    intro M N
    unfold _root_.Formalism.UG.cT
    ext i j
    simp
  obtain ⟨q, rfl⟩ := _root_.GlobalTheory.UTr.exists_aeval_root P z
  induction q using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, AlgHom.commutes, _root_.GlobalTheory.UTr.conj_algebraMap, AlgHom.commutes,
      hcT_alg]
    exact Algebra.commutes _ _
  | add p q hp hq =>
    rw [map_add, map_add, map_add, map_add, hcT_add, add_mul, hp, hq, mul_add]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval _) (C a * X ^ k) X, aeval_X]
    generalize aeval (_root_.GlobalTheory.UTr.root P) (C a * X ^ k) = w at ih ⊢
    simp only [map_mul]
    rw [_root_.Formalism.UG.cT_mul, hroot, _root_.GlobalTheory.UTr.conj_root, mul_assoc, ih, ← mul_assoc, hside, mul_assoc,
      ← map_mul, ← map_mul,
      mul_comm ((γ⁻¹ : (_root_.GlobalTheory.UTr.Alg P)ˣ) : _root_.GlobalTheory.UTr.Alg P)]

def torToU (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) : tor P →* UJ s J :=
  ((Units.map (evalMat P _ hg : Alg P →* Matrix n n B)).comp (tor P).subtype).codRestrict _ fun z => by
    change cT s (evalMat P _ hg (z.1 : Alg P)) * J * evalMat P _ hg (z.1 : Alg P) = J
    rw [cT_evalMat, Matrix.mul_assoc, ← map_mul, mul_comm (conj P _), mem_tor.1 z.2, map_one, Matrix.mul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_torToU (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) (z : tor P) :
    (torToU P g hg z).1.1 = evalMat P _ hg (z.1 : Alg P) := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext (evalMat_root P _ hg))`.
-/
theorem torToU_gamma (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) : torToU P g hg ⟨gamma P, gamma_mem_tor P⟩ = g :=
  Subtype.ext (Units.ext (evalMat_root P _ hg))

def torToCent (g : UJ s J) (hg : aeval g.1.1 P.1 = 0) : tor P →* Subgroup.centralizer ({g} : Set (UJ s J)) :=
  (torToU P g hg).codRestrict _ fun z => Subgroup.mem_centralizer_singleton_iff.2 (by
    have := congrArg (torToU P g hg) (mul_comm z ⟨gamma P, gamma_mem_tor P⟩)
    rwa [map_mul, map_mul, torToU_gamma] at this)

/- English proof (translation)
Establish `key : ∀ (M : Matrix n n B) (a b : n → B), hform s M a b = (s ∘ a) ⬝ᵥ M *ᵥ b` using `fun M a b => by`. Simplify using `[hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Establish `e : s ∘ (g *ᵥ u) = (s ∘ u) ᵥ* cT s g`. Rewrite using `[cT, Matrix.vecMul_transpose]`. Use function extensionality and compare the values at `i`.

Conclude with `RingHom.map_mulVec s g u i`. Rewrite using `[key, key, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem hform_mulVec (J g : Matrix n n B) (u v : n → B) :
    hform s J (g *ᵥ u) (g *ᵥ v) = hform s (cT s g * J * g) u v := by
  have key : ∀ (M : Matrix n n B) (a b : n → B), hform s M a b = (s ∘ a) ⬝ᵥ M *ᵥ b := fun M a b => by
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e : s ∘ (g *ᵥ u) = (s ∘ u) ᵥ* cT s g := by
    rw [cT, Matrix.vecMul_transpose]; funext i; exact RingHom.map_mulVec s g u i
  rw [key, key, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Simplify using `[hform, Pi.single_apply, apply_ite s, ite_mul]`.
-/
theorem hform_single (J : Matrix n n B) (i j : n) : hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite s, ite_mul]

variable (J) in

abbrev Isom (x : Alg P) : Type := {i : Alg P ≃ₗ[B] (n → B) // ∀ y z, hform s J (i z) (i y) = herm P x y z}

def stdIsom (x : Alg P) : Isom P (gram P x) x :=
  ⟨(powBasis P).equivFun, fun y z => by
    conv_rhs => rw [← (powBasis P).sum_equivFun y, ← (powBasis P).sum_equivFun z]
    simp only [hform, gram, herm, Matrix.of_apply, map_sum, conj_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
      smul_mul_assoc, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring⟩

variable {P}

def mulMat (i : Alg P ≃ₗ[B] (n → B)) : Alg P →ₐ[B] Matrix n n B :=
  (LinearMap.toMatrixAlgEquiv'.toAlgHom.comp (i.conjAlgEquiv B).toAlgHom).comp (Algebra.lmul B (Alg P))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `LinearMap.toMatrix' (i.conjAlgEquiv B (Algebra.lmul B (Alg P) z)) *ᵥ i y = _`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Simplify using `[LinearEquiv.conjAlgEquiv_apply]`.
-/
theorem mulMat_mulVec (i : Alg P ≃ₗ[B] (n → B)) (z y : Alg P) : mulMat i z *ᵥ i y = i (z * y) := by
  change LinearMap.toMatrix' (i.conjAlgEquiv B (Algebra.lmul B (Alg P) z)) *ᵥ i y = _
  rw [LinearMap.toMatrix'_mulVec]
  simp [LinearEquiv.conjAlgEquiv_apply]

/- English proof (translation)
The claim follows from `Matrix.toLin'.injective (LinearMap.ext fun u => by obtain ⟨y, rfl⟩ := i.surjective u rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, mulMat_mulVec])`.
-/
theorem eq_mulMat (i : Alg P ≃ₗ[B] (n → B)) {z : Alg P} {g : Matrix n n B} (h : ∀ y, g *ᵥ i y = i (z * y)) :
    g = mulMat i z :=
  Matrix.toLin'.injective (LinearMap.ext fun u => by
    obtain ⟨y, rfl⟩ := i.surjective u
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h, mulMat_mulVec])

/- English proof (translation)
Rewrite using `[aeval_algHom_apply, aeval_root, map_zero]`.
-/
theorem aeval_mulMat_root (i : Alg P ≃ₗ[B] (n → B)) : aeval (mulMat i (root P)) P.1 = 0 := by
  rw [aeval_algHom_apply, aeval_root, map_zero]

variable {x x' : Alg P}

def Isom.elt (i : Isom P J x) : UJ s J :=
  ⟨Units.map (mulMat i.1 : Alg P →* Matrix n n B) (gamma P), by
    change cT s (mulMat i.1 (root P)) * J * mulMat i.1 (root P) = J
    ext a b
    obtain ⟨y, hy⟩ := i.1.surjective (Pi.single a 1)
    obtain ⟨z, hz⟩ := i.1.surjective (Pi.single b 1)
    rw [← hform_single (s := s) (_ * _ * _), ← hform_single (s := s) J, ← hform_mulVec, ← hy, ← hz, mulMat_mulVec, mulMat_mulVec,
      i.2, i.2, herm_mul_mul, root_mul_conj_root, mul_one]⟩

def Isom.mulNorm (i : Isom P J x) (u : (Alg P)ˣ) : Isom P J (x * (u * conj P u)) :=
  ⟨(u.mulLeftLinearEquiv B (Alg P)).trans i.1, fun y z => (i.2 _ _).trans (herm_mul_mul P x u y z)⟩

variable (P) in

def IsCyc (g : Matrix n n B) : Prop := ∃ i : Alg P ≃ₗ[B] (n → B), mulMat i (root P) = g

/- English proof (translation)
Take `⟨i, rfl⟩` from `h`. Conclude with `aeval_mulMat_root i`.
-/
theorem IsCyc.aeval_eq_zero {g : Matrix n n B} (h : IsCyc P g) : aeval g P.1 = 0 := by
  obtain ⟨i, rfl⟩ := h; exact aeval_mulMat_root i

/- English proof (translation)
The claim follows from `(eq_evalMat hg (mulMat i) hi z).symm`.
-/
theorem evalMat_eq_mulMat {g : Matrix n n B} (hg : aeval g P.1 = 0) {i : Alg P ≃ₗ[B] (n → B)} (hi : mulMat i (root P) = g)
    (z : Alg P) : evalMat P g hg z = mulMat i z := (eq_evalMat hg (mulMat i) hi z).symm

open Polynomial Matrix in
variable {B B' : Type} [CommRing B] [CommRing B'] (s : B →+* B) {s' : B' →+* B'} in
variable {s} in
variable (P : _root_.GlobalTheory.UTr.Csr s) in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable {J : Matrix n n B} in
variable {P} in
variable {x x' : _root_.GlobalTheory.UTr.Alg P} in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = φ.mapMatrix (aeval g q)`. Rewrite using `[aeval_def, aeval_def, eval₂_map, hom_eval₂]`. Use `congr 1`. Use `RingHom.ext fun b => ?_` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[algebraMap_matrix_apply, apply_ite φ]`.
-/
theorem _root_.GlobalTheory.UTr.aeval_map_map (φ : B →+* B') (g : Matrix n n B) (q : B[X]) :
    aeval (g.map φ) (q.map φ) = (aeval g q).map φ := by
  change _ = φ.mapMatrix (aeval g q)
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1
  refine RingHom.ext fun b => ?_
  ext i j
  simp [algebraMap_matrix_apply, apply_ite φ]

/- English proof (translation)
Proceed by induction on `z using Alg.induction with`. Consider the case `hC b`. Rewrite using `[algMap_algebraMap, AlgHom.commutes, AlgHom.commutes]`. Use extensionality with `i j`. Simplify using `[Matrix.algebraMap_matrix_apply, apply_ite φ]`.

Consider the case `hr => rw [algMap_root, evalMat_root, evalMat_root]`. Consider the case `hadd y z hy hz => rw [map_add, map_add, map_add, hy, hz, Matrix.map_add _ (map_add φ)]`. Consider the case `hmul y z hy hz => rw [map_mul, map_mul, map_mul, hy, hz, Matrix.map_mul]`.
-/
theorem evalMat_algMap {Q : Csr s'} (φ : B →+* B') (h : Q.1 ∣ P.1.map φ) {g : Matrix n n B} (hg : aeval g P.1 = 0)
    (hg' : aeval (g.map φ) Q.1 = 0) (z : Alg P) : evalMat Q _ hg' (algMap φ h z) = (evalMat P g hg z).map φ := by
  induction z using Alg.induction with
  | hC b =>
    rw [algMap_algebraMap, AlgHom.commutes, AlgHom.commutes]
    ext i j
    simp [Matrix.algebraMap_matrix_apply, apply_ite φ]
  | hr => rw [algMap_root, evalMat_root, evalMat_root]
  | hadd y z hy hz => rw [map_add, map_add, map_add, hy, hz, Matrix.map_add _ (map_add φ)]
  | hmul y z hy hz => rw [map_mul, map_mul, map_mul, hy, hz, Matrix.map_mul]

/- English proof (translation)
Establish `hg` using `h.aeval_eq_zero`. Take `⟨i, hi⟩` from `h`. Establish `hg' : aeval (g.map φ) Q.1 = 0` using `by rw [hQ, aeval_map_map, hg, Matrix.map_zero _ (map_zero φ)]`. Set `l : Alg Q →ₗ[B'] (n → B')` to `{ toFun := fun z => evalMat Q _ hg' z *ᵥ (φ ∘ i 1) map_add' := fun y z => by rw [map_add, Matrix.add_mulVec] map_smul' := fun c z => by rw [map_smul, Matrix.smul_mulVec]; rfl }`. Establish `hl : ∀ z, l (algMap φ hQ.dvd z) = φ ∘ i z` using `fun z => by`.

Express the relevant statement in the definitionally equal form `evalMat Q _ hg' _ *ᵥ _ = _`. Rewrite using `[evalMat_algMap φ _ hg, evalMat_eq_mulMat hg hi, ← mul_one z, ← mulMat_mulVec, mul_one]`. Use function extensionality and compare the values at `a`. Conclude with `(RingHom.map_mulVec φ _ _ a).symm`. Establish `hs : Function.Surjective l`.

Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun B' n).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Use `⟨algMap φ hQ.dvd (i.symm (Pi.single a 1)), ?_⟩` and prove the remaining obligations. Rewrite using `[hl, i.apply_symm_apply]`. Use function extensionality and compare the values at `b`.

Simplify using `[Pi.single_apply, apply_ite φ]`. Establish `hb : Function.Bijective l`. Break down `subsingleton_or_nontrivial B' with hB | hB` into its components or cases. Use `haveI := Module.subsingleton B' (Alg Q)`. Conclude with `⟨fun _ _ _ => Subsingleton.elim _ _, hs⟩`.

Use `haveI := φ.domain_nontrivial`. Use `OrzechProperty.bijective_of_surjective_of_finrank_le l hs ?_` and prove the remaining obligations. Rewrite using `[Module.finrank_eq_card_basis (powBasis Q), Fintype.card_fin, hQ, P.2.1.natDegree_map, Module.finrank_fintype_fun_eq_card, ← Module.finrank_fintype_fun_eq_card B, ← i.finrank_eq, Module.finrank_eq_card_basis (powBasis P), Fintype.card_fin]`. Use `⟨LinearEquiv.ofBijective l hb, (eq_mulMat _ fun y => ?_).symm⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g.map φ *ᵥ (evalMat Q _ hg' y *ᵥ _) = evalMat Q _ hg' (root Q * y) *ᵥ _`.

Rewrite using `[map_mul, evalMat_root, Matrix.mulVec_mulVec]`.
-/
theorem IsCyc.map {g : Matrix n n B} (h : IsCyc P g) (φ : B →+* B') {Q : Csr s'} (hQ : Q.1 = P.1.map φ) :
    IsCyc Q (g.map φ) := by
  have hg := h.aeval_eq_zero
  obtain ⟨i, hi⟩ := h
  have hg' : aeval (g.map φ) Q.1 = 0 := by rw [hQ, aeval_map_map, hg, Matrix.map_zero _ (map_zero φ)]
  let l : Alg Q →ₗ[B'] (n → B') :=
    { toFun := fun z => evalMat Q _ hg' z *ᵥ (φ ∘ i 1)
      map_add' := fun y z => by rw [map_add, Matrix.add_mulVec]
      map_smul' := fun c z => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  have hl : ∀ z, l (algMap φ hQ.dvd z) = φ ∘ i z := fun z => by
    change evalMat Q _ hg' _ *ᵥ _ = _
    rw [evalMat_algMap φ _ hg, evalMat_eq_mulMat hg hi, ← mul_one z, ← mulMat_mulVec, mul_one]
    funext a; exact (RingHom.map_mulVec φ _ _ a).symm
  have hs : Function.Surjective l := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun B' n).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨algMap φ hQ.dvd (i.symm (Pi.single a 1)), ?_⟩
    rw [hl, i.apply_symm_apply]
    funext b; simp [Pi.single_apply, apply_ite φ]
  have hb : Function.Bijective l := by
    rcases subsingleton_or_nontrivial B' with hB | hB
    · haveI := Module.subsingleton B' (Alg Q)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, hs⟩
    · haveI := φ.domain_nontrivial
      refine OrzechProperty.bijective_of_surjective_of_finrank_le l hs ?_
      rw [Module.finrank_eq_card_basis (powBasis Q), Fintype.card_fin, hQ, P.2.1.natDegree_map,
        Module.finrank_fintype_fun_eq_card, ← Module.finrank_fintype_fun_eq_card B, ← i.finrank_eq,
        Module.finrank_eq_card_basis (powBasis P), Fintype.card_fin]
  refine ⟨LinearEquiv.ofBijective l hb, (eq_mulMat _ fun y => ?_).symm⟩
  change g.map φ *ᵥ (evalMat Q _ hg' y *ᵥ _) = evalMat Q _ hg' (root Q * y) *ᵥ _
  rw [map_mul, evalMat_root, Matrix.mulVec_mulVec]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `resultant (X - C α) (X - C β) = α - β`. Rewrite using `[natDegree_X_sub_C α, resultant_X_sub_C_left _ _ _ le_rfl]`. Simplify using the standard rewrite rules.
-/
example [Nontrivial B] {α β : B} (hα : s α * α = 1) (hβ : s β * β = 1) :
    (Csr.mulFactorisation ⟨X - C α, isCsr_X_sub_C.2 hα⟩ ⟨X - C β, isCsr_X_sub_C.2 hβ⟩).res = α - β := by
  change resultant (X - C α) (X - C β) = α - β
  rw [natDegree_X_sub_C α, resultant_X_sub_C_left _ _ _ le_rfl]; simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨isCsr_X_sub_C.2 (by simp), fun h => by have := isCsr_X_sub_C.1 h rw [map_ofNat] at this; norm_num at this⟩`.
-/
example : IsCsr (starRingEnd ℂ) (X - C Complex.I) ∧ ¬ IsCsr (starRingEnd ℂ) (X - C 2) :=
  ⟨isCsr_X_sub_C.2 (by simp), fun h => by
    have := isCsr_X_sub_C.1 h
    rw [map_ofNat] at this; norm_num at this⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨if_neg fun ⟨u, hu⟩ => by rw [Complex.mul_conj] at hu have : (-1 : ℝ) = Complex.normSq u := by exact_mod_cast hu linarith [Complex.normSq_nonneg u], if_pos ⟨Units.mk0 (1 + Complex.I) (fun h => by simpa using congrArg Complex.re h), by simp [Complex.ext_iff]; norm_num⟩⟩`.
-/
example : normSign (starRingEnd ℂ) (-1) = -1 ∧ normSign (starRingEnd ℂ) 2 = 1 :=
  ⟨if_neg fun ⟨u, hu⟩ => by
    rw [Complex.mul_conj] at hu
    have : (-1 : ℝ) = Complex.normSq u := by exact_mod_cast hu
    linarith [Complex.normSq_nonneg u],
  if_pos ⟨Units.mk0 (1 + Complex.I) (fun h => by simpa using congrArg Complex.re h), by
    simp [Complex.ext_iff]; norm_num⟩⟩

end GlobalTheory.UTr
