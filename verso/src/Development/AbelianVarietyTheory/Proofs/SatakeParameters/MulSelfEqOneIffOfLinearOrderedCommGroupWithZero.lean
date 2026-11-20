import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

abbrev W1 (L : Type) : Type := Matrix (Fin 1) (Fin 1) L

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_int {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

/- English proof (translation)
Take `⟨-, -, -, -, -, h2, hc⟩` from `h`. Set `O` to `(Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring`. Establish `hc' : Nat.card (IsLocalRing.ResidueField O) = q ^ 2` using `hc`. Use `haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)`. Use `haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)`.

Establish `h0 : ((q ^ 2 : ℕ) : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← hc', Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero _`. Establish `hle : Valued.v (2 : L) ≤ 1` using `(2 : O).2`. Assume the negation of the conclusion as `hne`.

Establish `hlt : Valued.v (2 : L) < 1` using `lt_of_le_of_ne hle hne`. Establish `hm : (2 : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[Valuation.mem_maximalIdeal_iff]`. Conclude with `hlt`. Establish `h2' : (2 : IsLocalRing.ResidueField O) = 0`.

Use `(IsLocalRing.residue_eq_zero_iff (2 : O)).2 hm` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take `⟨k, hk⟩ : Odd (q ^ 2)` from `hq.pow`. Rewrite `h0` using `[hk]`. Move the coercions through the operations in `at h0`.

Rewrite `h0` using `[h2']`. Simplify using `at h0`.
-/
theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc' : Nat.card (IsLocalRing.ResidueField O) = q ^ 2 := hc
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  have h0 : ((q ^ 2 : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← hc', Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  have hle : Valued.v (2 : L) ≤ 1 := (2 : O).2
  by_contra hne
  have hlt : Valued.v (2 : L) < 1 := lt_of_le_of_ne hle hne
  have hm : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h2' : (2 : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (2 : O)).2 hm
    rwa [map_ofNat] at this
  obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
  rw [hk] at h0
  push_cast at h0
  rw [h2'] at h0
  simp at h0

def bb (σ : L →+* L) (δ : L) (x y : L) : L := (δ * (σ y * x) + σ (δ * (σ y * x))) / 2

def rho0 (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) (x : L) : Module.End ℂ (L → ℂ) where
  toFun φ := fun w => ψ (bb σ δ w x) * φ (w + x)
  map_add' φ φ' := by funext w; simp [mul_add]
  map_smul' c φ := by funext w; simp [mul_left_comm]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Use function extensionality and compare the values at `w`. Use `show ψ (bb σ δ w x) * (ψ (bb σ δ (w + x) y) * φ (w + x + y)) = ψ (bb σ δ x y) * (ψ (bb σ δ w (x + y)) * φ (w + (x + y)))`. Rewrite using `[← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc]`. Use `congr 2`. Simplify using `only [bb, map_add, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem residual_rep_mul (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) (x y : L) (φ : L → ℂ) :
    rho0 σ δ ψ x (rho0 σ δ ψ y φ) = ψ (bb σ δ x y) • rho0 σ δ ψ (x + y) φ := by
  funext w
  show ψ (bb σ δ w x) * (ψ (bb σ δ (w + x) y) * φ (w + x + y)) = ψ (bb σ δ x y) * (ψ (bb σ δ w (x + y)) * φ (w + (x + y)))
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [bb, map_add, map_mul]; ring

open Classical in

def vac0 (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : L → ℂ := fun w => if w ∈ intL L then 1 else 0

def Mod (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) : Submodule ℂ (L → ℂ) := Submodule.span ℂ (Set.range fun x => rho0 σ δ ψ x (vac0 L))

/- English proof (translation)
Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ h`. Take `⟨y, rfl⟩` from `h`. Rewrite using `[residual_rep_mul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem weil_rep_mem_module (σ : L →+* L) (δ : L) (ψ : AddChar L ℂ) (x : L) : ∀ φ ∈ Mod σ δ ψ, rho0 σ δ ψ x φ ∈ Mod σ δ ψ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨y, rfl⟩ := h
    rw [residual_rep_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

def sub0 (u : L) : Module.End ℂ (L → ℂ) where
  toFun φ := fun w => φ (u * w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Use function extensionality and compare the values at `w`. Use `show ψ (bb σ δ (u * w) x) * φ (u * w + x) = ψ (bb σ δ w (σ u * x)) * φ (u * (w + σ u * x))`. Establish `: u * (w + σ u * x) = u * w + x` using `by linear_combination x * hu`. Rewrite using `[this]`. Use `congr 2`.

Simplify using `only [bb, map_mul, hσ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem translate_weil_rep_comm (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (δ : L) (ψ : AddChar L ℂ) {u : L} (hu : σ u * u = 1) (x : L) (φ : L → ℂ) :
    sub0 u (rho0 σ δ ψ x φ) = rho0 σ δ ψ (σ u * x) (sub0 u φ) := by
  funext w
  show ψ (bb σ δ (u * w) x) * φ (u * w + x) = ψ (bb σ δ w (σ u * x)) * φ (u * (w + σ u * x))
  have : u * (w + σ u * x) = u * w + x := by linear_combination x * hu
  rw [this]
  congr 2
  simp only [bb, map_mul, hσ]; ring

/- English proof (translation)
Establish `h` using `congrArg Valued.v hu`. Rewrite `h` using `[map_mul, hv, map_one]`. Conclude with `(mul_self_eq_one_iff_of_linearOrderedCommGroupWithZero h)`. Use `where mul_self_eq_one_iff_of_linearOrderedCommGroupWithZero {a : WithZero (Multiplicative ℤ)} (h : a * a = 1) : a = 1 := by`. Break down `lt_trichotomy a 1 with h1 | h1 | h1` into its components or cases.

Conclude with `absurd h (ne_of_lt (mul_lt_one_of_lt_of_le h1 h1.le))`. Conclude with `h1`. Conclude with `absurd h (ne_of_gt (one_lt_mul_of_lt_of_le h1 h1.le))`.
-/
theorem v_of_norm {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {u : L} (hu : σ u * u = 1) : Valued.v u = 1 := by
  have h := congrArg Valued.v hu
  rw [map_mul, hv, map_one] at h
  exact (mul_self_eq_one_iff_of_linearOrderedCommGroupWithZero h)
where
  mul_self_eq_one_iff_of_linearOrderedCommGroupWithZero {a : WithZero (Multiplicative ℤ)} (h : a * a = 1) : a = 1 := by
    rcases lt_trichotomy a 1 with h1 | h1 | h1
    · exact absurd h (ne_of_lt (mul_lt_one_of_lt_of_le h1 h1.le))
    · exact h1
    · exact absurd h (ne_of_gt (one_lt_mul_of_lt_of_le h1 h1.le))

/- English proof (translation)
Use function extensionality and compare the values at `w`. Use `show vac0 L (u * w) = vac0 L w`. Simplify using `only [vac0, mem_int, map_mul, hu, one_mul]`.
-/
theorem translate_vacuum_unit {u : L} (hu : Valued.v u = 1) : sub0 u (vac0 L) = vac0 L := by
  funext w
  show vac0 L (u * w) = vac0 L w
  simp only [vac0, mem_int, map_mul, hu, one_mul]

section Main

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ}

abbrev U1 (σ : L →+* L) : Type := UJ σ ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)

def ent (g : U1 σ) : L := ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) 0 0

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Establish `hg : cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) = ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L)` using `g.2`. Use `congrFun (congrFun hg 0) 0` as an intermediate fact. Simplify `this` using `[cT, Matrix.mul_apply, ent]`.
-/
theorem ent_norm (g : U1 σ) : σ (ent g) * ent g = 1 := by
  have hg : cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) *
    ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) = ((1 : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) := g.2
  have := congrFun (congrFun hg 0) 0
  simpa [cT, Matrix.mul_apply, ent] using this

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Simplify using `[ent, Matrix.mul_apply]`.
-/
theorem ent_mul (g g' : U1 σ) : ent (g * g') = ent g * ent g' := by
  simp [ent, Matrix.mul_apply]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Rewrite using `[map_mul, hσ]`. Take the linear combination `(σ (ent p.1) * ent p.1) * ent_norm p.2 + ent_norm p.1`.
-/
theorem uu_norm (hσ : ∀ x, σ (σ x) = x) (p : U1 σ × U1 σ) : σ (σ (ent p.2) * ent p.1) * (σ (ent p.2) * ent p.1) = 1 := by
  rw [map_mul, hσ]
  linear_combination (σ (ent p.1) * ent p.1) * ent_norm p.2 + ent_norm p.1

/- English proof (translation)
Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ hφ`. Take `⟨y, rfl⟩` from `hφ`. Rewrite using `[translate_weil_rep_comm σ h.1 δ ψ hu, translate_vacuum_unit (v_of_norm h.2.1 hu)]`.

Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem translate_mem_weil_module (h : IsUnramInv ϖ σ q) {u : L} (hu : σ u * u = 1) : ∀ φ ∈ Mod σ δ ψ, sub0 u φ ∈ Mod σ δ ψ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨y, rfl⟩ := hφ
    rw [translate_weil_rep_comm σ h.1 δ ψ hu, translate_vacuum_unit (v_of_norm h.2.1 hu)]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

variable (σ δ ψ) in

def rho (x : W1 L) : Module.End ℂ (Mod σ δ ψ) := (rho0 σ δ ψ (x 0 0)).restrict (weil_rep_mem_module σ δ ψ (x 0 0))

variable (δ ψ) in

def om (h : IsUnramInv ϖ σ q) : U1 σ × U1 σ →* Module.End ℂ (Mod σ δ ψ) where
  toFun p := (sub0 (σ (ent p.2) * ent p.1)).restrict (translate_mem_weil_module h (uu_norm h.1 p))
  map_one' := by
    ext φ w
    show (φ : L → ℂ) (σ (ent 1) * ent 1 * w) = (φ : L → ℂ) w
    simp [ent]
  map_mul' p p' := by
    ext φ w
    show (φ : L → ℂ) (σ (ent (p.2 * p'.2)) * ent (p.1 * p'.1) * w) =
      (φ : L → ℂ) (σ (ent p'.2) * ent p'.1 * (σ (ent p.2) * ent p.1 * w))
    rw [ent_mul, ent_mul, map_mul]; congr 1; ring

/- English proof (translation)
Use function extensionality and compare the values at `w`. Use `show ψ (bb σ δ w 0) * φ (w + 0) = φ w`. Simplify using `[bb]`.
-/
theorem weil_rep_zero (φ : L → ℂ) : rho0 σ δ ψ 0 φ = φ := by
  funext w
  show ψ (bb σ δ w 0) * φ (w + 0) = φ w
  simp [bb]

variable (σ δ ψ) in

def vac : Mod σ δ ψ := ⟨vac0 L, Submodule.subset_span ⟨0, weil_rep_zero _⟩⟩

end Main

section Laurent

abbrev K9 : Type := GaloisField 3 2

def frobL : LaurentSeries K9 →+* LaurentSeries K9 where
  toFun f := f.map (frobenius K9 3)
  map_one' := HahnSeries.map_one (frobenius K9 3).toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (frobenius K9 3).toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/- English proof (translation)
Rewrite using `[GaloisField.card 3 2 (by norm_num)]; norm_num`.
-/
theorem card_field_nine : Nat.card K9 = 9 := by rw [GaloisField.card 3 2 (by norm_num)]; norm_num

/- English proof (translation)
Use `haveI := Fintype.ofFinite K9`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hd : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K9).natDegree = 3` using `by compute_degree!`. Establish `hne : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K9) ≠ 0` using `fun h0 => by simp [h0] at hd`.

Use `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Polynomial.X ^ 3 - Polynomial.X : Polynomial K9) (f := id) Function.injective_id (fun a => by simp [h a]) (by rw [hd, ← Nat.card_eq_fintype_card, card_field_nine]; norm_num)` as an intermediate fact. Conclude with `hne this`.
-/
theorem exists_ne : ∃ a : K9, a ^ 3 ≠ a := by
  haveI := Fintype.ofFinite K9
  classical
  by_contra h
  push Not at h
  have hd : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K9).natDegree = 3 := by compute_degree!
  have hne : (Polynomial.X ^ 3 - Polynomial.X : Polynomial K9) ≠ 0 := fun h0 => by simp [h0] at hd
  have := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Polynomial.X ^ 3 - Polynomial.X : Polynomial K9)
    (f := id) Function.injective_id (fun a => by simp [h a]) (by rw [hd, ← Nat.card_eq_fintype_card, card_field_nine]; norm_num)
  exact hne this

end Laurent

end GlobalTheory.Hk3.Inh

end
