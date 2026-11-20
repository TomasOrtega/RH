import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.Qk

section Per
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[cv]`.
-/
theorem cv_add (M Nn : Fin g → ℤ) : cv (M + Nn) = cv M + cv Nn := by funext i; simp [cv]
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[cv]`.
-/
theorem cv_sub (M Nn : Fin g → ℤ) : cv (M - Nn) = cv M - cv Nn := by funext i; simp [cv]
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[cv]`.
-/
theorem cv_nsmul (k : ℕ) (M : Fin g → ℤ) : cv ((k : ℤ) • M) = k • cv M := by funext i; simp [cv]

/- English proof (translation)
Simplify using `only [perV, cv_add, mulVec_add]`. Normalize the expressions using the abelian group laws.
-/
theorem perV_add (M Nn M' Nn' : Fin g → ℤ) : perV τ (M + M') (Nn + Nn') = perV τ M Nn + perV τ M' Nn' := by
  simp only [perV, cv_add, mulVec_add]; abel

/- English proof (translation)
Simplify using `only [perV, cv_sub, mulVec_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem perV_sub (M Nn M' Nn' : Fin g → ℤ) : perV τ (M - M') (Nn - Nn') = perV τ M Nn - perV τ M' Nn' := by
  simp only [perV, cv_sub, mulVec_sub]; abel

/- English proof (translation)
Simplify using `only [perV, cv_nsmul, mulVec_smul, smul_add]`.
-/
theorem perV_nsmul (k : ℕ) (M Nn : Fin g → ℤ) : perV τ ((k : ℤ) • M) ((k : ℤ) • Nn) = k • perV τ M Nn := by
  simp only [perV, cv_nsmul, mulVec_smul, smul_add]

/- English proof (translation)
Establish `hN : Nn = 0`. Assume the negation of the conclusion as `hne`. Establish `hx : (fun i => (Nn i : ℝ)) ≠ 0` using `fun e => hne (funext fun i => by simpa using congrFun e i)`. Establish `h1` using `hp.dotProduct_mulVec_pos hx`. Establish `h2 : (τ.map Complex.im) *ᵥ (fun i => (Nn i : ℝ)) = 0`.

Use function extensionality and compare the values at `i`. Use `congrArg Complex.im (congrFun h i)` as an intermediate fact. Simplify `this` using `[perV, cv, mulVec, dotProduct, Complex.im_sum]`. Rewrite `h1` using `[h2]`. Simplify using `at h1`.

Substitute `hN` using the available equality. Use `⟨funext fun i => ?_, rfl⟩` and prove the remaining obligations. Use `congrFun h i` as an intermediate fact. Simplify `this` using `[perV, cv, mulVec, dotProduct]`.
-/
theorem perV_eq_zero (hp : (τ.map Complex.im).PosDef) {M Nn : Fin g → ℤ} (h : perV τ M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have hN : Nn = 0 := by
    by_contra hne
    have hx : (fun i => (Nn i : ℝ)) ≠ 0 := fun e => hne (funext fun i => by simpa using congrFun e i)
    have h1 := hp.dotProduct_mulVec_pos hx
    have h2 : (τ.map Complex.im) *ᵥ (fun i => (Nn i : ℝ)) = 0 := by
      funext i
      have := congrArg Complex.im (congrFun h i)
      simpa [perV, cv, mulVec, dotProduct, Complex.im_sum] using this
    rw [h2] at h1
    simp at h1
  subst hN
  refine ⟨funext fun i => ?_, rfl⟩
  have := congrFun h i
  simpa [perV, cv, mulVec, dotProduct] using this

end Per

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

/- English proof (translation)
Establish `h1 : perV d.τ (zP σ M) (zP σ Nn) = 0`. Use `congrArg (zP σ) h` as an intermediate fact. Rewrite `this` using `[Exp.leftComponent_periodVector, h0, Exp.cv_zero, mulVec_zero, add_zero]`. Conclude with `this`. Take `⟨a, b⟩` from `perV_eq_zero d.pos h1`.

Establish `h2 : tP σ M = 0`. Use `congrArg (tP σ) h` as an intermediate fact. Rewrite `this` using `[Exp.secondBlock_periodVector, h0, b, Exp.cv_zero, Exp.cv_zero, mulVec_zero, mulVec_zero, add_zero, add_zero]`. Use function extensionality and compare the values at `l`. Use `congrFun this l` as an intermediate fact.

Simplify `this` using `[cv, tP]`. Conclude with `⟨Exp.ext_zP_tP σ a h2, Exp.ext_zP_tP σ b h0⟩`.
-/
theorem eq_zero_of_perV_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) {M Nn : Fin g → ℤ} (h0 : tP σ Nn = 0)
    (h : perV (d.full σ 0) M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have h1 : perV d.τ (zP σ M) (zP σ Nn) = 0 := by
    have := congrArg (zP σ) h
    rw [Exp.leftComponent_periodVector, h0, Exp.cv_zero, mulVec_zero, add_zero] at this
    exact this
  obtain ⟨a, b⟩ := perV_eq_zero d.pos h1
  have h2 : tP σ M = 0 := by
    have := congrArg (tP σ) h
    rw [Exp.secondBlock_periodVector, h0, b, Exp.cv_zero, Exp.cv_zero, mulVec_zero, mulVec_zero, add_zero, add_zero] at this
    funext l
    have := congrFun this l
    simpa [cv, tP] using this
  exact ⟨Exp.ext_zP_tP σ a h2, Exp.ext_zP_tP σ b h0⟩

def yv (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) : N.X := ∑ l, tP σ Nn l • bX l

/- English proof (translation)
Simplify using `[yv, tP, add_smul, Finset.sum_add_distrib]`.
-/
theorem yv_add (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a + b) = yv bX σ a + yv bX σ b := by
  simp [yv, tP, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[yv, tP, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem yv_sub (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a - b) = yv bX σ a - yv bX σ b := by
  simp [yv, tP, sub_smul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[yv, tP, Finset.smul_sum, mul_smul]`.
-/
theorem yv_nsmul (σ : Fin g ≃ Fin g' ⊕ Fin r) (k : ℕ) (a : Fin g → ℤ) : yv bX σ ((k : ℤ) • a) = k • yv bX σ a := by
  simp [yv, tP, Finset.smul_sum, mul_smul]

/- English proof (translation)
Simplify using `[yv, h]`.
-/
theorem yv_of_tP (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : tP σ a = 0) : yv bX σ a = 0 := by
  simp [yv, h]

/- English proof (translation)
Use `Exp.co_sum (bX := bX) (tP σ a)` as an intermediate fact. Express the relevant statement in the definitionally equal form `co bX (yv bX σ a) = _ at this`. Rewrite `this` using `[h]`. Use function extensionality and compare the values at `l`. Use `congrFun this l` as an intermediate fact.

Simplify `this.symm` using `[co, cv]`.
-/
theorem tP_of_yv (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : yv bX σ a = 0) : tP σ a = 0 := by
  have := Exp.co_sum (bX := bX) (tP σ a)
  change co bX (yv bX σ a) = _ at this
  rw [h] at this
  funext l
  have := congrFun this l
  simpa [co, cv] using this.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨Exp.asm σ 0 (bX.repr z), by rw [yv, Exp.secondBlock_assemble]; exact bX.sum_repr z⟩`.
-/
theorem yv_surj (σ : Fin g ≃ Fin g' ⊕ Fin r) (z : N.X) : ∃ a, yv bX σ a = z :=
  ⟨Exp.asm σ 0 (bX.repr z), by rw [yv, Exp.secondBlock_assemble]; exact bX.sum_repr z⟩

end GlobalTheory.MBLow.Cl.Qk

namespace GlobalTheory.MBLow.Cl
open Qk

/- English proof (translation)
Introduce `N g' r g bX d σ k hk`. Take `⟨h1, h2, h3, h4, h5⟩` from `exp_onto_torusExt N g' r g bX d σ`. Use `choose E hE hU using h1`. Establish `hiff : ∀ v h, d.IsPt σ v h ↔ h = E v` using `fun v h => ⟨hU v h, fun e => e ▸ hE v⟩`. Establish `hadd : ∀ v v', E (v + v') = E v * E v'` using `fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm`.

Establish `hzero : E 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`. Establish `hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n` using `fun n v => by`.

Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, pow_zero, hzero]`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`. Establish `hper : ∀ M Nn, E (perV (d.full σ 0) M Nn) = N.io (yv bX σ Nn)` using `fun M Nn => (hU _ _ (h5 M Nn)).symm`. Establish `hker : ∀ v v', E v = E v' → ∃ M Nn, tP σ Nn = 0 ∧ v = v' + perV (d.full σ 0) M Nn` using `fun v v' h => by`.

Establish `e : E (v - v') * E v' = E v'` using `by rw [← hadd, sub_add_cancel, h]`. Take `⟨M, Nn, hy, hl⟩` from `(h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)`. Conclude with `⟨M, Nn, hy, by rw [← hl, add_sub_cancel]⟩`. Establish `hk0 : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `hc1 : ∀ v : Fin g → ℂ, (k : ℂ)⁻¹ • (k • v) = v` using `fun v => by`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]`. Establish `hc2 : ∀ v : Fin g → ℂ, k • ((k : ℂ)⁻¹ • v) = v` using `fun v => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]`. Establish `hrep : ∀ M Nn (p : N.QT k), d.Rep σ k M Nn p ↔ p.1.1.toAdd = yv bX σ Nn ∧ p.1.2 = E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)` using `fun M Nn p => and_congr Iff.rfl (hiff _ _)`. Use `⟨fun p => ?_, fun M Nn => ?_, fun M Nn M' Nn' p p' h h' => ?_, fun M Nn M' Nn' p p' h h' => ?_⟩` and prove the remaining obligations.

Take `⟨v, hv⟩` from `h2 p.1.2`. Establish `hv'` using `(hiff _ _).1 hv`. Take `⟨a, ha⟩` from `yv_surj (bX := bX) σ p.1.1.toAdd`. Establish `e : E (k • v) = E (perV (d.full σ 0) 0 a)`. Rewrite using `[hpow, hper, ← hv', ha]`.

Conclude with `N.mem_QT.1 p.2`. Take `⟨M, Nn, hy, hl⟩` from `hker _ _ e`. Use `⟨0 + M, a + Nn, (hrep _ _ _).2 ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[yv_add, yv_of_tP σ hy, add_zero, ha]`. Rewrite using `[perV_add, ← hl, hc1, hv']`.

Use `⟨⟨(Multiplicative.ofAdd (yv bX σ Nn), E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)), ?_⟩, (hrep _ _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite using `[NumD.mem_QT, ← hpow, hc2, hper]`. Both sides reduce to the same expression. Take `⟨a, b⟩` from `(hrep _ _ _).1 hp`. Conclude with `Subtype.ext (Prod.ext a b)`.

Take `⟨a, b⟩` from `(hrep _ _ _).1 h`. Take `⟨a', b'⟩` from `(hrep _ _ _).1 h'`. Use `(hrep _ _ _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[yv_add, ← a, ← a']`. Both sides reduce to the same expression.

Rewrite using `[perV_add, smul_add, hadd, ← b, ← b']`. Both sides reduce to the same expression. Take `⟨a, b⟩` from `(hrep _ _ _).1 h`. Take `⟨a', b'⟩` from `(hrep _ _ _).1 h'`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, c, c'⟩`. Take `⟨z₀, hz⟩` from `yv_surj (bX := bX) σ z`. Establish `e : E ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') = E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn + perV (d.full σ 0) 0 z₀)`. Rewrite using `[hadd, hper, hz, ← b, ← b', c']`. Take `⟨M₀, N₀, hy, hl⟩` from `hker _ _ e`.

Establish `key` using `eq_zero_of_perV_full d σ (M := M' - (M + (k : ℤ) • (0 + M₀))) (Nn := Nn' - (Nn + (k : ℤ) • (z₀ + N₀))) ?_ ?_`. Conclude with `⟨0 + M₀, z₀ + N₀, sub_eq_zero.1 key.1, sub_eq_zero.1 key.2⟩`. Apply `tP_of_yv (bX := bX)` to reduce the goal to its premises. Rewrite using `[yv_sub, yv_add, yv_nsmul, yv_add, yv_of_tP σ hy, add_zero, hz, ← a, ← a', c, sub_self]`. Rewrite using `[perV_sub, perV_add, perV_nsmul, perV_add, ← hc2 (perV (d.full σ 0) M' Nn'), hl, add_assoc, smul_add, hc2, sub_self]`.

Introduce and unpack `⟨M₁, N₁, rfl, rfl⟩`. Use `⟨yv bX σ N₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[a, a', yv_add, yv_nsmul]`. Rewrite using `[b, b', perV_add, perV_nsmul, smul_add, hc1, hadd, hper]`.
-/
theorem torsion_eq_periods_mod : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → (∀ p, ∃ M Nn, d.Rep σ k M Nn p) ∧ (∀ M Nn, ∃! p, d.Rep σ k M Nn p) ∧ (∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → d.Rep σ k (M + M') (Nn + Nn') (p * p')) ∧ ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → (N.QEq p p' ↔ ∃ M₁ N₁, M' = M + (k : ℤ) • M₁ ∧ Nn' = Nn + (k : ℤ) • N₁) := by
  intro N g' r g bX d σ k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := exp_onto_torusExt N g' r g bX d σ
  choose E hE hU using h1
  have hiff : ∀ v h, d.IsPt σ v h ↔ h = E v := fun v h => ⟨hU v h, fun e => e ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ M Nn, E (perV (d.full σ 0) M Nn) = N.io (yv bX σ Nn) := fun M Nn => (hU _ _ (h5 M Nn)).symm
  have hker : ∀ v v', E v = E v' → ∃ M Nn, tP σ Nn = 0 ∧ v = v' + perV (d.full σ 0) M Nn := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨M, Nn, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨M, Nn, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : Fin g → ℂ, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : Fin g → ℂ, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ M Nn (p : N.QT k), d.Rep σ k M Nn p ↔
      p.1.1.toAdd = yv bX σ Nn ∧ p.1.2 = E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn) :=
    fun M Nn p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun M Nn => ?_, fun M Nn M' Nn' p p' h h' => ?_, fun M Nn M' Nn' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    obtain ⟨a, ha⟩ := yv_surj (bX := bX) σ p.1.1.toAdd
    have e : E (k • v) = E (perV (d.full σ 0) 0 a) := by
      rw [hpow, hper, ← hv', ha]
      exact N.mem_QT.1 p.2
    obtain ⟨M, Nn, hy, hl⟩ := hker _ _ e
    refine ⟨0 + M, a + Nn, (hrep _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [yv_add, yv_of_tP σ hy, add_zero, ha]
    · rw [perV_add, ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (yv bX σ Nn), E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)), ?_⟩,
      (hrep _ _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    refine (hrep _ _ _).2 ⟨?_, ?_⟩
    · rw [yv_add, ← a, ← a']
      rfl
    · rw [perV_add, smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      obtain ⟨z₀, hz⟩ := yv_surj (bX := bX) σ z
      have e : E ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') =
          E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn + perV (d.full σ 0) 0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨M₀, N₀, hy, hl⟩ := hker _ _ e
      have key := eq_zero_of_perV_full d σ (M := M' - (M + (k : ℤ) • (0 + M₀)))
        (Nn := Nn' - (Nn + (k : ℤ) • (z₀ + N₀))) ?_ ?_
      · exact ⟨0 + M₀, z₀ + N₀, sub_eq_zero.1 key.1, sub_eq_zero.1 key.2⟩
      · apply tP_of_yv (bX := bX)
        rw [yv_sub, yv_add, yv_nsmul, yv_add, yv_of_tP σ hy, add_zero, hz, ← a, ← a', c, sub_self]
      · rw [perV_sub, perV_add, perV_nsmul, perV_add, ← hc2 (perV (d.full σ 0) M' Nn'), hl, add_assoc, smul_add, hc2,
          sub_self]
    · rintro ⟨M₁, N₁, rfl, rfl⟩
      refine ⟨yv bX σ N₁, ?_, ?_⟩
      · rw [a, a', yv_add, yv_nsmul]
      · rw [b, b', perV_add, perV_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.MBLow.Cl
end
