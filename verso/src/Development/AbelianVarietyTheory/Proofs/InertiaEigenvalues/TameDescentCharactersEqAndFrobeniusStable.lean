import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]

namespace Descent

variable {P : PhiMod O K l e a ι} (Δ : Descent P)

end Descent

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
/- English proof (translation)
Use `set f : ZMod a → K⟦X⟧ := fun ρ => if ρ = σ then 0 else 1 with hf`. Establish `hfx : f • _root_.GlobalTheory.BK.cst x = _root_.GlobalTheory.BK.cst x`. Apply `funext` to reduce the goal to its premises. Introduce `ρ`. Apply `funext` to reduce the goal to its premises.

Introduce `i`. Use `show f ρ * PowerSeries.C (x ρ i) = PowerSeries.C (x ρ i)`. Distinguish the cases in `h : ρ = σ`. Simplify using `[h, hx]`. Simplify using `[hf, h]`.

Establish `key : Δ.actD g x = _root_.GlobalTheory.BK.red (Δ.act g (_root_.GlobalTheory.BK.cst x))` using `rfl`. Rewrite using `[key, ← hfx, _root_.GlobalTheory.BK.Descent.act_smul_tot]`. Use function extensionality and compare the values at `i`. Use `show constantCoeff ((_root_.GlobalTheory.BK.ringAct g f (σ + g.shift)) * (Δ.act g (_root_.GlobalTheory.BK.cst x)) (σ + g.shift) i) = 0`. Rewrite using `[_root_.GlobalTheory.BK.ringAct_apply]`.

Simplify using `[hf]`.
-/
private lemma actD_apply_shift_eq_zero_of_apply_eq_zero {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x : P.D} {σ : ZMod a}
    (hx : x σ = 0) : Δ.actD g x (σ + g.shift) = 0 := by
  classical
  set f : ZMod a → K⟦X⟧ := fun ρ => if ρ = σ then 0 else 1 with hf
  have hfx : f • _root_.GlobalTheory.BK.cst x = _root_.GlobalTheory.BK.cst x := by
    apply funext; intro ρ; apply funext; intro i
    show f ρ * PowerSeries.C (x ρ i) = PowerSeries.C (x ρ i)
    by_cases h : ρ = σ
    · simp [h, hx]
    · simp [hf, h]
  have key : Δ.actD g x = _root_.GlobalTheory.BK.red (Δ.act g (_root_.GlobalTheory.BK.cst x)) := rfl
  rw [key, ← hfx, _root_.GlobalTheory.BK.Descent.act_smul_tot]
  funext i
  show constantCoeff ((_root_.GlobalTheory.BK.ringAct g f (σ + g.shift)) *
    (Δ.act g (_root_.GlobalTheory.BK.cst x)) (σ + g.shift) i) = 0
  rw [_root_.GlobalTheory.BK.ringAct_apply]
  simp [hf]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
/- English proof (translation)
Establish `hxy` using `actD_apply_shift_eq_zero_of_apply_eq_zero Δ g (x := x - y) (σ := σ) (by simp [h])`. Rewrite `hxy` using `[map_sub, Pi.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis.
-/
private lemma actD_apply_shift_eq_of_apply_eq {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (g : _root_.GlobalTheory.BK.TameGal K l e a) {x y : P.D} {σ : ZMod a}
    (h : x σ = y σ) : Δ.actD g x (σ + g.shift) = Δ.actD g y (σ + g.shift) := by
  have hxy := actD_apply_shift_eq_zero_of_apply_eq_zero Δ g (x := x - y) (σ := σ) (by simp [h])
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at hxy

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, map_one, pow_zero]`. Conclude with `_root_.GlobalTheory.BK.TameGal.root_one τ`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, map_mul, _root_.GlobalTheory.BK.TameGal.root_mul, _root_.GlobalTheory.BK.TameGal.shift_inertia, sub_zero, ih, pow_succ]`.
-/
private lemma tameGal_inertia_root_pow (ζ : rootsOfUnity e K) (n : ℕ) (τ : ZMod a) :
    (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ n)).root τ =
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, map_one, pow_zero]
    exact _root_.GlobalTheory.BK.TameGal.root_one τ
  | succ n ih =>
    rw [pow_succ, map_mul, _root_.GlobalTheory.BK.TameGal.root_mul,
      _root_.GlobalTheory.BK.TameGal.shift_inertia, sub_zero, ih, pow_succ]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
/- English proof (translation)
Introduce and unpack `c ⟨x, hx0, hx⟩`. Use `set F : _root_.GlobalTheory.BK.TameGal K l e a := _root_.GlobalTheory.BK.TameGal.fr with hF`. Establish `hFs : F.shift = 1` using `_root_.GlobalTheory.BK.TameGal.shift_fr`. Establish `hFis : (F⁻¹).shift = -1`. Establish `hs` using `_root_.GlobalTheory.BK.TameGal.shift_mul F⁻¹ F`.

Rewrite `hs` using `[inv_mul_cancel, _root_.GlobalTheory.BK.TameGal.shift_one, hFs]`. Take the linear combination `-hs`. Use `⟨Δ.actD F⁻¹ x, fun h => hx0 ?_, fun ζ => ?_⟩` and prove the remaining obligations. Establish `hb` using `actD_apply_shift_eq_of_apply_eq Δ F (x := Δ.actD F⁻¹ x) (y := 0) (σ := τ) (by rw [h]; rfl)`. Rewrite `hb` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero, hFs]`. Then use the resulting hypothesis.

Establish `hcomm : _root_.GlobalTheory.BK.TameGal.inertia ζ * F⁻¹ = F⁻¹ * _root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l)`. Rewrite using `[eq_inv_mul_iff_mul_eq, ← mul_assoc, hF, _root_.GlobalTheory.BK.TameGal.fr_mul_inertia, mul_assoc, mul_inv_cancel, mul_one]`. Establish `hroot : (_root_.GlobalTheory.BK.TameGal.inertia (l` using `l) (ζ ^ l)).root (τ + 1) ^ c.val = (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val := by`. Rewrite using `[tameGal_inertia_root_pow, ← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]`. Establish `hb` using `actD_apply_shift_eq_of_apply_eq Δ F⁻¹ (σ := τ + 1) (x := Δ.actD (_root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l)) x) (y := (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val • x) (by rw [hx, hroot]; rfl)`.

Rewrite `hb` using `[hFis, add_neg_cancel_right, map_smul]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hb, Pi.smul_apply]`.
-/
private lemma chars_succ_subset_chars {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) (τ : ZMod a) :
    Δ.chars (τ + 1) ⊆ Δ.chars τ := by
  rintro c ⟨x, hx0, hx⟩
  set F : _root_.GlobalTheory.BK.TameGal K l e a := _root_.GlobalTheory.BK.TameGal.fr with hF
  have hFs : F.shift = 1 := _root_.GlobalTheory.BK.TameGal.shift_fr
  have hFis : (F⁻¹).shift = -1 := by
    have hs := _root_.GlobalTheory.BK.TameGal.shift_mul F⁻¹ F
    rw [inv_mul_cancel, _root_.GlobalTheory.BK.TameGal.shift_one, hFs] at hs
    linear_combination -hs
  refine ⟨Δ.actD F⁻¹ x, fun h => hx0 ?_, fun ζ => ?_⟩
  · have hb := actD_apply_shift_eq_of_apply_eq Δ F (x := Δ.actD F⁻¹ x) (y := 0) (σ := τ)
      (by rw [h]; rfl)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      map_zero, hFs] at hb
  · have hcomm : _root_.GlobalTheory.BK.TameGal.inertia ζ * F⁻¹ =
        F⁻¹ * _root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hF,
        _root_.GlobalTheory.BK.TameGal.fr_mul_inertia, mul_assoc, mul_inv_cancel, mul_one]
    have hroot : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) (ζ ^ l)).root (τ + 1) ^ c.val =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val := by
      rw [tameGal_inertia_root_pow, ← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have hb := actD_apply_shift_eq_of_apply_eq Δ F⁻¹ (σ := τ + 1)
      (x := Δ.actD (_root_.GlobalTheory.BK.TameGal.inertia (ζ ^ l)) x)
      (y := (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ ^ c.val • x)
      (by rw [hx, hroot]; rfl)
    rw [hFis, add_neg_cancel_right, map_smul] at hb
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hb,
      Pi.smul_apply]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in
/- English proof (translation)
Take `⟨d, hd0, hd⟩` from `hc`. Use `⟨P.phiD d, fun h => hd0 ?_, fun ζ => ?_⟩` and prove the remaining obligations. Establish `heq : P.phiD (Function.update (0 : P.D) τ (d τ)) = P.phiD 0`. Use function extensionality and compare the values at `σ`. Rewrite using `[_root_.GlobalTheory.BK.PhiMod.phiD_apply, map_zero]`.

Distinguish the cases in `hσ : σ - 1 = τ`. Take `rfl` from `eq_add_of_sub_eq hσ`. Rewrite using `[add_sub_cancel_right, Function.update_self, Pi.zero_apply]`. Rewrite `h` using `[_root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right]`. Conclude with `h`.

Simplify using `[Function.update_of_ne hσ]`. Simplify using `using congrFun (P.phiD.injective heq) τ`. Rewrite using `[_root_.GlobalTheory.BK.Descent.actD_phiD, _root_.GlobalTheory.BK.PhiMod.phiD_apply, _root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right, hd, mulVec_smul]`. Use `congr 1`. Establish `hr : (_root_.GlobalTheory.BK.TameGal.inertia (l` using `l) ζ).root τ = (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root (τ + 1) ^ l := by`.

Rewrite using `[← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]`. Establish `he` using `_root_.GlobalTheory.BK.TameGal.root_pow (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ) (τ + 1)`. Rewrite using `[hr, ← pow_mul, pow_eq_pow_mod _ he, pow_eq_pow_mod ((l : ZMod e) * c).val he, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mod, Nat.mod_mul_mod]`.
-/
private lemma prime_mul_mem_chars_succ_of_mem [NeZero e] {P : _root_.GlobalTheory.BK.PhiMod O K l e a ι}
    (Δ : _root_.GlobalTheory.BK.Descent P) {τ : ZMod a} {c : ZMod e}
    (hc : c ∈ Δ.chars τ) :
    (l : ZMod e) * c ∈ Δ.chars (τ + 1) := by
  obtain ⟨d, hd0, hd⟩ := hc
  refine ⟨P.phiD d, fun h => hd0 ?_, fun ζ => ?_⟩
  · have heq : P.phiD (Function.update (0 : P.D) τ (d τ)) = P.phiD 0 := by
      funext σ
      rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, map_zero]
      by_cases hσ : σ - 1 = τ
      · obtain rfl := eq_add_of_sub_eq hσ
        rw [add_sub_cancel_right, Function.update_self, Pi.zero_apply]
        rw [_root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right] at h
        exact h
      · simp [Function.update_of_ne hσ]
    simpa using congrFun (P.phiD.injective heq) τ
  · rw [_root_.GlobalTheory.BK.Descent.actD_phiD, _root_.GlobalTheory.BK.PhiMod.phiD_apply,
      _root_.GlobalTheory.BK.PhiMod.phiD_apply, add_sub_cancel_right, hd, mulVec_smul]
    congr 1
    have hr : (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root τ =
        (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ).root (τ + 1) ^ l := by
      rw [← _root_.GlobalTheory.BK.TameGal.root_sub_one, add_sub_cancel_right]
    have he := _root_.GlobalTheory.BK.TameGal.root_pow
      (_root_.GlobalTheory.BK.TameGal.inertia (l := l) ζ) (τ + 1)
    rw [hr, ← pow_mul, pow_eq_pow_mod _ he, pow_eq_pow_mod ((l : ZMod e) * c).val he,
      ZMod.val_mul, ZMod.val_natCast, Nat.mod_mod, Nat.mod_mul_mod]

open PowerSeries Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a] in

/- English proof (translation)
Establish `hle : ∀ (τ : ZMod a) (n : ℕ), Δ.chars (τ + n) ⊆ Δ.chars τ`. Introduce `τ n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use `push_cast`. Rewrite using `[← add_assoc]`. Conclude with `(chars_succ_subset_chars Δ _).trans ih`. Establish `hsub : ∀ τ σ : ZMod a, Δ.chars τ ⊆ Δ.chars σ`. Introduce `τ σ`.

Establish `hs` using `hle σ (τ - σ).val`. Rewrite `hs` using `[ZMod.natCast_zmod_val, add_sub_cancel]`. Then use the resulting hypothesis. Conclude with `⟨fun τ σ => (hsub τ σ).antisymm (hsub σ τ), fun τ c hc => hsub (τ + 1) τ (prime_mul_mem_chars_succ_of_mem Δ hc)⟩`.
-/
theorem _root_.GlobalTheory.BK.chars_eq_and_mul_mem (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K]
    [_root_.GlobalTheory.BK.IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [_root_.GlobalTheory.BK.TameDescentExponentData K l e a]
    (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) (Δ : _root_.GlobalTheory.BK.Descent P) :
    (∀ τ σ, Δ.chars τ = Δ.chars σ) ∧
      ∀ τ, ∀ c ∈ Δ.chars τ,
        (l : ZMod e) * c ∈ Δ.chars τ := by
  have hle : ∀ (τ : ZMod a) (n : ℕ),
      Δ.chars (τ + n) ⊆ Δ.chars τ := by
    intro τ n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← add_assoc]
      exact (chars_succ_subset_chars Δ _).trans ih
  have hsub : ∀ τ σ : ZMod a,
      Δ.chars τ ⊆ Δ.chars σ := by
    intro τ σ
    have hs := hle σ (τ - σ).val
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at hs
  exact ⟨fun τ σ => (hsub τ σ).antisymm (hsub σ τ),
    fun τ c hc => hsub (τ + 1) τ (prime_mul_mem_chars_succ_of_mem Δ hc)⟩

end GlobalTheory.BK
