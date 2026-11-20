import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionSelfDualOfSelfDualLatticeStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Half

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
The claim follows from `_root_.GlobalTheory.AdLat.hermA_add_left c G x x' y`.
-/
theorem _root_.GlobalTheory.AdLat.Half.herm_add_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x + x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x' y :=
  _root_.GlobalTheory.AdLat.hermA_add_left c G x x' y

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem _root_.GlobalTheory.AdLat.Half.herm_add_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y y' : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (y + y') =
      _root_.GlobalTheory.AdLat.hermA c G x y + _root_.GlobalTheory.AdLat.hermA c G x y' := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Rewrite using `[sub_eq_add_neg, _root_.GlobalTheory.AdLat.hermA_add_left, _root_.GlobalTheory.AdLat.hermA_neg_left, ← sub_eq_add_neg]`.
-/
lemma _root_.GlobalTheory.AdLat.Half.herm_sub_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x x' y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (x - x') y =
      _root_.GlobalTheory.AdLat.hermA c G x y - _root_.GlobalTheory.AdLat.hermA c G x' y := by
  rw [sub_eq_add_neg, _root_.GlobalTheory.AdLat.hermA_add_left, _root_.GlobalTheory.AdLat.hermA_neg_left,
    ← sub_eq_add_neg]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]`.
-/
lemma _root_.GlobalTheory.AdLat.Half.herm_neg_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (-y) = -_root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Rewrite using `[sub_eq_add_neg, _root_.GlobalTheory.AdLat.Half.herm_add_right, _root_.GlobalTheory.AdLat.Half.herm_neg_right, ← sub_eq_add_neg]`.
-/
lemma _root_.GlobalTheory.AdLat.Half.herm_sub_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (x y y' : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (y - y') =
      _root_.GlobalTheory.AdLat.hermA c G x y - _root_.GlobalTheory.AdLat.hermA c G x y' := by
  rw [sub_eq_add_neg, _root_.GlobalTheory.AdLat.Half.herm_add_right, _root_.GlobalTheory.AdLat.Half.herm_neg_right,
    ← sub_eq_add_neg]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem _root_.GlobalTheory.AdLat.Half.herm_smul_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (r : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G (r • x) y = r * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem _root_.GlobalTheory.AdLat.Half.herm_smul_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (r : _root_.GlobalTheory.AdLat.RA F E) (x y : Fin n → _root_.GlobalTheory.AdLat.RA F E) :
    _root_.GlobalTheory.AdLat.hermA c G x (r • y) =
      _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c r * _root_.GlobalTheory.AdLat.hermA c G x y := by
  simp only [_root_.GlobalTheory.AdLat.hermA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.AdLat.hat at hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨a, ha, y, hy, rfl⟩` from `hw`. Establish `hw' : (fun i => a ⊗ₜ[F] y i) = (a ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • _root_.GlobalTheory.AdLat.fv F y`.

Use function extensionality and compare the values at `i`. Simplify using `[_root_.GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[hw', _root_.GlobalTheory.AdLat.Half.herm_smul_right]`. Establish `hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] (1 : E)) = a ⊗ₜ[F] (1 : E)`. Simplify using `[_root_.GlobalTheory.AdLat.sg]`.

Rewrite using `[hsg]`. Use `_root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun x hx y hy => ?_) (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F ha rfl) (hz y hy)` and prove the remaining obligations. Rewrite using `[Set.mem_singleton_iff.1 hx, one_mul]`. Conclude with `hy`. Consider the case `zero`.

Establish `h0 : _root_.GlobalTheory.AdLat.hermA c G z 0 = 0`. Simplify using `[_root_.GlobalTheory.AdLat.hermA]`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Consider the case `add w w' _ _ hw hw'`.

Rewrite using `[_root_.GlobalTheory.AdLat.Half.herm_add_right]`. Conclude with `add_mem hw hw'`. Consider the case `neg w _ hw`. Rewrite using `[_root_.GlobalTheory.AdLat.Half.herm_neg_right]`. Conclude with `neg_mem hw`.
-/
theorem _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : Set E) (L : Set (Fin n → E)) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E)
    (hz : ∀ y ∈ L, _root_.GlobalTheory.AdLat.hermA c G z (_root_.GlobalTheory.AdLat.fv F y) ∈
      _root_.GlobalTheory.AdLat.hat1 F J)
    (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) (hw : w ∈ _root_.GlobalTheory.AdLat.hat F L) :
    _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F J := by
  unfold _root_.GlobalTheory.AdLat.hat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hw
    have hw' : (fun i => a ⊗ₜ[F] y i) =
        (a ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • _root_.GlobalTheory.AdLat.fv F y := by
      funext i
      simp [_root_.GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hw', _root_.GlobalTheory.AdLat.Half.herm_smul_right]
    have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] (1 : E)) =
        a ⊗ₜ[F] (1 : E) := by
      simp [_root_.GlobalTheory.AdLat.sg]
    rw [hsg]
    refine _root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun x hx y hy => ?_)
      (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F ha rfl) (hz y hy)
    rw [Set.mem_singleton_iff.1 hx, one_mul]
    exact hy
  | zero =>
    have h0 : _root_.GlobalTheory.AdLat.hermA c G z 0 = 0 := by
      simp [_root_.GlobalTheory.AdLat.hermA]
    rw [h0]
    exact zero_mem _
  | add w w' _ _ hw hw' =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_add_right]
    exact add_mem hw hw'
  | neg w _ hw =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_neg_right]
    exact neg_mem hw

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, _root_.GlobalTheory.AdLat.adele_one_integral F, y, hy, rfl⟩`.
-/
theorem _root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ L) : _root_.GlobalTheory.AdLat.fv F y ∈ _root_.GlobalTheory.AdLat.hat F L :=
  AddSubgroup.subset_closure ⟨1, _root_.GlobalTheory.AdLat.adele_one_integral F, y, hy, rfl⟩

end GlobalTheory.AdLat.Half

namespace GlobalTheory.AdLat

open Half

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix nonZeroDivisors in
/- English proof (translation)
Introduce `F E _ _ _ _ _ n L c G J g M I I' hFG hspan hc hG hdet hJ hdual hg hM hsup hprod hcI hhalf`. Use `set Lh := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hLh`. Generalize the expression as in `(g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) = gm at hg hhalf ⊢`. Set `e : 𝓞 E → _root_.GlobalTheory.AdLat.RA F E` to `fun b => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)`. Establish `hh : ∀ b ∈ I, ∀ z ∈ Lh, ∃ y ∈ Lh, gm *ᵥ (e b • z) - e b • z = M • y` using `hhalf`.

Establish `hu : ∀ (r : _root_.GlobalTheory.AdLat.RA F E) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E), gm *ᵥ (r • z) - r • z = r • (gm *ᵥ z - z)` using `fun r z => by`. Rewrite using `[Matrix.mulVec_smul, smul_sub]`. Establish `hM0 : (M : F) ≠ 0` using `Nat.cast_ne_zero.2 hM.ne'`. Establish `hnat : ∀ (m : ℕ) (v : Fin n → _root_.GlobalTheory.AdLat.RA F E), m • v = (algebraMap F (_root_.GlobalTheory.AdLat.RA F E) m) • v` using `fun m v => by`. Rewrite using `[map_natCast, Nat.cast_smul_eq_nsmul]`.

Establish `hMcancel : ∀ x y : Fin n → _root_.GlobalTheory.AdLat.RA F E, M • x = M • y → x = y`. Introduce `x y hxy`. Rewrite `hxy` using `[← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F]`. Conclude with `smul_right_injective _ hM0 hxy`. Establish `heM : e (M : 𝓞 E) = algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M`.

Simplify using `only [e, map_natCast]`. Use `push_cast`. Rewrite using `[← Algebra.TensorProduct.includeRight_apply, map_natCast]`. Establish `hMI : (M : 𝓞 E) ∈ I`. Establish `h1 : (M : 𝓞 E) ∈ Ideal.span {(M : 𝓞 E)}` using `Ideal.mem_span_singleton_self _`.

Rewrite `h1` using `[← hprod]`. Establish `h2 : I * I' ≤ I` using `Ideal.mul_le_left`. Conclude with `h2 h1`. Establish `hstab : ∀ z ∈ Lh, gm *ᵥ z - z ∈ Lh` using `fun z hz => by`. Take `⟨y, hy, hyz⟩` from `hh _ hMI z hz`.

Rewrite `hyz` using `[hu, heM, ← hnat]`. Rewrite using `[hMcancel _ _ hyz]`. Conclude with `hy`. Establish `hgL : ∀ z ∈ Lh, gm *ᵥ z ∈ Lh` using `fun z hz => by`. Rewrite using `[← sub_add_cancel (gm *ᵥ z) z]`.

Conclude with `add_mem (hstab z hz) hz`. Establish `hpair : ∀ z ∈ Lh, ∀ w ∈ Lh, _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F (J : Set E)` using `fun z hz w hw => _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv c G J L z ((_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual z).2 hz) w hw`. Introduce `z hz`. Take `⟨i, hi, i', hi', hii'⟩` from `Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ I')`. Take `⟨b, hb, hbc⟩` from `hcI i' hi'`.

Establish `he1 : e i + e i' = 1`. Establish `h1 : (i : E) + (i' : E) = 1` using `by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hii'`. Simplify using `only [e, ← TensorProduct.tmul_add]`. Rewrite using `[h1]`. Both sides reduce to the same expression.

Use `set w := gm *ᵥ z - z with hw`. Take `⟨y₁, hy₁, hwy₁⟩` from `hh i hi z hz`. Rewrite `hwy₁` using `[hu]`. Use `set v : Fin n → _root_.GlobalTheory.AdLat.RA F E := ((M : F)⁻¹) • (e i' • w) with hv`. Establish `hMv : M • v = e i' • w`.

Rewrite using `[hv, ← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hM0, one_smul]`. Establish `hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (e b) = e i'`. Simplify using `only [e, _root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Rewrite using `[AlgEquiv.coe_algHom, hbc, hc]`. Establish `hvL : v ∈ Lh`.

Use `(_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual v).1 fun y hy => ?_` and prove the remaining obligations. Use `set Y := _root_.GlobalTheory.AdLat.fv F y`. Establish `hY : Y ∈ Lh` using `_root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) y hy`. Take `⟨y₂, hy₂, hY₂⟩` from `hh b hb Y hY`. Rewrite `hY₂` using `[hu]`.

Establish `key : _root_.GlobalTheory.AdLat.hermA c G w Y = -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y)`. Rewrite using `[hw, _root_.GlobalTheory.AdLat.Half.herm_sub_left, _root_.GlobalTheory.AdLat.Half.herm_sub_right, ← hg z Y]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : e i' * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) = algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂`. Rewrite using `[← hsg, ← _root_.GlobalTheory.AdLat.Half.herm_smul_right, hY₂, hnat, _root_.GlobalTheory.AdLat.Half.herm_smul_right, AlgHom.commutes]`.

Establish `h3 : _root_.GlobalTheory.AdLat.hermA c G v Y = -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂`. Rewrite using `[hv, algebra_compatible_smul (_root_.GlobalTheory.AdLat.RA F E), _root_.GlobalTheory.AdLat.Half.herm_smul_left, _root_.GlobalTheory.AdLat.Half.herm_smul_left, key, mul_neg, h2, mul_neg, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hM0, map_one, one_mul]`. Rewrite using `[h3]`. Conclude with `neg_mem (hpair _ (hgL z hz) y₂ hy₂)`. Use `⟨y₁ + v, add_mem hy₁ hvL, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.AdLat.trivial_level_of_half : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E)
    (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E)
    (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (M : ℕ) (I I' : Ideal (𝓞 E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) →
    G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) →
    (∀ x y, _root_.GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ y) = _root_.GlobalTheory.AdLat.hermA c G x y) →
    0 < M → I ⊔ I' = ⊤ → I * I' = Ideal.span {(M : 𝓞 E)} →
    (∀ b ∈ I', ∃ b' ∈ I, ((b' : 𝓞 E) : E) = c (b : E)) →
    (∀ b ∈ I, ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) -
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) = M • y) →
    ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ z - z = M • y := by
  intro F E _ _ _ _ _ n L c G J g M I I' hFG hspan hc hG hdet hJ hdual hg hM hsup hprod hcI hhalf
  set Lh := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hLh
  generalize (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) = gm at hg hhalf ⊢
  let e : 𝓞 E → _root_.GlobalTheory.AdLat.RA F E :=
    fun b => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)
  have hh : ∀ b ∈ I, ∀ z ∈ Lh, ∃ y ∈ Lh, gm *ᵥ (e b • z) - e b • z = M • y := hhalf
  have hu : ∀ (r : _root_.GlobalTheory.AdLat.RA F E) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      gm *ᵥ (r • z) - r • z = r • (gm *ᵥ z - z) := fun r z => by
    rw [Matrix.mulVec_smul, smul_sub]
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hnat : ∀ (m : ℕ) (v : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      m • v = (algebraMap F (_root_.GlobalTheory.AdLat.RA F E) m) • v := fun m v => by
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hMcancel : ∀ x y : Fin n → _root_.GlobalTheory.AdLat.RA F E, M • x = M • y → x = y := by
    intro x y hxy
    rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at hxy
    exact smul_right_injective _ hM0 hxy
  have heM : e (M : 𝓞 E) = algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M := by
    simp only [e, map_natCast]
    push_cast
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hMI : (M : 𝓞 E) ∈ I := by
    have h1 : (M : 𝓞 E) ∈ Ideal.span {(M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← hprod] at h1
    have h2 : I * I' ≤ I := Ideal.mul_le_left
    exact h2 h1

  have hstab : ∀ z ∈ Lh, gm *ᵥ z - z ∈ Lh := fun z hz => by
    obtain ⟨y, hy, hyz⟩ := hh _ hMI z hz
    rw [hu, heM, ← hnat] at hyz
    rw [hMcancel _ _ hyz]
    exact hy
  have hgL : ∀ z ∈ Lh, gm *ᵥ z ∈ Lh := fun z hz => by
    rw [← sub_add_cancel (gm *ᵥ z) z]
    exact add_mem (hstab z hz) hz
  have hpair : ∀ z ∈ Lh, ∀ w ∈ Lh,
      _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F (J : Set E) :=
    fun z hz w hw => _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv c G J L z
      ((_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual z).2
        hz) w hw
  intro z hz
  obtain ⟨i, hi, i', hi', hii'⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ I')
  obtain ⟨b, hb, hbc⟩ := hcI i' hi'
  have he1 : e i + e i' = 1 := by
    have h1 : (i : E) + (i' : E) = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hii'
    simp only [e, ← TensorProduct.tmul_add]
    rw [h1]
    rfl
  set w := gm *ᵥ z - z with hw
  obtain ⟨y₁, hy₁, hwy₁⟩ := hh i hi z hz
  rw [hu] at hwy₁
  set v : Fin n → _root_.GlobalTheory.AdLat.RA F E := ((M : F)⁻¹) • (e i' • w) with hv
  have hMv : M • v = e i' • w := by
    rw [hv, ← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hM0, one_smul]
  have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (e b) = e i' := by
    simp only [e, _root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgEquiv.coe_algHom, hbc, hc]
  have hvL : v ∈ Lh := by
    refine (_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual v).1
      fun y hy => ?_
    set Y := _root_.GlobalTheory.AdLat.fv F y
    have hY : Y ∈ Lh := _root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) y hy
    obtain ⟨y₂, hy₂, hY₂⟩ := hh b hb Y hY
    rw [hu] at hY₂
    have key : _root_.GlobalTheory.AdLat.hermA c G w Y =
        -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) := by
      rw [hw, _root_.GlobalTheory.AdLat.Half.herm_sub_left, _root_.GlobalTheory.AdLat.Half.herm_sub_right, ← hg z Y]
      ring
    have h2 : e i' * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) =
        algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [← hsg, ← _root_.GlobalTheory.AdLat.Half.herm_smul_right, hY₂, hnat,
        _root_.GlobalTheory.AdLat.Half.herm_smul_right, AlgHom.commutes]
    have h3 : _root_.GlobalTheory.AdLat.hermA c G v Y = -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [hv, algebra_compatible_smul (_root_.GlobalTheory.AdLat.RA F E),
        _root_.GlobalTheory.AdLat.Half.herm_smul_left, _root_.GlobalTheory.AdLat.Half.herm_smul_left, key, mul_neg,
        h2, mul_neg, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hM0, map_one, one_mul]
    rw [h3]
    exact neg_mem (hpair _ (hgL z hz) y₂ hy₂)
  refine ⟨y₁ + v, add_mem hy₁ hvL, ?_⟩
  calc w = e i • w + e i' • w := by rw [← add_smul, he1, one_smul]
    _ = M • (y₁ + v) := by rw [hwy₁, ← hMv, smul_add]

end GlobalTheory.AdLat
