import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `N l ν ω φ a c hN hl hc hφ htw hcu hau`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero l := ⟨hl.ne'⟩`. Use `haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩`. Establish `hlu : IsUnit (l : ZMod N)` using `(ZMod.unitOfCoprime l hc.symm).isUnit`.

Establish `hNu : IsUnit (N : ZMod l)` using `(ZMod.unitOfCoprime N hc).isUnit`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `haN : IsUnit ((a : ZMod l) * N)` using `hau.mul hNu`. Establish `hωaN : ω ((a : ZMod l) * N) ≠ 0` using `(haN.map ω).ne_zero`. Establish `hνcl : ν (-(c : ZMod N) * l) ≠ 0` using `((hcu.neg.mul hlu).map ν).ne_zero`.

Use `⟨ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹, mul_ne_zero hνcl (inv_ne_zero hωaN), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ x, mul_comm (hat φ x)]`. Set `f : ZMod N × ZMod l → ZMod (N * l)` to `fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))`. Establish `hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N)` using `fun k => map_natCast _ k`. Establish `hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l)` using `fun k => map_natCast _ k`.

Establish `hinj : Function.Injective f`. Introduce `p q hpq`. Establish `h1` using `congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq`. Establish `h2` using `congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq`. Simplify using `only [f, hcN, hcl] at h1 h2`.

Move the coercions through the operations in `at h1 h2`. Simplify using `only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2`. Conclude with `Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)`. Establish `hbij : Function.Bijective f`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`.

Conclude with `⟨hinj, by simp [ZMod.card]⟩`. Rewrite using `[hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl), Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]`. Use `Fintype.sum_congr _ _ (fun p => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_congr _ _ (fun q => ?_)` and prove the remaining obligations.

Establish `hN1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q)) = p * l`. Simplify using `only [f, hcN]`. Use `push_cast`. Simplify using `[ZMod.natCast_self]`. Establish `hl1 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)) = q * N`.

Simplify using `only [f, hcl]`. Use `push_cast`. Simplify using `[ZMod.natCast_self]`. Establish `htq` using `htw ((a : ZMod l) * N) q haN`. Establish `hval : ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q))) * φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q))) = ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹ * (ν p * φ q)`.

Rewrite using `[hN1, hl1, htq]`. Establish `e1 : -(c : ZMod N) * (p * l) = (-(c : ZMod N) * l) * p` using `by ring`. Establish `e2 : (a : ZMod l) * (q * N) = (a : ZMod l) * N * q` using `by ring`. Rewrite using `[e1, e2, map_mul]`. Clear the denominators using the available nonvanishing facts.

Establish `he : (ZMod.stdAddChar (f (p, q) * (x : ZMod (N * l))) : ℂ) = ZMod.stdAddChar (p * (x : ZMod N)) * ZMod.stdAddChar (q * (x : ZMod l))`. Establish `: f (p, q) * (x : ZMod (N * l)) = ((((p.val * l + q.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l))`. Simplify using `only [f]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int p x, stdAddChar_nat_mul_int q x, ← Complex.exp_add]`. Use `congr 1`. Establish `hN' : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Establish `hl' : (l : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hl.ne'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hval, he]`. Expand and normalize the polynomial expressions, which then agree. Introduce `d hd y`. Establish `hdN : IsUnit (d : ZMod N)` using `isUnit_of_isCoprime d (by`.

Use `hd` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this.of_mul_right_left)`. Establish `hdl : IsUnit (d : ZMod l)` using `isUnit_of_isCoprime d (by`. Use `hd` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this.of_mul_right_right)`. Establish `h1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (y * d) = ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y * (d : ZMod N)`. Rewrite using `[map_mul, map_intCast]`. Establish `h2 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (y * d) = ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y * (d : ZMod l)`.

Rewrite using `[map_mul, map_intCast]`. Rewrite using `[h1, h2]`. Use `set u := ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y`. Use `set v := ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y`. Establish `hν0 : ν (d : ZMod N) ≠ 0` using `(hdN.map ν).ne_zero`.

Establish `htv` using `htw (d : ZMod l) ((a : ZMod l) * v) hdl`. Establish `e1 : -(c : ZMod N) * (u * d) = (-(c : ZMod N) * u) * d` using `by ring`. Establish `e2 : (a : ZMod l) * (v * d) = (d : ZMod l) * ((a : ZMod l) * v)` using `by ring`. Rewrite using `[e1, e2, map_mul ν (-(c : ZMod N) * u) (d : ZMod N)]`. Unfold `ch`.

Rewrite using `[MulChar.inv_apply_eq_inv', htv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hat_mix_twist : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (ω : DirichletCharacter ℂ l) (φ : ZMod l → ℂ) (a c : ℤ),
    0 < N → 0 < l → N.Coprime l → (∀ x : ℤ, hat φ x = ch ω x) →
    (∀ d u : ZMod l, IsUnit d → φ u = ω d * φ (d * u)) → IsUnit (c : ZMod N) → IsUnit (a : ZMod l) →
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x : ℤ, hat (fun z : ZMod (N * l) => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) x = C * (ch ω x * hat ν x)) ∧
    ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y : ZMod (N * l),
      ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) y) * φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) y) =
      ch ω d * ch ν⁻¹ d * (ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) (y * d)) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) (y * d))) := by
  intro N l ν ω φ a c hN hl hc hφ htw hcu hau
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩
  have hlu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l hc.symm).isUnit
  have hNu : IsUnit (N : ZMod l) := (ZMod.unitOfCoprime N hc).isUnit
  refine ⟨?_, ?_⟩
  · have haN : IsUnit ((a : ZMod l) * N) := hau.mul hNu
    have hωaN : ω ((a : ZMod l) * N) ≠ 0 := (haN.map ω).ne_zero
    have hνcl : ν (-(c : ZMod N) * l) ≠ 0 := ((hcu.neg.mul hlu).map ν).ne_zero
    refine ⟨ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹, mul_ne_zero hνcl (inv_ne_zero hωaN), fun x => ?_⟩
    rw [← hφ x, mul_comm (hat φ x)]
    let f : ZMod N × ZMod l → ZMod (N * l) := fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))
    have hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N) :=
      fun k => map_natCast _ k
    have hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l) :=
      fun k => map_natCast _ k
    have hinj : Function.Injective f := by
      intro p q hpq
      have h1 := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq
      have h2 := congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq
      simp only [f, hcN, hcl] at h1 h2
      push_cast at h1 h2
      simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2
      exact Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hinj, by simp [ZMod.card]⟩
    rw [hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl),
      Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun p => ?_)
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ (fun q => ?_)
    have hN1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q)) = p * l := by
      simp only [f, hcN]; push_cast; simp [ZMod.natCast_self]
    have hl1 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)) = q * N := by
      simp only [f, hcl]; push_cast; simp [ZMod.natCast_self]
    have htq := htw ((a : ZMod l) * N) q haN
    have hval : ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (f (p, q))) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (f (p, q)))
        = ν (-(c : ZMod N) * l) * (ω ((a : ZMod l) * N))⁻¹ * (ν p * φ q) := by
      rw [hN1, hl1, htq]
      have e1 : -(c : ZMod N) * (p * l) = (-(c : ZMod N) * l) * p := by ring
      have e2 : (a : ZMod l) * (q * N) = (a : ZMod l) * N * q := by ring
      rw [e1, e2, map_mul]
      field_simp
    have he : (ZMod.stdAddChar (f (p, q) * (x : ZMod (N * l))) : ℂ)
        = ZMod.stdAddChar (p * (x : ZMod N)) * ZMod.stdAddChar (q * (x : ZMod l)) := by
      have : f (p, q) * (x : ZMod (N * l)) = ((((p.val * l + q.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l)) := by
        simp only [f]; push_cast; rfl
      rw [this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int p x, stdAddChar_nat_mul_int q x, ← Complex.exp_add]
      congr 1
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
      push_cast
      field_simp
    rw [hval, he]
    ring
  · intro d hd y
    have hdN : IsUnit (d : ZMod N) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_left)
    have hdl : IsUnit (d : ZMod l) := isUnit_of_isCoprime d (by
      have := hd; push_cast at this; exact this.of_mul_right_right)
    have h1 : ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (y * d)
        = ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y * (d : ZMod N) := by
      rw [map_mul, map_intCast]
    have h2 : ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (y * d)
        = ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y * (d : ZMod l) := by
      rw [map_mul, map_intCast]
    rw [h1, h2]
    set u := ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) y
    set v := ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) y
    have hν0 : ν (d : ZMod N) ≠ 0 := (hdN.map ν).ne_zero
    have htv := htw (d : ZMod l) ((a : ZMod l) * v) hdl
    have e1 : -(c : ZMod N) * (u * d) = (-(c : ZMod N) * u) * d := by ring
    have e2 : (a : ZMod l) * (v * d) = (d : ZMod l) * ((a : ZMod l) * v) := by ring
    rw [e1, e2, map_mul ν (-(c : ZMod N) * u) (d : ZMod N)]
    unfold ch
    rw [MulChar.inv_apply_eq_inv', htv]
    field_simp

end GlobalTheory.EisM

end
