import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPowStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Establish `hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0` using `Polynomial.map_ne_zero hi.ne_zero`. Establish `hr : aeval α f = 0`. Use `(mem_roots hf0).1 hα` as an intermediate fact. Rewrite `this` using `[IsRoot, eval_map_algebraMap]`. Then use the resulting hypothesis. Establish `hmin : f = minpoly F α` using `minpoly.eq_of_irreducible_of_monic hi hr hf`.

Establish `hx : IsIntegral F α` using `Algebra.IsIntegral.isIntegral α`. Establish `hfix : α ^ Nat.card F ^ m = α`. Establish `h1` using `((minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := m)).1 (by rw [← hmin]; exact hd)`. Rewrite `h1` using `[minpoly.dvd_iff]`. Simplify `h1` using `[sub_eq_zero]`.

Establish `hpos : 1 ≤ Nat.card F ^ m` using `Nat.one_le_pow _ _ Nat.card_pos`. Establish `: α ^ (Nat.card F ^ m - 1) * α = 1 * α`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]`. Conclude with `mul_right_cancel₀ h0 this`.
-/
theorem pow_card_pow_sub_one_of_root (F : Type) [Field F] [Finite F] (f : F[X]) (hf : f.Monic)
    (hi : Irreducible f) (m : ℕ) (hd : f.natDegree ∣ m) (α : AlgebraicClosure F)
    (hα : α ∈ (f.map (algebraMap F (AlgebraicClosure F))).roots) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ m - 1) = 1 := by
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have hr : aeval α f = 0 := by
    have := (mem_roots hf0).1 hα
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi hr hf
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfix : α ^ Nat.card F ^ m = α := by
    have h1 := ((minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := m)).1
      (by rw [← hmin]; exact hd)
    rw [minpoly.dvd_iff] at h1
    simpa [sub_eq_zero] using h1
  have hpos : 1 ≤ Nat.card F ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : α ^ (Nat.card F ^ m - 1) * α = 1 * α := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
  exact mul_right_cancel₀ h0 this

/- English proof (translation)
Rewrite using `[← Nat.div_add_mod a N, ← Nat.div_add_mod b N, pow_add, pow_add, pow_mul, pow_mul, h, one_pow, one_pow, hab]`.
-/
theorem pow_eq_pow_of_modEq' {M : Type} [Monoid M] (α : M) (N a b : ℕ) (h : α ^ N = 1)
    (hab : a ≡ b [MOD N]) : α ^ a = α ^ b := by
  rw [← Nat.div_add_mod a N, ← Nat.div_add_mod b N, pow_add, pow_add, pow_mul, pow_mul, h, one_pow,
    one_pow, hab]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

/- English proof (translation)
Establish `: Fintype F` using `Fintype.ofFinite F`. Take `⟨n, -, hn⟩` from `FiniteField.card F (ringChar F)`. Establish `hq : ringChar F ^ ((n : ℕ) * a) = Nat.card F ^ a`. Rewrite using `[Nat.card_eq_fintype_card, hn, pow_mul]`. Establish `hgal` using `GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (RingHom.id F) ((n : ℕ) * a) (fun x => by`.

Rewrite using `[hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]`. Use the proof step `rfl) k f`. Rewrite `hgal` using `[Polynomial.map_id, hq]`. Rewrite using `[hgal]`. Unfold `rootSum`.

Use `congr 1`. Use `Multiset.map_congr rfl fun α hα => ?_` and prove the remaining obligations. Establish `hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0` using `Polynomial.map_ne_zero hi.ne_zero`. Establish `h0 : α ≠ 0`. Introduce and unpack `rfl`.

Establish `h` using `(mem_roots hf0).1 hα`. Rewrite `h` using `[IsRoot, ← coeff_zero_eq_eval_zero, coeff_map]`. Conclude with `hc ((algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero]))`. Rewrite using `[← map_pow, ← map_pow, pow_eq_pow_of_modEq' α _ _ _ (pow_card_pow_sub_one_of_root F f hf hi m hd α hα h0) hk]`.
-/
theorem rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X])
    (hf : f.Monic) (hi : Irreducible f) (hc : f.coeff 0 ≠ 0) (m k k' a : ℕ) (hd : f.natDegree ∣ m)
    (hk : k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1]) :
    rootSum θ k' f = rootSum θ k f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hq : ringChar F ^ ((n : ℕ) * a) = Nat.card F ^ a := by
    rw [Nat.card_eq_fintype_card, hn, pow_mul]
  have hgal := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (RingHom.id F) ((n : ℕ) * a) (fun x => by
    rw [hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]; rfl) k f
  rw [Polynomial.map_id, hq] at hgal
  rw [hgal]
  unfold rootSum
  congr 1
  refine Multiset.map_congr rfl fun α hα => ?_
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have h0 : α ≠ 0 := by
    rintro rfl
    have h := (mem_roots hf0).1 hα
    rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map] at h
    exact hc ((algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero]))
  rw [← map_pow, ← map_pow,
    pow_eq_pow_of_modEq' α _ _ _ (pow_card_pow_sub_one_of_root F f hf hi m hd α hα h0) hk]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `F _ _ θ _ m k k' a _ hk`. Use function extensionality and compare the values at `x`. Unfold `cusp psiG`. Use `congr 1`. Use `set V := Fin m → F`.

Use `set g : Module.End F V := Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)`. Establish `hV : Finite V` using `Module.finite_of_finite F`. Establish `hE : Finite (Module.End F V)` using `Finite.of_injective _ DFunLike.coe_injective`. Establish `hs` using `(GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1`. Establish `hs'` using `(GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k').1`.

Set `φ : Module.End F V → ℂ` to `fun h => psi (rootSum θ k') V h - psi (rootSum θ k) V h`. Establish `hc : IsClassFn φ`. Introduce `e h`. Simplify using `only [φ, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]`. Establish `hp : GlobalTheory.CuspGL.IsPrimitive φ`.

Introduce `A hA hA' g' hg'`. Establish `e1` using `GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs' A hA hA' g' hg'`. Establish `e2` using `GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs A hA hA' g' hg'`. Use `finsum_mem_lin_comb_of_finite (nilRad A) 1 1 (fun h => psi (rootSum θ k') V (g' + h)) (fun h => psi (rootSum θ k) V (g' + h))` as an intermediate fact. Simplify using `only [one_mul] at this`.

Simplify using `only [φ]`. Rewrite using `[this, e1, e2, sub_zero]`. Establish `hP : (LinearMap.charpoly g).Monic` using `LinearMap.charpoly_monic g`. Establish `hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V` using `LinearMap.charpoly_natDegree g`. Establish `hdegm : (LinearMap.charpoly g).natDegree = m` using `by rw [hdeg, Module.finrank_fin_fun]`.

Establish `hc0 : (LinearMap.charpoly g).coeff 0 ≠ 0`. Introduce `h0`. Establish `hdet` using `LinearMap.det_eq_sign_charpoly_coeff g`. Rewrite `hdet` using `[h0, mul_zero, LinearMap.det_toLin']`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero hdet`.

Establish `hmang : mangoldt (rootSum θ k') (LinearMap.charpoly g) = mangoldt (rootSum θ k) (LinearMap.charpoly g)`. Unfold `mangoldt`. Use `finsum_mem_congr rfl fun f hf => ?_` and prove the remaining obligations. Take `⟨hfm, hfi, r, hr, hfr⟩` from `hf`. Use `rootSum_eq_of_modEq F θ f hfm hfi ?_ m k k' a ?_ hk` and prove the remaining obligations.

Introduce `h`. Apply `hc0` to reduce the goal to its premises. Rewrite using `[hfr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h, zero_pow hr.ne']`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdegm, hfr, natDegree_pow, mul_comm]`.

Establish `hmass : mass φ (LinearMap.charpoly g) = 0`. Use `finsum_mem_lin_comb_of_finite {h : Module.End F V | LinearMap.charpoly h = LinearMap.charpoly g} 1 1 (psi (rootSum θ k') V) (psi (rootSum θ k) V)` as an intermediate fact. Simplify using `only [one_mul] at this`. Unfold `mass`. Simplify using `only [φ]`.

Rewrite using `[this]`. Establish `m1` using `GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs' _ hP hdeg`. Establish `m2` using `GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs _ hP hdeg`. Unfold `mass at m1 m2`. Rewrite using `[m1, m2, hmang, sub_self]`.

Conclude with `sub_eq_zero.1 (GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g hmass)`.
-/
theorem cusp_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] →
      cusp θ m k' = cusp θ m k := by
  intro F _ _ θ _ m k k' a _ hk
  funext x
  unfold cusp psiG
  congr 1
  set V := Fin m → F
  set g : Module.End F V := Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)
  have hV : Finite V := Module.finite_of_finite F
  have hE : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  have hs := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
  have hs' := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k').1
  let φ : Module.End F V → ℂ := fun h => psi (rootSum θ k') V h - psi (rootSum θ k) V h
  have hc : IsClassFn φ := by
    intro e h
    simp only [φ, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]
  have hp : GlobalTheory.CuspGL.IsPrimitive φ := by
    intro A hA hA' g' hg'
    have e1 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs' A hA hA' g' hg'
    have e2 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs A hA hA' g' hg'
    have := finsum_mem_lin_comb_of_finite (nilRad A) 1 1 (fun h => psi (rootSum θ k') V (g' + h))
      (fun h => psi (rootSum θ k) V (g' + h))
    simp only [one_mul] at this
    simp only [φ]
    rw [this, e1, e2, sub_zero]
  have hP : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hdegm : (LinearMap.charpoly g).natDegree = m := by rw [hdeg, Module.finrank_fin_fun]
  have hc0 : (LinearMap.charpoly g).coeff 0 ≠ 0 := by
    intro h0
    have hdet := LinearMap.det_eq_sign_charpoly_coeff g
    rw [h0, mul_zero, LinearMap.det_toLin'] at hdet
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero hdet
  have hmang : mangoldt (rootSum θ k') (LinearMap.charpoly g) =
      mangoldt (rootSum θ k) (LinearMap.charpoly g) := by
    unfold mangoldt
    refine finsum_mem_congr rfl fun f hf => ?_
    obtain ⟨hfm, hfi, r, hr, hfr⟩ := hf
    refine rootSum_eq_of_modEq F θ f hfm hfi ?_ m k k' a ?_ hk
    · intro h
      apply hc0
      rw [hfr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h, zero_pow hr.ne']
    · refine ⟨r, ?_⟩
      rw [← hdegm, hfr, natDegree_pow, mul_comm]
  have hmass : mass φ (LinearMap.charpoly g) = 0 := by
    have := finsum_mem_lin_comb_of_finite {h : Module.End F V | LinearMap.charpoly h = LinearMap.charpoly g}
      1 1 (psi (rootSum θ k') V) (psi (rootSum θ k) V)
    simp only [one_mul] at this
    unfold mass
    simp only [φ]
    rw [this]
    have m1 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs' _ hP hdeg
    have m2 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs _ hP hdeg
    unfold mass at m1 m2
    rw [m1, m2, hmang, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g hmass)

end GlobalTheory.Shin
