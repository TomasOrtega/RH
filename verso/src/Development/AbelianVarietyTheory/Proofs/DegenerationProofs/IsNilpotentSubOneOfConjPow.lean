import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqOneOfPowEqOneOfCongrOne

namespace GlobalTheory

namespace Unipotence

open Polynomial

/- English proof (translation)
Establish `hm` using `Y.charpoly_monic`. Establish `hs : Y.charpoly.Splits` using `IsAlgClosed.splits _`. Establish `hr : Y.charpoly.roots = Multiset.replicate (Multiset.card Y.charpoly.roots) 0`. Rewrite using `[Multiset.eq_replicate_card]`. Introduce `μ hμ`.

Conclude with `h μ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (isRoot_of_mem_roots hμ))`. Establish `he` using `hs.eq_prod_roots_of_monic hm`. Rewrite `he` using `[hr]`. Establish `hch` using `Matrix.aeval_self_charpoly Y`. Rewrite `hch` using `[he]`.

Use `⟨Multiset.card Y.charpoly.roots, ?_⟩` and prove the remaining obligations. Simplify using `using hch`.
-/
theorem pow_card_eq_zero {K n : Type} [Field K] [IsAlgClosed K] [Fintype n] [DecidableEq n]
    (Y : Matrix n n K) (h : ∀ μ ∈ spectrum K Y, μ = 0) : IsNilpotent Y := by
  have hm := Y.charpoly_monic
  have hs : Y.charpoly.Splits := IsAlgClosed.splits _
  have hr : Y.charpoly.roots = Multiset.replicate (Multiset.card Y.charpoly.roots) 0 := by
    rw [Multiset.eq_replicate_card]
    intro μ hμ
    exact h μ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (isRoot_of_mem_roots hμ))
  have he := hs.eq_prod_roots_of_monic hm
  rw [hr] at he
  have hch := Matrix.aeval_self_charpoly Y
  rw [he] at hch
  refine ⟨Multiset.card Y.charpoly.roots, ?_⟩
  simpa using hch

/- English proof (translation)
Establish `hconj : A ^ q = P * A * (P⁻¹ : (Matrix n n K)ˣ)`. Rewrite using `[h, mul_assoc, Units.mul_inv, mul_one]`. Establish `hstep : ∀ y ∈ spectrum K A, y ^ q ∈ spectrum K A`. Introduce `y hy`. Use `spectrum.pow_mem_pow A q hy` as an intermediate fact.

Rewrite `this` using `[hconj, spectrum.units_conjugate]`. Then use the resulting hypothesis. Establish `hall : ∀ k : ℕ, x ^ (q ^ k) ∈ spectrum K A`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hx`.

Consider the case `succ k ih => rw [pow_succ, pow_mul]`. Conclude with `hstep _ ih`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `(spectrum.zero_mem_iff K).mp hx hA`.

Take `⟨i, j, hij, he⟩` from `(Matrix.finite_spectrum A).exists_lt_map_eq_of_forall_mem hall`. Establish `hlt : q ^ i < q ^ j` using `Nat.pow_lt_pow_right (by omega) hij`. Use `⟨q ^ j - q ^ i, by omega, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ (pow_ne_zero (q ^ i) hx0)` to reduce the goal to its premises. Rewrite using `[← pow_add, mul_one, Nat.add_sub_cancel' hlt.le]`.

Conclude with `he.symm`.
-/
theorem root_of_unity {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hA : IsUnit A) (P : (Matrix n n K)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (h : (P : Matrix n n K) * A = A ^ q * P) (x : K) (hx : x ∈ spectrum K A) :
    ∃ m : ℕ, m ≠ 0 ∧ x ^ m = 1 := by
  have hconj : A ^ q = P * A * (P⁻¹ : (Matrix n n K)ˣ) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  have hstep : ∀ y ∈ spectrum K A, y ^ q ∈ spectrum K A := by
    intro y hy
    have := spectrum.pow_mem_pow A q hy
    rwa [hconj, spectrum.units_conjugate] at this
  have hall : ∀ k : ℕ, x ^ (q ^ k) ∈ spectrum K A := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ, pow_mul]; exact hstep _ ih
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact (spectrum.zero_mem_iff K).mp hx hA
  obtain ⟨i, j, hij, he⟩ := (Matrix.finite_spectrum A).exists_lt_map_eq_of_forall_mem hall
  have hlt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
  refine ⟨q ^ j - q ^ i, by omega, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (q ^ i) hx0)
  rw [← pow_add, mul_one, Nat.add_sub_cancel' hlt.le]
  exact he.symm

/- English proof (translation)
Set `E` to `Algebra.adjoin ℤ_[l] ({μ} : Set K)`. Use `haveI : Module.Finite ℤ_[l] E := Module.Finite.iff_fg.mpr hμ.fg_adjoin_singleton`. Set `ψ : E` to `⟨μ, Algebra.self_mem_adjoin_singleton _ _⟩`. Establish `hl0 : l ≠ 0` using `by omega`. Establish `key : (1 : E) + l • ψ = 1`.

Use `SerreTorsion.eq_one_of_pow (E := E) (q := l) (c := l) ?_ hl.out ?_ hl0 dvd_rfl (fun h2 => by omega) m hm ψ ?_` and prove the remaining obligations. Introduce `n x hn hx`. Establish `: (n : K) * (x : K) = 0`. Use `congrArg (Subtype.val : E → K) hx` as an intermediate fact. Simplify using `using this`.

Conclude with `Subtype.ext ((mul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hn))`. Introduce `x hx`. Establish `hk` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := ℤ_[l]) (M := E) (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top`. Rewrite using `[← Submodule.mem_bot ℤ_[l], ← hk, Submodule.mem_iInf]`. Introduce `k`.

Take `⟨y, hy⟩` from `hx k`. Rewrite using `[hy, ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]`. Use `Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ k) Submodule.mem_top` and prove the remaining obligations. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`. Conclude with `Ideal.mem_span_singleton_self _`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify `h` using `[ψ]`. Use `congrArg (Subtype.val : E → K) key` as an intermediate fact. Simplify `this` using `[ψ, hl0]`.
-/
theorem eq_zero_of_integral (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {K : Type} [Field K] [CharZero K]
    [Algebra ℤ_[l] K] (μ : K) (hμ : IsIntegral ℤ_[l] μ) (m : ℕ) (hm : m ≠ 0)
    (h : (1 + l • μ) ^ m = 1) : μ = 0 := by
  let E := Algebra.adjoin ℤ_[l] ({μ} : Set K)
  haveI : Module.Finite ℤ_[l] E := Module.Finite.iff_fg.mpr hμ.fg_adjoin_singleton
  let ψ : E := ⟨μ, Algebra.self_mem_adjoin_singleton _ _⟩
  have hl0 : l ≠ 0 := by omega
  have key : (1 : E) + l • ψ = 1 := by
    refine SerreTorsion.eq_one_of_pow (E := E) (q := l) (c := l) ?_ hl.out ?_ hl0 dvd_rfl
      (fun h2 => by omega) m hm ψ ?_
    · intro n x hn hx
      have : (n : K) * (x : K) = 0 := by
        have := congrArg (Subtype.val : E → K) hx
        simpa using this
      exact Subtype.ext ((mul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hn))
    · intro x hx
      have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := ℤ_[l]) (M := E)
        (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      rw [← Submodule.mem_bot ℤ_[l], ← hk, Submodule.mem_iInf]
      intro k
      obtain ⟨y, hy⟩ := hx k
      rw [hy, ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
      refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ k) Submodule.mem_top
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    · apply Subtype.ext
      simpa [ψ] using h
  have := congrArg (Subtype.val : E → K) key
  simpa [ψ, hl0] using this

/- English proof (translation)
Set `K` to `AlgebraicClosure ℚ_[l]`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] K)`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]`. Conclude with `(algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])`. Set `f : Matrix n n ℤ_[l] →+* Matrix n n K` to `(algebraMap ℤ_[l] K).mapMatrix`.

Establish `hf : Function.Injective f` using `Matrix.map_injective hinj`. Rewrite using `[← IsNilpotent.map_iff hf]`. Apply `pow_card_eq_zero` to reduce the goal to its premises. Introduce `μ hμ`. Establish `hint : IsIntegral ℤ_[l] μ`.

Use `⟨Y.charpoly, Y.charpoly_monic, ?_⟩` and prove the remaining obligations. Use `Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ` as an intermediate fact. Rewrite `this` using `[show f Y = Y.map (algebraMap ℤ_[l] K) from rfl, Matrix.charpoly_map]`. Rewrite using `[← Polynomial.eval_map]`. Conclude with `this`.

Establish `hspec : 1 + l • μ ∈ spectrum K (f (1 + l • Y))`. Use `spectrum.subset_polynomial_aeval (f Y) (1 + l • (X : K[X])) ⟨μ, hμ, rfl⟩` as an intermediate fact. Simplify using `using this`. Take `⟨m, hm, hx⟩` from `root_of_unity (f (1 + l • Y)) (hA.map f) (hP.map f).unit q hq (by rw [IsUnit.unit_spec, ← map_mul, h, map_mul, map_pow]) _ hspec`. Conclude with `eq_zero_of_integral l h3 μ hint m hm hx`.
-/
theorem matrix_nilpotent (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {n : Type} [Fintype n]
    [DecidableEq n] (Y P : Matrix n n ℤ_[l]) (hA : IsUnit (1 + l • Y)) (hP : IsUnit P)
    (q : ℕ) (hq : 2 ≤ q) (h : P * (1 + l • Y) = (1 + l • Y) ^ q * P) : IsNilpotent Y := by
  let K := AlgebraicClosure ℚ_[l]
  have hinj : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  let f : Matrix n n ℤ_[l] →+* Matrix n n K := (algebraMap ℤ_[l] K).mapMatrix
  have hf : Function.Injective f := Matrix.map_injective hinj
  rw [← IsNilpotent.map_iff hf]
  apply pow_card_eq_zero
  intro μ hμ
  have hint : IsIntegral ℤ_[l] μ := by
    refine ⟨Y.charpoly, Y.charpoly_monic, ?_⟩
    have := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
    rw [show f Y = Y.map (algebraMap ℤ_[l] K) from rfl, Matrix.charpoly_map] at this
    rw [← Polynomial.eval_map]
    exact this
  have hspec : 1 + l • μ ∈ spectrum K (f (1 + l • Y)) := by
    have := spectrum.subset_polynomial_aeval (f Y) (1 + l • (X : K[X])) ⟨μ, hμ, rfl⟩
    simpa using this
  obtain ⟨m, hm, hx⟩ := root_of_unity (f (1 + l • Y)) (hA.map f) (hP.map f).unit q hq
    (by rw [IsUnit.unit_spec, ← map_mul, h, map_mul, map_pow]) _ hspec
  exact eq_zero_of_integral l h3 μ hint m hm hx

end Unipotence

/- English proof (translation)
Introduce `l _ h3 T _ _ _ _ S Φ q hq h hS`. Set `b` to `Module.Free.chooseBasis ℤ_[l] T`. Use `choose y hy using hS`. Set `Y : Module.End ℤ_[l] T` to `b.constr ℤ_[l] (fun i => y (b i))`. Establish `hSY : (S : T →ₗ[ℤ_[l]] T) = 1 + l • Y`.

Apply `b.ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [Y, LinearMap.add_apply, LinearMap.smul_apply, Module.Basis.constr_basis, Module.End.one_apply, LinearEquiv.coe_coe, ← hy]`. Normalize the expressions using the abelian group laws. Set `g : (T ≃ₗ[ℤ_[l]] T) →* Module.End ℤ_[l] T` to `LinearEquiv.automorphismGroup.toLinearMapMonoidHom`.

Establish `hgS : g S = 1 + l • Y` using `hSY`. Set `e` to `LinearMap.toMatrixAlgEquiv b`. Establish `heS : e (g S) = 1 + l • e Y` using `by rw [hgS, map_add, map_one, map_nsmul]`. Establish `hN : IsNilpotent (e Y)`. Use `Unipotence.matrix_nilpotent l h3 (e Y) (e (g Φ)) ?_ (((Group.isUnit Φ).map g).map e) q hq ?_` and prove the remaining obligations.

Rewrite using `[← heS]`. Conclude with `((Group.isUnit S).map g).map e`. Rewrite using `[← heS, ← map_mul, ← map_mul, h, map_mul, map_mul, map_pow, map_pow]`. Rewrite `hN` using `[IsNilpotent.map_iff (f := e) e.injective]`. Rewrite using `[hSY, add_sub_cancel_left]`.

Conclude with `hN.smul l`.
-/
theorem isNilpotent_sub_one_of_conj_pow :
    ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (S Φ : T ≃ₗ[ℤ_[l]] T) (q : ℕ), 2 ≤ q → Φ * S = S ^ q * Φ → (∀ x, ∃ y, S x - x = l • y) → IsNilpotent ((S : T →ₗ[ℤ_[l]] T) - 1) := by
  intro l _ h3 T _ _ _ _ S Φ q hq h hS
  classical
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose y hy using hS
  let Y : Module.End ℤ_[l] T := b.constr ℤ_[l] (fun i => y (b i))
  have hSY : (S : T →ₗ[ℤ_[l]] T) = 1 + l • Y := by
    apply b.ext
    intro i
    simp only [Y, LinearMap.add_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Module.End.one_apply, LinearEquiv.coe_coe, ← hy]
    abel
  let g : (T ≃ₗ[ℤ_[l]] T) →* Module.End ℤ_[l] T := LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hgS : g S = 1 + l • Y := hSY
  let e := LinearMap.toMatrixAlgEquiv b
  have heS : e (g S) = 1 + l • e Y := by rw [hgS, map_add, map_one, map_nsmul]
  have hN : IsNilpotent (e Y) := by
    refine Unipotence.matrix_nilpotent l h3 (e Y) (e (g Φ)) ?_ (((Group.isUnit Φ).map g).map e) q hq ?_
    · rw [← heS]; exact ((Group.isUnit S).map g).map e
    · rw [← heS, ← map_mul, ← map_mul, h, map_mul, map_mul, map_pow, map_pow]
  rw [IsNilpotent.map_iff (f := e) e.injective] at hN
  rw [hSY, add_sub_cancel_left]
  exact hN.smul l

end GlobalTheory
