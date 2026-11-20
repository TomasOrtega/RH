import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ n r X L h`. Establish `hLX : ∀ z, L *ᵥ (X *ᵥ z) = z` using `fun z => by`. Rewrite using `[Matrix.mulVec_mulVec, h, Matrix.one_mulVec]`. Establish `hsurj : LinearMap.range (Matrix.toLin' L) = ⊤`. Rewrite using `[LinearMap.range_eq_top]`.

Introduce `z`. Conclude with `⟨X *ᵥ z, by simp only [Matrix.toLin'_apply]; exact hLX z⟩`. Establish `hrk` using `LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' L)`. Rewrite `hrk` using `[hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun]`. Use `set Kr := LinearMap.ker (Matrix.toLin' L) with hKr`.

Take `⟨m, hm⟩ : ∃ m, m = Module.finrank K Kr` from `⟨_, rfl⟩`. Rewrite `hrk` using `[← hm]`. Set `e : Kr ≃ₗ[K] (Fin m → K)` to `LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hm])`. Set `p : (Fin n → K) →ₗ[K] Kr` to `LinearMap.codRestrict Kr (LinearMap.id - Matrix.toLin' X ∘ₗ Matrix.toLin' L) (fun z => by`. Simplify using `only [hKr, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_sub, hLX, sub_self])`.

Establish `hp : ∀ z, ((p z : Kr) : Fin n → K) = z - Matrix.toLin' X (Matrix.toLin' L z)` using `fun z => rfl`. Set `Y : Matrix (Fin n) (Fin m) K` to `LinearMap.toMatrix' (Kr.subtype ∘ₗ e.symm.toLinearMap)`. Set `M : Matrix (Fin m) (Fin n) K` to `LinearMap.toMatrix' (e.toLinearMap ∘ₗ p)`. Establish `hLY : L * Y = 0`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Conclude with `(e.symm z).2`. Establish `hMX : M * X = 0`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Establish `: p (Matrix.toLin' X z) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hp]`.

Simplify using `only [Matrix.toLin'_apply, hLX, sub_self, ZeroMemClass.coe_zero]`. Simplify using `only [LinearMap.comp_apply, this, map_zero, LinearMap.zero_apply]`. Establish `hMY : M * Y = 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]`.

Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Establish `: p ((e.symm z : Kr) : Fin n → K) = e.symm z`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h0 : Matrix.toLin' L ((e.symm z : Kr) : Fin n → K) = 0` using `(e.symm z).2`. Rewrite using `[hp, h0, map_zero, sub_zero]`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, this, LinearEquiv.apply_symm_apply, LinearMap.id_apply]`. Use `clear_value Y M`. Use `clear hp p e hm hKr hsurj`. Use `clear Kr`. Substitute `hrk` using the available equality.

Use `⟨Nat.le_add_right _ _, ?_⟩` and prove the remaining obligations. Set `C : Matrix (Fin (r + m)) (Fin (r + m)) K` to `Matrix.of fun a k => Fin.addCases (motive := fun _ => K) (X a) (Y a) k`. Set `D : Matrix (Fin (r + m)) (Fin (r + m)) K` to `Matrix.of fun k a => Fin.addCases (motive := fun _ => K) (fun j => L j a) (fun i => M i a) k`. Establish `hDC : D * C = 1`. Use extensionality with `i k`.

Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>`. Apply the tactic sequence `refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;>`. Simplify using `only [D, C, Matrix.mul_apply, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]`. Rewrite using `[← Matrix.mul_apply, h]`. Simplify using `[Matrix.one_apply]`.

Rewrite using `[← Matrix.mul_apply, hLY, Matrix.one_apply_ne]`. Both sides reduce to the same expression. Introduce `hh`. Use `congrArg Fin.val hh` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← Matrix.mul_apply, hMX, Matrix.one_apply_ne]`. Both sides reduce to the same expression. Introduce `hh`. Use `congrArg Fin.val hh` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Matrix.mul_apply, hMY]`. Simplify using `[Matrix.one_apply]`. Establish `hCD : C * D = 1` using `mul_eq_one_comm.mp hDC`.

Use `⟨⟨C, D, hCD, hDC⟩, ?_⟩` and prove the remaining obligations. Introduce `j k hk`. Establish `hk' : k = Fin.castAdd m j` using `Fin.ext hk`. Substitute `hk'` using the available equality. Use `⟨fun a => ?_, fun a => ?_⟩` and prove the remaining obligations.

Simplify using `only [C, Matrix.of_apply, Fin.addCases_left]`. Use `show D _ _ = _`. Simplify using `only [D, Matrix.of_apply, Fin.addCases_left]`.
-/
theorem exists_GL_cols_eq_inv_rows_eq_of_mul_eq_one :
    ∀ (K : Type) [Field K] (n r : ℕ) (X : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), L * X = 1 →
    r ≤ n ∧ ∃ C : GL (Fin n) K, ∀ (j : Fin r) (k : Fin n), (k : ℕ) = j → (∀ a, C.1 a k = X a j) ∧ ∀ a, (C⁻¹).1 k a = L j a := by
  intro K _ n r X L h
  have hLX : ∀ z, L *ᵥ (X *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have hsurj : LinearMap.range (Matrix.toLin' L) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro z
    exact ⟨X *ᵥ z, by simp only [Matrix.toLin'_apply]; exact hLX z⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' L)
  rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrk
  set Kr := LinearMap.ker (Matrix.toLin' L) with hKr
  obtain ⟨m, hm⟩ : ∃ m, m = Module.finrank K Kr := ⟨_, rfl⟩
  rw [← hm] at hrk
  let e : Kr ≃ₗ[K] (Fin m → K) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hm])
  let p : (Fin n → K) →ₗ[K] Kr :=
    LinearMap.codRestrict Kr (LinearMap.id - Matrix.toLin' X ∘ₗ Matrix.toLin' L) (fun z => by
      simp only [hKr, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_sub, hLX, sub_self])
  have hp : ∀ z, ((p z : Kr) : Fin n → K) = z - Matrix.toLin' X (Matrix.toLin' L z) :=
    fun z => rfl
  let Y : Matrix (Fin n) (Fin m) K := LinearMap.toMatrix' (Kr.subtype ∘ₗ e.symm.toLinearMap)
  let M : Matrix (Fin m) (Fin n) K := LinearMap.toMatrix' (e.toLinearMap ∘ₗ p)
  have hLY : L * Y = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]
    refine LinearMap.ext fun z => ?_
    exact (e.symm z).2
  have hMX : M * X = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]
    refine LinearMap.ext fun z => ?_
    have : p (Matrix.toLin' X z) = 0 := by
      apply Subtype.ext
      rw [hp]
      simp only [Matrix.toLin'_apply, hLX, sub_self, ZeroMemClass.coe_zero]
    simp only [LinearMap.comp_apply, this, map_zero, LinearMap.zero_apply]
  have hMY : M * Y = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun z => ?_
    have : p ((e.symm z : Kr) : Fin n → K) = e.symm z := by
      apply Subtype.ext
      have h0 : Matrix.toLin' L ((e.symm z : Kr) : Fin n → K) = 0 := (e.symm z).2
      rw [hp, h0, map_zero, sub_zero]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, this,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  clear_value Y M
  clear hp p e hm hKr hsurj
  clear Kr
  subst hrk
  refine ⟨Nat.le_add_right _ _, ?_⟩
  let C : Matrix (Fin (r + m)) (Fin (r + m)) K :=
    Matrix.of fun a k => Fin.addCases (motive := fun _ => K) (X a) (Y a) k
  let D : Matrix (Fin (r + m)) (Fin (r + m)) K :=
    Matrix.of fun k a => Fin.addCases (motive := fun _ => K) (fun j => L j a) (fun i => M i a) k
  have hDC : D * C = 1 := by
    ext i k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;>
    simp only [D, C, Matrix.mul_apply, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    · rw [← Matrix.mul_apply, h]
      simp [Matrix.one_apply]
    · rw [← Matrix.mul_apply, hLY, Matrix.one_apply_ne]
      · rfl
      · intro hh
        have := congrArg Fin.val hh
        simp at this
        omega
    · rw [← Matrix.mul_apply, hMX, Matrix.one_apply_ne]
      · rfl
      · intro hh
        have := congrArg Fin.val hh
        simp at this
        omega
    · rw [← Matrix.mul_apply, hMY]
      simp [Matrix.one_apply]
  have hCD : C * D = 1 := mul_eq_one_comm.mp hDC
  refine ⟨⟨C, D, hCD, hDC⟩, ?_⟩
  intro j k hk
  have hk' : k = Fin.castAdd m j := Fin.ext hk
  subst hk'
  refine ⟨fun a => ?_, fun a => ?_⟩
  · simp only [C, Matrix.of_apply, Fin.addCases_left]
  · show D _ _ = _
    simp only [D, Matrix.of_apply, Fin.addCases_left]

end GlobalTheory
