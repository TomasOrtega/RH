import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd

noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P
open Formalism.UG

section Mat
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "Rv" => E ⊗[F] v.adicCompletion F
local notation "R" => E ⊗[F] 𝔸

def afsplitC (M : Matrix n n Rv) (N : Matrix n n R) : Matrix n n R :=
  M.map (afsplitIE v) + (1 - afsplitEps E v) • N

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem afsplitC_apply (M : Matrix n n Rv) (N : Matrix n n R) (i j : n) :
    afsplitC v M N i j = afsplitIE v (M i j) + (1 - afsplitEps E v) * N i j := rfl

/- English proof (translation)
Rewrite using `[sub_mul, one_mul, afsplit_eps_mul_IE, sub_self]`.
-/
theorem afsplit_om_eps_IE (x : Rv) : (1 - afsplitEps E v) * afsplitIE v x = 0 := by
  rw [sub_mul, one_mul, afsplit_eps_mul_IE, sub_self]

/- English proof (translation)
Take the linear combination `(afsplit_eps_idem (E := E) v)`.
-/
theorem afsplit_om_idem : (1 - afsplitEps E v) * (1 - afsplitEps E v) = 1 - afsplitEps E v := by
  linear_combination (afsplit_eps_idem (E := E) v)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]`. Conclude with `afsplit_om_eps_IE v (M i j)`.
-/
theorem afsplit_smul_map (M : Matrix n n Rv) : (1 - afsplitEps E v) • M.map (afsplitIE v) = 0 := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.zero_apply]
  exact afsplit_om_eps_IE v (M i j)

/- English proof (translation)
Unfold `afsplitC`. Establish `h1 : M.map (afsplitIE v) * ((1 - afsplitEps E v) • N') = 0`. Rewrite using `[Matrix.mul_smul, ← Matrix.smul_mul, afsplit_smul_map, Matrix.zero_mul]`. Establish `h2 : ((1 - afsplitEps E v) • N) * M'.map (afsplitIE v) = 0`. Rewrite using `[Matrix.smul_mul, ← Matrix.mul_smul, afsplit_smul_map, Matrix.mul_zero]`.

Establish `h3 : ((1 - afsplitEps E v) • N) * ((1 - afsplitEps E v) • N') = (1 - afsplitEps E v) • (N * N')`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, afsplit_om_idem]`. Rewrite using `[add_mul, mul_add, mul_add, h1, h2, h3, Matrix.map_mul, add_zero, zero_add]`.
-/
theorem afsplitC_mul (M M' : Matrix n n Rv) (N N' : Matrix n n R) :
    afsplitC v M N * afsplitC v M' N' = afsplitC v (M * M') (N * N') := by
  unfold afsplitC
  have h1 : M.map (afsplitIE v) * ((1 - afsplitEps E v) • N') = 0 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, afsplit_smul_map, Matrix.zero_mul]
  have h2 : ((1 - afsplitEps E v) • N) * M'.map (afsplitIE v) = 0 := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, afsplit_smul_map, Matrix.mul_zero]
  have h3 : ((1 - afsplitEps E v) • N) * ((1 - afsplitEps E v) • N') =
      (1 - afsplitEps E v) • (N * N') := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, afsplit_om_idem]
  rw [add_mul, mul_add, mul_add, h1, h2, h3, Matrix.map_mul, add_zero, zero_add]

/- English proof (translation)
Establish `h1 : afsplitIE v (1 : Rv) = afsplitEps E v`. Establish `h` using `afsplit_decomp (E := E) v 1`. Rewrite `h` using `[map_one, mul_one]`. Then use the resulting hypothesis. Use extensionality with `i j`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[Matrix.one_apply, h1]`. Simplify using `[Matrix.one_apply, h]`.
-/
theorem afsplit_one_map : (1 : Matrix n n Rv).map (afsplitIE v) = afsplitEps E v • (1 : Matrix n n R) := by
  have h1 : afsplitIE v (1 : Rv) = afsplitEps E v := by
    have h := afsplit_decomp (E := E) v 1
    rwa [map_one, mul_one] at h
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, h1]
  · simp [Matrix.one_apply, h]

/- English proof (translation)
Unfold `afsplitC`. Rewrite using `[afsplit_one_map, ← add_smul]`. Simplify using the standard rewrite rules.
-/
theorem afsplitC_one : afsplitC v (1 : Matrix n n Rv) (1 : Matrix n n R) = 1 := by
  unfold afsplitC
  rw [afsplit_one_map, ← add_smul]
  simp

/- English proof (translation)
Unfold `afsplitC`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[afsplit_decomp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem afsplitC_decomp (N : Matrix n n R) : afsplitC v (N.map (prV (E := E) v)) N = N := by
  unfold afsplitC
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [afsplit_decomp]
  ring

/- English proof (translation)
Unfold `afsplitC`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]`. Rewrite using `[afsplit_prV_IE, map_sub, map_one, afsplit_prV_eps, sub_self, zero_mul, add_zero]`.
-/
theorem afsplitC_prV (M : Matrix n n Rv) (N : Matrix n n R) :
    (afsplitC v M N).map (prV (E := E) v) = M := by
  unfold afsplitC
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
  rw [afsplit_prV_IE, map_sub, map_one, afsplit_prV_eps, sub_self, zero_mul, add_zero]

/- English proof (translation)
Unfold `afsplitC`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, afsplit_prV_IE_ne v w h, afsplit_prV_eps_ne v w h, sub_zero, one_mul, zero_add]`.
-/
theorem afsplitC_prV_ne (w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (M : Matrix n n Rv)
    (N : Matrix n n R) : (afsplitC v M N).map (prV (E := E) w) = N.map (prV (E := E) w) := by
  unfold afsplitC
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub,
    map_one, afsplit_prV_IE_ne v w h, afsplit_prV_eps_ne v w h, sub_zero, one_mul, zero_add]

/- English proof (translation)
Unfold `afsplitC`. Rewrite using `[smul_add, afsplit_smul_map, zero_add, smul_smul, afsplit_om_idem]`.
-/
theorem afsplitC_C (M M' : Matrix n n Rv) (N : Matrix n n R) :
    afsplitC v M (afsplitC v M' N) = afsplitC v M N := by
  unfold afsplitC
  rw [smul_add, afsplit_smul_map, zero_add, smul_smul, afsplit_om_idem]

/- English proof (translation)
Unfold `cT afsplitC`. Use extensionality with `i j`. Simplify using `[Matrix.transpose_apply, Matrix.map_apply, afsplit_sigR_IE, afsplit_sigR_eps]`.
-/
theorem afsplitC_cT (σ : E →ₐ[F] E) (M : Matrix n n Rv) (N : Matrix n n R) :
    cT (sigR σ 𝔸) (afsplitC v M N) =
      afsplitC v (cT (sigR σ (v.adicCompletion F)) M) (cT (sigR σ 𝔸) N) := by
  unfold cT afsplitC
  ext i j
  simp [Matrix.transpose_apply, Matrix.map_apply, afsplit_sigR_IE, afsplit_sigR_eps]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [afsplitC, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Establish `h` using `afsplit_decomp (E := E) v (inclE (F := F) 𝔸 (J i j))`. Rewrite `h` using `[afsplit_prV_inclE]`. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem afsplitC_J (J : Matrix n n E) :
    J.map (inclE (F := F) 𝔸) = afsplitC v (J.map (inclE (F := F) (v.adicCompletion F)))
      (J.map (inclE (F := F) 𝔸)) := by
  ext i j
  simp only [afsplitC, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h := afsplit_decomp (E := E) v (inclE (F := F) 𝔸 (J i j))
  rw [afsplit_prV_inclE] at h
  rw [h]
  ring

def afsplitU (h : GL n Rv) (k : GL n R) : GL n R where
  val := afsplitC v h k
  inv := afsplitC v (h⁻¹ : GL n Rv) (k⁻¹ : GL n R)
  val_inv := by rw [afsplitC_mul, Units.mul_inv, Units.mul_inv, afsplitC_one]
  inv_val := by rw [afsplitC_mul, Units.inv_mul, Units.inv_mul, afsplitC_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem afsplitU_coe (h : GL n Rv) (k : GL n R) :
    ((afsplitU v h k : GL n R) : Matrix n n R) = afsplitC v h k := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem afsplitU_inv_coe (h : GL n Rv) (k : GL n R) :
    (((afsplitU v h k)⁻¹ : GL n R) : Matrix n n R) = afsplitC v (h⁻¹ : GL n Rv) (k⁻¹ : GL n R) := rfl

/- English proof (translation)
Use extensionality with `: 1`. Simplify using `only [Units.val_mul, afsplitU_coe, afsplitC_mul]`.
-/
theorem afsplitU_mul (h h' : GL n Rv) (k k' : GL n R) :
    afsplitU v (h * h') (k * k') = afsplitU v h k * afsplitU v h' k' := by
  ext : 1
  simp only [Units.val_mul, afsplitU_coe, afsplitC_mul]

/- English proof (translation)
Unfold `UPts UJ at hh hk ⊢`. Simplify using `only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hh hk ⊢`. Rewrite using `[afsplitU_coe]`. Use `conv_lhs => rw [afsplitC_J v J]`. Rewrite using `[afsplitC_cT, afsplitC_mul, afsplitC_mul, hh, hk, ← afsplitC_J]`.
-/
theorem afsplitU_mem (σ : E →ₐ[F] E) (J : Matrix n n E) (h : GL n Rv) (k : GL n R)
    (hh : h ∈ UPts σ J (v.adicCompletion F)) (hk : k ∈ UPts σ J 𝔸) :
    afsplitU v h k ∈ UPts σ J 𝔸 := by
  unfold UPts UJ at hh hk ⊢
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hh hk ⊢
  rw [afsplitU_coe]
  conv_lhs => rw [afsplitC_J v J]
  rw [afsplitC_cT, afsplitC_mul, afsplitC_mul, hh, hk, ← afsplitC_J]

end Mat
end Formalism.UG.P
