import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)

namespace GlobalTheory.EisCT.Eichler

variable {E : Type} [Field E] (s : E →+* E)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, hs]`.
-/
theorem cT_cT (hs : ∀ e, s (s e) = e) {m p : Type} (M : Matrix m p E) : cT s (cT s M) = M := by
  ext i j; simp [cT, hs]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_add {m p : Type} (M N : Matrix m p E) : cT s (M + N) = cT s M + cT s N := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_sub {m p : Type} (M N : Matrix m p E) : cT s (M - N) = cT s M - cT s N := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_smul {m p : Type} (e : E) (M : Matrix m p E) : cT s (e • M) = s e • cT s M := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT]`.
-/
theorem cT_zero {m p : Type} : cT s (0 : Matrix m p E) = 0 := by
  ext i j; simp [cT]

/- English proof (translation)
Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using the standard rewrite rules.
-/
theorem eq_smul_one (M : Matrix (Fin 1) (Fin 1) E) : M = M 0 0 • (1 : Matrix (Fin 1) (Fin 1) E) := by
  ext i j; fin_cases i; fin_cases j; simp

/- English proof (translation)
Establish `hsym : ∀ u w : Matrix (Fin n) (Fin 1) E, cT s u * J * w = cT s (cT s w * J * u)` using `fun u w => by`. Rewrite using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT s hs, hJ, Matrix.mul_assoc]`. Take `⟨a, ha⟩ : ∃ a, cT s x * J = a` from `⟨_, rfl⟩`. Take `⟨d, hd⟩ : ∃ d, y - v = d` from `⟨_, rfl⟩`. Take `⟨b, hb⟩ : ∃ b, cT s d * J = b` from `⟨_, rfl⟩`.

Take `⟨c, hc⟩ : ∃ c, (cT s y * J * v) 0 0 = c` from `⟨_, rfl⟩`. Take `⟨A, hA⟩ : ∃ A, J * x = A` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B, J * d = B` from `⟨_, rfl⟩`. Establish `hcA : cT s a = A` using `by rw [← ha, ← hA, Formalism.UG.cT_mul, cT_cT s hs, hJ]`. Establish `hcB : cT s b = B` using `by rw [← hb, ← hB, Formalism.UG.cT_mul, cT_cT s hs, hJ]`.

Establish `hcA' : cT s A = a` using `by rw [← hcA, cT_cT s hs]`. Establish `hcB' : cT s B = b` using `by rw [← hcB, cT_cT s hs]`. Establish `ax : a * x = 0` using `ha ▸ hxx`. Establish `ay : a * y = 1` using `ha ▸ hxy`. Establish `av : a * v = 1` using `ha ▸ hxv`.

Establish `ad : a * d = 0` using `by rw [← hd, Matrix.mul_sub, ay, av, sub_self]`. Establish `bx : b * x = 0`. Rewrite using `[← hb, hsym, ha, ad, cT_zero]`. Establish `yv : cT s y * J * v = c • 1` using `hc ▸ eq_smul_one _`. Establish `vy : cT s v * J * y = s c • 1` using `by rw [hsym, yv, cT_smul, Formalism.UG.cT_one]`.

Establish `bv : b * v = c • 1`. Rewrite using `[← hb, ← hd, cT_sub, Matrix.sub_mul, Matrix.sub_mul, yv, hvv, sub_zero]`. Establish `bd : b * d = (-(c + s c)) • 1`. Rewrite using `[← hb, ← hd, cT_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, yv, vy, hyy, hvv]`. Rewrite using `[neg_smul, add_smul]`.

Normalize the expressions using the abelian group laws. Establish `ax' : ∀ {p : Type} (M : Matrix (Fin 1) p E), a * (x * M) = 0` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ax, Matrix.zero_mul]`. Establish `ad' : ∀ {p : Type} (M : Matrix (Fin 1) p E), a * (d * M) = 0` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ad, Matrix.zero_mul]`.

Establish `bx' : ∀ {p : Type} (M : Matrix (Fin 1) p E), b * (x * M) = 0` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, bx, Matrix.zero_mul]`. Establish `bd' : ∀ {p : Type} (M : Matrix (Fin 1) p E), b * (d * M) = (-(c + s c)) • M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, bd, Matrix.smul_mul, Matrix.one_mul]`. Establish `Jx' : ∀ {p : Type} (M : Matrix (Fin 1) p E), J * (x * M) = A * M` using `fun M => by`.

Rewrite using `[← Matrix.mul_assoc, hA]`. Establish `Jd' : ∀ {p : Type} (M : Matrix (Fin 1) p E), J * (d * M) = B * M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, hB]`. Use `⟨d * a - x * b + c • (x * a), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hJN : J * (d * a - x * b + c • (x * a)) = B * a - A * b + c • (A * a)`.

Rewrite using `[Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Jx', Jd', Jx']`. Establish `hL : cT s (1 + (d * a - x * b + c • (x * a))) * J = J + (A * b - B * a + s c • (A * a))`. Rewrite using `[cT_add, Formalism.UG.cT_one, Matrix.add_mul, Matrix.one_mul]`. Use `congr 1`. Establish `: cT s (d * a - x * b + c • (x * a)) * J = cT s (J * (d * a - x * b + c • (x * a)))`.

Rewrite using `[Formalism.UG.cT_mul, hJ]`. Rewrite using `[this, hJN, cT_add, cT_sub, cT_smul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcA, hcB, hcA', hcB']`. Rewrite using `[hL]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_one, Jx', Jd', ax', ad', bx', bd', Matrix.mul_zero, smul_zero, sub_zero, zero_sub, add_zero, zero_add]`. Use `module`.

Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, av, bv, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, ← hd]`. Normalize the expressions using the abelian group laws. Rewrite using `[Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ax, bx]`. Simplify using the standard rewrite rules. Rewrite using `[ha, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ad, ax]`.

Simplify using the standard rewrite rules. Introduce `z hz`. Rewrite `hz` using `[ha]`. Use `⟨-(b *ᵥ z), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero, Matrix.mulVec_neg]`.

Normalize the expressions using the abelian group laws.
-/
theorem exists_eichler (hs : ∀ e, s (s e) = e) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : cT s J = J)
    (x y v : Matrix (Fin n) (Fin 1) E) (hxx : cT s x * J * x = 0) (hyy : cT s y * J * y = 0)
    (hxy : cT s x * J * y = 1) (hvv : cT s v * J * v = 0) (hxv : cT s x * J * v = 1) :
    ∃ N : Matrix (Fin n) (Fin n) E, cT s (1 + N) * J * (1 + N) = J ∧ (1 + N) * v = y ∧ N * x = 0 ∧
      cT s x * J * N = 0 ∧ ∀ z : Fin n → E, (cT s x * J) *ᵥ z = 0 → ∃ w : Fin 1 → E, N *ᵥ z = x *ᵥ w := by
  have hsym : ∀ u w : Matrix (Fin n) (Fin 1) E, cT s u * J * w = cT s (cT s w * J * u) := fun u w => by
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT s hs, hJ, Matrix.mul_assoc]
  obtain ⟨a, ha⟩ : ∃ a, cT s x * J = a := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, y - v = d := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, cT s d * J = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (cT s y * J * v) 0 0 = c := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, J * x = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, J * d = B := ⟨_, rfl⟩
  have hcA : cT s a = A := by rw [← ha, ← hA, Formalism.UG.cT_mul, cT_cT s hs, hJ]
  have hcB : cT s b = B := by rw [← hb, ← hB, Formalism.UG.cT_mul, cT_cT s hs, hJ]
  have hcA' : cT s A = a := by rw [← hcA, cT_cT s hs]
  have hcB' : cT s B = b := by rw [← hcB, cT_cT s hs]
  have ax : a * x = 0 := ha ▸ hxx
  have ay : a * y = 1 := ha ▸ hxy
  have av : a * v = 1 := ha ▸ hxv
  have ad : a * d = 0 := by rw [← hd, Matrix.mul_sub, ay, av, sub_self]
  have bx : b * x = 0 := by
    rw [← hb, hsym, ha, ad, cT_zero]
  have yv : cT s y * J * v = c • 1 := hc ▸ eq_smul_one _
  have vy : cT s v * J * y = s c • 1 := by rw [hsym, yv, cT_smul, Formalism.UG.cT_one]
  have bv : b * v = c • 1 := by
    rw [← hb, ← hd, cT_sub, Matrix.sub_mul, Matrix.sub_mul, yv, hvv, sub_zero]
  have bd : b * d = (-(c + s c)) • 1 := by
    rw [← hb, ← hd, cT_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, yv, vy, hyy, hvv]
    rw [neg_smul, add_smul]; abel
  have ax' : ∀ {p : Type} (M : Matrix (Fin 1) p E), a * (x * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, ax, Matrix.zero_mul]
  have ad' : ∀ {p : Type} (M : Matrix (Fin 1) p E), a * (d * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, ad, Matrix.zero_mul]
  have bx' : ∀ {p : Type} (M : Matrix (Fin 1) p E), b * (x * M) = 0 := fun M => by
    rw [← Matrix.mul_assoc, bx, Matrix.zero_mul]
  have bd' : ∀ {p : Type} (M : Matrix (Fin 1) p E), b * (d * M) = (-(c + s c)) • M := fun M => by
    rw [← Matrix.mul_assoc, bd, Matrix.smul_mul, Matrix.one_mul]
  have Jx' : ∀ {p : Type} (M : Matrix (Fin 1) p E), J * (x * M) = A * M := fun M => by
    rw [← Matrix.mul_assoc, hA]
  have Jd' : ∀ {p : Type} (M : Matrix (Fin 1) p E), J * (d * M) = B * M := fun M => by
    rw [← Matrix.mul_assoc, hB]
  refine ⟨d * a - x * b + c • (x * a), ?_, ?_, ?_, ?_, ?_⟩
  · have hJN : J * (d * a - x * b + c • (x * a)) = B * a - A * b + c • (A * a) := by
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Jx', Jd', Jx']
    have hL : cT s (1 + (d * a - x * b + c • (x * a))) * J = J + (A * b - B * a + s c • (A * a)) := by
      rw [cT_add, Formalism.UG.cT_one, Matrix.add_mul, Matrix.one_mul]
      congr 1
      have : cT s (d * a - x * b + c • (x * a)) * J = cT s (J * (d * a - x * b + c • (x * a))) := by
        rw [Formalism.UG.cT_mul, hJ]
      rw [this, hJN, cT_add, cT_sub, cT_smul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcA, hcB, hcA', hcB']
    rw [hL]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_one, Jx', Jd', ax', ad', bx', bd', Matrix.mul_zero, smul_zero, sub_zero,
      zero_sub, add_zero, zero_add]
    module
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_assoc, av, bv, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, ← hd]
    abel
  · rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ax,
      bx]
    simp
  · rw [ha, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ad, ax]
    simp
  · intro z hz
    rw [ha] at hz
    refine ⟨-(b *ᵥ z), ?_⟩
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero, Matrix.mulVec_neg]
    abel

end GlobalTheory.EisCT.Eichler

open GlobalTheory.EisCT.Eichler in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y hCM hJ hW w hw hwy γ hγ hO`. Establish `hs : ∀ e, σ (σ e) = e` using `sigma_sigma hCM`. Establish `hJc : cT (σ : E →+* E) J = J`. Use extensionality with `i j`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.coe_coe]`.

Conclude with `hJ.1 i j`. Establish `hxx : cT (σ : E →+* E) (col0 X) * J * col0 X = 0`. Use extensionality with `i j`. Use `congrFun (congrFun hW.xx 0) 0` as an intermediate fact. Simplify `this` using `[cT, col0, Matrix.mul_apply]`.

Establish `hyy : cT (σ : E →+* E) (col0 Y) * J * col0 Y = 0`. Use extensionality with `i j`. Use `congrFun (congrFun hW.yy 0) 0` as an intermediate fact. Simplify `this` using `[cT, col0, Matrix.mul_apply]`. Establish `hxy : cT (σ : E →+* E) (col0 X) * J * col0 Y = 1`.

Use extensionality with `i j`. Use `congrFun (congrFun hW.xy 0) 0` as an intermediate fact. Use `fin_cases i`. Use `fin_cases j`. Simplify `this` using `[cT, col0, Matrix.mul_apply]`.

Take `⟨γ0, rfl⟩ : γ ∈ (ratEmb σ J).range` from `by rw [range_ratEmb]; exact hγ`. Take `⟨g, hgdef⟩ : ∃ g : Matrix (Fin n) (Fin n) E, (((γ0⁻¹ : GRat σ J) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = g` from `⟨_, rfl⟩`. Establish `hg : cT (σ : E →+* E) g * J * g = J` using `hgdef ▸ (γ0⁻¹).2`. Establish `hγinv : (matHom _ σ J (ratEmb σ J γ0)⁻¹).1 = adMat F g` using `by rw [← map_inv, ← hgdef]; rfl`. Take `⟨β, hβdef⟩ : ∃ β, (cT (σ : E →+* E) (col0 X) * J * (g * col0 X)) 0 0 = β` from `⟨_, rfl⟩`.

Establish `hM : cT (σ : E →+* E) (col0 X) * J * (g * col0 X) = β • 1` using `hβdef ▸ eq_smul_one _`. Establish `hβ : β ≠ 0`. Introduce `h0`. Apply `hO` to reduce the goal to its premises. Unfold `OrthL`.

Rewrite using `[hγinv, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc _ g, hM, h0, zero_smul]`. Simplify using the standard rewrite rules. Establish `hvv : cT (σ : E →+* E) (β⁻¹ • (g * col0 X)) * J * (β⁻¹ • (g * col0 X)) = 0`. Rewrite using `[cT_smul, Formalism.UG.cT_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, show cT (σ : E →+* E) (col0 X) * cT (σ : E →+* E) g * J * (g * col0 X) = cT (σ : E →+* E) (col0 X) * J * col0 X by`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc J g (col0 X), ← Matrix.mul_assoc (cT _ g) (J * g) (col0 X), ← Matrix.mul_assoc (cT _ g) J g, hg], hxx, smul_zero, smul_zero]`. Establish `hxv : cT (σ : E →+* E) (col0 X) * J * (β⁻¹ • (g * col0 X)) = 1`. Rewrite using `[Matrix.mul_smul, hM, smul_smul, inv_mul_cancel₀ hβ, one_smul]`. Take `⟨N, hU, hNv, hNx, hxN, hNz⟩` from `exists_eichler (σ : E →+* E) hs J hJc (col0 X) (col0 Y) _ hxx hyy hxy hvv hxv`. Establish `hdet : IsUnit (1 + N).det`.

Use `isUnit_iff_ne_zero.2 fun h0 => hJ.2 ?_` and prove the remaining obligations. Use `congrArg Matrix.det hU` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Conclude with `this.symm`. Set `ν0 : GRat σ J` to `⟨Matrix.nonsingInvUnit (1 + N) hdet, hU⟩`.

Establish `hνm : (matHom _ σ J (ratEmb σ J ν0)).1 = adMat F (1 + N)` using `rfl`. Establish `hm : adMat F (1 + N) - 1 = adMat F N`. Rewrite using `[show adMat F (1 + N) = (inclR (F := F) (AF F)).mapMatrix (1 + N) from rfl, map_add, map_one, add_sub_cancel_left]`. Both sides reduce to the same expression. Establish `hνU : ratEmb σ J ν0 ∈ unipRad σ J (col0 X)`.

Use `Subgroup.subset_closure ?_` and prove the remaining obligations. Use `show _ ∧ _ ∧ _`. Rewrite using `[hνm, hm]`. Use `⟨?_, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[adMat, adMat, ← Matrix.map_mul, hNx]`.

Simplify using the standard rewrite rules. Rewrite using `[adMat, adMat, ← Matrix.map_mul, hxN]`. Simplify using the standard rewrite rules. Take `⟨w', hw'⟩` from `hNz z hz`. Use `⟨fun i => inclR (F := F) (AF F) (w' i), funext fun i => ?_⟩` and prove the remaining obligations.

Conclude with `(RingHom.map_mulVec _ N z i).symm.trans (by rw [hw']; exact RingHom.map_mulVec _ (col0 X) w' i)`. Establish `hνR : ratEmb σ J ν0 ∈ ratPts σ J` using `by rw [← range_ratEmb]; exact ⟨ν0, rfl⟩`. Use `⟨⟨⟨ratEmb σ J ν0, hνU⟩, Subgroup.mem_subgroupOf.2 hνR⟩, (Units.mk0 β hβ).map (inclR (F := F) (AF F)).toMonoidHom, ?_⟩` and prove the remaining obligations. Establish `hy : (1 + N) * (g * col0 X) = β • col0 Y`. Establish `e : g * col0 X = β • (β⁻¹ • (g * col0 X))` using `by rw [smul_smul, mul_inv_cancel₀ hβ, one_smul]`.

Rewrite using `[e, Matrix.mul_smul, hNv]`. Establish `hsm : adMat F (β • col0 Y) = inclR (F` using `F) (AF F) β • adMat F (col0 Y) := by`. Use extensionality with `i j`. Simplify using `[adMat, map_mul]`. Simplify using `only [map_mul, Units.val_mul, hγinv, hνm, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe]`.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, hy, ← adMat, hsm, Matrix.mul_smul, hwy]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.EisCT.exists_unipRad_stabL_big : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X) →
    ∀ γ ∈ ratPts σ J, ¬ GlobalTheory.EisCT.OrthL σ J (col0 X) γ →
    ∃ ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X)), GlobalTheory.EisCT.StabL σ J (col0 X) (w * ν.1.1 * γ⁻¹) := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW w hw hwy γ hγ hO
  have hs : ∀ e, σ (σ e) = e := sigma_sigma hCM
  have hJc : cT (σ : E →+* E) J = J := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.coe_coe]; exact hJ.1 i j
  have hxx : cT (σ : E →+* E) (col0 X) * J * col0 X = 0 := by
    ext i j
    have := congrFun (congrFun hW.xx 0) 0
    simpa [cT, col0, Matrix.mul_apply] using this
  have hyy : cT (σ : E →+* E) (col0 Y) * J * col0 Y = 0 := by
    ext i j
    have := congrFun (congrFun hW.yy 0) 0
    simpa [cT, col0, Matrix.mul_apply] using this
  have hxy : cT (σ : E →+* E) (col0 X) * J * col0 Y = 1 := by
    ext i j
    have := congrFun (congrFun hW.xy 0) 0
    fin_cases i; fin_cases j
    simpa [cT, col0, Matrix.mul_apply] using this
  obtain ⟨γ0, rfl⟩ : γ ∈ (ratEmb σ J).range := by rw [range_ratEmb]; exact hγ
  obtain ⟨g, hgdef⟩ : ∃ g : Matrix (Fin n) (Fin n) E, (((γ0⁻¹ : GRat σ J) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = g :=
    ⟨_, rfl⟩
  have hg : cT (σ : E →+* E) g * J * g = J := hgdef ▸ (γ0⁻¹).2
  have hγinv : (matHom _ σ J (ratEmb σ J γ0)⁻¹).1 = adMat F g := by rw [← map_inv, ← hgdef]; rfl
  obtain ⟨β, hβdef⟩ : ∃ β, (cT (σ : E →+* E) (col0 X) * J * (g * col0 X)) 0 0 = β := ⟨_, rfl⟩
  have hM : cT (σ : E →+* E) (col0 X) * J * (g * col0 X) = β • 1 := hβdef ▸ eq_smul_one _
  have hβ : β ≠ 0 := by
    intro h0
    apply hO
    unfold OrthL
    rw [hγinv, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc _ g, hM, h0, zero_smul]
    simp
  have hvv : cT (σ : E →+* E) (β⁻¹ • (g * col0 X)) * J * (β⁻¹ • (g * col0 X)) = 0 := by
    rw [cT_smul, Formalism.UG.cT_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      show cT (σ : E →+* E) (col0 X) * cT (σ : E →+* E) g * J * (g * col0 X) = cT (σ : E →+* E) (col0 X) * J * col0 X by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc J g (col0 X), ← Matrix.mul_assoc (cT _ g) (J * g) (col0 X),
          ← Matrix.mul_assoc (cT _ g) J g, hg], hxx, smul_zero, smul_zero]
  have hxv : cT (σ : E →+* E) (col0 X) * J * (β⁻¹ • (g * col0 X)) = 1 := by
    rw [Matrix.mul_smul, hM, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  obtain ⟨N, hU, hNv, hNx, hxN, hNz⟩ :=
    exists_eichler (σ : E →+* E) hs J hJc (col0 X) (col0 Y) _ hxx hyy hxy hvv hxv
  have hdet : IsUnit (1 + N).det := by
    refine isUnit_iff_ne_zero.2 fun h0 => hJ.2 ?_
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  let ν0 : GRat σ J := ⟨Matrix.nonsingInvUnit (1 + N) hdet, hU⟩
  have hνm : (matHom _ σ J (ratEmb σ J ν0)).1 = adMat F (1 + N) := rfl
  have hm : adMat F (1 + N) - 1 = adMat F N := by
    rw [show adMat F (1 + N) = (inclR (F := F) (AF F)).mapMatrix (1 + N) from rfl, map_add, map_one,
      add_sub_cancel_left]; rfl
  have hνU : ratEmb σ J ν0 ∈ unipRad σ J (col0 X) := by
    refine Subgroup.subset_closure ?_
    show _ ∧ _ ∧ _
    rw [hνm, hm]
    refine ⟨?_, ?_, fun z hz => ?_⟩
    · rw [adMat, adMat, ← Matrix.map_mul, hNx]; simp
    · rw [adMat, adMat, ← Matrix.map_mul, hxN]; simp
    · obtain ⟨w', hw'⟩ := hNz z hz
      refine ⟨fun i => inclR (F := F) (AF F) (w' i), funext fun i => ?_⟩
      exact (RingHom.map_mulVec _ N z i).symm.trans (by rw [hw']; exact RingHom.map_mulVec _ (col0 X) w' i)
  have hνR : ratEmb σ J ν0 ∈ ratPts σ J := by rw [← range_ratEmb]; exact ⟨ν0, rfl⟩
  refine ⟨⟨⟨ratEmb σ J ν0, hνU⟩, Subgroup.mem_subgroupOf.2 hνR⟩,
    (Units.mk0 β hβ).map (inclR (F := F) (AF F)).toMonoidHom, ?_⟩
  have hy : (1 + N) * (g * col0 X) = β • col0 Y := by
    have e : g * col0 X = β • (β⁻¹ • (g * col0 X)) := by rw [smul_smul, mul_inv_cancel₀ hβ, one_smul]
    rw [e, Matrix.mul_smul, hNv]
  have hsm : adMat F (β • col0 Y) = inclR (F := F) (AF F) β • adMat F (col0 Y) := by
    ext i j; simp [adMat, map_mul]
  simp only [map_mul, Units.val_mul, hγinv, hνm, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, hy, ← adMat, hsm,
    Matrix.mul_smul, hwy]
  rfl
