import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincTransv

/- English proof (translation)
Introduce `E _ _ _ H l Di r ξ₀ Gm φ0 hξ h`. Establish `hξ' : IsCMField.complexConj E ξ₀ = -ξ₀` using `hξ`. Establish `hG` using `h.2.2.1`. Establish `hint` using `(GlobalTheory.HermModel.rank_integral_selfDual E H Di r (-ξ₀) Gm φ0 (by simp [cc, hξ']) h).2.2.1`. Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`.

Use `set d : ℕ := (NumberField.discr E).natAbs with hd`. Establish `hd0 : 0 < d` using `Int.natAbs_pos.2 (NumberField.discr_ne_zero E)`. Use `⟨l.M * l.A * d, Nat.mul_pos (Nat.mul_pos hM l.A_pos) hd0, ?_⟩` and prove the remaining obligations. Introduce `κ0 hκ ξ hξΛ hiso s hs hsi`. Establish `hκc : IsCMField.complexConj E κ0 = -κ0`.

Apply the tactic sequence `rcases hκ with h | h <;> simp [h, hξ', map_ofNat]`. Establish `hs' : IsCMField.complexConj E s = s` using `hs`. Use `set α : E := ((l.M * l.A * d : ℕ) : E) * s * κ0 with hαdef`. Establish `hα : cc α = -α`. Simplify using `[hαdef, cc, hs', hκc]`.

Establish `h2 : IsIntegral ℤ (2 : E)` using `isIntegral_natCast 2`. Establish `hint' : ∀ v ∈ LinearMap.range φ0, IsIntegral ℤ ((d : E) * κ0 * herm Gm v ξ)`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, rfl⟩` from `hξΛ`. Establish `h1` using `h2.mul (hint x y)`.

Establish `hdd : (d : E) = (NumberField.discr E : E) ∨ (d : E) = -(NumberField.discr E : E)`. Break down `Int.natAbs_eq (NumberField.discr E) with h | h` into its components or cases. Use `left`. Rewrite using `[h, Int.cast_natCast]`. Use `right`.

Rewrite using `[h, Int.cast_neg, Int.cast_natCast, neg_neg]`. Establish `hpm : (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) = 2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y))) ∨ (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) = -(2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y))))`. Apply the tactic sequence `rcases hdd with e | e <;> rcases hκ with e' | e' <;> rw [e, e']`. Use `right`. Expand and normalize the polynomial expressions, which then agree.

Use `left`. Expand and normalize the polynomial expressions, which then agree. Use `left`. Expand and normalize the polynomial expressions, which then agree. Use `right`.

Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `rcases hpm with e | e <;> rw [e]`. Conclude with `h1`. Conclude with `h1.neg`. Establish `key : ∀ v ∈ LinearMap.range φ0, (s * ((d : E) * κ0 * herm Gm v ξ)) • ξ ∈ LinearMap.range φ0` using `fun v hv => GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hsi.mul (hint' v hv)) hξΛ`.

Establish `e : ∀ v, (α * herm Gm v ξ) • ξ = (l.M * l.A) • ((s * ((d : E) * κ0 * herm Gm v ξ)) • ξ)`. Introduce `v`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, smul_smul, hαdef]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨GlobalTheory.FlagData.transv Gm hiso α, ⟨⟨GlobalTheory.FlagData.herm_transvMat hG hiso hα, fun x => ?_⟩, fun a _ => ?_, fun a => ?_⟩, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ LinearMap.range φ0 ↔ transvMat Gm ξ α *ᵥ x ∈ LinearMap.range φ0`. Rewrite using `[GlobalTheory.FlagData.transvMat_mulVec]`. Use `⟨fun hx => Submodule.add_mem _ hx (by rw [e]; exact nsmul_mem (key x hx) _), fun hx => ?_⟩` and prove the remaining obligations.

Establish `h` using `nsmul_mem (key _ hx) (l.M * l.A)`. Rewrite `h` using `[← e, GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero]`. Simplify using `using Submodule.sub_mem _ hx h`. Take `⟨b, hb⟩` from `key _ (LinearMap.mem_range_self φ0 a)`. Use `⟨l.A • b, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `transvMat Gm ξ α *ᵥ φ0 a = _`. Rewrite using `[GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_smul]`. Take `⟨b, hb⟩` from `key _ (LinearMap.mem_range_self φ0 a)`. Use `⟨l.M • b, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `transvMat Gm ξ α *ᵥ φ0 a = _`.

Rewrite using `[GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_comm, mul_smul]`.
-/
theorem transv_mem_princ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) → ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s → ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0) := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 hξ h
  have hξ' : IsCMField.complexConj E ξ₀ = -ξ₀ := hξ
  have hG := h.2.2.1
  have hint := (GlobalTheory.HermModel.rank_integral_selfDual E H Di r (-ξ₀) Gm φ0
    (by simp [cc, hξ']) h).2.2.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  set d : ℕ := (NumberField.discr E).natAbs with hd
  have hd0 : 0 < d := Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  refine ⟨l.M * l.A * d, Nat.mul_pos (Nat.mul_pos hM l.A_pos) hd0, ?_⟩
  intro κ0 hκ ξ hξΛ hiso s hs hsi
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have hs' : IsCMField.complexConj E s = s := hs
  set α : E := ((l.M * l.A * d : ℕ) : E) * s * κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hs', hκc]
  have h2 : IsIntegral ℤ (2 : E) := isIntegral_natCast 2
  have hint' : ∀ v ∈ LinearMap.range φ0, IsIntegral ℤ ((d : E) * κ0 * herm Gm v ξ) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hξΛ
    have h1 := h2.mul (hint x y)
    have hdd : (d : E) = (NumberField.discr E : E) ∨ (d : E) = -(NumberField.discr E : E) := by
      rcases Int.natAbs_eq (NumberField.discr E) with h | h
      · left; rw [h, Int.cast_natCast]
      · right; rw [h, Int.cast_neg, Int.cast_natCast, neg_neg]
    have hpm : (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y))) ∨
        (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          -(2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y)))) := by
      rcases hdd with e | e <;> rcases hκ with e' | e' <;> rw [e, e']
      · right; ring
      · left; ring
      · left; ring
      · right; ring
    rcases hpm with e | e <;> rw [e]
    · exact h1
    · exact h1.neg
  have key : ∀ v ∈ LinearMap.range φ0,
      (s * ((d : E) * κ0 * herm Gm v ξ)) • ξ ∈ LinearMap.range φ0 := fun v hv =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hsi.mul (hint' v hv)) hξΛ
  have e : ∀ v, (α * herm Gm v ξ) • ξ =
      (l.M * l.A) • ((s * ((d : E) * κ0 * herm Gm v ξ)) • ξ) := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  refine ⟨GlobalTheory.FlagData.transv Gm hiso α, ⟨⟨GlobalTheory.FlagData.herm_transvMat hG hiso hα, fun x => ?_⟩,
    fun a _ => ?_, fun a => ?_⟩, rfl⟩
  · change x ∈ LinearMap.range φ0 ↔ transvMat Gm ξ α *ᵥ x ∈ LinearMap.range φ0
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (by rw [e]; exact nsmul_mem (key x hx) _), fun hx => ?_⟩
    have h := nsmul_mem (key _ hx) (l.M * l.A)
    rw [← e, GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.A • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_smul]
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.M • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_comm, mul_smul]

end GlobalTheory.PrincTransv
