import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowMulMemOrder

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Use `haveI : Module.Free F E := L.free`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Establish `hc : IsIntegral F c` using `Algebra.IsIntegral.isIntegral c`. Take `⟨⟨m, hm0⟩, hm⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors 𝒪[F]) c hc`. Establish `hmne : m ≠ 0` using `nonZeroDivisors.ne_zero hm0`.

Take `⟨k, hk⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hmne hϖ`. Take `⟨u, hu⟩` from `hk`. Use `⟨k, (L.O_def _).2 ?_⟩` and prove the remaining obligations. Establish `h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • ((⟨m, hm0⟩ : nonZeroDivisors 𝒪[F]) • c))` using `hm.smul _`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Submonoid.smul_def, smul_smul, ← hu]`. Rewrite using `[Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]`. Rewrite using `[mul_comm (u : 𝒪[F]) m, hu]`. Both sides reduce to the same expression.
-/
theorem exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨⟨m, hm0⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) c hc
  have hmne : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hmne hϖ
  obtain ⟨u, hu⟩ := hk
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • ((⟨m, hm0⟩ : nonZeroDivisors 𝒪[F]) • c)) := hm.smul _
  convert h2 using 1
  simp only [Submonoid.smul_def, smul_smul, ← hu]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rw [mul_comm (u : 𝒪[F]) m, hu]
  rfl

/- English proof (translation)
Introduce `F _ _ _ _ E _ _ _ L ϖ hϖ p hp n Λ hΛ v`. Establish `key : ∀ c : E, ∃ k : ℕ, ((p ^ k : L.O) : E) * c ∈ L.O`. Introduce `c`. Take `⟨k, hk⟩` from `exists_pow_mul_mem L hϖ c`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `: ((p ^ k : L.O) : E) = algebraMap F E ((ϖ : F) ^ k)`. Rewrite using `[SubmonoidClass.coe_pow, hp, map_pow]`. Rewrite using `[this]`. Conclude with `hk`. Establish `mono : ∀ (x : Fin n → E) (i j : ℕ), p ^ j • x ∈ Λ → p ^ (i + j) • x ∈ Λ`.

Introduce `x i j h`. Rewrite using `[pow_add, mul_smul]`. Conclude with `Λ.smul_mem _ h`. Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin n → E))` using `by rw [hΛ.2]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨0, by simpa using hx⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Λ.add_mem ?_ (mono y a b hb)` and prove the remaining obligations. Rewrite using `[add_comm]`. Conclude with `mono x b a ha`.

Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`. Take `⟨k, hk⟩` from `key c`. Use `⟨k + a, ?_⟩` and prove the remaining obligations. Establish `e1 : p ^ (k + a) • (c • x) = (⟨((p ^ k : L.O) : E) * c, hk⟩ : L.O) • (p ^ a • x)`.

Simplify using `only [Subring.smul_def, smul_smul, pow_add, Subring.coe_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `Λ.smul_mem _ ha`.
-/
theorem main : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type} [inst_4 : CommRing E] [inst_5 : Algebra F E] [inst_6 : TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) {ϖ : ↥(Valuation.integer (ValuativeRel.valuation F))}, Irreducible ϖ → ∀ (p : ↥(Formalism.MainNotions.S.Loc.LocE.O L)), (↑p : E) = (Algebra.algebraMap F E : F → E) (↑ϖ : F) → ∀ {n : ℕ} {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)}, GlobalTheory.HL.IsLat L Λ → ∀ (v : Fin n → E), ∃ (j : ℕ), p ^ j • v ∈ Λ := by
  intro F _ _ _ _ E _ _ _ L ϖ hϖ p hp n Λ hΛ v
  have key : ∀ c : E, ∃ k : ℕ, ((p ^ k : L.O) : E) * c ∈ L.O := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_mul_mem L hϖ c
    refine ⟨k, ?_⟩
    have : ((p ^ k : L.O) : E) = algebraMap F E ((ϖ : F) ^ k) := by
      rw [SubmonoidClass.coe_pow, hp, map_pow]
    rw [this]; exact hk
  have mono : ∀ (x : Fin n → E) (i j : ℕ), p ^ j • x ∈ Λ → p ^ (i + j) • x ∈ Λ := by
    intro x i j h
    rw [pow_add, mul_smul]
    exact Λ.smul_mem _ h
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ (mono y a b hb)
    rw [add_comm]; exact mono x b a ha
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨k, hk⟩ := key c
    refine ⟨k + a, ?_⟩
    have e1 : p ^ (k + a) • (c • x) = (⟨((p ^ k : L.O) : E) * c, hk⟩ : L.O) • (p ^ a • x) := by
      simp only [Subring.smul_def, smul_smul, pow_add, Subring.coe_mul]
      congr 1
      ring
    rw [e1]
    exact Λ.smul_mem _ ha

end GlobalTheory.PowMulMemOrder
