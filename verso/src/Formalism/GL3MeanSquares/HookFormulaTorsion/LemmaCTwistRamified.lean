import Mathlib
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral

namespace Formalism.HermitianLattices.RamifiedHeckeModels

/- English proof (translation)
Unfold `LemmaC_twist_ram`. Introduce `R _ _ _ ϖ hϖ M _ _ P S B U D e b hSB hBU hSD hPU hPD hsat hUD hfree hfin`. Establish `hpow : ∀ n : ℕ, ∀ x : M, ϖ ^ n • x ∈ P → x ∈ P`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ n ih`. Introduce `x hx`. Apply `hsat` to reduce the goal to its premises.

Apply `ih` to reduce the goal to its premises. Rewrite using `[← mul_smul, ← pow_succ]` and apply the resulting hypothesis. Establish `h1 : (S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B ⊓ P`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `⟨hSB ⟨s, hs.1, rfl⟩, by simpa using P.smul_mem (ϖ ^ b) hs.2⟩`.

Establish `h2 : (B ⊓ P).map U ≤ S ⊓ P`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨hBU ⟨x, hx.1, rfl⟩, hPU ⟨x, hx.2, rfl⟩⟩`. Establish `h3 : (S ⊓ P).map D ≤ B ⊓ P`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `⟨hSD ⟨x, hx.1, rfl⟩, hPD ⟨x, hx.2, rfl⟩⟩`. Set `ι : (S ⊓ P : Submodule R M) →ₗ[R] S` to `Submodule.inclusion inf_le_left`. Establish `hι : Function.Injective ι` using `Submodule.inclusion_injective _`. Take `⟨n, bN⟩` from `Submodule.basisOfPid (Module.Free.chooseBasis R S) ((S ⊓ P).comap S.subtype)`. Set `eN : ((S ⊓ P).comap S.subtype) ≃ₗ[R] (S ⊓ P : Submodule R M)` to `Submodule.comapSubtypeEquivOfLe inf_le_left`.

Use `haveI : Module.Free R (S ⊓ P : Submodule R M) := Module.Free.of_basis (bN.map eN)`. Use `haveI : Module.Finite R (S ⊓ P : Submodule R M) := Module.Finite.of_basis (bN.map eN)`. Establish `key` using `lemma_c_under_twist`. Unfold `LemmaC_twist at key`. Establish `key'` using `key R ϖ hϖ M (S ⊓ P) (B ⊓ P) U D e b h1 h2 h3 hUD inferInstance inferInstance`.

Establish `hrank : Module.finrank R (S ⊓ P : Submodule R M) ≤ Module.finrank R S` using `LinearMap.finrank_le_finrank_of_injective hι`. Establish `hlen : Module.length R ((B ⊓ P : Submodule R M) ⧸ ((S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap (B ⊓ P).subtype) ≤ Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype)`. Use `Module.length_le_of_injective (Submodule.mapQ _ _ (Submodule.inclusion (inf_le_left : B ⊓ P ≤ B)) ?_) ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢`.

Conclude with `Submodule.map_mono inf_le_left hx`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `q hq`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Rewrite `hq` using `[LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`.

Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hq ⊢`. Take `⟨s, hs, hsx⟩` from `hq`. Use `⟨s, ⟨hs, ?_⟩, hsx⟩` and prove the remaining obligations. Apply `hpow b` to reduce the goal to its premises.

Establish `hx' : (ϖ ^ b • s : M) = x` using `by simpa using hsx`. Rewrite using `[hx']`. Conclude with `x.2.2`. Use `key'.trans (add_le_add hlen ?_)` and prove the remaining obligations. Conclude with `Nat.mul_le_mul_left e hrank` after adjusting the coercions.
-/
theorem lemma_c_twist_ramified : LemmaC_twist_ram := by
  unfold LemmaC_twist_ram
  intro R _ _ _ ϖ hϖ M _ _ P S B U D e b hSB hBU hSD hPU hPD hsat hUD hfree hfin
  have hpow : ∀ n : ℕ, ∀ x : M, ϖ ^ n • x ∈ P → x ∈ P := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply hsat
      apply ih
      rwa [← mul_smul, ← pow_succ]
  have h1 : (S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B ⊓ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hSB ⟨s, hs.1, rfl⟩, by simpa using P.smul_mem (ϖ ^ b) hs.2⟩
  have h2 : (B ⊓ P).map U ≤ S ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hBU ⟨x, hx.1, rfl⟩, hPU ⟨x, hx.2, rfl⟩⟩
  have h3 : (S ⊓ P).map D ≤ B ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hSD ⟨x, hx.1, rfl⟩, hPD ⟨x, hx.2, rfl⟩⟩
  let ι : (S ⊓ P : Submodule R M) →ₗ[R] S := Submodule.inclusion inf_le_left
  have hι : Function.Injective ι := Submodule.inclusion_injective _
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Module.Free.chooseBasis R S)
    ((S ⊓ P).comap S.subtype)
  let eN : ((S ⊓ P).comap S.subtype) ≃ₗ[R] (S ⊓ P : Submodule R M) :=
    Submodule.comapSubtypeEquivOfLe inf_le_left
  haveI : Module.Free R (S ⊓ P : Submodule R M) := Module.Free.of_basis (bN.map eN)
  haveI : Module.Finite R (S ⊓ P : Submodule R M) := Module.Finite.of_basis (bN.map eN)
  have key := lemma_c_under_twist
  unfold LemmaC_twist at key
  have key' := key R ϖ hϖ M (S ⊓ P) (B ⊓ P) U D e b h1 h2 h3 hUD inferInstance inferInstance
  have hrank : Module.finrank R (S ⊓ P : Submodule R M) ≤ Module.finrank R S :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hlen : Module.length R ((B ⊓ P : Submodule R M) ⧸
      ((S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap (B ⊓ P).subtype) ≤
      Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) := by
    refine Module.length_le_of_injective
      (Submodule.mapQ _ _ (Submodule.inclusion (inf_le_left : B ⊓ P ≤ B)) ?_) ?_
    · intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact Submodule.map_mono inf_le_left hx
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hq ⊢
      obtain ⟨s, hs, hsx⟩ := hq
      refine ⟨s, ⟨hs, ?_⟩, hsx⟩
      apply hpow b
      have hx' : (ϖ ^ b • s : M) = x := by simpa using hsx
      rw [hx']
      exact x.2.2
  refine key'.trans (add_le_add hlen ?_)
  exact_mod_cast Nat.mul_le_mul_left e hrank

end Formalism.HermitianLattices.RamifiedHeckeModels
