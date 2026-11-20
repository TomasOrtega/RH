import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.InertCoh

/- English proof (translation)
Set `f : Y →ₗ[R] N` to `ev ∘ₗ Y.subtype`. Set `g : Y →ₗ[R] (M ⧸ B)` to `B.mkQ ∘ₗ Y.subtype`. Establish `hf : (LinearMap.range f).FG`. Use `hL.of_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `h2 y y.2`. Establish `hker : LinearMap.ker f ≤ LinearMap.ker g`. Introduce `y hy`. Conclude with `(Submodule.Quotient.mk_eq_zero B).2 (h3 y y.2 hy)`. Use `haveI : Module.Finite R (LinearMap.range f) := Module.Finite.iff_fg.2 hf`.

Use `haveI : Module.Finite R (Y ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm`. Establish `hg : (LinearMap.range g).FG`. Rewrite using `[← Submodule.range_liftQ (LinearMap.ker f) g hker, LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`. Use `hg.of_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨y, hy, hzy⟩` from `h1 z hz`. Conclude with `⟨⟨y, hy⟩, ((Submodule.Quotient.eq B).2 hzy).symm⟩`.
-/
theorem fg_map_mkQ_of_ev {R M N : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Z B Y : Submodule R M) (ev : M →ₗ[R] N) (L : Submodule R N) (hL : L.FG)
    (h1 : ∀ z ∈ Z, ∃ y ∈ Y, z - y ∈ B) (h2 : ∀ y ∈ Y, ev y ∈ L) (h3 : ∀ y ∈ Y, ev y = 0 → y ∈ B) :
    (Z.map B.mkQ).FG := by
  let f : Y →ₗ[R] N := ev ∘ₗ Y.subtype
  let g : Y →ₗ[R] (M ⧸ B) := B.mkQ ∘ₗ Y.subtype
  have hf : (LinearMap.range f).FG := by
    refine hL.of_le ?_
    rintro _ ⟨y, rfl⟩
    exact h2 y y.2
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro y hy
    exact (Submodule.Quotient.mk_eq_zero B).2 (h3 y y.2 hy)
  haveI : Module.Finite R (LinearMap.range f) := Module.Finite.iff_fg.2 hf
  haveI : Module.Finite R (Y ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  have hg : (LinearMap.range g).FG := by
    rw [← Submodule.range_liftQ (LinearMap.ker f) g hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine hg.of_le ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hzy⟩ := h1 z hz
  exact ⟨⟨y, hy⟩, ((Submodule.Quotient.eq B).2 hzy).symm⟩

/- English proof (translation)
Establish `hm : Continuous fun s => mat W s` using `Units.continuous_val.comp hW`. Use `mem_coc.2 ⟨fun i => ?_, fun s i => ?_, fun s _ t _ => ?_⟩` and prove the remaining obligations. Conclude with `(continuous_apply i).comp ((hm.matrix_mulVec continuous_const).sub continuous_const)`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct]`. Conclude with `c.O.sub_mem (c.O.sum_mem fun j _ => c.O.mul_mem (hO s i j) (hv j)) (hv i)`.

Simplify using `only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem cobound_mem_coc {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {W : R2 Ω l} {c : Coef l}
    (I : Subgroup (G ℚ Ω)) (hW : Continuous W) (hO : ∀ s i j, mat W s i j ∈ c.O) {v : Fin 2 → Qbar l}
    (hv : ∀ i, v i ∈ c.O) : (fun s => mat W s *ᵥ v - v) ∈ coc W c I := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hW
  refine mem_coc.2 ⟨fun i => ?_, fun s i => ?_, fun s _ t _ => ?_⟩
  · exact (continuous_apply i).comp ((hm.matrix_mulVec continuous_const).sub continuous_const)
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    exact c.O.sub_mem (c.O.sum_mem fun j _ => c.O.mul_mem (hO s i j) (hv j)) (hv i)
  · simp only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel

/- English proof (translation)
Introduce `l _ Ω _ _ W c I P γ hW hO hP hγ`. Use `haveI := c.dvr`. Use `haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing`. Set `Y : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l)` to `coc W c I ⊓ ⨅ σ ∈ P, LinearMap.ker (LinearMap.proj σ : (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (Fin 2 → Qbar l))`. Establish `hY : ∀ z, z ∈ Y ↔ z ∈ coc W c I ∧ ∀ σ ∈ P, z σ = 0`.

Introduce `z`. Simplify using `[Y, Submodule.mem_iInf]`. Set `ι : (Fin 2 → c.O) →ₗ[c.O] (Fin 2 → Qbar l)` to `(Algebra.linearMap c.O (Qbar l)).compLeft (Fin 2)`. Establish `hL : (LinearMap.range ι).FG`. Rewrite using `[LinearMap.range_eq_map]`.

Conclude with `Module.Finite.fg_top.map _`. Use `fg_map_mkQ_of_ev _ _ Y (LinearMap.proj γ) _ hL ?_ ?_ ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨v, hv, hzv⟩` from `hP z hz`. Use `⟨z - fun s => mat W s *ᵥ v - v, (hY _).2 ⟨Submodule.sub_mem _ hz (cobound_mem_coc I hW hO hv), ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `σ hσ`. Simplify using `only [Pi.sub_apply, hzv σ hσ, sub_self]`. Conclude with `mem_cob.2 ⟨v, fun s _ => by simp only [sub_sub_cancel]⟩`. Introduce `y hy`. Conclude with `⟨fun i => ⟨y γ i, (mem_coc.1 ((hY y).1 hy).1).2.1 γ i⟩, rfl⟩`.

Introduce `y hy h0`. Use `mem_cob.2 ⟨0, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[hγ y ((hY y).1 hy).1 ((hY y).1 hy).2 h0 s hs]`. Simplify using the standard rewrite rules.
-/
theorem fg_coc_mod_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  intro l _ Ω _ _ W c I P γ hW hO hP hγ
  haveI := c.dvr
  haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  let Y : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) :=
    coc W c I ⊓ ⨅ σ ∈ P, LinearMap.ker (LinearMap.proj σ : (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (Fin 2 → Qbar l))
  have hY : ∀ z, z ∈ Y ↔ z ∈ coc W c I ∧ ∀ σ ∈ P, z σ = 0 := by
    intro z
    simp [Y, Submodule.mem_iInf]
  let ι : (Fin 2 → c.O) →ₗ[c.O] (Fin 2 → Qbar l) := (Algebra.linearMap c.O (Qbar l)).compLeft (Fin 2)
  have hL : (LinearMap.range ι).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine fg_map_mkQ_of_ev _ _ Y (LinearMap.proj γ) _ hL ?_ ?_ ?_
  · intro z hz
    obtain ⟨v, hv, hzv⟩ := hP z hz
    refine ⟨z - fun s => mat W s *ᵥ v - v, (hY _).2 ⟨Submodule.sub_mem _ hz (cobound_mem_coc I hW hO hv), ?_⟩, ?_⟩
    · intro σ hσ
      simp only [Pi.sub_apply, hzv σ hσ, sub_self]
    · exact mem_cob.2 ⟨v, fun s _ => by simp only [sub_sub_cancel]⟩
  · intro y hy
    exact ⟨fun i => ⟨y γ i, (mem_coc.1 ((hY y).1 hy).1).2.1 γ i⟩, rfl⟩
  · intro y hy h0
    refine mem_cob.2 ⟨0, fun s hs => ?_⟩
    rw [hγ y ((hY y).1 hy).1 ((hY y).1 hy).2 h0 s hs]
    simp

end GlobalTheory.InertCoh
