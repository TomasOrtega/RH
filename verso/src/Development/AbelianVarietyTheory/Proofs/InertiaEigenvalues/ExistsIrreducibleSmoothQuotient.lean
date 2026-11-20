import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.IrrQuot

/- English proof (translation)
Introduce `G V _ _ _ _ _ ρ hsm hfl hnt`. Use `haveI : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1`. Establish `hbt : (⊥ : Subrepresentation ρ) ≠ ⊤`. Introduce `h`. Take `⟨x, hx⟩` from `exists_ne (0 : V)`.

Establish `hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `hmem` using `[← h]`. Conclude with `hx ((Submodule.mem_bot ℂ).1 hmem)`. Take `⟨M, hM, -⟩` from `(IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt`. Set `W : Submodule ℂ V` to `M.toSubmodule`.

Establish `hW : ∀ g : G, W ≤ W.comap (ρ g)` using `fun g v hv => M.apply_mem_toSubmodule g hv`. Set `τ : Representation ℂ G (V ⧸ W)` to `ρ.quotient W hW`. Establish `hτ : ∀ (g : G) (v : V), τ g (W.mkQ v) = W.mkQ (ρ g v)` using `fun g v => rfl`. Set `q : ρ.IntertwiningMap τ` to `⟨W.mkQ, fun g => by ext v; rfl⟩`. Establish `hq : Function.Surjective q` using `Submodule.mkQ_surjective W`.

Use `⟨V ⧸ W, inferInstance, inferInstance, τ, ?_, ?_, q, hq⟩` and prove the remaining obligations. Introduce `x`. Take `⟨v, rfl⟩` from `Submodule.mkQ_surjective W x`. Set `stab : (u : Type) → [AddCommGroup u] → [Module ℂ u] → (σ : Representation ℂ G u) → u → Subgroup G` to `fun u _ _ σ y => { carrier := {g | σ g y = y} mul_mem' := by`. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`.

Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `hle : stab V ρ v ≤ stab (V ⧸ W) τ (W.mkQ v)`. Introduce `g hg`.

Express the relevant statement in the definitionally equal form `τ g (W.mkQ v) = W.mkQ v`. Rewrite using `[hτ]`. Conclude with `congrArg W.mkQ hg`. Conclude with `Subgroup.isOpen_mono hle (hsm v)`. Establish `hMtop : M ≠ ⊤` using `hM.1`.

Use `{ exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }` and prove the remaining obligations. Introduce `h`. Apply `hMtop` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `eq_top_iff.2` to reduce the goal to its premises.

Introduce `v _`. Establish `hmem : W.mkQ v ∈ (⊤ : Subrepresentation τ).toSubmodule` using `Submodule.mem_top`. Rewrite `hmem` using `[← h]`. Conclude with `(Submodule.Quotient.mk_eq_zero W).1 ((Submodule.mem_bot ℂ).1 hmem)`. Introduce `S`.

Set `T : Subrepresentation ρ` to `⟨S.toSubmodule.comap W.mkQ, fun g v hv => by`. Express the relevant statement in the definitionally equal form `W.mkQ (ρ g v) ∈ S.toSubmodule`. Rewrite using `[← hτ]`. Conclude with `S.apply_mem_toSubmodule g hv⟩`. Establish `hMT : M ≤ T`.

Introduce `v hv`. Express the relevant statement in the definitionally equal form `W.mkQ v ∈ S.toSubmodule`. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hv]`. Conclude with `S.toSubmodule.zero_mem`. Break down `hM.le_iff.1 hMT with h | h` into its components or cases.

Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `eq_top_iff.2` to reduce the goal to its premises. Introduce `x _`. Take `⟨v, rfl⟩` from `Submodule.mkQ_surjective W x`.

Establish `hvT : v ∈ T.toSubmodule` using `by rw [h]; exact Submodule.mem_top`. Conclude with `hvT`. Use `left`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Apply `eq_bot_iff.2` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨v, rfl⟩` from `Submodule.mkQ_surjective W x`. Establish `hvT : v ∈ T.toSubmodule` using `hx`. Rewrite `hvT` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).2 (by rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero W).2 hvT)`.
-/
theorem exists_irreducible_smooth_quotient : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → Nontrivial V →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y),
      IsSmooth τ ∧ τ.IsIrreducible ∧ ∃ q : ρ.IntertwiningMap τ, Function.Surjective q := by
  intro G V _ _ _ _ _ ρ hsm hfl hnt
  haveI : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  let W : Submodule ℂ V := M.toSubmodule
  have hW : ∀ g : G, W ≤ W.comap (ρ g) := fun g v hv => M.apply_mem_toSubmodule g hv
  let τ : Representation ℂ G (V ⧸ W) := ρ.quotient W hW
  have hτ : ∀ (g : G) (v : V), τ g (W.mkQ v) = W.mkQ (ρ g v) := fun g v => rfl
  let q : ρ.IntertwiningMap τ := ⟨W.mkQ, fun g => by ext v; rfl⟩
  have hq : Function.Surjective q := Submodule.mkQ_surjective W
  refine ⟨V ⧸ W, inferInstance, inferInstance, τ, ?_, ?_, q, hq⟩
  ·
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
    let stab : (u : Type) → [AddCommGroup u] → [Module ℂ u] → (σ : Representation ℂ G u) → u → Subgroup G :=
      fun u _ _ σ y =>
        { carrier := {g | σ g y = y}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at ha hb ⊢
            rw [map_mul, Module.End.mul_apply, hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at ha ⊢
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hle : stab V ρ v ≤ stab (V ⧸ W) τ (W.mkQ v) := by
      intro g hg
      change τ g (W.mkQ v) = W.mkQ v
      rw [hτ]
      exact congrArg W.mkQ hg
    exact Subgroup.isOpen_mono hle (hsm v)
  ·
    have hMtop : M ≠ ⊤ := hM.1
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro h
      apply hMtop
      apply Subrepresentation.toSubmodule_injective
      apply eq_top_iff.2
      intro v _
      have hmem : W.mkQ v ∈ (⊤ : Subrepresentation τ).toSubmodule := Submodule.mem_top
      rw [← h] at hmem
      exact (Submodule.Quotient.mk_eq_zero W).1 ((Submodule.mem_bot ℂ).1 hmem)
    · intro S
      let T : Subrepresentation ρ := ⟨S.toSubmodule.comap W.mkQ, fun g v hv => by
        change W.mkQ (ρ g v) ∈ S.toSubmodule
        rw [← hτ]
        exact S.apply_mem_toSubmodule g hv⟩
      have hMT : M ≤ T := by
        intro v hv
        change W.mkQ v ∈ S.toSubmodule
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hv]
        exact S.toSubmodule.zero_mem
      rcases hM.le_iff.1 hMT with h | h
      · right
        apply Subrepresentation.toSubmodule_injective
        apply eq_top_iff.2
        intro x _
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := by rw [h]; exact Submodule.mem_top
        exact hvT
      · left
        apply Subrepresentation.toSubmodule_injective
        apply eq_bot_iff.2
        intro x hx
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W x
        have hvT : v ∈ T.toSubmodule := hx
        rw [h] at hvT
        exact (Submodule.mem_bot ℂ).2 (by rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero W).2 hvT)

end GlobalTheory.SmGL.IrrQuot
