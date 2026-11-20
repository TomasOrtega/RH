import Mathlib

/- English proof (translation)
Introduce `K L _ _ _ _ _ τ`. Use `letI : Algebra K ℂ := τ.toAlgebra`. Use `haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L`. Rewrite using `[← AlgHom.card K L ℂ, ← Finset.card_univ]`. Use `symm`.

Use `Finset.card_bij (fun (f : L →ₐ[K] ℂ) _ => (f : L →+* ℂ)) ?_ ?_ ?_` and prove the remaining obligations. Introduce `f _`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, RingHom.ext fun x => f.commutes x⟩`. Introduce `f _ g _ h`.

Conclude with `AlgHom.ext fun x => RingHom.congr_fun h x`. Introduce `σ hσ`. Rewrite `hσ` using `[Finset.mem_filter]`. Conclude with `⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ.2 x }, Finset.mem_univ _, rfl⟩`.
-/
theorem UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
    [inst_4 : Algebra K L] (τ : K →+* ℂ),
    (open Classical in Finset.filter (fun σ : L →+* ℂ => σ.comp (Algebra.algebraMap K L) = τ) Finset.univ).card = Module.finrank K L := by
  intro K L _ _ _ _ _ τ
  classical
  letI : Algebra K ℂ := τ.toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rw [← AlgHom.card K L ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun (f : L →ₐ[K] ℂ) _ => (f : L →+* ℂ)) ?_ ?_ ?_
  · intro f _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, RingHom.ext fun x => f.commutes x⟩
  · intro f _ g _ h
    exact AlgHom.ext fun x => RingHom.congr_fun h x
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact ⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ.2 x }, Finset.mem_univ _, rfl⟩
