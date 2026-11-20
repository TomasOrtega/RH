import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.UnitaryEntriesCompact

open scoped Matrix

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hJ K hK`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Establish `hJt : (Jᵀ).det ≠ 0` using `by rwa [Matrix.det_transpose]`. Take `⟨K', hK', hKe⟩` from `GlobalTheory.StabCompact.exists_compact_of_entries (AF F) σ Jᵀ hJt K hK`.

Establish `hmem : ∀ g : UA σ J, g.1 ∈ HR (AF F) σ Jᵀ`. Introduce `g`. Establish `hg : ((g.1 : Matrix (Fin n) (Fin n) (AE F E)))ᵀ * incM F J * (g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J` using `g.2`. Use `show Formalism.UG.cT (sigR (AF F) σ) (g.1 : Matrix (Fin n) (Fin n) (AE F E)) * JR (AF F) Jᵀ * (g.1 : Matrix (Fin n) (Fin n) (AE F E)) = JR (AF F) Jᵀ`. Establish `h1 : JR (F` using `F) (AF F) Jᵀ = (incM F J)ᵀ := rfl`.

Establish `h2 : Formalism.UG.cT (sigR (AF F) σ) (g.1 : Matrix (Fin n) (Fin n) (AE F E)) = (((g.1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ))ᵀ` using `rfl`. Rewrite using `[h1, h2]`. Use `congrArg Matrix.transpose hg` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[Matrix.mul_assoc]`.

Conclude with `this`. Set `f : HA (AF F) σ Jᵀ → UA σ J` to `fun h => ⟨(h : HR (AF F) σ Jᵀ).1, by`. Establish `hh : Formalism.UG.cT (sigR (AF F) σ) ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)) * JR (AF F) Jᵀ * ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)) = JR (AF F) Jᵀ` using `(h : HR (AF F) σ Jᵀ).2`. Use `show (((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)))ᵀ * incM F J * ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J`. Establish `h1 : JR (F` using `F) (AF F) Jᵀ = (incM F J)ᵀ := rfl`.

Establish `h2 : Formalism.UG.cT (sigR (AF F) σ) ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)) = ((((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ))ᵀ` using `rfl`. Rewrite `hh` using `[h1, h2]`. Use `congrArg Matrix.transpose hh` as an intermediate fact. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this⟩` and apply the resulting hypothesis. Establish `hf : Continuous f` using `by show Continuous fun h : HR (AF F) σ Jᵀ => (⟨h.1, _⟩ : UA σ J)`.

Conclude with `continuous_subtype_val.subtype_mk _`. Use `⟨f '' K', hK'.image hf, fun g hg => ?_⟩` and prove the remaining obligations. Use `⟨(⟨g.1, hmem g⟩ : HR (AF F) σ Jᵀ), hKe _ (fun i j => hg i j), rfl⟩` and prove the remaining obligations.
-/
theorem exists_compact_of_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), IsCompact K → ∃ C : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J), IsCompact C ∧ ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J, (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g i j ∈ K) → g ∈ C := by
  intro F E _ _ _ _ _ σ n J hJ K hK
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hJt : (Jᵀ).det ≠ 0 := by rwa [Matrix.det_transpose]
  obtain ⟨K', hK', hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF F) σ Jᵀ hJt K hK
  have hmem : ∀ g : UA σ J, g.1 ∈ HR (AF F) σ Jᵀ := by
    intro g
    have hg : ((g.1 : Matrix (Fin n) (Fin n) (AE F E)))ᵀ * incM F J * (g.1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J := g.2
    show Formalism.UG.cT (sigR (AF F) σ) (g.1 : Matrix (Fin n) (Fin n) (AE F E)) * JR (AF F) Jᵀ * (g.1 : Matrix (Fin n) (Fin n) (AE F E)) = JR (AF F) Jᵀ
    have h1 : JR (F := F) (AF F) Jᵀ = (incM F J)ᵀ := rfl
    have h2 : Formalism.UG.cT (sigR (AF F) σ) (g.1 : Matrix (Fin n) (Fin n) (AE F E)) = (((g.1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ))ᵀ := rfl
    rw [h1, h2]
    have := congrArg Matrix.transpose hg
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
    rw [Matrix.mul_assoc]
    exact this
  let f : HA (AF F) σ Jᵀ → UA σ J := fun h => ⟨(h : HR (AF F) σ Jᵀ).1, by
    have hh : Formalism.UG.cT (sigR (AF F) σ) ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)) * JR (AF F) Jᵀ * ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)) = JR (AF F) Jᵀ := (h : HR (AF F) σ Jᵀ).2
    show (((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)))ᵀ * incM F J * ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J
    have h1 : JR (F := F) (AF F) Jᵀ = (incM F J)ᵀ := rfl
    have h2 : Formalism.UG.cT (sigR (AF F) σ) ((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E)) = ((((h : HR (AF F) σ Jᵀ).1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ))ᵀ := rfl
    rw [h1, h2] at hh
    have := congrArg Matrix.transpose hh
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this⟩
  have hf : Continuous f := by
    show Continuous fun h : HR (AF F) σ Jᵀ => (⟨h.1, _⟩ : UA σ J)
    exact continuous_subtype_val.subtype_mk _
  refine ⟨f '' K', hK'.image hf, fun g hg => ?_⟩
  refine ⟨(⟨g.1, hmem g⟩ : HR (AF F) σ Jᵀ), hKe _ (fun i j => hg i j), rfl⟩

end GlobalTheory.UnitaryEntriesCompact
