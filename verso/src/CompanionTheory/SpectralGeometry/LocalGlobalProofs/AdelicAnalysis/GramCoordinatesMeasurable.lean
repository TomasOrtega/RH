import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB

/- English proof (translation)
Establish `hact` using `((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R).2.2.2.2.2 1).1`. Establish `hco : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k` using `(GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R).2.2.2.2.2.2.1 d b`. Set `X : Fin 1 → Fin M → R ⊗[F] E` to `fun _ => Pi.single q.1 (inclR R (b q.2))`. Establish `h1 : Continuous fun h : HA R σ J => actW R σ J h X` using `hact.comp (continuous_id.prodMk continuous_const)`. Establish `h2 : Continuous fun h : HA R σ J => actW R σ J h X 0 p.1` using `(continuous_apply p.1).comp ((continuous_apply (0 : Fin 1)).comp h1)`.

Establish `h3 : Continuous fun h : HA R σ J => (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2` using `(continuous_apply p.2).comp (hco.continuous.comp h2)`. Use `h3.congr fun h => ?_` and prove the remaining obligations. Simplify using `[gmat, actW, actTup, X, Matrix.mulVec_single]`.
-/
theorem continuous_gmat_entry {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (p q : Fin M × Fin d) :
    Continuous fun h : HA R σ J => gmat R σ J b h p q := by
  classical
  have hact := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R).2.2.2.2.2 1).1
  have hco : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R).2.2.2.2.2.2.1 d b
  let X : Fin 1 → Fin M → R ⊗[F] E := fun _ => Pi.single q.1 (inclR R (b q.2))
  have h1 : Continuous fun h : HA R σ J => actW R σ J h X :=
    hact.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun h : HA R σ J => actW R σ J h X 0 p.1 :=
    (continuous_apply p.1).comp ((continuous_apply (0 : Fin 1)).comp h1)
  have h3 : Continuous fun h : HA R σ J =>
      (Algebra.TensorProduct.basis R b).repr (actW R σ J h X 0 p.1) p.2 :=
    (continuous_apply p.2).comp (hco.continuous.comp h2)
  refine h3.congr fun h => ?_
  simp [gmat, actW, actTup, X, Matrix.mulVec_single]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ d b e he`. Take `⟨⟨hlc, hsc, ht2⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Take `⟨htg, -, -, -, hbor, -⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)`. Apply the tactic sequence `have hinv : ∀ p q, Continuous fun ω : HA (AF F) σ J => gmat (AF F) σ J b ω⁻¹ p q := fun p q => (continuous_gmat_entry σ hσ J hJ b (AF F) p q).comp continuous_inv`. Use `haveI : BorelSpace (Af F) := ⟨rfl⟩`.

Use `⟨fun w p q => ?_, fun p q => ?_⟩` and prove the remaining obligations. Establish `hf : Continuous fun t : AF F => e (fstA F t) w` using `(continuous_apply w).comp (he.continuous.comp continuous_fst)`. Conclude with `(hf.comp (hinv p q)).measurable`. Establish `hf : Continuous fun t : AF F => sndA F t` using `continuous_snd`. Conclude with `(hf.comp (hinv p q)).measurable`.
-/
theorem ginf_gfin_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b e he
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨htg, -, -, -, hbor, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  have hinv : ∀ p q, Continuous fun ω : HA (AF F) σ J => gmat (AF F) σ J b ω⁻¹ p q := fun p q =>
    (continuous_gmat_entry σ hσ J hJ b (AF F) p q).comp continuous_inv
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  refine ⟨fun w p q => ?_, fun p q => ?_⟩
  · have hf : Continuous fun t : AF F => e (fstA F t) w :=
      (continuous_apply w).comp (he.continuous.comp continuous_fst)
    exact (hf.comp (hinv p q)).measurable
  · have hf : Continuous fun t : AF F => sndA F t := continuous_snd
    exact (hf.comp (hinv p q)).measurable

end GlobalTheory.CompanionTheory.SW.BB
