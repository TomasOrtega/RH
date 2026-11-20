import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartzStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RelevantSpaceNonzero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, ι, hι, h2⟩`. Conclude with `⟨h1, ι, ⟨hι.bij, hι.trans, hι.mult⟩, h2⟩`. Introduce and unpack `⟨h1, ι, hι, h2⟩`.

Conclude with `⟨h1, ι, ⟨hι.bij, hι.trans, hι.mult⟩, h2⟩`.
-/
theorem soLoc_reS {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    (t : E →ₐ[F] Fv F v) :
    (⟨M.co, M.vac, M.μ, M.dom⟩ : Model σ (reS X Y) (reS W Z)).SoLoc ψ t = M.SoLoc ψ t := by
  ext φ
  constructor
  · rintro ⟨h1, ι, hι, h2⟩
    exact ⟨h1, ι, ⟨hι.bij, hι.trans, hι.mult⟩, h2⟩
  · rintro ⟨h1, ι, hι, h2⟩
    exact ⟨h1, ι, ⟨hι.bij, hι.trans, hι.mult⟩, h2⟩

/- English proof (translation)
Unfold `Model.So`. Rewrite using `[soLoc_reS]`.
-/
theorem so_reS {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    (t : E →ₐ[F] Fv F v) :
    (⟨M.co, M.vac, M.μ, M.dom⟩ : Model σ (reS X Y) (reS W Z)).So ψ t = M.So ψ t := by
  unfold Model.So
  rw [soLoc_reS]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pure_eq_pureA {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = pureA F f (fun z => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)) := rfl

/- English proof (translation)
The claim follows from `so_reS G.M' ψ t`.
-/
theorem so_reG {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a'))
    (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.So ψ t = G.M'.So ψ t :=
  so_reS G.M' ψ t

end GlobalTheory.RelevantSpaceNonzero

namespace GlobalTheory.RelevantSpaceNonzero

open GlobalTheory.ThKSoCont

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' V V' W hT _ ⟨Φ₀, hΦ₀, hI₀⟩`. Establish `hSo : Φ₀ ∈ G.M'.So B.ψ B.τ₁`. Use `hΦ₀.2` as an intermediate fact. Rewrite `this` using `[so_reG]`. Then use the resulting hypothesis. Establish `hI : G.M'.I om' Φ₀ ≠ 0` using `hI₀`.

Choose the witnesses or unpack the hypotheses as in `⟨h, hh⟩ : ∃ h, G.M'.I om' Φ₀ h ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hI (funext hc)`. Establish `hPair` using `GlobalTheory.ThK.Inhab.pairV' hT`.

Establish `hstd` using `hT.geo.hM'.std`. Take `⟨m, c, g, hg⟩` from `Submodule.mem_span_set'.1 hSo`. Establish `hgen : ∀ j, ∃ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in cofinite, φ v = G.M'.vac v) ∧ φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ ∧ (g j : (Fin a' × Fin (a + a') → AF F) → ℂ) = GlobalTheory.IndefiniteRowSideFullHeck …` using `fun j => (g j).2`. Use `choose f φ hφSB hφvac hφSo hφeq using hgen`. Set `A : Fin m → (Fin a' × Fin (a + a') → Af F) → ℂ` to `fun j z => ∏ᶠ v, φ j v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)`.

Establish `hA : ∀ j, A j ∈ SB (Fin a' × Fin (a + a') → Af F)` using `fun j => GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ (φ j) (hφSB j) (((hφvac j).and hstd).mono fun v hv => hv.1.trans hv.2)`. Establish `hpure : ∀ j (u : SInf F (Fin a' × Fin (a + a'))), pureA F u (A j) ∈ G.M'.So B.ψ B.τ₁` using `fun j u => Submodule.subset_span ⟨u, φ j, hφSB j, hφvac j, hφSo j, (pure_eq_pureA u (φ j)).symm⟩`. Establish `hpol : ∀ j (u : SInf F (Fin a' × Fin (a + a'))), u ∈ G.M'.Pol B.ψ B.emb → pureA F u (A j) ∈ PolData B G.M'` using `fun j u hu => Submodule.subset_span ⟨u, hu, φ j, hφSB j, hφvac j, (pure_eq_pureA u (φ j)).symm⟩`. Establish `hΦ₀ : Φ₀ = ∑ j, pureA F ((c j • f j : SInf F _) : _ → ℂ) (A j)`. Rewrite using `[← hg]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hφeq j, pure_eq_pureA]`. Use function extensionality and compare the values at `x`. Simplify using `only [pureA, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdense` using `GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair`. Establish `happrox : ∀ j, ∃ u : ℕ → SInf F (Fin a' × Fin (a + a')), (∀ k, u k ∈ G.M'.Pol B.ψ B.emb) ∧ Tendsto u atTop (𝓝 (c j • f j))` using `fun j => mem_closure_iff_seq_limit.1 (hdense (c j • f j))`. Use `choose u hu hlim using happrox`. Set `w : ℕ → Fin m → SInf F (Fin a' × Fin (a + a'))` to `fun k j => u j k`. Establish `hcont` using `soCont hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair m A (fun j => c j • f j) w (fun j => ⟨hA j, hlim j⟩) (fun k => Submodule.sum_mem _ fun j _ => hpure j (w k j)) (Submodule.sum_mem _ fun j _ => hpure j _) h`.

Rewrite `hcont` using `[← hΦ₀]`. Take `⟨k, hk⟩` from `(hcont.eventually_ne hh).exists`. Use `⟨∑ j, pureA F (w k j : _ → ℂ) (A j), ⟨Submodule.sum_mem _ fun j _ => hpol j _ (hu j k), Submodule.sum_mem _ fun j _ => hpure j _⟩, fun h0 => hk ?_⟩` and prove the remaining obligations. Rewrite using `[h0]`. Both sides reduce to the same expression.
-/
theorem nonZero_reG (hP : KP) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (V : Spc F E a) (V' : Spc F E a')
    (W : Spc F E (a + a')), IsTriple B G X om om' → IsTriple B (reG G V V' W) X om om' →
    (∃ Φ' ∈ PolData B (reG G V V' W).M' ⊓ (reG G V V' W).M'.So B.ψ B.τ₁, (reG G V V' W).M'.I om' Φ' ≠ 0) →
    ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' V V' W hT _ ⟨Φ₀, hΦ₀, hI₀⟩
  have hSo : Φ₀ ∈ G.M'.So B.ψ B.τ₁ := by
    have := hΦ₀.2
    rwa [so_reG] at this
  have hI : G.M'.I om' Φ₀ ≠ 0 := hI₀
  obtain ⟨h, hh⟩ : ∃ h, G.M'.I om' Φ₀ h ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hI (funext hc)
  have hPair := GlobalTheory.ThK.Inhab.pairV' hT
  have hstd := hT.geo.hM'.std

  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 hSo
  have hgen : ∀ j, ∃ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in cofinite, φ v = G.M'.vac v) ∧ φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ ∧
        (g j : (Fin a' × Fin (a + a') → AF F) → ℂ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := fun j => (g j).2
  choose f φ hφSB hφvac hφSo hφeq using hgen
  let A : Fin m → (Fin a' × Fin (a + a') → Af F) → ℂ :=
    fun j z => ∏ᶠ v, φ j v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)
  have hA : ∀ j, A j ∈ SB (Fin a' × Fin (a + a') → Af F) := fun j =>
    GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ (φ j) (hφSB j)
      (((hφvac j).and hstd).mono fun v hv => hv.1.trans hv.2)
  have hpure : ∀ j (u : SInf F (Fin a' × Fin (a + a'))),
      pureA F u (A j) ∈ G.M'.So B.ψ B.τ₁ := fun j u =>
    Submodule.subset_span ⟨u, φ j, hφSB j, hφvac j, hφSo j, (pure_eq_pureA u (φ j)).symm⟩
  have hpol : ∀ j (u : SInf F (Fin a' × Fin (a + a'))), u ∈ G.M'.Pol B.ψ B.emb →
      pureA F u (A j) ∈ PolData B G.M' := fun j u hu =>
    Submodule.subset_span ⟨u, hu, φ j, hφSB j, hφvac j, (pure_eq_pureA u (φ j)).symm⟩
  have hΦ₀ : Φ₀ = ∑ j, pureA F ((c j • f j : SInf F _) : _ → ℂ) (A j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hφeq j, pure_eq_pureA]
    funext x
    simp only [pureA, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
    ring

  have hdense := GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair
  have happrox : ∀ j, ∃ u : ℕ → SInf F (Fin a' × Fin (a + a')), (∀ k, u k ∈ G.M'.Pol B.ψ B.emb) ∧
      Tendsto u atTop (𝓝 (c j • f j)) := fun j =>
    mem_closure_iff_seq_limit.1 (hdense (c j • f j))
  choose u hu hlim using happrox
  let w : ℕ → Fin m → SInf F (Fin a' × Fin (a + a')) := fun k j => u j k
  have hcont := soCont hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair m A
    (fun j => c j • f j) w (fun j => ⟨hA j, hlim j⟩)
    (fun k => Submodule.sum_mem _ fun j _ => hpure j (w k j))
    (Submodule.sum_mem _ fun j _ => hpure j _) h
  rw [← hΦ₀] at hcont
  obtain ⟨k, hk⟩ := (hcont.eventually_ne hh).exists
  refine ⟨∑ j, pureA F (w k j : _ → ℂ) (A j), ⟨Submodule.sum_mem _ fun j _ => hpol j _ (hu j k),
    Submodule.sum_mem _ fun j _ => hpure j _⟩, fun h0 => hk ?_⟩
  rw [h0]
  rfl

end GlobalTheory.RelevantSpaceNonzero
