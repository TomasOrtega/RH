import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImgSet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]`.
-/
theorem smul_pure {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    c • pure f φ = pure (c • f) φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun j => ⟨(h.1 j).1, (h.1 j).2.1, fun v hv => (h.1 j).2.2 v fun hv' => hv (hT hv')⟩, h.2⟩`.
-/
theorem DecOn.mono {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {T T' : Finset (Pl F)}
    {Ψ : (Fin n × Fin d → AF F) → ℂ} {m : ℕ} {f : Fin m → SInf F (Fin n × Fin d)}
    {φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (hT : T ⊆ T') (h : DecOn B M T Ψ m f φ) :
    DecOn B M T' Ψ m f φ :=
  ⟨fun j => ⟨(h.1 j).1, (h.1 j).2.1, fun v hv => (h.1 j).2.2 v fun hv' => hv (hT hv')⟩, h.2⟩

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, φ, hφ, hcof, rfl⟩` from `hx`. Establish `hfin : {v | ¬ φ v = M.vac v}.Finite` using `Filter.eventually_cofinite.1 hcof`. Use `⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hv => ?_⟩, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hv (hfin.mem_toFinset.2 h)`. Simplify using the standard rewrite rules. Consider the case `zero`. Conclude with `⟨∅, 0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨T, m, f, φ, h1, rfl⟩` from `hx`. Take `⟨T', m', f', φ', h1', rfl⟩` from `hy`. Use `⟨T ∪ T', m + m', Fin.append f f', Fin.append φ φ', fun j => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations.

Simplify using `only [Fin.append_left]`. Conclude with `⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩`. Simplify using `only [Fin.append_right]`. Conclude with `⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩`. Rewrite using `[Fin.sum_univ_add]`.

Simplify using `only [Fin.append_left, Fin.append_right]`. Consider the case `smul c x _ hx`. Take `⟨T, m, f, φ, h1, rfl⟩` from `hx`. Use `⟨T, m, fun j => c • f j, φ, fun j => ⟨Submodule.smul_mem _ c (h1 j).1, (h1 j).2.1, (h1 j).2.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => smul_pure c (f j) (φ j)`.
-/
theorem exists_decOn_some {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ PolData B M) :
    ∃ (T₀ : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), DecOn B M T₀ Φ m f φ := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hcof, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hcof
    refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hv => ?_⟩, ?_⟩
    · by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    · simp
  | zero =>
    exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    obtain ⟨T', m', f', φ', h1', rfl⟩ := hy
    refine ⟨T ∪ T', m + m', Fin.append f f', Fin.append φ φ', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun h => hv (Finset.mem_union_left _ h)⟩
      · simp only [Fin.append_right]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v fun h => hv (Finset.mem_union_right _ h)⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨T, m, f, φ, h1, rfl⟩ := hx
    refine ⟨T, m, fun j => c • f j, φ, fun j => ⟨Submodule.smul_mem _ c (h1 j).1, (h1 j).2.1, (h1 j).2.2⟩, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_pure c (f j) (φ j)

end GlobalTheory.ThK.CycGen

end
