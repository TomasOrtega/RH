import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbOverSumInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeEmbeddingEqTop

noncomputable section

open Matrix NumberField
open scoped TensorProduct Classical

namespace GlobalTheory.LKTrip.HTGroup

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top`. Consider the case `exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top`. Consider the case `(apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top ..)`.
-/
theorem span_real_embedding_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | (apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top ..)

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Simplify using `only [psiR, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  simp only [psiR, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
  rfl

/- English proof (translation)
Set `Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ)` to `Pi.algHom ℝ _ fun v => G.psiR v`. Establish `hΨ : ∀ x, Ψ x = fun v => G.psiR v x` using `fun x => rfl`. Use `set S := Ψ.range with hS`. Establish `hsc : ∀ a : G.F, Ψ (1 ⊗ₜ algebraMap G.F G.C a) = fun v : InfinitePlace G.F => Matrix.scalar (Fin G.n) (v.embedding a)`. Introduce `a`.

Use function extensionality and compare the values at `v`. Rewrite using `[hΨ]`. Simplify using `only`. Rewrite using `[psiR_tmul, one_smul, G.psi_F]`. Set `sc : (InfinitePlace G.F → ℂ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ)` to `{ toFun := fun c v => Matrix.scalar (Fin G.n) (c v) map_add' := fun c d => by funext v; simp map_smul' := fun r c => by`.

Use function extensionality and compare the values at `v`. Simplify using `only [Pi.smul_apply, RingHom.id_apply]`. Rewrite using `[Matrix.scalar_apply, Matrix.scalar_apply]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.diagonal_apply, h] }`.

Establish `hscS : ∀ c : InfinitePlace G.F → ℂ, sc c ∈ S`. Establish `htop` using `span_real_embedding_places G.F`. Establish `hle : Submodule.span ℝ (Set.range fun (a : G.F) (v : InfinitePlace G.F) => v.embedding a) ≤ (Subalgebra.toSubmodule S).comap sc`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Conclude with `Submodule.mem_comap.2 ((AlgHom.mem_range _).2 ⟨_, hsc a⟩)`. Introduce `c`. Conclude with `hle (htop ▸ Submodule.mem_top)`. Establish `hsingle : ∀ (v₁ : InfinitePlace G.F) (m : Matrix (Fin G.n) (Fin G.n) ℂ), Pi.single v₁ m ∈ S`. Introduce `v₁ m`.

Establish `hspan` using `GlobalTheory.UPel.HT.RealRepBij.span_range_eq_top v₁.embedding (G.psi v₁) G.rankC (G.psi_F v₁)`. Establish `hm : m ∈ Submodule.span ℂ (Set.range (G.psi v₁))` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`.

Establish `: (Pi.single v₁ (G.psi v₁ b) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) = sc (Pi.single v₁ 1) * Ψ (1 ⊗ₜ b)`. Use function extensionality and compare the values at `v`. Rewrite using `[hΨ]`. Distinguish the cases in `h : v = v₁`. Substitute `h` using the available equality.

Simplify using `[sc, psiR_tmul]`. Simplify using `[sc, h, psiR_tmul]`. Rewrite using `[this]`. Conclude with `S.mul_mem (hscS _) ((AlgHom.mem_range _).2 ⟨_, rfl⟩)`. Consider the case `zero => simpa using S.zero_mem`.

Consider the case `add x y _ _ hx hy => rw [Pi.single_add]`. Conclude with `S.add_mem hx hy`. Consider the case `smul z x _ hx`. Establish `: (Pi.single v₁ (z • x) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) = sc (Pi.single v₁ z) * Pi.single v₁ x`. Use function extensionality and compare the values at `v`.

Distinguish the cases in `h : v = v₁`. Substitute `h` using the available equality. Simplify using `[sc, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]`. Simplify using `[sc, h]`. Rewrite using `[this]`.

Conclude with `S.mul_mem (hscS _) hx`. Establish `hsurj : Function.Surjective Ψ`. Introduce `y`. Establish `: y ∈ S`. Rewrite using `[← Finset.univ_sum_single y]`.

Conclude with `Subalgebra.sum_mem _ fun v _ => hsingle v (y v)`. Conclude with `(AlgHom.mem_range _).1 this`. Establish `hc : 2 * Fintype.card (InfinitePlace G.F) = Module.finrank ℚ G.F`. Rewrite using `[← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero G.F]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hfin : Module.finrank ℝ (ℝ ⊗[ℚ] G.C) = Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ)`. Rewrite using `[Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Rewrite using `[← hc]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := Ψ.toLinearMap)).2 hsurj, hsurj⟩`.
-/
theorem psiR_pi_bijective (G : HTGroup p) :
    Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  let Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := Pi.algHom ℝ _ fun v => G.psiR v
  have hΨ : ∀ x, Ψ x = fun v => G.psiR v x := fun x => rfl
  set S := Ψ.range with hS
  have hsc : ∀ a : G.F, Ψ (1 ⊗ₜ algebraMap G.F G.C a) =
      fun v : InfinitePlace G.F => Matrix.scalar (Fin G.n) (v.embedding a) := by
    intro a; funext v; rw [hΨ]; dsimp only; rw [psiR_tmul, one_smul, G.psi_F]
  let sc : (InfinitePlace G.F → ℂ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    { toFun := fun c v => Matrix.scalar (Fin G.n) (c v)
      map_add' := fun c d => by funext v; simp
      map_smul' := fun r c => by
        funext v
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Matrix.scalar_apply, Matrix.scalar_apply]
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, h] }
  have hscS : ∀ c : InfinitePlace G.F → ℂ, sc c ∈ S := by
    have htop := span_real_embedding_places G.F
    have hle : Submodule.span ℝ (Set.range fun (a : G.F) (v : InfinitePlace G.F) => v.embedding a) ≤
        (Subalgebra.toSubmodule S).comap sc := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_comap.2 ((AlgHom.mem_range _).2 ⟨_, hsc a⟩)
    intro c
    exact hle (htop ▸ Submodule.mem_top)
  have hsingle : ∀ (v₁ : InfinitePlace G.F) (m : Matrix (Fin G.n) (Fin G.n) ℂ), Pi.single v₁ m ∈ S := by
    intro v₁ m
    have hspan := GlobalTheory.UPel.HT.RealRepBij.span_range_eq_top v₁.embedding (G.psi v₁) G.rankC (G.psi_F v₁)
    have hm : m ∈ Submodule.span ℂ (Set.range (G.psi v₁)) := hspan ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have : (Pi.single v₁ (G.psi v₁ b) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ 1) * Ψ (1 ⊗ₜ b) := by
        funext v
        rw [hΨ]
        by_cases h : v = v₁
        · subst h; simp [sc, psiR_tmul]
        · simp [sc, h, psiR_tmul]
      rw [this]; exact S.mul_mem (hscS _) ((AlgHom.mem_range _).2 ⟨_, rfl⟩)
    | zero => simpa using S.zero_mem
    | add x y _ _ hx hy => rw [Pi.single_add]; exact S.add_mem hx hy
    | smul z x _ hx =>
      have : (Pi.single v₁ (z • x) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ z) * Pi.single v₁ x := by
        funext v
        by_cases h : v = v₁
        · subst h; simp [sc, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
        · simp [sc, h]
      rw [this]; exact S.mul_mem (hscS _) hx
  have hsurj : Function.Surjective Ψ := by
    intro y
    have : y ∈ S := by
      rw [← Finset.univ_sum_single y]
      exact Subalgebra.sum_mem _ fun v _ => hsingle v (y v)
    exact (AlgHom.mem_range _).1 this
  have hc : 2 * Fintype.card (InfinitePlace G.F) = Module.finrank ℚ G.F := by
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero G.F]
    ring
  have hfin : Module.finrank ℝ (ℝ ⊗[ℚ] G.C) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    rw [← hc]; ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := Ψ.toLinearMap)).2 hsurj, hsurj⟩

end GlobalTheory.LKTrip.HTGroup
