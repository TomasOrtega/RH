import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

namespace GlobalTheory.ThK.LemF.QuotInv.AdSpan

/- English proof (translation)
Use `choose s t u hs using fun i : Fin n => h (Pi.single i 1)`. Use `⟨∑ i, w i * f (s i), ∑ i, w i * f (t i), ∑ i, w i • (fun j => f (u i j)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `r`. Establish `h1 : ∀ i, f ((Pi.single i 1 : Fin n → E) r) = f (s i) * f (x r) + (∑ j, f (ι r j) * f (u i j)) + f (t i) * f (y r)`. Introduce `i`.

Rewrite using `[hs i]`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`. Establish `h2 : w r = ∑ i, w i * f ((Pi.single i 1 : Fin n → E) r)`. Rewrite using `[Finset.sum_eq_single r]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne (Ne.symm hb)]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Simplify using `only [h1, mul_add, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Finset.mul_sum, mul_assoc]`.

Rewrite using `[Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i j => w i * (f (ι r j) * f (u i j)))]`. Use `congr 2`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem span_map {E R : Type} [CommRing E] [CommRing R] (f : E →+* R) {n n₁ : ℕ} (x y : Fin n → E)
    (ι : Matrix (Fin n) (Fin n₁) E)
    (h : ∀ e : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), e = s • x + ι *ᵥ u + t • y) (w : Fin n → R) :
    ∃ (α β : R) (z : Fin n₁ → R), w = α • (fun i => f (x i)) + ι.map f *ᵥ z + β • (fun i => f (y i)) := by
  choose s t u hs using fun i : Fin n => h (Pi.single i 1)
  refine ⟨∑ i, w i * f (s i), ∑ i, w i * f (t i), ∑ i, w i • (fun j => f (u i j)), ?_⟩
  funext r
  have h1 : ∀ i, f ((Pi.single i 1 : Fin n → E) r)
      = f (s i) * f (x r) + (∑ j, f (ι r j) * f (u i j)) + f (t i) * f (y r) := by
    intro i
    rw [hs i]
    simp [Matrix.mulVec, dotProduct, map_sum]
  have h2 : w r = ∑ i, w i * f ((Pi.single i 1 : Fin n → E) r) := by
    rw [Finset.sum_eq_single r]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · simp
  rw [h2]
  simp only [h1, mul_add, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i j => w i * (f (ι r j) * f (u i j)))]
  congr 2
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ hL hH w`. Use `span_map (inclR (F := F) (AF F)) H.x H.y H.ι (fun e => ?_) w` and prove the remaining obligations. Establish `he : e ∈ Submodule.span E (Y.L : Set (Fin n → E))`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s, t, u, -, -, -, h⟩` from `hH.split z hz`. Conclude with `⟨s, t, u, h⟩`. Consider the case `zero => exact ⟨0, 0, 0, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨s, t, u, rfl⟩` from `ha`. Take `⟨s', t', u', rfl⟩` from `hb`. Use `⟨s + s', t + t', u + u', ?_⟩` and prove the remaining obligations. Rewrite using `[add_smul, add_smul, Matrix.mulVec_add]`.

Normalize the expressions using the abelian group laws. Consider the case `smul c a _ ha`. Take `⟨s, t, u, rfl⟩` from `ha`. Use `⟨c * s, c * t, c • u, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, smul_add, Matrix.mulVec_smul, mul_smul, mul_smul]`.
-/
theorem adelic_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ : ℕ), Y.L.IsLattice E →
    H.IsAdapted σ B Y Y₁ i₀ i₁ → ∀ w : Fin n → AE F E, ∃ (α β : AE F E) (z : Fin n₁ → AE F E),
      w = α • incV F H.x + incM F H.ι *ᵥ z + β • incV F H.y := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ hL hH w
  refine span_map (inclR (F := F) (AF F)) H.x H.y H.ι (fun e => ?_) w
  have he : e ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction he using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, u, rfl⟩ := ha
    obtain ⟨s', t', u', rfl⟩ := hb
    refine ⟨s + s', t + t', u + u', ?_⟩
    rw [add_smul, add_smul, Matrix.mulVec_add]
    abel
  | smul c a _ ha =>
    obtain ⟨s, t, u, rfl⟩ := ha
    refine ⟨c * s, c * t, c • u, ?_⟩
    rw [smul_add, smul_add, Matrix.mulVec_smul, mul_smul, mul_smul]

end GlobalTheory.ThK.LemF.QuotInv.AdSpan
