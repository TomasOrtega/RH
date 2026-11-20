import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeCharacterTrivialStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
namespace GlobalTheory.SchrCharPure

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ a ha b hb f f' hf'`. Use function extensionality and compare the values at `x`. Simplify using `only [schr, pureA, add_zero, zero_dotProduct, mul_zero]`. Rewrite using `[hf']`. Distinguish the cases in `hz : (fun i => (x i).2) ∈ GlobalTheory.EvAdm.scaledInt F κ a`.

Rewrite using `[Set.indicator_of_mem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz] set u : AF F := x ⬝ᵥ fun i => algebraMap F (AF F) (b i) with hu`. Establish `hsplit : u = (show AF F from (u.1, 0)) + (show AF F from (0, u.2))` using `by show u = ((u.1 + 0, 0 + u.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)`. Rewrite using `[add_zero, zero_add]`. Both sides reduce to the same expression. Establish `hu2 : u.2 = ∑ i, (x i).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)`.

Establish `e : u.2 = (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u` using `rfl`. Rewrite using `[e, hu, dotProduct]`. Conclude with `(map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans (Finset.sum_congr rfl fun i _ => rfl)`. Establish `hu1 : u.1 = ∑ i, (x i).1 * algebraMap F (InfiniteAdeleRing F) (b i)`. Establish `e : u.1 = (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u` using `rfl`.

Rewrite using `[e, hu, dotProduct]`. Conclude with `(map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans (Finset.sum_congr rfl fun i _ => rfl)`. Establish `hfin : ψ (show AF F from (0, u.2)) = 1`. Use `GlobalTheory.T.scaled_lattice_character_trivial F ψ hψ κ a ha b hb _ hz` as an intermediate fact. Rewrite `this` using `[← hu2]`.

Conclude with `this`. Establish `hAt : At (evI F) (show AF F from (u.1, 0))`. Introduce `w hw`. Establish `h1 : w.1 = 0`. Establish `: InfiniteAdeleRing.ringEquiv_mixedSpace F w.1 = 0` using `hw`.

Conclude with `(map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this`. Use `show ((w.1 * u.1, w.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)`. Rewrite using `[h1, zero_mul, mul_zero]`. Establish `hinf` using `hψ.2.2 _ hAt`. Establish `hev : evI F (show AF F from (u.1, 0)) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * mixedEmbedding F (b i)` using `by show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = _`.

Rewrite using `[hu1, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_mul]`. Rewrite using `[hsplit, AddChar.map_add_eq_mul, hfin, hinf, hev]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Set.indicator_of_notMem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]`. Simplify using the standard rewrite rules.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
      schr ψ (0, fun i => algebraMap F (AF F) (b i))
          (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)))) =
        pureA F f' ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))) := by
  intro F _ _ ψ hψ κ _ a ha b hb f f' hf'
  funext x
  simp only [schr, pureA, add_zero, zero_dotProduct, mul_zero]
  rw [hf']
  by_cases hz : (fun i => (x i).2) ∈ GlobalTheory.EvAdm.scaledInt F κ a
  · rw [Set.indicator_of_mem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    set u : AF F := x ⬝ᵥ fun i => algebraMap F (AF F) (b i) with hu
    have hsplit : u = (show AF F from (u.1, 0)) + (show AF F from (0, u.2)) := by
      show u = ((u.1 + 0, 0 + u.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
      rw [add_zero, zero_add]
      rfl
    have hu2 : u.2 = ∑ i, (x i).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i) := by
      have e : u.2 = (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hu1 : u.1 = ∑ i, (x i).1 * algebraMap F (InfiniteAdeleRing F) (b i) := by
      have e : u.1 = (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hfin : ψ (show AF F from (0, u.2)) = 1 := by
      have := GlobalTheory.T.scaled_lattice_character_trivial F ψ hψ κ a ha b hb _ hz
      rw [← hu2] at this
      exact this
    have hAt : At (evI F) (show AF F from (u.1, 0)) := by
      intro w hw
      have h1 : w.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F w.1 = 0 := hw
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
      show ((w.1 * u.1, w.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
      rw [h1, zero_mul, mul_zero]
    have hinf := hψ.2.2 _ hAt
    have hev : evI F (show AF F from (u.1, 0)) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * mixedEmbedding F (b i) := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = _
      rw [hu1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_mul]
    rw [hsplit, AddChar.map_add_eq_mul, hfin, hinf, hev]
    ring
  · rw [Set.indicator_of_notMem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    simp

end GlobalTheory.SchrCharPure
