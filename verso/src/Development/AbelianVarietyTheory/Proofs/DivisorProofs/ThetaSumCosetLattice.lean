import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

noncomputable section
namespace GlobalTheory.ThetaCoset
open GlobalTheory.BoxLattice GlobalTheory.EvAdm
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hi : ∀ i, ∃ c : 𝓞 F, (c : F) = a⁻¹ * ξ i`. Introduce `i`. Take `⟨c, hc⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (a⁻¹ * ξ i) fun v => by`.

Establish `h1` using `h i v`. Establish `e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (ratFin F κ ξ i) v = algebraMap F (v.adicCompletion F) (a⁻¹ * ξ i)`. Rewrite using `[map_mul, map_inv₀]`. Both sides reduce to the same expression. Rewrite `h1` using `[e, HeightOneSpectrum.mem_adicCompletionIntegers]`.

Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']` and apply the resulting hypothesis. Conclude with `⟨c, hc⟩`. Use `choose b hb using hi`. Use `⟨b, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hb i, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]`.

Introduce and unpack `⟨b, rfl⟩ i v`. Establish `e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (ratFin F κ (fun i => a * (b i : F)) i) v = algebraMap F (v.adicCompletion F) ((b i : 𝓞 F) : F)`. Establish `e2 : (ratFin F κ (fun i => a * (b i : F)) i) v = algebraMap F (v.adicCompletion F) (a * (b i : F))` using `rfl`. Rewrite using `[e2, map_mul, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 ha), one_mul]`. Rewrite using `[e, HeightOneSpectrum.mem_adicCompletionIntegers]`.

Use `show Valued.v ((((b i : 𝓞 F) : F)) : v.adicCompletion F) ≤ 1`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `v.valuation_le_one _`.
-/
theorem ratFin_mem_scaledInt_iff {a : F} (ha : a ≠ 0) (ξ : κ → F) :
    ratFin F κ ξ ∈ scaledInt F κ a ↔ ∃ b : κ → 𝓞 F, ξ = fun i => a * (b i : F) := by
  constructor
  · intro h
    have hi : ∀ i, ∃ c : 𝓞 F, (c : F) = a⁻¹ * ξ i := by
      intro i
      obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (a⁻¹ * ξ i) fun v => by
        have h1 := h i v
        have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (ratFin F κ ξ i) v =
            algebraMap F (v.adicCompletion F) (a⁻¹ * ξ i) := by
          rw [map_mul, map_inv₀]; rfl
        rw [e, HeightOneSpectrum.mem_adicCompletionIntegers] at h1
        rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact ⟨c, hc⟩
    choose b hb using hi
    refine ⟨b, funext fun i => ?_⟩
    rw [hb i, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · rintro ⟨b, rfl⟩ i v
    have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (ratFin F κ (fun i => a * (b i : F)) i) v =
        algebraMap F (v.adicCompletion F) ((b i : 𝓞 F) : F) := by
      have e2 : (ratFin F κ (fun i => a * (b i : F)) i) v = algebraMap F (v.adicCompletion F) (a * (b i : F)) := rfl
      rw [e2, map_mul, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 ha), one_mul]
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((((b i : 𝓞 F) : F)) : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one _

/- English proof (translation)
Use `set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator {y | y - r ∈ scaledInt F κ a} fun _ => (1 : ℂ)`. Establish `hterm : ∀ ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = f (ratInf F κ ξ) * g (ratFin F κ ξ)`. Introduce `ξ`. Simplify using `only [pureA]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Conclude with `(InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm`. Establish `hmem : ∀ ξ : κ → F, ratFin F κ ξ - r ∈ scaledInt F κ a ↔ ∃ b : κ → 𝓞 F, ξ = ρ + fun i => a * (b i : F)`. Introduce `ξ`. Establish `e : ratFin F κ ξ - r = ratFin F κ (ξ - ρ) + (ratFin F κ ρ - r)`.

Use function extensionality and compare the values at `i`. Simplify using `[ratFin]`. Rewrite using `[e, AddSubgroup.add_mem_cancel_right _ hρ, ratFin_mem_scaledInt_iff ha]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩; exact ⟨b, by rw [← hb]; abel⟩`.

Introduce and unpack `⟨b, hb⟩; exact ⟨b, by rw [hb]; abel⟩`. Use `set e1 : (κ → 𝓞 F) → (κ → F) := fun b => ρ + fun i => a * (b i : F) with he1`. Establish `hinj1 : Function.Injective e1`. Introduce `b b' h`. Use function extensionality and compare the values at `i`.

Establish `h1` using `congrFun h i`. Simplify using `only [he1, Pi.add_apply, add_right_inj] at h1`. Conclude with `RingOfIntegers.coe_injective (mul_left_cancel₀ ha h1)`. Establish `hg1 : ∀ b, g (ratFin F κ (e1 b)) = 1`. Introduce `b`.

Simplify using `only [g]`. Rewrite using `[Set.indicator_of_mem]`. Conclude with `(hmem _).2 ⟨b, rfl⟩`. Establish `hL : thetaSum F (pureA F f g) = ∑' b : κ → 𝓞 F, f (ratInf F κ (e1 b))`. Rewrite using `[thetaSum, ← hinj1.tsum_eq]`.

Use `tsum_congr fun b => ?_` and prove the remaining obligations. Rewrite using `[hterm, hg1, mul_one]`. Introduce `ξ hξ`. Rewrite `hξ` using `[Function.mem_support, hterm]`. Assume the negation of the conclusion as `hn`.

Apply `hξ` to reduce the goal to its premises. Establish `: g (ratFin F κ ξ) = 0`. Simplify using `only [g]`. Rewrite using `[Set.indicator_of_notMem]`. Introduce `hm`.

Take `⟨b, hb⟩` from `(hmem ξ).1 hm`. Conclude with `hn ⟨b, hb.symm⟩`. Rewrite using `[this, mul_zero]`. Use `set e2 : (κ → 𝓞 F) → boxLat F κ a := fun b => ⟨ratInf F κ fun i => a * (b i : F), b, rfl⟩ with he2`. Establish `hinj2 : Function.Injective e2`.

Introduce `b b' h`. Establish `h1` using `congrArg Subtype.val h`. Use function extensionality and compare the values at `i`. Establish `h2` using `congrFun h1 i`. Simplify using `only [he2, ratInf] at h2`.

Conclude with `RingOfIntegers.coe_injective (mul_left_cancel₀ ha (mixedEmbedding_injective F h2))`. Establish `hsurj2 : Function.Surjective e2`. Introduce and unpack `⟨l, b, rfl⟩`. Conclude with `⟨b, rfl⟩`. Rewrite using `[hL, ← (Equiv.ofBijective e2 ⟨hinj2, hsurj2⟩).tsum_eq]`.

Use `tsum_congr fun b => ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[he1, he2, ratInf, map_add]`.
-/
theorem thetaSum_coset (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (ha : a ≠ 0)
    (r : κ → FiniteAdeleRing (𝓞 F) F) (ρ : κ → F) (hρ : ratFin F κ ρ - r ∈ scaledInt F κ a)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    thetaSum F (pureA F f (Set.indicator {y | y - r ∈ scaledInt F κ a} fun _ => (1 : ℂ))) =
      ∑' l : boxLat F κ a, f (ratInf F κ ρ + l) := by
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator {y | y - r ∈ scaledInt F κ a} fun _ => (1 : ℂ)

  have hterm : ∀ ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) =
      f (ratInf F κ ξ) * g (ratFin F κ ξ) := by
    intro ξ
    simp only [pureA]
    congr 2
    funext i
    exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm

  have hmem : ∀ ξ : κ → F, ratFin F κ ξ - r ∈ scaledInt F κ a ↔ ∃ b : κ → 𝓞 F, ξ = ρ + fun i => a * (b i : F) := by
    intro ξ
    have e : ratFin F κ ξ - r = ratFin F κ (ξ - ρ) + (ratFin F κ ρ - r) := by
      funext i; simp [ratFin]
    rw [e, AddSubgroup.add_mem_cancel_right _ hρ, ratFin_mem_scaledInt_iff ha]
    constructor
    · rintro ⟨b, hb⟩; exact ⟨b, by rw [← hb]; abel⟩
    · rintro ⟨b, hb⟩; exact ⟨b, by rw [hb]; abel⟩
  set e1 : (κ → 𝓞 F) → (κ → F) := fun b => ρ + fun i => a * (b i : F) with he1
  have hinj1 : Function.Injective e1 := by
    intro b b' h
    funext i
    have h1 := congrFun h i
    simp only [he1, Pi.add_apply, add_right_inj] at h1
    exact RingOfIntegers.coe_injective (mul_left_cancel₀ ha h1)
  have hg1 : ∀ b, g (ratFin F κ (e1 b)) = 1 := by
    intro b
    simp only [g]
    rw [Set.indicator_of_mem]
    exact (hmem _).2 ⟨b, rfl⟩
  have hL : thetaSum F (pureA F f g) = ∑' b : κ → 𝓞 F, f (ratInf F κ (e1 b)) := by
    rw [thetaSum, ← hinj1.tsum_eq]
    · refine tsum_congr fun b => ?_
      rw [hterm, hg1, mul_one]
    · intro ξ hξ
      rw [Function.mem_support, hterm] at hξ
      by_contra hn
      apply hξ
      have : g (ratFin F κ ξ) = 0 := by
        simp only [g]
        rw [Set.indicator_of_notMem]
        intro hm
        obtain ⟨b, hb⟩ := (hmem ξ).1 hm
        exact hn ⟨b, hb.symm⟩
      rw [this, mul_zero]

  set e2 : (κ → 𝓞 F) → boxLat F κ a := fun b => ⟨ratInf F κ fun i => a * (b i : F), b, rfl⟩ with he2
  have hinj2 : Function.Injective e2 := by
    intro b b' h
    have h1 := congrArg Subtype.val h
    funext i
    have h2 := congrFun h1 i
    simp only [he2, ratInf] at h2
    exact RingOfIntegers.coe_injective (mul_left_cancel₀ ha (mixedEmbedding_injective F h2))
  have hsurj2 : Function.Surjective e2 := by
    rintro ⟨l, b, rfl⟩
    exact ⟨b, rfl⟩
  rw [hL, ← (Equiv.ofBijective e2 ⟨hinj2, hsurj2⟩).tsum_eq]
  refine tsum_congr fun b => ?_
  congr 1
  funext i
  simp [he1, he2, ratInf, map_add]

end GlobalTheory.ThetaCoset
