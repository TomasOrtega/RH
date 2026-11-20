import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifLift

/- English proof (translation)
Introduce `p`. Use `⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩` and prove the remaining obligations. Use `PrimeSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.fst ∈ (⊥ : Ideal K) ↔ x ∈ PrimeSpectrum.asIdeal p`. Rewrite using `[Ideal.mem_bot]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Apply `p.isPrime.mem_of_pow_mem 2` to reduce the goal to its premises. Establish `: x ^ 2 = 0`. Rewrite using `[pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl, TrivSqZeroExt.inr_mul_inr]`.

Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`. Introduce `hx`. Assume the negation of the conclusion as `h0`. Establish `hu : IsUnit x` using `TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)`.

Conclude with `p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)`.
-/
theorem spMap_fst_surjective_sqZero (K : Type) [Field K] (ι : Type) :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal K) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

/- English proof (translation)
Use `set f := spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom with hf`. Establish `hs` using `spMap_fst_surjective_sqZero K ι`. Establish `hr : Set.range w ⊆ Set.range (inc₀ X Z)`. Introduce and unpack `_ ⟨t, rfl⟩`. Take `⟨s, rfl⟩` from `hs t`.

Use `⟨M.σ (z s), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z ≫ M.σ ≫ inc₀ X Z) s = (f ≫ w) s`. Rewrite using `[hw]`. Use `set w₀ := IsOpenImmersion.lift (inc₀ X Z) w hr with hw₀`. Establish `hw₀f : w₀ ≫ inc₀ X Z = w` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `hfw₀ : f ≫ w₀ = z ≫ M.σ`. Rewrite using `[← cancel_mono (inc₀ X Z), Category.assoc, hw₀f, hw, Category.assoc]`. Establish `hzU : ∀ s, M.σ (z s) ∈ U₀ X Z` using `fun s => by`. Use `hz (Set.mem_univ s)` as an intermediate fact. Rewrite `this` using `[M.off_eq]`.

Conclude with `this`. Establish `hU : ⊤ ≤ w₀ ⁻¹ᵁ U₀ X Z`. Introduce `t _`. Take `⟨s, rfl⟩` from `hs t`. Express the relevant statement in the definitionally equal form `(f ≫ w₀) s ∈ U₀ X Z`.

Rewrite using `[hfw₀]`. Conclude with `hzU s`. Take `⟨w', hw', -⟩` from `M.existsUnique_lift w₀ hU`. Establish `hU' : ⊤ ≤ (f ≫ w₀) ⁻¹ᵁ U₀ X Z` using `fun s _ => hU (Set.mem_univ (f s))`. Establish `hfw' : f ≫ w' = z`.

Take `⟨_, -, huniq⟩` from `M.existsUnique_lift (f ≫ w₀) hU'`. Conclude with `(huniq _ (show (f ≫ w') ≫ M.σ = f ≫ w₀ by rw [Category.assoc, hw'])).trans (huniq z hfw₀.symm).symm`. Use `⟨w', ?_, hfw', fun O hO t _ => ?_⟩` and prove the remaining obligations. Rewrite using `[toFlag, ← Category.assoc, hw', hw₀f]`. Take `⟨s, rfl⟩` from `hs t`.

Express the relevant statement in the definitionally equal form `(f ≫ w') s ∈ O`. Rewrite using `[hfw']`. Conclude with `hO (Set.mem_univ s)`.
-/
theorem exists_lift_sqZero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
    (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) {K : Type} [Field K] {ι : Type} (z : Sp K ⟶ M.X)
    (hz : ⊤ ≤ z ⁻¹ᵁ M.off) (w : Sp (TrivSqZeroExt K (ι → K)) ⟶ X.YY)
    (hw : spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w = z ≫ toFlag M) :
    ∃ w' : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, w' ≫ toFlag M = w ∧
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom ≫ w' = z ∧
      ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ w' ⁻¹ᵁ O := by
  set f := spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom with hf
  have hs := spMap_fst_surjective_sqZero K ι
  have hr : Set.range w ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hs t
    refine ⟨M.σ (z s), ?_⟩
    change (z ≫ M.σ ≫ inc₀ X Z) s = (f ≫ w) s
    rw [hw]
  set w₀ := IsOpenImmersion.lift (inc₀ X Z) w hr with hw₀
  have hw₀f : w₀ ≫ inc₀ X Z = w := IsOpenImmersion.lift_fac _ _ _
  have hfw₀ : f ≫ w₀ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw₀f, hw, Category.assoc]
  have hzU : ∀ s, M.σ (z s) ∈ U₀ X Z := fun s => by
    have := hz (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hU : ⊤ ≤ w₀ ⁻¹ᵁ U₀ X Z := by
    intro t _
    obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w₀) s ∈ U₀ X Z
    rw [hfw₀]
    exact hzU s
  obtain ⟨w', hw', -⟩ := M.existsUnique_lift w₀ hU
  have hU' : ⊤ ≤ (f ≫ w₀) ⁻¹ᵁ U₀ X Z := fun s _ => hU (Set.mem_univ (f s))
  have hfw' : f ≫ w' = z := by
    obtain ⟨_, -, huniq⟩ := M.existsUnique_lift (f ≫ w₀) hU'
    exact (huniq _ (show (f ≫ w') ≫ M.σ = f ≫ w₀ by rw [Category.assoc, hw'])).trans (huniq z hfw₀.symm).symm
  refine ⟨w', ?_, hfw', fun O hO t _ => ?_⟩
  · rw [toFlag, ← Category.assoc, hw', hw₀f]
  · obtain ⟨s, rfl⟩ := hs t
    change (f ≫ w') s ∈ O
    rw [hfw']
    exact hO (Set.mem_univ s)

end GlobalTheory.ModifLift
