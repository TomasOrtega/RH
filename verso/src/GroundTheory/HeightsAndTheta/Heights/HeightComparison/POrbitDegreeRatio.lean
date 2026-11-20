import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatioLemmas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def ratioVec (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Coord n → ratioField x :=
  fun p ↦ ⟨x p.1 p.2 / x p.1 (c p.1), div_mem_ratioField x _ _ _⟩

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (comp_aeval (ratioVec x c) (ratioField x).val) f`.
-/
theorem val_aeval_ratioVec (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    ((aeval (ratioVec x c) f : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f :=
  DFunLike.congr_fun (comp_aeval (ratioVec x c) (ratioField x).val) f

/- English proof (translation)
Use `set S := Set.range fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)`. Establish `hL : ratioField x = IntermediateField.adjoin ℚ S`. Use `le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, i, j⟩, rfl⟩ dsimp only`. Rewrite using `[← div_div_div_cancel_right₀ (hc k) (x k i) (x k j)]`.

Conclude with `div_mem (IntermediateField.subset_adjoin ℚ S ⟨⟨k, i⟩, rfl⟩) (IntermediateField.subset_adjoin ℚ S ⟨⟨k, j⟩, rfl⟩)`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `div_mem_ratioField x _ _ _`. Introduce `a`. Establish `ha : (a : AlgebraicClosure ℚ) ∈ (aeval (R` using `ℚ) fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)).range := by`.

Establish `: Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` using `AlgebraicClosure.isAlgebraic ℚ`. Rewrite using `[aeval_range, ← IntermediateField.adjoin_toSubalgebra, ← hL]`. Conclude with `a.2`. Take `⟨f, hf⟩` from `ha`. Conclude with `⟨f, Subtype.ext ((val_aeval_ratioVec x c f).trans hf)⟩`.
-/
theorem aeval_ratioVec_surjective (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) :
    Function.Surjective (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ratioField x) := by
  set S := Set.range fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)
  have hL : ratioField x = IntermediateField.adjoin ℚ S := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro _ ⟨⟨k, i, j⟩, rfl⟩
      dsimp only
      rw [← div_div_div_cancel_right₀ (hc k) (x k i) (x k j)]
      exact div_mem (IntermediateField.subset_adjoin ℚ S ⟨⟨k, i⟩, rfl⟩)
        (IntermediateField.subset_adjoin ℚ S ⟨⟨k, j⟩, rfl⟩)
    · rintro _ ⟨p, rfl⟩
      exact div_mem_ratioField x _ _ _
  intro a
  have ha : (a : AlgebraicClosure ℚ) ∈
      (aeval (R := ℚ) fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)).range := by
    have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    rw [aeval_range, ← IntermediateField.adjoin_toSubalgebra, ← hL]
    exact a.2
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, Subtype.ext ((val_aeval_ratioVec x c f).trans hf)⟩

/- English proof (translation)
Set `: Algebra L ℂ` to `τ.toAlgebra`. Establish `: Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` using `AlgebraicClosure.isAlgebraic ℚ`. Establish `: Algebra.IsAlgebraic L (AlgebraicClosure ℚ)` using `Algebra.IsAlgebraic.tower_top (K := ℚ) L`. Conclude with `⟨(IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).toRingHom, fun a ↦ (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).commutes a⟩`.
-/
theorem exists_extend_embedding (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (τ : L →+* ℂ) :
    ∃ σ : AlgebraicClosure ℚ →+* ℂ, ∀ a : L, σ a = τ a := by
  let : Algebra L ℂ := τ.toAlgebra
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsAlgebraic L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact ⟨(IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).toRingHom, fun a ↦
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[L] ℂ).commutes a⟩

/- English proof (translation)
Introduce `ι _ _ _ n x hx`. Take `⟨c, hc⟩` from `exists_chart hx`. Use `set W := orbitIdeal x`. Use `set L := ratioField x`. Use `set Q := Quot fun z z' : Geo.mcPts (ι := blockIdx n) W ↦ ∃ a : ι → ℂ, (∀ k, a k ≠ 0) ∧ (z' : Coord n → ℂ) = fun p ↦ a p.1 * (z : Coord n → ℂ) p`.

Use `show Nat.card Q = _`. Use `choose σ hσ using exists_extend_embedding L`. Establish `hpt : ∀ τ : L →+* ℂ, (fun p ↦ σ τ (flatCone x p)) ∈ Geo.mcPts (ι` using `blockIdx n) W := by`. Introduce `τ`. Use `⟨fun k ↦ ?_, fun f hf ↦ eval_conj_eq_zero x (σ τ) hf⟩` and prove the remaining obligations.

Take `⟨i, hi⟩` from `Function.ne_iff.mp (hx k)`. Conclude with `⟨i, (map_ne_zero _).mpr hi⟩`. Set `Φ : (L →+* ℂ) → Q` to `fun τ ↦ Quot.mk _ ⟨_, hpt τ⟩`. Set `R : Q → Coord n → ℂ` to `Quot.lift (fun z p ↦ (z : Coord n → ℂ) p / (z : Coord n → ℂ) ⟨p.1, c p.1⟩) (by`. Introduce and unpack `z z' ⟨a, ha, e⟩`.

Use function extensionality and compare the values at `p`. Simplify using `only [e]`. Rewrite using `[mul_div_mul_left _ _ (ha p.1)])`. Establish `hRΦ : ∀ τ p, R (Φ τ) p = τ (ratioVec x c p)`. Introduce `τ p`.

Use `show σ τ (x p.1 p.2) / σ τ (x p.1 (c p.1)) = _`. Rewrite using `[← map_div₀]`. Conclude with `hσ τ (ratioVec x c p)`. Establish `hτ : ∀ (τ : L →+* ℂ) f, τ (aeval (ratioVec x c) f) = aeval (fun p ↦ τ (ratioVec x c p)) f` using `fun τ f ↦ DFunLike.congr_fun (comp_aeval (ratioVec x c) τ.toRatAlgHom) f`. Set `ψ : MvPolynomial (Coord n) ℚ →+* L` to `(aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] L).toRingHom`.

Establish `hsurj : Function.Surjective ψ` using `aeval_ratioVec_surjective x c hc`. Establish `hinj : Function.Injective Φ`. Introduce `τ τ' h`. Establish `e : (fun p ↦ τ (ratioVec x c p)) = fun p ↦ τ' (ratioVec x c p)` using `funext fun p ↦ by`. Rewrite using `[← hRΦ, ← hRΦ, h]`.

Use extensionality with `a`. Take `⟨f, rfl⟩` from `hsurj a`. Use `show τ (aeval (ratioVec x c) f) = τ' (aeval (ratioVec x c) f)`. Rewrite using `[hτ, hτ, e]`. Establish `hΦ : Function.Surjective Φ`.

Use `Quot.ind fun z ↦ ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `z`. Establish `hz0` using `chart_ne_zero_of_mem_mcPts x c hc hz`. Set `g : {g : MvPolynomial (Coord n) ℚ →+* ℂ // RingHom.ker ψ ≤ RingHom.ker g}` to `⟨(aeval fun p ↦ z p / z ⟨p.1, c p.1⟩ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ).toRingHom, fun f hf ↦ by`. Rewrite `hf`, the goal using `[RingHom.mem_ker]`.

Use `aeval_ratio_eq_zero x c hc hz hz0 f ?_` and prove the remaining obligations. Rewrite using `[← val_aeval_ratioVec]`. Conclude with `congrArg Subtype.val hf⟩`. Establish `hτp : ∀ p, ψ.liftOfSurjective hsurj g (ratioVec x c p) = z p / z ⟨p.1, c p.1⟩` using `fun p ↦ by`. Establish `h` using `RingHom.liftOfSurjective_comp_apply ψ hsurj g (X p)`.

Simplify using `only [ψ, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at h`. Conclude with `h`. Use `set τ := ψ.liftOfSurjective hsurj g`. Use `⟨τ, (Quot.sound ⟨fun k ↦ σ τ (x k (c k)) / z ⟨k, c k⟩, fun k ↦ div_ne_zero ((map_ne_zero _).mpr (hc k)) (hz0 k), ?_⟩).symm⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Establish `h1 : σ τ (x p.1 p.2) = σ τ (x p.1 p.2 / x p.1 (c p.1)) * σ τ (x p.1 (c p.1))`. Rewrite using `[← map_mul, div_mul_cancel₀ _ (hc p.1)]`. Establish `h2 : σ τ (x p.1 p.2 / x p.1 (c p.1)) = z p / z ⟨p.1, c p.1⟩` using `(hσ τ (ratioVec x c p)).trans (hτp p)`. Use `show σ τ (x p.1 p.2) = σ τ (x p.1 (c p.1)) / z ⟨p.1, c p.1⟩ * z p`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hΦ⟩), Nat.card_eq_fintype_card, NumberField.Embeddings.card]`.
-/
theorem OrbitDegreeRatio.proof : OrbitDegreeRatio.Statement := by
  intro ι _ _ _ n x hx
  obtain ⟨c, hc⟩ := exists_chart hx
  set W := orbitIdeal x
  set L := ratioField x
  set Q := Quot fun z z' : Geo.mcPts (ι := blockIdx n) W ↦
    ∃ a : ι → ℂ, (∀ k, a k ≠ 0) ∧ (z' : Coord n → ℂ) = fun p ↦ a p.1 * (z : Coord n → ℂ) p
  show Nat.card Q = _
  choose σ hσ using exists_extend_embedding L
  have hpt : ∀ τ : L →+* ℂ, (fun p ↦ σ τ (flatCone x p)) ∈ Geo.mcPts (ι := blockIdx n) W := by
    intro τ
    refine ⟨fun k ↦ ?_, fun f hf ↦ eval_conj_eq_zero x (σ τ) hf⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  let Φ : (L →+* ℂ) → Q := fun τ ↦ Quot.mk _ ⟨_, hpt τ⟩

  let R : Q → Coord n → ℂ := Quot.lift
    (fun z p ↦ (z : Coord n → ℂ) p / (z : Coord n → ℂ) ⟨p.1, c p.1⟩) (by
      rintro z z' ⟨a, ha, e⟩
      funext p
      simp only [e]
      rw [mul_div_mul_left _ _ (ha p.1)])
  have hRΦ : ∀ τ p, R (Φ τ) p = τ (ratioVec x c p) := by
    intro τ p
    show σ τ (x p.1 p.2) / σ τ (x p.1 (c p.1)) = _
    rw [← map_div₀]
    exact hσ τ (ratioVec x c p)
  have hτ : ∀ (τ : L →+* ℂ) f, τ (aeval (ratioVec x c) f) =
      aeval (fun p ↦ τ (ratioVec x c p)) f := fun τ f ↦
    DFunLike.congr_fun (comp_aeval (ratioVec x c) τ.toRatAlgHom) f
  let ψ : MvPolynomial (Coord n) ℚ →+* L :=
    (aeval (ratioVec x c) : MvPolynomial (Coord n) ℚ →ₐ[ℚ] L).toRingHom
  have hsurj : Function.Surjective ψ := aeval_ratioVec_surjective x c hc

  have hinj : Function.Injective Φ := by
    intro τ τ' h
    have e : (fun p ↦ τ (ratioVec x c p)) = fun p ↦ τ' (ratioVec x c p) := funext fun p ↦ by
      rw [← hRΦ, ← hRΦ, h]
    ext a
    obtain ⟨f, rfl⟩ := hsurj a
    show τ (aeval (ratioVec x c) f) = τ' (aeval (ratioVec x c) f)
    rw [hτ, hτ, e]

  have hΦ : Function.Surjective Φ := by
    refine Quot.ind fun z ↦ ?_
    obtain ⟨z, hz⟩ := z
    have hz0 := chart_ne_zero_of_mem_mcPts x c hc hz
    let g : {g : MvPolynomial (Coord n) ℚ →+* ℂ // RingHom.ker ψ ≤ RingHom.ker g} :=
      ⟨(aeval fun p ↦ z p / z ⟨p.1, c p.1⟩ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ).toRingHom,
        fun f hf ↦ by
          rw [RingHom.mem_ker] at hf ⊢
          refine aeval_ratio_eq_zero x c hc hz hz0 f ?_
          rw [← val_aeval_ratioVec]
          exact congrArg Subtype.val hf⟩
    have hτp : ∀ p, ψ.liftOfSurjective hsurj g (ratioVec x c p) =
        z p / z ⟨p.1, c p.1⟩ := fun p ↦ by
      have h := RingHom.liftOfSurjective_comp_apply ψ hsurj g (X p)
      simp only [ψ, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at h
      exact h
    set τ := ψ.liftOfSurjective hsurj g
    refine ⟨τ, (Quot.sound ⟨fun k ↦ σ τ (x k (c k)) / z ⟨k, c k⟩,
      fun k ↦ div_ne_zero ((map_ne_zero _).mpr (hc k)) (hz0 k), ?_⟩).symm⟩
    funext p
    have h1 : σ τ (x p.1 p.2) = σ τ (x p.1 p.2 / x p.1 (c p.1)) * σ τ (x p.1 (c p.1)) := by
      rw [← map_mul, div_mul_cancel₀ _ (hc p.1)]
    have h2 : σ τ (x p.1 p.2 / x p.1 (c p.1)) = z p / z ⟨p.1, c p.1⟩ :=
      (hσ τ (ratioVec x c p)).trans (hτp p)
    show σ τ (x p.1 p.2) = σ τ (x p.1 (c p.1)) / z ⟨p.1, c p.1⟩ * z p
    rw [h1, h2]
    ring
  rw [← Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hΦ⟩), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

/- English proof (translation)
The claim follows from `samplePoint_blockNonzero`.
-/
example : BlockNonzero samplePoint := samplePoint_blockNonzero

end

end GroundTheory.Heights₂.Heights
