import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGalStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.KmapA

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨(A.valuation_le_one_iff y).1 h.le, (A.valuation_le_one_iff _).1 ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀, h, inv_one]`. Introduce and unpack `⟨h1, h2⟩`.

Establish `hu : IsUnit (⟨y, h1⟩ : A)` using `isUnit_iff_exists_inv.2 ⟨⟨y⁻¹, h2⟩, Subtype.ext (by simp [hy])⟩`. Conclude with `(A.valuation_eq_one_iff _).1 hu`.
-/
theorem val_eq_one_iff {K : Type} [Field K] (A : ValuationSubring K) {y : K} (hy : y ≠ 0) :
    A.valuation y = 1 ↔ y ∈ A ∧ y⁻¹ ∈ A := by
  constructor
  · intro h
    refine ⟨(A.valuation_le_one_iff y).1 h.le, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]
  · rintro ⟨h1, h2⟩
    have hu : IsUnit (⟨y, h1⟩ : A) :=
      isUnit_iff_exists_inv.2 ⟨⟨y⁻¹, h2⟩, Subtype.ext (by simp [hy])⟩
    exact (A.valuation_eq_one_iff _).1 hu

/- English proof (translation)
Introduce `W hW`. Take `⟨g, hg⟩` from `hf _ (hφ W hW)`. Use `⟨Units.map φ.toMonoidHom g, ?_⟩` and prove the remaining obligations. Establish `hx : ((f : X.K) / (g : X.K) ^ m) ≠ 0` using `div_ne_zero f.ne_zero (pow_ne_zero _ g.ne_zero)`. Rewrite `hg` using `[val_eq_one_iff _ hx]`.

Establish `hx' : φ ((f : X.K) / (g : X.K) ^ m) ≠ 0` using `(map_ne_zero φ).2 hx`. Establish `e : ((Units.map φ.toMonoidHom f : X.Kˣ) : X.K) / ((Units.map φ.toMonoidHom g : X.Kˣ) : X.K) ^ m = φ ((f : X.K) / (g : X.K) ^ m)`. Simplify using `[map_div₀, map_pow]`. Rewrite using `[e, val_eq_one_iff _ hx']`. Use `⟨ValuationSubring.mem_comap.1 hg.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv₀]`. Conclude with `ValuationSubring.mem_comap.1 hg.2`.
-/
theorem un_map (X : Tower Ω ε) (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) (m : ℕ) (f : X.Kˣ)
    (hf : f ∈ X.Un m) : Units.map φ.toMonoidHom f ∈ X.Un m := by
  intro W hW
  obtain ⟨g, hg⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom g, ?_⟩
  have hx : ((f : X.K) / (g : X.K) ^ m) ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ g.ne_zero)
  rw [val_eq_one_iff _ hx] at hg
  have hx' : φ ((f : X.K) / (g : X.K) ^ m) ≠ 0 := (map_ne_zero φ).2 hx
  have e : ((Units.map φ.toMonoidHom f : X.Kˣ) : X.K) / ((Units.map φ.toMonoidHom g : X.Kˣ) : X.K) ^ m =
      φ ((f : X.K) / (g : X.K) ^ m) := by
    simp [map_div₀, map_pow]
  rw [e, val_eq_one_iff _ hx']
  refine ⟨ValuationSubring.mem_comap.1 hg.1, ?_⟩
  rw [← map_inv₀]
  exact ValuationSubring.mem_comap.1 hg.2

/- English proof (translation)
Rewrite `he`, the goal using `[AdicCompletion.eval_apply]`. Establish `h2` using `AdicCompletion.map_val_apply (idl l) (LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) a`. Use `Eq.trans h2 ?_` and prove the remaining obligations. Rewrite using `[he]`. Both sides reduce to the same expression.
-/
theorem eval_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (n : ℕ) (a : X.Khat l) (f : X.Kˣ)
    (he : AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ a) = X.cls l n (Units.map φ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply] at he ⊢
  have h2 := AdicCompletion.map_val_apply (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))) (n := n) a
  refine Eq.trans h2 ?_
  rw [he]
  rfl

/- English proof (translation)
Establish `h : X.A l ≤ (X.A l).comap (X.kmap l φ)`. Use `Submodule.span_le.2 (fun x hx => ?_)` and prove the remaining obligations. Use `Submodule.subset_span (fun n => ?_)` and prove the remaining obligations. Take `⟨f, hf, he⟩` from `hx n`. Conclude with `⟨_, un_map X φ hφ (l ^ n) f hf, eval_kmap X l φ n x f he⟩`.

Introduce `a ha`. Conclude with `h ha`.
-/
theorem kmap_mem_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ.toRingHom)) :
    ∀ a ∈ X.A l, X.kmap l φ a ∈ X.A l := by
  have h : X.A l ≤ (X.A l).comap (X.kmap l φ) := by
    refine Submodule.span_le.2 (fun x hx => ?_)
    refine Submodule.subset_span (fun n => ?_)
    obtain ⟨f, hf, he⟩ := hx n
    exact ⟨_, un_map X φ hφ (l ^ n) f hf, eval_kmap X l φ n x f he⟩
  intro a ha
  exact h ha

end GlobalTheory.KZ.KmapA

open GlobalTheory.KZ.KmapA in

/- English proof (translation)
Introduce `Ω _ _ _ ε X hinj hhol l _`. Establish `hY` using `GlobalTheory.T.overAffineJLine_comap_sl_gal ε X hinj hhol`. Conclude with `⟨fun g => kmap_mem_A X l _ (fun W hW => (hY W hW).1 g), fun s => kmap_mem_A X l _ (fun W hW => (hY W hW).2 s)⟩`.
-/
theorem GlobalTheory.KZ.kmap_A_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (l : ℕ) [Fact l.Prime], (∀ (g : GQ), ∀ a ∈ X.A l, X.kmap l (X.sl g).toRingEquiv a ∈ X.A l) ∧
      ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l := by
  intro Ω _ _ _ ε X hinj hhol l _
  have hY := GlobalTheory.T.overAffineJLine_comap_sl_gal ε X hinj hhol
  exact ⟨fun g => kmap_mem_A X l _ (fun W hW => (hY W hW).1 g),
    fun s => kmap_mem_A X l _ (fun W hW => (hY W hW).2 s)⟩
