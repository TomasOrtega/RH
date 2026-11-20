import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.GramBaseChange

/- English proof (translation)
Introduce `E _ _ _ H K _ _ ρ σ₁ A B p q hρ hA f₁ f₂ hf₁ hf₂`. Establish `hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K))` using `σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)`. Take `⟨⟨A', mA, -⟩, hA2⟩` from `GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A`. Take `⟨⟨B', mB, -⟩, hB2⟩` from `GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) B`. Take `⟨-, -, wA, hwA⟩` from `hA2 A' mA inferInstance`.

Take `⟨-, -, wB, hwB⟩` from `hB2 B' mB inferInstance`. Use `haveI := hf₁.isMonHom`. Use `haveI := hf₂.isMonHom`. Take `⟨f₁', hm₁, e₁⟩` from `GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₁`. Take `⟨f₂', hm₂, e₂⟩` from `GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₂`.

Establish `lin : ∀ (f : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G), Serre.IsLinearHom A.t.act B.t.act f → IsMonHom f' → f'.left ≫ mB.φ = mA.φ ≫ f.left → Serre.IsLinearHom A'.t.act B'.t.act f'`. Introduce `f f' hf hm e`. Use `⟨hm, fun c => ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `mB.cart.1.hom_ext` to reduce the goal to its premises.

Establish `hc` using `congrArg CommaMorphism.left (hf.comm c)`. Simplify using `only [Over.comp_left] at hc ⊢`. Rewrite using `[Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c, ← Category.assoc, ← Category.assoc, e]`. Simplify using `only [Over.comp_left, Category.assoc, Over.w]`. Establish `hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔ LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n` using `fun τ n => by`.

Use `GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis. Establish `hweil : ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) → WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K)))`. Introduce `g h`. Use `(GlobalTheory.PairingFibre.weilEq_iff (g₂ := 𝟙 _) mA.cart mA.cart mB.cart mA.cart B.t.PP.isLB A.t.PP.isLB B'.t.PP.isLB A'.t.PP.isLB ⟨wB, hwB.1⟩ ⟨wA, hwA.1⟩ e₁ e₂ (mA.act g) (by simp) (𝟙 (Sp ℂ))).1 h` as an intermediate fact.

Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis. Establish `hT` using `hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi`. Establish `hd0 : (H.d : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 H.d_prime.ne_zero`. Establish `hr0 : H.rt0 ≠ 0` using `fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)`. Establish `hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0` using `fun x hx => sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)`.

Establish `hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ)`. Rewrite using `[← map_pow, hρ]`. Simplify using the standard rewrite rules. Establish `hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ)` using `fun τ => by`. Rewrite using `[← map_pow, H.rt_sq]`.

Simplify using the standard rewrite rules. Establish `hne : H.rt0 ≠ -H.rt0` using `fun h => hr0 (by linear_combination h / 2)`. Break down `hsq _ hβρ with hc | hc` into its components or cases. Use `⟨A', B', f₁', f₂', p, q, rfl, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩, lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩` and prove the remaining obligations. Conclude with `(hlie τ p).2 ((hT τ).1 (ht.trans hc.symm))`.

Conclude with `(hlie τ q).2 ((hT τ).2 (fun h => ht (h.trans hc)))`. Use `⟨A', B', f₁', f₂', q, p, add_comm _ _, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩, lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩` and prove the remaining obligations. Conclude with `(hlie τ q).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))`. Break down `hsq _ (hτ τ) with h | h` into its components or cases. Conclude with `absurd h ht`.

Conclude with `(hlie τ p).2 ((hT τ).1 (h.trans hc.symm))`.
-/
theorem exists_complex_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ (A' B' : PAT H (Sp ℂ)) (f₁' f₂' : A'.t.G ⟶ B'.t.G) (p' q' : ℕ), p' + q' = p + q ∧ (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ p') ∧ (τ H.rt ≠ H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ q')) ∧ Serre.IsLinearHom A'.t.act B'.t.act f₁' ∧ Serre.IsLinearHom A'.t.act B'.t.act f₂' ∧ ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) → WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hA f₁ f₂ hf₁ hf₂
  have hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨⟨A', mA, -⟩, hA2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A
  obtain ⟨⟨B', mB, -⟩, hB2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) B
  obtain ⟨-, -, wA, hwA⟩ := hA2 A' mA inferInstance
  obtain ⟨-, -, wB, hwB⟩ := hB2 B' mB inferInstance
  haveI := hf₁.isMonHom
  haveI := hf₂.isMonHom
  obtain ⟨f₁', hm₁, e₁⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₁
  obtain ⟨f₂', hm₂, e₂⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₂
  have lin : ∀ (f : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G), Serre.IsLinearHom A.t.act B.t.act f → IsMonHom f' →
      f'.left ≫ mB.φ = mA.φ ≫ f.left → Serre.IsLinearHom A'.t.act B'.t.act f' := by
    intro f f' hf hm e
    refine ⟨hm, fun c => ?_⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · have hc := congrArg CommaMorphism.left (hf.comm c)
      simp only [Over.comp_left] at hc ⊢
      rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
        ← Category.assoc, ← Category.assoc, e]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  have hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔
      LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n := fun τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rwa [Category.id_comp] at this
  have hweil : ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) →
      WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
    intro g h
    have := (GlobalTheory.PairingFibre.weilEq_iff (g₂ := 𝟙 _) mA.cart mA.cart mB.cart mA.cart B.t.PP.isLB A.t.PP.isLB B'.t.PP.isLB
      A'.t.PP.isLB ⟨wB, hwB.1⟩ ⟨wA, hwA.1⟩ e₁ e₂ (mA.act g) (by simp) (𝟙 (Sp ℂ))).1 h
    rwa [Category.id_comp] at this
  have hT := hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi
  have hd0 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0 := fun x hx =>
    sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)
  have hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  rcases hsq _ hβρ with hc | hc
  · refine ⟨A', B', f₁', f₂', p, q, rfl, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ p).2 ((hT τ).1 (ht.trans hc.symm))
    · exact (hlie τ q).2 ((hT τ).2 (fun h => ht (h.trans hc)))
  · refine ⟨A', B', f₁', f₂', q, p, add_comm _ _, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ q).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))
    · rcases hsq _ (hτ τ) with h | h
      · exact absurd h ht
      · exact (hlie τ p).2 ((hT τ).1 (h.trans hc.symm))

end GlobalTheory.GramBaseChange

end
