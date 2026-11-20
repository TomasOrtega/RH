import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `k L _ _ _ n e Q g hQ hg x j₀ hx hj`. Use `hQ.isPrime` as an intermediate fact. Establish `hdim` using `h₁ k n (e + 1) Q g hQ hg`. Establish `hXj : (X j₀ : MvPolynomial (Fin n) k) ∉ Q` using `fun h => hj (by simpa using hx _ h)`. Establish `htr` using `h₂ k n e Q j₀ hQ hdim hXj`.

Set `R` to `MvPolynomial (Fin n) k ⧸ Q`. Set `K` to `FractionRing R`. Set `π : R →ₐ[k] L` to `Ideal.Quotient.liftₐ Q (aeval x) hx`. Set `s : R` to `Ideal.Quotient.mk Q (X j₀)`. Establish `hs : s ≠ 0`.

Introduce `h`. Conclude with `hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Establish `hπX : ∀ m, π (Ideal.Quotient.mk Q (X m)) = x m` using `fun m => (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp Q (aeval x) hx) (X m)).trans (aeval_X x m)`. Establish `hπs : π s = x j₀` using `hπX j₀`. Establish `hπu : IsUnit (π s)` using `by rw [hπs]; exact hj.isUnit`.

Establish `hKs : algebraMap R K s ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs`. Set `S` to `Localization.Away s`. Set `ρ : S →ₐ[k] L` to `IsLocalization.Away.liftAlgHom s hπu`. Set `ι : S →ₐ[k] K` to `IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom k R K) s hKs.isUnit`. Establish `hSinj : Function.Injective (algebraMap R S)` using `IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)`.

Establish `hι : Function.Injective ι` using `by show Function.Injective (IsLocalization.Away.lift (g := algebraMap R K) s hKs.isUnit)`. Use `(IsLocalization.lift_injective_iff _).mpr fun a b => ?_` and prove the remaining obligations. Rewrite using `[hSinj.eq_iff, (IsFractionRing.injective R K).eq_iff]`. Set `y : Fin n → S` to `fun m => algebraMap R S (Ideal.Quotient.mk Q (X m)) * IsLocalization.Away.invSelf s`. Establish `hinv : ∀ {B : Type} [Field B] [Algebra k B] (φ : S →ₐ[k] B), φ (IsLocalization.Away.invSelf s) = (φ (algebraMap R S s))⁻¹`.

Introduce `B _ _ φ`. Use `eq_inv_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← map_mul, IsLocalization.Away.mul_invSelf, map_one]`. Establish `hιR : ∀ a, ι (algebraMap R S a) = algebraMap R K a` using `fun a => IsLocalization.Away.lift_eq (g := algebraMap R K) s hKs.isUnit a`. Establish `hρR : ∀ a, ρ (algebraMap R S a) = π a` using `fun a => IsLocalization.Away.lift_eq (g := (π : R →+* L)) s hπu a`.

Establish `hιy : ι ∘ y = fun m => genPt Q m * (genPt Q j₀)⁻¹`. Use function extensionality and compare the values at `m`. Simplify using `only [Function.comp_apply, y, map_mul, hinv ι, hιR]`. Both sides reduce to the same expression. Establish `hρy : ρ ∘ y = fun m => x m * (x j₀)⁻¹`.

Use function extensionality and compare the values at `m`. Simplify using `only [Function.comp_apply, y, map_mul, hinv ρ, hρR, hπX, s]`. Set `T` to `Algebra.adjoin k (Set.range y)`. Establish `hA : T.map ι = Algebra.adjoin k (Set.range fun m => genPt Q m * (genPt Q j₀)⁻¹)`. Rewrite using `[← Algebra.adjoin_image, ← Set.range_comp, hιy]`.

Establish `hB : T.map ρ = Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)`. Rewrite using `[← Algebra.adjoin_image, ← Set.range_comp, hρy]`. Establish `hTA : Algebra.trdeg k T = Algebra.trdeg k (T.map ι)` using `(Subalgebra.equivMapOfInjective T ι hι).trdeg_eq`. Establish `hBT : Algebra.trdeg k (T.map ρ) ≤ Algebra.trdeg k T`. Use `trdeg_le_of_surjective ((ρ.comp T.val).codRestrict (T.map ρ) (fun t => ⟨t, t.2, rfl⟩)) ?_` and prove the remaining obligations.

Introduce and unpack `⟨b, t, ht, rfl⟩`. Conclude with `⟨⟨t, ht⟩, rfl⟩`. Rewrite using `[← hB]`. Rewrite `hTA` using `[hA, htr]`. Conclude with `hBT.trans hTA.le`.
-/
theorem ChartPointTrdeg.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : AffineChartTrdeg.Statement) :
    ChartPointTrdeg.Statement := by
  intro k L _ _ _ n e Q g hQ hg x j₀ hx hj
  have := hQ.isPrime
  have hdim := h₁ k n (e + 1) Q g hQ hg
  have hXj : (X j₀ : MvPolynomial (Fin n) k) ∉ Q := fun h => hj (by simpa using hx _ h)
  have htr := h₂ k n e Q j₀ hQ hdim hXj
  let R := MvPolynomial (Fin n) k ⧸ Q
  let K := FractionRing R
  let π : R →ₐ[k] L := Ideal.Quotient.liftₐ Q (aeval x) hx
  let s : R := Ideal.Quotient.mk Q (X j₀)
  have hs : s ≠ 0 := by
    intro h
    exact hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hπX : ∀ m, π (Ideal.Quotient.mk Q (X m)) = x m := fun m =>
    (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp Q (aeval x) hx) (X m)).trans (aeval_X x m)
  have hπs : π s = x j₀ := hπX j₀
  have hπu : IsUnit (π s) := by rw [hπs]; exact hj.isUnit
  have hKs : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
  let S := Localization.Away s
  let ρ : S →ₐ[k] L := IsLocalization.Away.liftAlgHom s hπu
  let ι : S →ₐ[k] K :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom k R K) s hKs.isUnit
  have hSinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hι : Function.Injective ι := by
    show Function.Injective (IsLocalization.Away.lift (g := algebraMap R K) s hKs.isUnit)
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ?_
    rw [hSinj.eq_iff, (IsFractionRing.injective R K).eq_iff]
  let y : Fin n → S := fun m => algebraMap R S (Ideal.Quotient.mk Q (X m)) * IsLocalization.Away.invSelf s
  have hinv : ∀ {B : Type} [Field B] [Algebra k B] (φ : S →ₐ[k] B),
      φ (IsLocalization.Away.invSelf s) = (φ (algebraMap R S s))⁻¹ := by
    intro B _ _ φ
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hιR : ∀ a, ι (algebraMap R S a) = algebraMap R K a := fun a =>
    IsLocalization.Away.lift_eq (g := algebraMap R K) s hKs.isUnit a
  have hρR : ∀ a, ρ (algebraMap R S a) = π a := fun a =>
    IsLocalization.Away.lift_eq (g := (π : R →+* L)) s hπu a
  have hιy : ι ∘ y = fun m => genPt Q m * (genPt Q j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ι, hιR]
    rfl
  have hρy : ρ ∘ y = fun m => x m * (x j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ρ, hρR, hπX, s]
  let T := Algebra.adjoin k (Set.range y)
  have hA : T.map ι = Algebra.adjoin k (Set.range fun m => genPt Q m * (genPt Q j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hιy]
  have hB : T.map ρ = Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hρy]
  have hTA : Algebra.trdeg k T = Algebra.trdeg k (T.map ι) :=
    (Subalgebra.equivMapOfInjective T ι hι).trdeg_eq
  have hBT : Algebra.trdeg k (T.map ρ) ≤ Algebra.trdeg k T := by
    refine trdeg_le_of_surjective ((ρ.comp T.val).codRestrict (T.map ρ)
      (fun t => ⟨t, t.2, rfl⟩)) ?_
    rintro ⟨b, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hB]
  rw [hA, htr] at hTA
  exact hBT.trans hTA.le

end

end GroundTheory.Heights₂.Heights.Vertical
