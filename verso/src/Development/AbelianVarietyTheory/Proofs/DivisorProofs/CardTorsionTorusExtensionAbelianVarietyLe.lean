import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusExtTorsion

/- English proof (translation)
Introduce `k _ _ G _ hGc X _ _ _ B _ i q hQ hB a ha m hm s hs`. Take `⟨hi, hq, -, -, -, hk, -⟩` from `hQ`. Use `haveI := hGc`. Set `P` to `𝟙_ (Over (Sp k))`. Set `I` to `IsMonHom.monoidHom i P`.

Set `Q` to `IsMonHom.monoidHom q P`. Establish `hIinj : Function.Injective I` using `fun a b h => hk.hom_ext h (toUnit_unique _ _)`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm Nat.cast_zero`. Take `⟨e⟩` from `GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k X`. Take `⟨-, hTcard⟩` from `GlobalTheory.SemiAbTorsionCount.divisible_and_card e m hm`.

Use `haveI hTfin : Finite {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} := Nat.finite_of_card_ne_zero (by rw [hTcard]; exact pow_ne_zero _ hm0)`. Use `letI : Fintype {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} := Fintype.ofFinite _`. Establish `hBcard` using `GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B a m hB ha hm`. Use `haveI hBfin : Finite {b : P ⟶ B // b ^ m = 1} := Nat.finite_of_card_ne_zero (by rw [hBcard]; exact pow_ne_zero _ hm0)`. Establish `himg : (s.image Q).card ≤ m ^ (2 * a)`.

Rewrite using `[← hBcard, ← Nat.card_eq_finsetCard]`. Use `Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) (fun y z h => Subtype.ext (congrArg Subtype.val h :))` and prove the remaining obligations. Take `⟨x, hx, hy⟩` from `Finset.mem_image.1 y.2`. Rewrite using `[← hy, ← map_pow, hs x hx, map_one]`. Establish `hfib : ∀ b ∈ s.image Q, (s.filter (fun x => Q x = b)).card ≤ m ^ Module.finrank ℤ X`.

Introduce `b hb`. Take `⟨x₀, hx₀, rfl⟩` from `Finset.mem_image.1 hb`. Establish `hsub : s.filter (fun x => Q x = Q x₀) ⊆ Finset.univ.image (fun t : {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} => x₀ * I t.1)`. Introduce `x hx`. Take `⟨hxs, hxq⟩` from `Finset.mem_filter.1 hx`.

Establish `hy : (x₀⁻¹ * x) ≫ q = 1`. Express the relevant statement in the definitionally equal form `Q (x₀⁻¹ * x) = 1`. Rewrite using `[map_mul, map_inv, hxq, inv_mul_cancel]`. Set `t` to `hk.lift (x₀⁻¹ * x) (toUnit _) (by rw [hy, Hom.one_def])`. Establish `ht : I t = x₀⁻¹ * x` using `hk.lift_fst _ _ _`.

Establish `htm : t ^ m = 1`. Apply `hIinj` to reduce the goal to its premises. Rewrite using `[map_pow, ht, map_one, mul_pow, inv_pow, hs x hxs, hs x₀ hx₀, inv_one, _root_.one_mul]`. Use `Finset.mem_image.2 ⟨⟨t, htm⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x₀ * I t = x`.

Rewrite using `[ht, mul_inv_cancel_left]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsCommMonObj G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → ∀ a : ℕ, SmoothOfRelativeDimension a B.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → s.card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
  classical
  intro k _ _ G _ hGc X _ _ _ B _ i q hQ hB a ha m hm s hs
  obtain ⟨hi, hq, -, -, -, hk, -⟩ := hQ
  haveI := hGc
  let P := 𝟙_ (Over (Sp k))
  let I := IsMonHom.monoidHom i P
  let Q := IsMonHom.monoidHom q P
  have hIinj : Function.Injective I := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero

  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k X
  obtain ⟨-, hTcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e m hm
  haveI hTfin : Finite {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hTcard]; exact pow_ne_zero _ hm0)
  letI : Fintype {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} := Fintype.ofFinite _

  have hBcard := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B a m hB ha hm
  haveI hBfin : Finite {b : P ⟶ B // b ^ m = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hBcard]; exact pow_ne_zero _ hm0)

  have himg : (s.image Q).card ≤ m ^ (2 * a) := by
    rw [← hBcard, ← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) (fun y z h => Subtype.ext (congrArg Subtype.val h :))
    obtain ⟨x, hx, hy⟩ := Finset.mem_image.1 y.2
    rw [← hy, ← map_pow, hs x hx, map_one]

  have hfib : ∀ b ∈ s.image Q, (s.filter (fun x => Q x = b)).card ≤ m ^ Module.finrank ℤ X := by
    intro b hb
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hb
    have hsub : s.filter (fun x => Q x = Q x₀) ⊆
        Finset.univ.image (fun t : {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} => x₀ * I t.1) := by
      intro x hx
      obtain ⟨hxs, hxq⟩ := Finset.mem_filter.1 hx
      have hy : (x₀⁻¹ * x) ≫ q = 1 := by
        change Q (x₀⁻¹ * x) = 1
        rw [map_mul, map_inv, hxq, inv_mul_cancel]
      let t := hk.lift (x₀⁻¹ * x) (toUnit _) (by rw [hy, Hom.one_def])
      have ht : I t = x₀⁻¹ * x := hk.lift_fst _ _ _
      have htm : t ^ m = 1 := by
        apply hIinj
        rw [map_pow, ht, map_one, mul_pow, inv_pow, hs x hxs, hs x₀ hx₀, inv_one, _root_.one_mul]
      refine Finset.mem_image.2 ⟨⟨t, htm⟩, Finset.mem_univ _, ?_⟩
      change x₀ * I t = x
      rw [ht, mul_inv_cancel_left]
    calc (s.filter (fun x => Q x = Q x₀)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = m ^ Module.finrank ℤ X := by rw [Finset.card_univ, Fintype.card_eq_nat_card, hTcard]
  calc s.card ≤ m ^ Module.finrank ℤ X * (s.image Q).card := Finset.card_le_mul_card_image s _ hfib
    _ ≤ m ^ Module.finrank ℤ X * m ^ (2 * a) := Nat.mul_le_mul_left _ himg
    _ = m ^ (Module.finrank ℤ X + 2 * a) := (pow_add _ _ _).symm

end GlobalTheory.TorusExtTorsion
