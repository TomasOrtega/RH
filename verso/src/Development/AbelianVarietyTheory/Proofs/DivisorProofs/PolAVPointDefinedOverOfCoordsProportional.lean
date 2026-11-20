import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCoordPtLocal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

/- English proof (translation)
Introduce `K _ _ k₀ hk₀ P₀ m hm hm3 hmK z v l r H hr hv`. Set `Ix` to `{y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1}`. Establish `Lw` using `GlobalTheory.abelianSchemeLaws_all`. Establish `hm1 : 1 ≤ m ^ 2` using `Nat.one_le_pow _ _ (by omega)`. Establish `hm2K : ((m ^ 2 : ℕ) : K) ≠ 0` using `by rw [Nat.cast_pow]; exact pow_ne_zero _ hmK`.

Establish `hcard` using `(Lw.1.mulN (Sp k₀) P₀ (m ^ 2) hm1).2.2.2.2 K (spMap k₀.subtype) hm2K`. Establish `hfin : Finite Ix` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))`. Establish `hσs : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype`. Introduce `σ hσ`. Simplify using `only [spMap, ← Spec.map_comp]`.

Use `congr 2`. Use extensionality with `w`. Conclude with `hσ _ w.2`. Establish `hfix : ∀ (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) (y : Ix), (Over.homMk (spMap σ.toRingHom) (hσs σ hσ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1 = y.1`. Introduce `σ hσ y`.

Establish `hdef : DefOver k₀ y.1.left`. Use `defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y' : Ix => y'.1.left).subset ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, hτ, rfl⟩`. Use `⟨⟨(Over.homMk (spMap τ.toRingHom) (hσs τ hτ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← MonObj.comp_pow, y.2, MonObj.comp_one]`.

Both sides reduce to the same expression. Take `⟨y₀, hy₀⟩` from `hdef`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show spMap σ.toRingHom ≫ y.1.left = y.1.left`. Rewrite using `[← hy₀, ← Category.assoc, hσs σ hσ]`.

Take `⟨-, U₂, -, U₄⟩` from `CoordSep.coord_exists_unique_separate Lw.1 K (Sp k₀) P₀ (spMap k₀.subtype) m hm hmK Ix (fun i => i.1) (fun i => i.2)`. Establish `hall : ∀ y : Over.mk (spMap k₀.subtype) ⟶ P₀.A, y ^ m ^ 2 = 1 → ∃ i : Ix, i.1 = y` using `fun y hy => ⟨⟨y, hy⟩, rfl⟩`. Establish `hv0 : v ≠ 0` using `(U₄ hm3 hall z z v H H).2`. Establish `hl : l ≠ 0`. Introduce `h0`.

Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite using `[hv i, h0, zero_mul, Pi.zero_apply]`. Establish `horb : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ z.left = z.left`. Introduce `σ hσ`.

Set `h : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)` to `Over.homMk (spMap σ.toRingHom) (hσs σ hσ)`. Establish `H2` using `CoordReduce.isCoordPt_map Lw.2 P₀ σ.toRingHom (hσs σ hσ) (p := fun i : Ix => i.1) (fun i => i.2) (w := v) H`. Establish `hp : (fun i : Ix => h ≫ i.1) = fun i => i.1` using `funext fun i => hfix σ hσ i`. Express the relevant statement in the definitionally equal form `GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => h ≫ i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (σ (v i))) at H2`. Rewrite `H2` using `[hp]`.

Establish `hσl : σ l ≠ 0` using `(map_ne_zero σ).2 hl`. Establish `H3 : GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (v i))`. Use `(U₂ (h ≫ z) (fun i => σ (v i)) v H2).2 ⟨Units.mk0 (l / σ l) (div_ne_zero hl hσl), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[hv i, map_mul, hσ _ (hr i)]`. Clear the denominators using the available nonvanishing facts. Use `(U₄ hm3 hall (h ≫ z) z v H3 H).1` as an intermediate fact. Establish `e2` using `congrArg CommaMorphism.left this`. Conclude with `e2`.

Use `defOver_of_finite_orbit K k₀ hk₀ _ z.left ((Set.finite_singleton z.left).subset ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Conclude with `horb σ hσ`.
-/
theorem defOver_of_coord_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 →
    ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K)
      (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K),
      GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) →
      (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  intro K _ _ k₀ hk₀ P₀ m hm hm3 hmK z v l r H hr hv
  classical
  let Ix := {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1}
  have Lw := GlobalTheory.abelianSchemeLaws_all
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm2K : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hmK
  have hcard := (Lw.1.mulN (Sp k₀) P₀ (m ^ 2) hm1).2.2.2.2 K (spMap k₀.subtype) hm2K
  have hfin : Finite Ix := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))

  have hσs : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
    intro σ hσ
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ w.2

  have hfix : ∀ (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) (y : Ix),
      (Over.homMk (spMap σ.toRingHom) (hσs σ hσ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1 = y.1 := by
    intro σ hσ y
    have hdef : DefOver k₀ y.1.left := by
      refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y' : Ix => y'.1.left).subset ?_)
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨⟨(Over.homMk (spMap τ.toRingHom) (hσs τ hτ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1, ?_⟩, ?_⟩
      · rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      · rfl
    obtain ⟨y₀, hy₀⟩ := hdef
    apply Over.OverMorphism.ext
    show spMap σ.toRingHom ≫ y.1.left = y.1.left
    rw [← hy₀, ← Category.assoc, hσs σ hσ]

  obtain ⟨-, U₂, -, U₄⟩ := CoordSep.coord_exists_unique_separate Lw.1 K (Sp k₀) P₀ (spMap k₀.subtype) m hm hmK Ix
    (fun i => i.1) (fun i => i.2)
  have hall : ∀ y : Over.mk (spMap k₀.subtype) ⟶ P₀.A, y ^ m ^ 2 = 1 → ∃ i : Ix, i.1 = y := fun y hy => ⟨⟨y, hy⟩, rfl⟩
  have hv0 : v ≠ 0 := (U₄ hm3 hall z z v H H).2
  have hl : l ≠ 0 := by
    intro h0
    apply hv0
    funext i
    rw [hv i, h0, zero_mul, Pi.zero_apply]
  have horb : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ z.left = z.left := by
    intro σ hσ
    let h : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype) := Over.homMk (spMap σ.toRingHom) (hσs σ hσ)
    have H2 := CoordReduce.isCoordPt_map Lw.2 P₀ σ.toRingHom (hσs σ hσ) (p := fun i : Ix => i.1)
      (fun i => i.2) (w := v) H
    have hp : (fun i : Ix => h ≫ i.1) = fun i => i.1 := funext fun i => hfix σ hσ i
    change GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => h ≫ i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (σ (v i))) at H2
    rw [hp] at H2
    have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl
    have H3 : GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (v i)) := by
      refine (U₂ (h ≫ z) (fun i => σ (v i)) v H2).2 ⟨Units.mk0 (l / σ l) (div_ne_zero hl hσl), ?_⟩
      funext i
      simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
      rw [hv i, map_mul, hσ _ (hr i)]
      field_simp
    have := (U₄ hm3 hall (h ≫ z) z v H3 H).1
    have e2 := congrArg CommaMorphism.left this
    exact e2
  refine defOver_of_finite_orbit K k₀ hk₀ _ z.left ((Set.finite_singleton z.left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  exact horb σ hσ

end GlobalTheory.Poinc.Sep
