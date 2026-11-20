import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianSubgroupFinite

/- English proof (translation)
Establish `hs : Surjective (pullback.snd ν x)` using `⟨by`. Rewrite using `[← Set.range_eq_univ, Scheme.Pullback.range_snd]`. Conclude with `Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩`. Establish `: IsIso (pullback.snd ν x)` using `isIso_of_isClosedImmersion_of_surjective _`. Conclude with `⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by`.

Rewrite using `[Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩`.
-/
theorem exists_lift_of_range_subset {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have hs : Surjective (pullback.snd ν x) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun t => h ⟨t, rfl⟩⟩
  have : IsIso (pullback.snd ν x) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

/- English proof (translation)
Rewrite using `[← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]`.
-/
theorem isCommMonObj_of_mono {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]
    [BraidedCategory 𝒞] {N B : 𝒞} [MonObj N] [MonObj B] [IsCommMonObj B] (ν : N ⟶ B) [Mono ν]
    [IsMonHom ν] : IsCommMonObj N where
  mul_comm := by
    rw [← cancel_mono ν, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

/- English proof (translation)
Introduce `hcount k _ _ B _ n hB hn hnk C Z hZ hC htor`. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hB.comm` as an intermediate fact. Take `⟨N, _, ν, hν, hνc, hNs, hr⟩` from `GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC`.

Establish `hNp : IsProper N.hom` using `by rw [← ν.w]; infer_instance`. Take `⟨N₀, _, ν₀, g, hν₀, -, hν₀c, hgc, hg, hfin⟩` from `GlobalTheory.exists_neutralComponent k N hNs inferInstance`. Establish `: IsClosedImmersion (ν₀ ≫ ν).left` using `by rw [Over.comp_left]; infer_instance`. Establish `: Mono (ν₀ ≫ ν)` using `Over.mono_of_mono_left _`. Establish `hA : IsAbelianScheme N₀` using `{ comm := isCommMonObj_of_mono (ν₀ ≫ ν) smooth := SmoothOfRelativeDimension.smooth g N₀.hom proper := by rw [← ν₀.w]; infer_instance geomConnected := hgc }`.

Establish `hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C` using `fun x => by`. Rewrite using `[hC, ← hr]`. Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨x.left t, rfl⟩`. Establish `h1 : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ N₀) // x ^ n = 1} = 1`.

Rewrite using `[Nat.card_eq_one_iff_exists]`. Use `⟨⟨1, one_pow n⟩, fun x => Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h2 : x.1 ≫ ν₀ ≫ ν = 1`. Use `htor _ (by rw [← Category.assoc]; exact hmem _) ?_` and prove the remaining obligations. Rewrite using `[← MonObj.pow_comp, x.2, MonObj.one_comp]`.

Rewrite using `[← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]`. Rewrite `h1` using `[hcount k N₀ g n hA hg hnk]`. Establish `hg0 : g = 0`. Break down `(Nat.pow_eq_one.1 h1) with h | h` into its components or cases. Conclude with `absurd h hn.one_lt.ne'`.

Use linear arithmetic over natural numbers and integers. Use `hfin hg0` as an intermediate fact. Use `Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`. Establish `: IsReduced (𝟙_ (Over (Sp k))).left` using `inferInstanceAs (IsReduced (Sp k))`.

Take `⟨l, hl⟩` from `exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)`. Use `⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩` and prove the remaining obligations. Rewrite using `[← ν.w, ← Category.assoc, hl, x.w]`.
-/
theorem finite_of_no_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) := by
  intro hcount k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, -, hν₀c, hgc, hg, hfin⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have h1 : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ N₀) // x ^ n = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, one_pow n⟩, fun x => Subtype.ext ?_⟩
    have h2 : x.1 ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, x.2, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  rw [hcount k N₀ g n hA hg hnk] at h1
  have hg0 : g = 0 := by
    rcases (Nat.pow_eq_one.1 h1) with h | h
    · exact absurd h hn.one_lt.ne'
    · omega
  have := hfin hg0
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

end GlobalTheory.AbelianSubgroupFinite
