import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfIsogeny
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtensionOfSurjectivePointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFiniteKerOfSurjPointsSameDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisibleStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

namespace IsogenyOntoExtension

/- English proof (translation)
Establish `hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B]`. Use `IsPullback.of_hasPullback f η[B]` as an intermediate fact. Rewrite `this` using `[toUnit_unique (pullback.snd f η[B]) (toUnit _)]`. Then use the resulting hypothesis. Rewrite `hf` using `[toUnit_unique (pullback.snd f η[B]) (toUnit _)]`. Generalize the expression as in `pullback.fst f η[B] = i at hp`.

Generalize the expression as in `pullback f η[B] = Z at i hp hf`. Establish `hm : Mono i` using `⟨fun a b h => hp.hom_ext h (toUnit_unique _ _)⟩`. Establish `hi : i ≫ f = 1` using `hp.w`. Take `⟨gZ, hZ⟩` from `exists_grpObj_of_mono i (hp.lift η[G] (toUnit _) (by simp)) (hp.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by`. Rewrite using `[MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one, _root_.mul_one, Hom.one_def]))`.

Use the proof step `(hp.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))`. Use the proof step `(hp.lift_fst _ _ _) (by rw [hp.lift_fst, Hom.mul_def]; congr 1)`. Use the proof step `(by rw [hp.lift_fst, Hom.inv_def])`. Establish `hZf : IsFinite Z.hom` using `by simpa using hf`. Use `isCommMonObj_of_mono i` as an intermediate fact.

Take `⟨N, hN, hZN⟩` from `FiniteFlatKilled.main k Z hZf inferInstance`. Use `⟨N, hN, fun T x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : i ^ N = 1`. Rewrite using `[← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]`. Rewrite using `[← hp.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]`.
-/
theorem exists_pow_eq_one_of_finite_kernel {k : Type} [Field k] {G B : Over (Sp k)} [GrpObj G]
    [GrpObj B] [IsCommMonObj G] (f : G ⟶ B) [IsMonHom f]
    (hf : IsFinite (pullback.snd f (η[B] : 𝟙_ _ ⟶ B)).left) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → x ^ n = 1 := by
  have hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B] := by
    have := IsPullback.of_hasPullback f η[B]
    rwa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at this
  rw [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at hf
  generalize pullback.fst f η[B] = i at hp
  generalize pullback f η[B] = Z at i hp hf
  have hm : Mono i := ⟨fun a b h => hp.hom_ext h (toUnit_unique _ _)⟩
  have hi : i ≫ f = 1 := hp.w
  obtain ⟨gZ, hZ⟩ := exists_grpObj_of_mono i (hp.lift η[G] (toUnit _) (by simp))
    (hp.lift ((fst Z Z ≫ i) * (snd Z Z ≫ i)) (toUnit _) (by
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hi, MonObj.comp_one, MonObj.comp_one,
        _root_.mul_one, Hom.one_def]))
    (hp.lift i⁻¹ (toUnit _) (by rw [GrpObj.inv_comp, hi, inv_one, Hom.one_def]))
    (hp.lift_fst _ _ _) (by rw [hp.lift_fst, Hom.mul_def]; congr 1)
    (by rw [hp.lift_fst, Hom.inv_def])
  have hZf : IsFinite Z.hom := by simpa using hf
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main k Z hZf inferInstance
  refine ⟨N, hN, fun T x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hp.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

open RationalPoint in

/- English proof (translation)
Establish `hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B]`. Use `IsPullback.of_hasPullback f η[B]` as an intermediate fact. Rewrite `this` using `[toUnit_unique (pullback.snd f η[B]) (toUnit _)]`. Then use the resulting hypothesis. Rewrite `hf` using `[toUnit_unique (pullback.snd f η[B]) (toUnit _)]`. Generalize the expression as in `pullback.fst f η[B] = i at hp`.

Generalize the expression as in `pullback f η[B] = Z at i hp hf`. Establish `hZf : IsFinite Z.hom` using `by simpa using hf`. Establish `h1 : Finite Z.left`. Use `Z.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)` as an intermediate fact. Rewrite using `[← Set.finite_univ_iff]`.

Conclude with `this.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum k) _ _`. Establish `h2 : Finite (𝟙_ (Over (Sp k)) ⟶ Z)` using `Finite.of_injective _ pt_injective`. Use `(Set.finite_range fun z : 𝟙_ (Over (Sp k)) ⟶ Z => z ≫ i).subset fun x hx => ?_` and prove the remaining obligations. Conclude with `⟨hp.lift x (toUnit _) hx, hp.lift_fst _ _ _⟩`.
-/
theorem finite_kernel_points {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)}
    [GrpObj B] (f : G ⟶ B) (hf : IsFinite (pullback.snd f (η[B] : 𝟙_ _ ⟶ B)).left) :
    {x : 𝟙_ (Over (Sp k)) ⟶ G | x ≫ f = 1}.Finite := by
  have hp : IsPullback (pullback.fst f η[B]) (toUnit _) f η[B] := by
    have := IsPullback.of_hasPullback f η[B]
    rwa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at this
  rw [toUnit_unique (pullback.snd f η[B]) (toUnit _)] at hf
  generalize pullback.fst f η[B] = i at hp
  generalize pullback f η[B] = Z at i hp hf
  have hZf : IsFinite Z.hom := by simpa using hf
  have h1 : Finite Z.left := by
    have := Z.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)
    rw [← Set.finite_univ_iff]
    exact this.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
  have h2 : Finite (𝟙_ (Over (Sp k)) ⟶ Z) := Finite.of_injective _ pt_injective
  refine (Set.finite_range fun z : 𝟙_ (Over (Sp k)) ⟶ Z => z ≫ i).subset fun x hx => ?_
  exact ⟨hp.lift x (toUnit _) hx, hp.lift_fst _ _ _⟩

open RationalPoint in

/- English proof (translation)
Set `t : (𝟙_ (Over (Sp k)) ⟶ G) → (G ⟶ G)` to `fun a => (toUnit G ≫ a) * 𝟙 G`. Establish `ht : ∀ a y : 𝟙_ (Over (Sp k)) ⟶ G, y ≫ t a = a * y` using `fun a y => by`. Simplify using `only [t]`. Rewrite using `[MonObj.comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]`. Set `C : (𝟙_ (Over (Sp k)) ⟶ G) → Set G.left` to `fun a => (t a).left ⁻¹' Z`.

Establish `hC : ∀ a, IsClosed (C a)` using `fun a => hZ.preimage (t a).left.continuous`. Establish `hCm : ∀ a y, pt y ∈ C a ↔ a * y ∈ H` using `fun a y => by`. Rewrite using `[hH, ← ht, pt_comp]`. Both sides reduce to the same expression. Establish `hU : IsClosed (⋃ a ∈ F, C a)` using `hF.isClosed_biUnion fun a _ => hC a`.

Establish `hcov : (Set.univ : Set G.left) ⊆ ⋃ a ∈ F, C a`. Assume the negation of the conclusion as `hne`. Establish `hne' : (⋃ a ∈ F, C a)ᶜ.Nonempty`. Rewrite using `[Set.nonempty_compl]`. Conclude with `fun h => hne (h ▸ subset_rfl)`.

Establish `: JacobsonSpace G.left` using `LocallyOfFiniteType.jacobsonSpace G.hom`. Take `⟨c, hcZ, hc'⟩` from `nonempty_inter_closedPoints hne' hU.isOpen_compl.isLocallyClosed`. Take `⟨x, hx⟩` from `exists_pt_mem (X := G) (Z := {c}) hc' ⟨c, rfl⟩`. Take `⟨a, ha, hax⟩` from `hc x`. Use `hcZ ?_` and prove the remaining obligations.

Rewrite using `[← show pt x = c from hx]`. Conclude with `Set.mem_biUnion ha ((hCm a x).2 hax)`. Take `⟨D, hD, hDu⟩` from `(isIrreducible_iff_sUnion_isClosed.1 (IrreducibleSpace.isIrreducible_univ G.left)) (hF.image C).toFinset (by`. Introduce `z hz`. Take `⟨a, -, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hz`.

Conclude with `hC a) (by rwa [Set.Finite.coe_toFinset, Set.sUnion_image])`. Take `⟨a, -, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hD`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Use `(hCm a (a⁻¹ * y)).1 (hDu trivial)` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem eq_top_of_finite_cover {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G]
    [LocallyOfFiniteType G.hom] [IrreducibleSpace G.left]
    (H : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) {Z : Set G.left} (hZ : IsClosed Z)
    (hH : ∀ x, x ∈ H ↔ pt x ∈ Z) {F : Set (𝟙_ (Over (Sp k)) ⟶ G)} (hF : F.Finite)
    (hc : ∀ y, ∃ a ∈ F, a * y ∈ H) : H = ⊤ := by
  classical
  let t : (𝟙_ (Over (Sp k)) ⟶ G) → (G ⟶ G) := fun a => (toUnit G ≫ a) * 𝟙 G
  have ht : ∀ a y : 𝟙_ (Over (Sp k)) ⟶ G, y ≫ t a = a * y := fun a y => by
    simp only [t]
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp,
      Category.comp_id]
  let C : (𝟙_ (Over (Sp k)) ⟶ G) → Set G.left := fun a => (t a).left ⁻¹' Z
  have hC : ∀ a, IsClosed (C a) := fun a => hZ.preimage (t a).left.continuous
  have hCm : ∀ a y, pt y ∈ C a ↔ a * y ∈ H := fun a y => by
    rw [hH, ← ht, pt_comp]; rfl
  have hU : IsClosed (⋃ a ∈ F, C a) := hF.isClosed_biUnion fun a _ => hC a
  have hcov : (Set.univ : Set G.left) ⊆ ⋃ a ∈ F, C a := by
    by_contra hne
    have hne' : (⋃ a ∈ F, C a)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (h ▸ subset_rfl)
    have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
    obtain ⟨c, hcZ, hc'⟩ := nonempty_inter_closedPoints hne' hU.isOpen_compl.isLocallyClosed
    obtain ⟨x, hx⟩ := exists_pt_mem (X := G) (Z := {c}) hc' ⟨c, rfl⟩
    obtain ⟨a, ha, hax⟩ := hc x
    refine hcZ ?_
    rw [← show pt x = c from hx]
    exact Set.mem_biUnion ha ((hCm a x).2 hax)
  obtain ⟨D, hD, hDu⟩ := (isIrreducible_iff_sUnion_isClosed.1
    (IrreducibleSpace.isIrreducible_univ G.left)) (hF.image C).toFinset (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hz
      exact hC a) (by rwa [Set.Finite.coe_toFinset, Set.sUnion_image])
  obtain ⟨a, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hD
  rw [eq_top_iff]
  intro y _
  have := (hCm a (a⁻¹ * y)).1 (hDu trivial)
  rwa [mul_inv_cancel_left] at this

end IsogenyOntoExtension

open IsogenyOntoExtension RationalPoint in

/- English proof (translation)
Introduce `k _ _ G G' _ _ g hG hG' hg hg' hT i hi hs`. Establish `hker` using `GlobalTheory.T.isFinite_ker_of_surj_points_same_dimension k G G' g hG hG' hg hg' i hi hs`. Take `⟨hfl, hsu⟩` from `GlobalTheory.T.flat_and_surjective_of_surjective_points' k G G' hG hG' i hi hs`. Take `⟨c, s, p, q, n⟩` from `id hG`. Take `⟨c', s', p', q', n'⟩` from `id hG'`.

Take `⟨N, hN, hkill⟩` from `exists_pow_eq_one_of_finite_kernel i hker`. Establish `hqc : QuasiCompact i.left`. Establish `: QuasiCompact (i.left ≫ G'.hom)` using `by rw [Over.w]; infer_instance`. Conclude with `QuasiCompact.of_comp i.left G'.hom`. Establish `hmul : IsMonHom (𝟙 G ^ N)` using `by clear hkill hN`.

Proceed by induction on `N with`. Consider the case `zero => rw [pow_zero]`. Conclude with `Serre.isMonHom_one`. Consider the case `succ m ih => rw [pow_succ]`. Conclude with `Serre.isMonHom_mul _ _`.

Take `⟨⟨r, hr, hir⟩, -⟩` from `exists_monHom_factor_of_flat_surjective _ G G' G i (𝟙 G ^ N) hi hmul hfl hsu hqc fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hkill T x hx]`. Use `GlobalTheory.T.nonempty_torusExtension_of_surjective_points' k G' G hG hT r hr ?_` and prove the remaining obligations. Take `⟨Z, hZ, hZm⟩` from `exists_isClosed_image_of_isClosed_subgroup k G' G r hr inferInstance q' inferInstance q ⊤ Set.univ isClosed_univ (by simp)`. Set `φ : (𝟙_ (Over (Sp k)) ⟶ G') →* (𝟙_ (Over (Sp k)) ⟶ G)` to `MonoidHom.mk' (fun x => x ≫ r) fun x y => MonObj.mul_comp x y r`. Use `grpObj_geometricallyIntegral_of_smooth _ G` as an intermediate fact.

Establish `: IsIntegral G.left` using `GeometricallyIntegral.isIntegral_of_subsingleton G.hom`. Establish `htop : φ.range = ⊤`. Use `eq_top_of_finite_cover φ.range hZ (fun x => ?_) (finite_kernel_points i hker) fun y => ?_` and prove the remaining obligations. Rewrite using `[← range_left_subset_iff, ← hZm]`. Conclude with `⟨fun ⟨a, ha⟩ => ⟨a, trivial, ha⟩, fun ⟨a, _, ha⟩ => ⟨a, ha⟩⟩`.

Take `⟨z, hz⟩` from `GlobalTheory.T.torusExtension_points_divisible' k G' hT N hN (y ≫ i)`. Take `⟨x, rfl⟩` from `hs z`. Use `⟨x ^ N * y⁻¹, ?_, x ≫ i, ?_⟩` and prove the remaining obligations. Use `show _ ≫ i = 1`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, MonObj.pow_comp, hz, mul_inv_cancel]`.

Use `show (x ≫ i) ≫ r = _`. Rewrite using `[Category.assoc, hir, MonObj.comp_pow, Category.comp_id, inv_mul_cancel_right]`. Introduce `y`. Conclude with `(htop ▸ Subgroup.mem_top y : y ∈ φ.range)`.
-/
theorem torusExtension_of_surjective_of_dim_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), SmConn G → SmConn G' → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g G'.hom → Nonempty (TorusExtension G') → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → Nonempty (TorusExtension G) := by
  intro k _ _ G G' _ _ g hG hG' hg hg' hT i hi hs
  have hker := GlobalTheory.T.isFinite_ker_of_surj_points_same_dimension k G G' g hG hG' hg hg' i hi hs
  obtain ⟨hfl, hsu⟩ := GlobalTheory.T.flat_and_surjective_of_surjective_points' k G G' hG hG' i hi hs
  obtain ⟨c, s, p, q, n⟩ := id hG
  obtain ⟨c', s', p', q', n'⟩ := id hG'
  obtain ⟨N, hN, hkill⟩ := exists_pow_eq_one_of_finite_kernel i hker
  have hqc : QuasiCompact i.left := by
    have : QuasiCompact (i.left ≫ G'.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp i.left G'.hom
  have hmul : IsMonHom (𝟙 G ^ N) := by
    clear hkill hN
    induction N with
    | zero => rw [pow_zero]; exact Serre.isMonHom_one
    | succ m ih => rw [pow_succ]; exact Serre.isMonHom_mul _ _
  obtain ⟨⟨r, hr, hir⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ G G' G i (𝟙 G ^ N) hi hmul
    hfl hsu hqc fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hkill T x hx]
  refine GlobalTheory.T.nonempty_torusExtension_of_surjective_points' k G' G hG hT r hr ?_
  obtain ⟨Z, hZ, hZm⟩ := exists_isClosed_image_of_isClosed_subgroup k G' G r hr inferInstance q'
    inferInstance q ⊤ Set.univ isClosed_univ (by simp)
  let φ : (𝟙_ (Over (Sp k)) ⟶ G') →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ r) fun x y => MonObj.mul_comp x y r
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have htop : φ.range = ⊤ := by
    refine eq_top_of_finite_cover φ.range hZ (fun x => ?_) (finite_kernel_points i hker) fun y => ?_
    · rw [← range_left_subset_iff, ← hZm]
      exact ⟨fun ⟨a, ha⟩ => ⟨a, trivial, ha⟩, fun ⟨a, _, ha⟩ => ⟨a, ha⟩⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.T.torusExtension_points_divisible' k G' hT N hN (y ≫ i)
      obtain ⟨x, rfl⟩ := hs z
      refine ⟨x ^ N * y⁻¹, ?_, x ≫ i, ?_⟩
      · show _ ≫ i = 1
        rw [MonObj.mul_comp, GrpObj.inv_comp, MonObj.pow_comp, hz, mul_inv_cancel]
      · show (x ≫ i) ≫ r = _
        rw [Category.assoc, hir, MonObj.comp_pow, Category.comp_id, inv_mul_cancel_right]
  intro y
  exact (htop ▸ Subgroup.mem_top y : y ∈ φ.range)

end GlobalTheory
