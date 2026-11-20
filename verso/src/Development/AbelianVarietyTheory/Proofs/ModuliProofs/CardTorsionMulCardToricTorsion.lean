import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SemiAbTorsionCount

/- English proof (translation)
Set `K : Subgroup G` to `(powMonoidHom n : G →* G).ker`. Set `f : K →* B` to `q.comp K.subtype`. Establish `h0 : Nat.card {x : G // x ^ n = 1} = Nat.card K` using `rfl`. Establish `h1 : Nat.card {b : B // b ^ n = 1} = Nat.card f.range`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun b => ⟨fun hb => ?_, ?_⟩)` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `hq b`. Take `⟨t, ht⟩` from `(hk (x ^ n)).1 (by rw [map_pow, hb])`. Take `⟨s, rfl⟩` from `hT t`. Use `⟨⟨x / i s, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x / i s) ^ n = 1`.

Rewrite using `[div_pow, ← map_pow, ht, div_self']`. Express the relevant statement in the definitionally equal form `q (x / i s) = q x`. Rewrite using `[map_div, (hk _).2 ⟨s, rfl⟩, div_one]`. Introduce and unpack `⟨x, rfl⟩`. Establish `hx : x.1 ^ n = 1` using `x.2`.

Express the relevant statement in the definitionally equal form `q x.1 ^ n = 1`. Rewrite using `[← map_pow, hx, map_one]`. Establish `h2 : Nat.card {t : T // t ^ n = 1} = Nat.card f.ker`. Use `Nat.card_eq_of_bijective (fun t => ⟨⟨i t.1, ?_⟩, (hk _).2 ⟨t.1, rfl⟩⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `i t.1 ^ n = 1`.

Rewrite using `[← map_pow, t.2, map_one]`. Introduce `a b h`. Conclude with `Subtype.ext (hi (congrArg (fun z : f.ker => z.1.1) h))`. Introduce and unpack `⟨⟨x, hx⟩, hx'⟩`. Take `⟨t, rfl⟩` from `(hk x).1 hx'`.

Establish `hx₁ : i t ^ n = 1` using `hx`. Conclude with `⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩`. Rewrite using `[h0, h1, h2, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]`.
-/
theorem card_pow_eq_one_of_extension {T G B : Type} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 ↔ ∃ t, i t = x)
    (hq : Function.Surjective q) (n : ℕ) (hT : ∀ t : T, ∃ s : T, s ^ n = t) :
    Nat.card {x : G // x ^ n = 1} =
      Nat.card {b : B // b ^ n = 1} * Nat.card {t : T // t ^ n = 1} := by
  let K : Subgroup G := (powMonoidHom n : G →* G).ker
  let f : K →* B := q.comp K.subtype
  have h0 : Nat.card {x : G // x ^ n = 1} = Nat.card K := rfl
  have h1 : Nat.card {b : B // b ^ n = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ⟨fun hb => ?_, ?_⟩)
    · obtain ⟨x, rfl⟩ := hq b
      obtain ⟨t, ht⟩ := (hk (x ^ n)).1 (by rw [map_pow, hb])
      obtain ⟨s, rfl⟩ := hT t
      refine ⟨⟨x / i s, ?_⟩, ?_⟩
      · change (x / i s) ^ n = 1
        rw [div_pow, ← map_pow, ht, div_self']
      · change q (x / i s) = q x
        rw [map_div, (hk _).2 ⟨s, rfl⟩, div_one]
    · rintro ⟨x, rfl⟩
      have hx : x.1 ^ n = 1 := x.2
      change q x.1 ^ n = 1
      rw [← map_pow, hx, map_one]
  have h2 : Nat.card {t : T // t ^ n = 1} = Nat.card f.ker := by
    refine Nat.card_eq_of_bijective (fun t => ⟨⟨i t.1, ?_⟩, (hk _).2 ⟨t.1, rfl⟩⟩) ⟨?_, ?_⟩
    · change i t.1 ^ n = 1
      rw [← map_pow, t.2, map_one]
    · intro a b h
      exact Subtype.ext (hi (congrArg (fun z : f.ker => z.1.1) h))
    · rintro ⟨⟨x, hx⟩, hx'⟩
      obtain ⟨t, rfl⟩ := (hk x).1 hx'
      have hx₁ : i t ^ n = 1 := hx
      exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
  rw [h0, h1, h2, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

/- English proof (translation)
Set `b` to `Module.finBasis ℤ X`. Set `ev : (Multiplicative X →* M) →* (Fin (Module.finrank ℤ X) → M)` to `{ toFun := fun t j => t (Multiplicative.ofAdd (b j)) map_one' := rfl map_mul' := fun _ _ => rfl }`. Use `⟨MulEquiv.ofBijective ev ⟨fun s t h => ?_, fun v => ?_⟩⟩` and prove the remaining obligations. Establish `: (MonoidHom.toAdditiveRight s).toIntLinearMap = (MonoidHom.toAdditiveRight t).toIntLinearMap` using `b.ext fun j => congrArg Additive.ofMul (congrFun h j)`. Use extensionality with `x`.

Conclude with `congrArg Additive.toMul (DFunLike.congr_fun this x)`. Use `⟨AddMonoidHom.toMultiplicativeLeft (b.constr ℤ (fun j => Additive.ofMul (v j))).toAddMonoidHom, funext fun j => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Additive.toMul (b.constr_basis ℤ (fun j => Additive.ofMul (v j)) j)`.
-/
theorem nonempty_hom_mulEquiv_pi (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (M : Type) [CommGroup M] :
    Nonempty ((Multiplicative X →* M) ≃* (Fin (Module.finrank ℤ X) → M)) := by
  let b := Module.finBasis ℤ X
  let ev : (Multiplicative X →* M) →* (Fin (Module.finrank ℤ X) → M) :=
    { toFun := fun t j => t (Multiplicative.ofAdd (b j))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨MulEquiv.ofBijective ev ⟨fun s t h => ?_, fun v => ?_⟩⟩
  · have : (MonoidHom.toAdditiveRight s).toIntLinearMap = (MonoidHom.toAdditiveRight t).toIntLinearMap :=
      b.ext fun j => congrArg Additive.ofMul (congrFun h j)
    ext x
    exact congrArg Additive.toMul (DFunLike.congr_fun this x)
  · refine ⟨AddMonoidHom.toMultiplicativeLeft
      (b.constr ℤ (fun j => Additive.ofMul (v j))).toAddMonoidHom, funext fun j => ?_⟩
    exact congrArg Additive.toMul (b.constr_basis ℤ (fun j => Additive.ofMul (v j)) j)

/- English proof (translation)
Take `⟨e₂⟩` from `nonempty_hom_mulEquiv_pi X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ`. Set `e₃ : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k` to `(Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv`. Conclude with `⟨((splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))).trans e₂).trans (MulEquiv.piCongrRight fun _ => Units.mapEquiv e₃.toMulEquiv)⟩`.
-/
theorem nonempty_torus_points_mulEquiv (k : Type) [Field k] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] :
    Nonempty ((𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) ≃* (Fin (Module.finrank ℤ X) → kˣ)) := by
  obtain ⟨e₂⟩ := nonempty_hom_mulEquiv_pi X Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ
  let e₃ : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  exact ⟨((splitTorusPointsEquiv (Sp k) X (𝟙_ (Over (Sp k)))).trans e₂).trans
    (MulEquiv.piCongrRight fun _ => Units.mapEquiv e₃.toMulEquiv)⟩

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `by rintro rfl; exact hN Nat.cast_zero`. Use `haveI : NeZero N := ⟨hN0⟩`. Use `haveI : NeZero (N : k) := ⟨hN⟩`. Prove the components needed by the constructor for the conclusion. Introduce `x`.

Establish `: ∀ u : kˣ, ∃ s : kˣ, s ^ N = u` using `fun u => by`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (u : k) (Nat.pos_of_ne_zero hN0)`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hN0]`.

Conclude with `u.ne_zero hz.symm`. Conclude with `⟨Units.mk0 z hz0, Units.ext hz⟩`. Use `choose r hr using this`. Use `⟨e.symm fun j => r (e x j), e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, e.apply_symm_apply]`.

Conclude with `funext fun j => hr _`. Establish `h1 : Nat.card {x : T // x ^ N = 1} = Nat.card (Fin t → rootsOfUnity N k)`. Use `Nat.card_congr ((e.toEquiv.subtypeEquiv (q := fun v => ∀ j, v j ∈ rootsOfUnity N k) fun x => ?_).trans Equiv.subtypePiEquivPi)` and prove the remaining obligations. Rewrite using `[← e.map_eq_one_iff, map_pow, funext_iff]`. Both sides reduce to the same expression.

Rewrite using `[h1, Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card, Fintype.card_fin]`.
-/
theorem divisible_and_card {k : Type} [Field k] [IsAlgClosed k] {T : Type} [Group T] {t : ℕ}
    (e : T ≃* (Fin t → kˣ)) (N : ℕ) (hN : (N : k) ≠ 0) :
    (∀ x : T, ∃ s : T, s ^ N = x) ∧ Nat.card {x : T // x ^ N = 1} = N ^ t := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  haveI : NeZero N := ⟨hN0⟩
  haveI : NeZero (N : k) := ⟨hN⟩
  constructor
  · intro x
    have : ∀ u : kˣ, ∃ s : kˣ, s ^ N = u := fun u => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) (Nat.pos_of_ne_zero hN0)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow hN0] at hz
        exact u.ne_zero hz.symm
      exact ⟨Units.mk0 z hz0, Units.ext hz⟩
    choose r hr using this
    refine ⟨e.symm fun j => r (e x j), e.injective ?_⟩
    rw [map_pow, e.apply_symm_apply]
    exact funext fun j => hr _
  · have h1 : Nat.card {x : T // x ^ N = 1} = Nat.card (Fin t → rootsOfUnity N k) := by
      refine Nat.card_congr ((e.toEquiv.subtypeEquiv (q := fun v => ∀ j, v j ∈ rootsOfUnity N k)
        fun x => ?_).trans Equiv.subtypePiEquivPi)
      rw [← e.map_eq_one_iff, map_pow, funext_iff]
      rfl
    rw [h1, Nat.card_fun, HasEnoughRootsOfUnity.natCard_rootsOfUnity, Nat.card_eq_fintype_card,
      Fintype.card_fin]

/- English proof (translation)
Use `letI := E.addCommGroup`. Use `letI := E.grpB`. Use `E.free` as an intermediate fact. Use `E.finite` as an intermediate fact. Take `⟨y⟩ : Nonempty ↥(Sp k)` from `inferInstance`.

Use `E.i_hom` as an intermediate fact. Use `(GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1` as an intermediate fact. Take `⟨m, W, hW, d₁⟩` from `H1.exists_dim E.q.left (eSec G y)`. Establish `g₂ : m = Module.finrank ℤ E.X` using `H1.dim_base (E.isKernel.map (Over.forget _)) d₁ (H1.torus_dim (Sp k) E.X) (eSec _ y) ((congrArg (fun f => f.left y ∈ W) (IsMonHom.one_hom E.i)).mpr hW)`. Establish `d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom)`.

Rewrite using `[← Over.w E.q, ← Category.assoc]`. Use `infer_instance`. Establish `d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom)` using `inferInstance`. Use `H1.dim_unique _ d₂ d₃ ⟨_, hW⟩` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem dim_eq {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g g' : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' E.B.hom) :
    g = g' + @Module.finrank ℤ E.X _ E.addCommGroup.toAddCommMonoid _ := by
  letI := E.addCommGroup
  letI := E.grpB
  have := E.free
  have := E.finite
  obtain ⟨y⟩ : Nonempty ↥(Sp k) := inferInstance
  have := E.i_hom
  have := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim E.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ E.X :=
    H1.dim_base (E.isKernel.map (Over.forget _)) d₁ (H1.torus_dim (Sp k) E.X) (eSec _ y)
      ((congrArg (fun f => f.left y ∈ W) (IsMonHom.one_hom E.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w E.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end SemiAbTorsionCount

open SemiAbTorsionCount

/- English proof (translation)
Introduce `k _ _ G _ E g N hG dG hN`. Use `letI := E.addCommGroup`. Use `letI := E.grpB`. Use `haveI := E.free`. Use `haveI := E.finite`.

Use `haveI := E.q_hom`. Use `haveI := E.i_hom`. Use `haveI := hG.comm`. Use `haveI := E.q_surjective`. Use `haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1`.

Establish `hk` using `E.isKernel`. Take `⟨g', dB⟩` from `GlobalTheory.AbelianDim.exists_relDim k E.B E.isAbelian`. Establish `hg` using `dim_eq G E g g' dG dB`. Take `⟨e⟩` from `nonempty_torus_points_mulEquiv k E.X`. Take `⟨hdiv, hcard⟩` from `divisible_and_card e N hN`.

Establish `hB` using `GlobalTheory.T.card_torsion_eq_pow_two_mul_dim k E.B g' N E.isAbelian dB hN`. Set `i` to `IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))`. Establish `hi : Function.Injective i` using `fun a b h => hk.hom_ext h (toUnit_unique _ _)`. Establish `h1` using `card_pow_eq_one_of_extension i (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) hi (fun x => ⟨fun hx => ?_, ?_⟩) (fun x => ?_) N hdiv`. Establish `h2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} = N ^ Module.finrank ℤ E.X`.

Rewrite using `[← hcard]`. Use `(Nat.card_eq_of_bijective (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm` and prove the remaining obligations. Introduce `a b h`. Conclude with `Subtype.ext (hi (congrArg Subtype.val h))`. Introduce and unpack `⟨x, hx, t, rfl⟩`.

Establish `hx₁ : i t ^ N = 1` using `hx`. Conclude with `⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩`. Rewrite using `[h2, h1, hB, hcard, hg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx' : x ≫ E.q = 1` using `hx`.

Conclude with `⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩`. Introduce and unpack `⟨t, rfl⟩`. Express the relevant statement in the definitionally equal form `(t ≫ E.i) ≫ E.q = 1`. Rewrite using `[Category.assoc, hk.w, ← Category.assoc, Hom.one_def]`. Use `congr 1`.

Conclude with `toUnit_unique _ _`. Take `⟨p, hp⟩` from `GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := k) E.q.left x.left`. Use `⟨Over.homMk p ?_, Over.OverMorphism.ext hp.symm⟩` and prove the remaining obligations. Rewrite using `[← Over.w E.q, ← Category.assoc, ← hp]`. Conclude with `Over.w x`.
-/
theorem card_torsion_mul_card_toric_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (T : TorusExtension G) (g N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (N : k) ≠ 0 → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1} * Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ T.i} = N ^ (2 * g) := by
  intro k _ _ G _ E g N hG dG hN
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := hG.comm
  haveI := E.q_surjective
  haveI := (GlobalTheory.torusExtension_smooth_geometricallyConnected G E).1
  have hk := E.isKernel
  obtain ⟨g', dB⟩ := GlobalTheory.AbelianDim.exists_relDim k E.B E.isAbelian
  have hg := dim_eq G E g g' dG dB
  obtain ⟨e⟩ := nonempty_torus_points_mulEquiv k E.X
  obtain ⟨hdiv, hcard⟩ := divisible_and_card e N hN
  have hB := GlobalTheory.T.card_torsion_eq_pow_two_mul_dim k E.B g' N E.isAbelian dB hN
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have h1 := card_pow_eq_one_of_extension i (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))) hi
    (fun x => ⟨fun hx => ?_, ?_⟩) (fun x => ?_) N hdiv
  · have h2 : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ N = 1 ∧ ∃ y, x = y ≫ E.i} =
        N ^ Module.finrank ℤ E.X := by
      rw [← hcard]
      refine (Nat.card_eq_of_bijective
        (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩).symm
      · intro a b h
        exact Subtype.ext (hi (congrArg Subtype.val h))
      · rintro ⟨x, hx, t, rfl⟩
        have hx₁ : i t ^ N = 1 := hx
        exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩
    rw [h2, h1, hB, hcard, hg]
    ring
  · have hx' : x ≫ E.q = 1 := hx
    exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
  · rintro ⟨t, rfl⟩
    change (t ≫ E.i) ≫ E.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  · obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := k) E.q.left x.left
    refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp.symm⟩
    rw [← Over.w E.q, ← Category.assoc, ← hp]
    exact Over.w x

end GlobalTheory
