import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforwardStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.VertForm

namespace GlobalTheory.NefDescent

/- English proof (translation)
Introduce `Z i _ _ κ _ _ _ _ hdim`. Use `letI : Algebra (ZMod l) κ := ZMod.algebra κ l`. Use `letI : Algebra (ZMod l) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ)).toAlgebra`. Use `haveI : IsScalarTower (ZMod l) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl`. Establish `h1` using `h Z i hdim`.

Establish `e` using `GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod l) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)`. Rewrite `h1`, the goal using `[topSelf_def]`. Rewrite `h1` using `[e]`. Use `haveI : Module.Finite (ZMod l) κ := Module.Finite.of_finite`. Establish `hpos : (0 : ℤ) < (Module.finrank (ZMod l) κ : ℤ)`.

Conclude with `Module.finrank_pos` after adjusting the coercions. Conclude with `(mul_nonneg_iff_of_pos_left hpos).mp h1`.
-/
theorem nefOver_of_primeField {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (l : ℕ)
    [Fact l.Prime]
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod l) (L.B.pull i) 1) :
    NefOver L l := by
  intro Z i _ _ κ _ _ _ _ hdim
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ)).toAlgebra
  haveI : IsScalarTower (ZMod l) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod l) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod l) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod l) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

/- English proof (translation)
Introduce `k _ _ X Y p q hp hq π hπ hsurj L l hl hL`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Use `nefOver_of_primeField L l ?_` and prove the remaining obligations. Introduce `Z i _ _ _ hd`. Establish `: IsNoetherianRing k` using `IsNoetherianRing.of_finite ℤ k`.

Establish `: IsProper p` using `(isProper_and_exists_isAmpleLB_of_isProjOver hp).1`. Establish `: IsProper q` using `(isProper_and_exists_isAmpleLB_of_isProjOver hq).1`. Establish `: IsProper (π ≫ p)` using `by rw [hπ]; infer_instance`. Establish `: IsProper π` using `IsProper.of_comp π p`. Establish `: Surjective π` using `⟨hsurj⟩`.

Establish `: IsNoetherian Y` using `isNoetherian_of_isProjOver hq`. Establish `: IsNoetherian X` using `isNoetherian_of_isProjOver hp`. Establish `: IsNoetherian Z`. Use `LocallyOfFiniteType.isLocallyNoetherian i` as an intermediate fact. Use `QuasiCompact.compactSpace_of_compactSpace i` as an intermediate fact.

Conclude with `{}`. Set `g` to `pullback.snd π i`. Establish `: IsProper g` using `inferInstance`. Establish `: Surjective g` using `inferInstance`. Take `⟨w, hw, hdeg⟩` from `fibre_point _ Z g (genericPoint Z) (g.surjective _)`.

Set `C : Closeds (pullback π i : Scheme.{0})` to `⟨closure {w}, isClosed_closure⟩`. Establish `: IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme` using `isIntegral_red isIrreducible_singleton.closure`. Establish `hgen` using `red_genericPoint _ w C rfl`. Set `f` to `redι C ≫ g`. Set `i'` to `redι C ≫ pullback.fst π i`.

Establish `hη : f (genericPoint _) = genericPoint Z`. Simplify using `only [f, Scheme.Hom.comp_apply, hgen, hw]`. Establish `hdeg' : 0 < f.residueDegree (genericPoint _)`. Simplify using `only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]`. Conclude with `hdeg`.

Establish `hd'` using `dim_eq_one _ Z f hd hη hdeg'`. Establish `: IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme`. Use `LocallyOfFiniteType.isLocallyNoetherian i'` as an intermediate fact. Use `QuasiCompact.compactSpace_of_compactSpace i'` as an intermediate fact. Conclude with `{}`.

Establish `: IsFinite f` using `isFinite_of_dim _ Z f hd' hd hη`. Use `letI : Algebra (ZMod l) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod l) f`. Establish `h1` using `hL _ i' (ZMod l) hd'`. Establish `hN : (L.B.pull i).IsLB` using `LB.isLB_pull L.isLB i`. Establish `hcomm : i' ≫ π = f ≫ i` using `by simp only [i', f, g, Category.assoc, pullback.condition]`.

Establish `e1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1`. Rewrite using `[topSelf_def, topSelf_def]`. Use `interNum_congr_cls (ZMod l) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i') (fun _ => LB.isLB_pull hN f) fun _ => ?_` and prove the remaining obligations. Use `show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))`. Rewrite using `[← pull_comp, ← pull_comp, hcomm]`.

Establish `e2 : topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1 = interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i)` using `(interNumOn_const_eq_topSelf (k := ZMod l) (fun _ => rfl) hN 1).symm`. Establish `e3 : interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod l) f ![L.B.pull i]` using `congrArg _ (funext fun j => by fin_cases j; rfl)`. Establish `hproj : IsProjOver (strHom (ZMod l) Z)`. Establish `: IsFinite (spMap (Int.castRingHom k))`. Rewrite using `[spMap, IsFinite.SpecMap_iff]`.

Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k)` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)))` using `by rw [e]; infer_instance`. Establish `: IsProper (strHom (ZMod l) Z)` using `IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))`. Conclude with `ProperCurve.isProjOver_of_isProper _ hd`.

Establish `e4` using `GlobalTheory.T.intersection_number_finite_pushforward (ZMod l) Z _ f hproj hd hη (L.B.pull i) hN`. Establish `e5 : interNum (ZMod l) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod l) (L.B.pull i) 1`. Rewrite using `[topSelf_def]`. Conclude with `congrArg _ (funext fun j => by fin_cases j; rfl)`. Establish `hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod l) (L.B.pull i) 1`.

Rewrite using `[← e5, ← e4, ← e3, ← e2, ← e1]`. Conclude with `h1`. Conclude with `nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')`.
-/
theorem nefOver_of_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p) (l : ℕ), l.Prime → NefOver (L.pull π hπ) l → NefOver L l := by
  intro k _ _ X Y p q hp hq π hπ hsurj L l hl hL
  haveI : Fact l.Prime := ⟨hl⟩
  refine nefOver_of_primeField L l ?_
  intro Z i _ _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod l) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod l) f
  have h1 := hL _ i' (ZMod l) hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod l) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1 = interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod l) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod l) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod l) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod l) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod l) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

end GlobalTheory.NefDescent

end
