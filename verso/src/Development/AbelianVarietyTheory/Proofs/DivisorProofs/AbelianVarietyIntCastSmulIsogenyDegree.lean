import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulIsogeny

/- English proof (translation)
Use `ext1`. Simplify using `only [bcMap, mk_hom, zsmul_hom, id_hom, zpow_natCast]`. Conclude with `GlobalTheory.MulFiniteFlat.pullback_map_mulA _ A.X n`.
-/
theorem bcMap_natCast_smul_id (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (n : ℕ) :
    bcMap L ((n : ℤ) • 𝟙 A) = (n : ℤ) • 𝟙 (baseChange L A) := by
  ext1
  simp only [bcMap, mk_hom, zsmul_hom, id_hom, zpow_natCast]
  exact GlobalTheory.MulFiniteFlat.pullback_map_mulA _ A.X n

/- English proof (translation)
Establish `e : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X ^ n : A.X ⟶ A.X)`. Rewrite using `[zsmul_hom, id_hom, zpow_natCast]`. Take `⟨hfin, hfl⟩` from `GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp k) A.X A.ab n (Nat.one_le_iff_ne_zero.2 hn)`. Establish `hmon : IsMonHom (𝟙 A.X ^ n : A.X ⟶ A.X)` using `e ▸ inferInstanceAs (IsMonHom ((n : ℤ) • 𝟙 A).hom)`. Establish `hsurj : Surjective (𝟙 A.X ^ n : A.X ⟶ A.X).left` using `(GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A.X A.ab _ inferInstance hfin).2`.

Establish `hiso : IsIsogeny ((n : ℤ) • 𝟙 A)`. Unfold `IsIsogeny`. Rewrite using `[e]`. Conclude with `⟨hfin, hsurj⟩`. Use `⟨hiso, ?_⟩` and prove the remaining obligations.

Unfold `deg`. Rewrite using `[if_pos hiso, e]`. Conclude with `GlobalTheory.UU.MulDegree.finrank_mul_eq k A.X A.dim n A.ab A.smooth hn _`.
-/
theorem natCast_algClosed (k : Type) [Field k] [IsAlgClosed k] (A : AbVar k) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  have e : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X ^ n : A.X ⟶ A.X) := by
    rw [zsmul_hom, id_hom, zpow_natCast]
  obtain ⟨hfin, hfl⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp k) A.X A.ab n (Nat.one_le_iff_ne_zero.2 hn)
  have hmon : IsMonHom (𝟙 A.X ^ n : A.X ⟶ A.X) := e ▸ inferInstanceAs (IsMonHom ((n : ℤ) • 𝟙 A).hom)
  have hsurj : Surjective (𝟙 A.X ^ n : A.X ⟶ A.X).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A.X A.ab _ inferInstance hfin).2
  have hiso : IsIsogeny ((n : ℤ) • 𝟙 A) := by
    unfold IsIsogeny
    rw [e]
    exact ⟨hfin, hsurj⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso, e]
  exact GlobalTheory.UU.MulDegree.finrank_mul_eq k A.X A.dim n A.ab A.smooth hn _

/- English proof (translation)
Take `⟨h1, h2⟩` from `natCast_algClosed (AlgebraicClosure K) (baseChange (AlgebraicClosure K) A) n hn`. Take `⟨e1, e2⟩` from `GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq K (AlgebraicClosure K) A A ((n : ℤ) • 𝟙 A)`. Rewrite `e1`, `e2` using `[bcMap_natCast_smul_id]`. Conclude with `⟨e1.1 h1, e2.symm.trans h2⟩`.
-/
theorem natCast (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  obtain ⟨h1, h2⟩ := natCast_algClosed (AlgebraicClosure K) (baseChange (AlgebraicClosure K) A) n hn
  obtain ⟨e1, e2⟩ := GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq K (AlgebraicClosure K) A A ((n : ℤ) • 𝟙 A)
  rw [bcMap_natCast_smul_id] at e1 e2
  exact ⟨e1.1 h1, e2.symm.trans h2⟩

/- English proof (translation)
Establish `hsq : (-𝟙 A) ≫ (-𝟙 A) = 𝟙 A` using `by simp`. Establish `hsq' : (-𝟙 A).hom.left ≫ (-𝟙 A).hom.left = 𝟙 A.X.left`. Rewrite using `[← Over.comp_left, ← comp_hom, hsq, id_hom, Over.id_left]`. Use `haveI : IsIso (-𝟙 A).hom.left := ⟨⟨(-𝟙 A).hom.left, hsq', hsq'⟩⟩`. Establish `hiso : IsIsogeny (-𝟙 A)` using `⟨inferInstance, inferInstance⟩`.

Use `⟨hiso, ?_⟩` and prove the remaining obligations. Unfold `deg`. Rewrite using `[if_pos hiso]`. Conclude with `congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _`.
-/
theorem neg_one (K : Type) [Field K] (A : AbVar K) : IsIsogeny (-𝟙 A) ∧ deg (-𝟙 A) = 1 := by
  have hsq : (-𝟙 A) ≫ (-𝟙 A) = 𝟙 A := by simp
  have hsq' : (-𝟙 A).hom.left ≫ (-𝟙 A).hom.left = 𝟙 A.X.left := by
    rw [← Over.comp_left, ← comp_hom, hsq, id_hom, Over.id_left]
  haveI : IsIso (-𝟙 A).hom.left := ⟨⟨(-𝟙 A).hom.left, hsq', hsq'⟩⟩
  have hiso : IsIsogeny (-𝟙 A) := ⟨inferInstance, inferInstance⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

/- English proof (translation)
Introduce `K _ A n hn`. Break down `Int.natAbs_eq n with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)`. Establish `e : n • 𝟙 A = ((n.natAbs : ℤ) • 𝟙 A) ≫ (-𝟙 A)`.

Rewrite using `[Preadditive.comp_neg, Category.comp_id, ← neg_smul, ← h]`. Take `⟨h1, h2⟩` from `natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)`. Take `⟨h3, h4⟩` from `neg_one K A`. Take `⟨h5, h6⟩` from `GlobalTheory.T.isogeny_comp_and_degree_mul K A A A _ _ h1 h3`. Rewrite using `[e]`.

Conclude with `⟨h5, by rw [h6, h2, h4, _root_.mul_one]⟩`.
-/
theorem mul_isogeny : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  intro K _ A n hn
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    exact natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
  · have e : n • 𝟙 A = ((n.natAbs : ℤ) • 𝟙 A) ≫ (-𝟙 A) := by
      rw [Preadditive.comp_neg, Category.comp_id, ← neg_smul, ← h]
    obtain ⟨h1, h2⟩ := natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
    obtain ⟨h3, h4⟩ := neg_one K A
    obtain ⟨h5, h6⟩ := GlobalTheory.T.isogeny_comp_and_degree_mul K A A A _ _ h1 h3
    rw [e]
    exact ⟨h5, by rw [h6, h2, h4, _root_.mul_one]⟩

end GlobalTheory.MulIsogeny
