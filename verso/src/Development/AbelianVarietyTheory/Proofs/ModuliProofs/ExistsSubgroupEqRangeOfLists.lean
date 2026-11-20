import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.ListedSubgroup

variable {S : Scheme.{0}}

/- English proof (translation)
Use `isClosedImmersion_of_section_of_isSeparated f s hs` as an intermediate fact. Establish `hsurj : Surjective (pullback.fst z s)`. Use `⟨fun y => ?_⟩` and prove the remaining obligations. Take `rfl : y = q` from `Subsingleton.elim _ _`. Establish `h : y ∈ Set.range (pullback.fst z s)`.

Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `hz`. Conclude with `h`. Establish `: IsIso (pullback.fst z s)` using `isIso_of_isClosedImmersion_of_surjective _`. Rewrite using `[← cancel_epi (pullback.fst z s)]`.

Simplify using `only [pullback.condition_assoc, pullback.condition, Category.assoc, reassoc_of% hs]`.
-/
theorem eq_comp_section {X : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {k : Type} [Field k] (z : Sp k ⟶ X) (q : Sp k) (hz : z q ∈ Set.range s) : z = (z ≫ f) ≫ s := by
  have := isClosedImmersion_of_section_of_isSeparated f s hs
  have hsurj : Surjective (pullback.fst z s) := by
    refine ⟨fun y => ?_⟩
    obtain rfl : y = q := Subsingleton.elim _ _
    have h : y ∈ Set.range (pullback.fst z s) := by
      rw [Scheme.Pullback.range_fst]
      exact hz
    exact h
  have : IsIso (pullback.fst z s) := isIso_of_isClosedImmersion_of_surjective _
  rw [← cancel_epi (pullback.fst z s)]
  simp only [pullback.condition_assoc, pullback.condition, Category.assoc, reassoc_of% hs]

/- English proof (translation)
Take `⟨-, hfin, het⟩` from `GrpTangent.finiteEtale_mulN_torsion G hN`. Take `⟨a', rfl, -⟩` from `LatticeTorsion.existsUnique_torsion G N a ha`. Take `⟨b', rfl, -⟩` from `LatticeTorsion.existsUnique_torsion G N b hb`. Establish `hx : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) = (toUnit (Over.mk x) ≫ b') ≫ torsion.ι G N`. Rewrite using `[Category.assoc, Category.assoc]`.

Conclude with `Over.OverMorphism.ext h`. Establish `hpow : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) ^ N = 1`. Rewrite using `[Category.assoc, ← MonObj.comp_pow, ha, MonObj.comp_one]`. Establish `hab : toUnit (Over.mk x) ≫ a' = toUnit (Over.mk x) ≫ b'` using `(LatticeTorsion.existsUnique_torsion G N _ hpow).unique rfl hx.symm`. Establish `: a' = b'` using `Over.OverMorphism.ext (eq_of_preconnected_of_unramified (T := S) (torsion G N).hom ((Over.w a').trans (Over.w b').symm) x (congrArg CommaMorphism.left hab))`.

Rewrite using `[this]`.
-/
theorem section_eq [ConnectedSpace S] (G : Over S) [GrpObj G] [IsAbelianScheme G] {N : ℕ}
    (hN : IsUnit (N : Γ(S, ⊤))) {a b : 𝟙_ (Over S) ⟶ G} (ha : a ^ N = 1) (hb : b ^ N = 1)
    {k : Type} [Field k] (x : Sp k ⟶ S) (h : x ≫ a.left = x ≫ b.left) : a = b := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  obtain ⟨a', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N a ha
  obtain ⟨b', rfl, -⟩ := LatticeTorsion.existsUnique_torsion G N b hb
  have hx : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) = (toUnit (Over.mk x) ≫ b') ≫ torsion.ι G N := by
    rw [Category.assoc, Category.assoc]
    exact Over.OverMorphism.ext h
  have hpow : ((toUnit (Over.mk x) ≫ a') ≫ torsion.ι G N) ^ N = 1 := by
    rw [Category.assoc, ← MonObj.comp_pow, ha, MonObj.comp_one]
  have hab : toUnit (Over.mk x) ≫ a' = toUnit (Over.mk x) ≫ b' :=
    (LatticeTorsion.existsUnique_torsion G N _ hpow).unique rfl hx.symm
  have : a' = b' := Over.OverMorphism.ext
    (eq_of_preconnected_of_unramified (T := S) (torsion G N).hom ((Over.w a').trans (Over.w b').symm) x
      (congrArg CommaMorphism.left hab))
  rw [this]

end GlobalTheory.HkFam.ListedSubgroup

namespace GlobalTheory.HkFam

open ListedSubgroup in

/- English proof (translation)
Introduce `E _ _ _ H D 𝔓 p i n S _ t σ K hpr hp ⟨hσ, hK, _⟩ hH`. Establish `hab : IsAbelianScheme t.G` using `⟨t.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩`. Establish `hN : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤))`. Rewrite using `[Nat.cast_pow]`. Conclude with `hp.pow 2`.

Take `⟨s₀⟩ : Nonempty S` from `inferInstance`. Set `k : Type` to `AlgebraicClosure (S.residueField s₀)`. Set `x : Sp k ⟶ S` to `Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀`. Take `⟨C, hC, -⟩` from `hH k x`. Take `⟨q⟩ : Nonempty (Sp k)` from `inferInstance`.

Establish `hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C` using `fun j => by`. Rewrite using `[hC, hK]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩`. Establish `key : ∀ a : 𝟙_ (Over S) ⟶ t.G, a ^ (p ^ 2) = 1 → toUnit (Over.mk x) ≫ a ∈ C → a ∈ Set.range σ`.

Introduce `a ha h`. Rewrite `h` using `[hC, hK]`. Take `⟨j, hj⟩` from `Set.mem_iUnion.1 (h ⟨q, rfl⟩)`. Establish `h1` using `eq_comp_section t.G.hom (σ j).left (Over.w (σ j)) _ q hj`. Rewrite `h1` using `[Over.w (toUnit (Over.mk x) ≫ a)]`.

Conclude with `⟨j, (section_eq t.G hN ha (hσ j) x h1).symm⟩`. Use `⟨{ carrier := Set.range σ, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ _ ⟨j, rfl⟩ ⟨j', rfl⟩`. Use `key _ (by rw [mul_pow, hσ, hσ, _root_.one_mul]) ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul]`.

Conclude with `C.mul_mem (hmem j) (hmem j')`. Use `key _ (one_pow _) ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_one]`. Conclude with `C.one_mem`. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `key _ (by rw [inv_pow, hσ, inv_one]) ?_` and prove the remaining obligations. Rewrite using `[GrpObj.comp_inv]`. Conclude with `C.inv_mem (hmem j)`.
-/
theorem exists_subgroup_eq_range_of_lists :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) [ConnectedSpace S] (t : SAB H S) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (K : Set t.G.left), IsProper t.G.hom → IsUnit (p : Γ(S, ⊤)) → Lists (p ^ 2) σ K → HeckeSet D t 𝔓 p i K → ∃ C : Subgroup (𝟙_ (Over S) ⟶ t.G), (C : Set _) = Set.range σ := by
  intro E _ _ _ H D 𝔓 p i n S _ t σ K hpr hp ⟨hσ, hK, _⟩ hH
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  have hN : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hp.pow 2
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, -⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j => by
    rw [hC, hK]
    rintro _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩
  have key : ∀ a : 𝟙_ (Over S) ⟶ t.G, a ^ (p ^ 2) = 1 → toUnit (Over.mk x) ≫ a ∈ C → a ∈ Set.range σ := by
    intro a ha h
    rw [hC, hK] at h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨q, rfl⟩)
    have h1 := eq_comp_section t.G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w (toUnit (Over.mk x) ≫ a)] at h1
    exact ⟨j, (section_eq t.G hN ha (hσ j) x h1).symm⟩
  refine ⟨{ carrier := Set.range σ, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨j, rfl⟩ ⟨j', rfl⟩
    refine key _ (by rw [mul_pow, hσ, hσ, _root_.one_mul]) ?_
    rw [MonObj.comp_mul]
    exact C.mul_mem (hmem j) (hmem j')
  · refine key _ (one_pow _) ?_
    rw [MonObj.comp_one]
    exact C.one_mem
  · rintro _ ⟨j, rfl⟩
    refine key _ (by rw [inv_pow, hσ, inv_one]) ?_
    rw [GrpObj.comp_inv]
    exact C.inv_mem (hmem j)

end GlobalTheory.HkFam
