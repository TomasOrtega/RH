import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLieBasisOfIsLocalRing
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Use `choose b hb using fun i => LieEigen.exists_prodPts hw (hv.1 i)`. Establish `key : ∀ c, prodPts c v = prodPts (∑ i, c i • b i) w` using `fun c => by`. Rewrite using `[← LieEigen.prodPts_prodPts hw.1]`. Conclude with `congrArg (prodPts c) (funext fun i => (hb i).symm)`. Set `L : (Fin n → R) →ₗ[R] (Fin m → R)` to `Fintype.linearCombination R b`.

Establish `hL : ∀ c, L c = ∑ i, c i • b i` using `fun c => Fintype.linearCombination_apply R b c`. Establish `bij : Function.Bijective L`. Use `⟨fun c c' h => LieEigen.prodPts_injective hv ?_, fun d => ?_⟩` and prove the remaining obligations. Use `show prodPts c v = prodPts c' v`. Rewrite using `[key, key, ← hL, ← hL, h]`.

Take `⟨c, hc⟩` from `LieEigen.exists_prodPts hv (LieEigen.isTangent_prodPts hw.1 d)`. Conclude with `⟨c, LieEigen.prodPts_injective hw (show prodPts (L c) w = prodPts d w by rw [hL, ← key, hc])⟩`. Use `(LinearEquiv.ofBijective L bij).finrank_eq` as an intermediate fact. Simplify using `using this`.
-/
theorem card_eq_of_isLieBasis [Nontrivial R] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {w : Fin m → (epsR R ⟶ G)} (hv : IsLieBasis v) (hw : IsLieBasis w) : n = m := by
  choose b hb using fun i => LieEigen.exists_prodPts hw (hv.1 i)
  have key : ∀ c, prodPts c v = prodPts (∑ i, c i • b i) w := fun c => by
    rw [← LieEigen.prodPts_prodPts hw.1]
    exact congrArg (prodPts c) (funext fun i => (hb i).symm)
  let L : (Fin n → R) →ₗ[R] (Fin m → R) := Fintype.linearCombination R b
  have hL : ∀ c, L c = ∑ i, c i • b i := fun c => Fintype.linearCombination_apply R b c
  have bij : Function.Bijective L := by
    refine ⟨fun c c' h => LieEigen.prodPts_injective hv ?_, fun d => ?_⟩
    · show prodPts c v = prodPts c' v
      rw [key, key, ← hL, ← hL, h]
    · obtain ⟨c, hc⟩ := LieEigen.exists_prodPts hv (LieEigen.isTangent_prodPts hw.1 d)
      exact ⟨c, LieEigen.prodPts_injective hw (show prodPts (L c) w = prodPts d w by rw [hL, ← key, hc])⟩
  have := (LinearEquiv.ofBijective L bij).finrank_eq
  simpa using this

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem push_left (x : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) x).left = x.left ≫ pullback.fst G.hom (spMap f) := rfl

/- English proof (translation)
Introduce `x y e` and use `Over.OverMorphism.ext ((isGrpPullback_pullback G (spMap f)).1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))`.
-/
theorem push_injective : Function.Injective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) :=
  fun x y e => Over.OverMorphism.ext ((isGrpPullback_pullback G (spMap f)).1.hom_ext
    (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))

/- English proof (translation)
Introduce `w`. Establish `hk` using `isGrpPullback_pullback G (spMap f)`. Use `⟨Over.homMk (hk.1.lift w.left (epsR k).hom (Over.w w)) (hk.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Conclude with `Over.OverMorphism.ext (hk.1.lift_fst _ _ _)`.
-/
theorem push_surjective : Function.Surjective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) := by
  intro w
  have hk := isGrpPullback_pullback G (spMap f)
  refine ⟨Over.homMk (hk.1.lift w.left (epsR k).hom (Over.w w)) (hk.1.lift_snd _ _ _), ?_⟩
  exact Over.OverMorphism.ext (hk.1.lift_fst _ _ _)

/- English proof (translation)
Establish `e` using `congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback G (spMap f)) (𝟙_ (Over (Sp k)))))`. Establish `e₁ : (1 : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap f)).obj G) = η[(Over.pullback (spMap f)).obj G]` using `by rw [Hom.one_def]; simp`. Rewrite `e` using `[e₁]`. Use `e.trans ?_` and prove the remaining obligations. Use `show (toUnit _ ≫ η[G]).left = _`.

Simplify using the standard rewrite rules.
-/
theorem unit_fst : η[(Over.pullback (spMap f)).obj G].left ≫ pullback.fst G.hom (spMap f) = spMap f ≫ η[G].left := by
  have e := congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback G (spMap f)) (𝟙_ (Over (Sp k)))))
  have e₁ : (1 : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap f)).obj G) = η[(Over.pullback (spMap f)).obj G] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

/- English proof (translation)
Rewrite using `[push_left]`. Use `show _ ↔ _ = spMap f ≫ η[G].left`. Unfold `IsTangent`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[← Category.assoc, h, unit_fst]`. Introduce `h`. Apply `(isGrpPullback_pullback G (spMap f)).1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, h, unit_fst]`. Rewrite using `[Category.assoc, Over.w y, Over.w η[(Over.pullback (spMap f)).obj G]]`.

Simplify using `only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k`. Use extensionality with `s`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Rewrite using `[this]`.

Simplify using the standard rewrite rules.
-/
theorem isTangent_iff_push (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    IsTangent y ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫
      (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y).left = (1 : Over.mk (spMap f) ⟶ G).left := by
  rw [push_left]
  show _ ↔ _ = spMap f ≫ η[G].left
  unfold IsTangent
  constructor
  · intro h
    rw [← Category.assoc, h, unit_fst]
  · intro h
    apply (isGrpPullback_pullback G (spMap f)).1.hom_ext
    · rw [Category.assoc, h, unit_fst]
    · rw [Category.assoc, Over.w y, Over.w η[(Over.pullback (spMap f)).obj G]]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
        ext s; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      simp

def scaleAt (a : k) : epsPt (spMap f) ⟶ epsPt (spMap f) :=
  Over.homMk (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)).left
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap f) (Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)))))

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (Category.assoc _ _ _)`.
-/
theorem push_scale (a : k) (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a) ≫ y) =
      scaleAt f a ≫ pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

open Classical in

def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) R :=
  if h : IsMonHom u then Matrix.transpose (haveI := h; (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose) else 0

/- English proof (translation)
Establish `h` using `(SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose_spec j`. Rewrite `h` using `[ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff]`. Rewrite using `[lieMat, dif_pos (show IsMonHom u from inferInstance)]`. Conclude with `h`.
-/
theorem comp_eq_prodPts (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (j : Fin n) :
    v j ≫ u = prodPts (fun i => lieMat hv u i j) v := by
  have h := (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose_spec j
  rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff] at h
  rw [lieMat, dif_pos (show IsMonHom u from inferInstance)]
  exact h

end GlobalTheory.LieCoordFibre

open GlobalTheory.LieCoordFibre ReciprocityTheory.ChartRestriction.G.Chart in

/- English proof (translation)
Introduce `R _ _ G _ _ hs`. Take `⟨n, v, hv⟩` from `LieLocalBasis.exists_isLieBasis_of_isLocalRing R G hs`. Use `⟨n, lieMat hv, fun g hg => ?_, fun k _ f => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `KeyPow.exists_isLieBasis G hg`. Conclude with `card_eq_of_isLieBasis hv hw`.

Establish `hk` using `isGrpPullback_pullback G (spMap f)`. Take `⟨v', hv', e⟩` from `exists_isLieBasis_baseChange R k f G _ _ hk hs n v hv`. Set `P` to `pushHom hk (epsR k)`. Use `⟨fun c => P (prodPts c v'), fun c c' h => LieEigen.prodPts_injective hv' (push_injective f h), fun w => ?_, fun c c' => ?_, fun t c => ?_, fun u hu c => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨y, rfl⟩` from `push_surjective f w`. Take `⟨c, rfl⟩` from `LieEigen.exists_prodPts hv' ((isTangent_iff_push f y).2 h)`. Conclude with `⟨c, rfl⟩`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `(isTangent_iff_push f _).1 (LieEigen.isTangent_prodPts hv'.1 c)`. Use `show P _ = P _ * P _`. Rewrite using `[LieEigen.prodPts_add hv'.1, map_mul]`. Use `show (prodPts (t • c) v').left ≫ _ = _ ≫ (prodPts c v').left ≫ _`. Rewrite using `[LieEigen.prodPts_smul, Over.comp_left, Category.assoc]`.

Both sides reduce to the same expression. Use `haveI := hu`. Set `col : Fin n → Fin n → R` to `fun j i => lieMat hv u i j`. Establish `hz : ∀ j, P (v' j) ≫ u = P (prodPts (f ∘ col j) v')` using `fun j => Over.OverMorphism.ext (by`. Rewrite using `[Over.comp_left, push_left, push_left, e j, Category.assoc, ← Over.comp_left, comp_eq_prodPts hv u j, ← LieEigen.prodPts_left hk e])`.

Set `Q` to `(IsMonHom.monoidHom u (epsPt (spMap f))).comp P`. Establish `hQ : ∀ y, Q y = P y ≫ u` using `fun y => rfl`. Establish `hs' : ∀ j, Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j) = P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v')` using `fun j => by`. Rewrite using `[hQ, push_scale, push_scale, Category.assoc, hz]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Use `_ = (List.ofFn fun j => P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v')).prod := by`. Simplify using `only [hs']`. Use `_ = P (prodPts c fun j => prodPts (f ∘ col j) v') := by`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Use `_ = P (prodPts (∑ j, c j • (f ∘ col j)) v') := by rw [LieEigen.prodPts_prodPts hv'.1]`. Use `_ = P (prodPts (((lieMat hv u).map f).mulVec c) v') := by`. Use `congr 2`.

Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, col, mul_comm]`.
-/
theorem GlobalTheory.exists_lie_coordinates_fibres : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R), (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → n = g) ∧ ∀ (k : Type) [Field k] (f : R →+* k), ∃ T : (Fin n → k) → (epsPt (spMap f) ⟶ G), Function.Injective T ∧ (∀ v : epsPt (spMap f) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (v).left = (1 : Over.mk (spMap f) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (t : k) c, (T (t • c)).left = spMap (epsScale t) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c) := by
  intro R _ _ G _ _ hs
  obtain ⟨n, v, hv⟩ := LieLocalBasis.exists_isLieBasis_of_isLocalRing R G hs
  refine ⟨n, lieMat hv, fun g hg => ?_, fun k _ f => ?_⟩
  · obtain ⟨w, hw⟩ := KeyPow.exists_isLieBasis G hg
    exact card_eq_of_isLieBasis hv hw
  have hk := isGrpPullback_pullback G (spMap f)
  obtain ⟨v', hv', e⟩ := exists_isLieBasis_baseChange R k f G _ _ hk hs n v hv
  let P := pushHom hk (epsR k)
  refine ⟨fun c => P (prodPts c v'), fun c c' h => LieEigen.prodPts_injective hv' (push_injective f h),
    fun w => ?_, fun c c' => ?_, fun t c => ?_, fun u hu c => ?_⟩
  · constructor
    · intro h
      obtain ⟨y, rfl⟩ := push_surjective f w
      obtain ⟨c, rfl⟩ := LieEigen.exists_prodPts hv' ((isTangent_iff_push f y).2 h)
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact (isTangent_iff_push f _).1 (LieEigen.isTangent_prodPts hv'.1 c)
  · show P _ = P _ * P _
    rw [LieEigen.prodPts_add hv'.1, map_mul]
  · show (prodPts (t • c) v').left ≫ _ = _ ≫ (prodPts c v').left ≫ _
    rw [LieEigen.prodPts_smul, Over.comp_left, Category.assoc]
    rfl
  haveI := hu
  let col : Fin n → Fin n → R := fun j i => lieMat hv u i j
  have hz : ∀ j, P (v' j) ≫ u = P (prodPts (f ∘ col j) v') := fun j => Over.OverMorphism.ext (by
    rw [Over.comp_left, push_left, push_left, e j, Category.assoc, ← Over.comp_left,
      comp_eq_prodPts hv u j, ← LieEigen.prodPts_left hk e])
  let Q := (IsMonHom.monoidHom u (epsPt (spMap f))).comp P
  have hQ : ∀ y, Q y = P y ≫ u := fun y => rfl
  have hs' : ∀ j, Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j) =
      P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v') := fun j => by
    rw [hQ, push_scale, push_scale, Category.assoc, hz]
  calc P (prodPts c v') ≫ u = Q (prodPts c v') := rfl
    _ = (List.ofFn fun j => Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j)).prod := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = (List.ofFn fun j => P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v')).prod := by
      simp only [hs']
    _ = P (prodPts c fun j => prodPts (f ∘ col j) v') := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = P (prodPts (∑ j, c j • (f ∘ col j)) v') := by rw [LieEigen.prodPts_prodPts hv'.1]
    _ = P (prodPts (((lieMat hv u).map f).mulVec c) v') := by
      congr 2
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
