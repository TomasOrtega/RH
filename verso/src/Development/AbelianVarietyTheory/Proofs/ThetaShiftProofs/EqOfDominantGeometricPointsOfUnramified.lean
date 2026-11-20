import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace GlobalTheory

/- English proof (translation)
Take `⟨z, u, hu⟩` from `t.denseRange.exists_mem_open g.isOpenMap.isOpen_range (Set.range_nonempty _)`. Take `⟨w, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := g) (g := t) u z hu`. Establish `: JacobsonSpace ↥(pullback g t)` using `LocallyOfFiniteType.jacobsonSpace (pullback.snd g t)`. Take `⟨c, -, hc⟩` from `nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback g t))) ⟨w, trivial⟩ isOpen_univ.isLocallyClosed`. Use `replace hc : IsClosed {c} := hc`.

Use `⟨pointOfClosedPoint (pullback.snd g t) c hc ≫ pullback.fst g t, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]`.
-/
theorem exists_point_over_dominant_geometric_point {U S : Scheme.{u}} (g : U ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] [Nonempty U] {F : Type u} [Field F]
    [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t] :
    ∃ j : Spec (.of F) ⟶ U, j ≫ g = t := by
  obtain ⟨z, u, hu⟩ := t.denseRange.exists_mem_open g.isOpenMap.isOpen_range
    (Set.range_nonempty _)
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := t) u z hu
  have : JacobsonSpace ↥(pullback g t) := LocallyOfFiniteType.jacobsonSpace (pullback.snd g t)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback g t)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd g t) c hc ≫ pullback.fst g t, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

/- English proof (translation)
Establish `hab : a ≫ f = b ≫ f` using `ha.trans hb.symm`. Use `isClosedImmersion_equalizer_ι_of_isSeparated f hab` as an intermediate fact. Use `eq_of_range_equalizer_ι_eq_univ f hab ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Set `U : T.Opens` to `⟨(Set.range (equalizer.ι a b))ᶜ, (equalizer.ι a b).isClosedEmbedding.isClosed_range.isOpen_compl⟩`.

Take `⟨y, hy⟩` from `Set.nonempty_compl.mpr hne`. Establish `: Nonempty U.toScheme` using `⟨⟨y, hy⟩⟩`. Take `⟨j, hj⟩` from `exists_point_over_dominant_geometric_point (U.ι ≫ g) t`. Establish `h1` using `range_subset_range_equalizer_ι (j ≫ U.ι) (h _ (by simpa using hj))`. Take `⟨p⟩ : Nonempty (Spec (CommRingCat.of F))` from `inferInstance`.

Establish `h2 : (j ≫ U.ι) p ∈ U`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `(j p).2`. Conclude with `h2 (h1 ⟨_, rfl⟩)`.
-/
theorem eq_of_dominant_geometric_points_of_unramified {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] (g : T ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] {a b : T ⟶ X} (ha : a ≫ f = g) (hb : b ≫ f = g)
    {F : Type u} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (h : ∀ j : Spec (.of F) ⟶ T, j ≫ g = t → j ≫ a = j ≫ b) : a = b := by
  have hab : a ≫ f = b ≫ f := ha.trans hb.symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab ?_
  by_contra hne
  let U : T.Opens := ⟨(Set.range (equalizer.ι a b))ᶜ,
    (equalizer.ι a b).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hne
  have : Nonempty U.toScheme := ⟨⟨y, hy⟩⟩
  obtain ⟨j, hj⟩ := exists_point_over_dominant_geometric_point (U.ι ≫ g) t
  have h1 := range_subset_range_equalizer_ι (j ≫ U.ι) (h _ (by simpa using hj))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have h2 : (j ≫ U.ι) p ∈ U := by
    rw [Scheme.Hom.comp_apply]
    exact (j p).2
  exact h2 (h1 ⟨_, rfl⟩)

/- English proof (translation)
Establish `hmul : ∀ {Z : Over S} (y : Z ⟶ A), y ≫ mulA A M = y ^ M` using `fun y => by`. Rewrite using `[mulA, MonObj.comp_pow, Category.comp_id]`. Establish `hone : ∀ {Z : Over S}, (1 : Z ⟶ A).left = Z.hom ≫ η[A].left` using `fun {Z} => by`. Rewrite using `[Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression.

Set `K : Over S` to `Over.mk (pullback.snd (mulA A M).left η[A].left)`. Establish `hη : η[A].left ≫ A.hom = 𝟙 S` using `Over.w η[A]`. Set `i : K ⟶ A` to `Over.homMk (pullback.fst (mulA A M).left η[A].left) (by`. Express the relevant statement in the definitionally equal form `pullback.fst (mulA A M).left η[A].left ≫ A.hom = pullback.snd (mulA A M).left η[A].left`. Rewrite using `[← Over.w (mulA A M), pullback.condition_assoc]`.

Use `erw [hη]`. Conclude with `Category.comp_id _)`. Establish `hi : i ^ M = 1`. Rewrite using `[← hmul]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hone]`. Conclude with `pullback.condition`. Establish `hlift : ∀ {Z : Over S} (y : Z ⟶ A), y ^ M = 1 → ∃ l : Z ⟶ K, l ≫ i = y`. Introduce `Z y hy`. Establish `e : y.left ≫ (mulA A M).left = Z.hom ≫ η[A].left`.

Rewrite using `[← Over.comp_left, hmul, hy, hone]`. Conclude with `⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _), Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩`. Establish `hmono : ∀ {Z : Over S} (l l' : Z ⟶ K), l ≫ i = l' ≫ i → l = l'`. Introduce `Z l l' e`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `congr(($e).left)`. Conclude with `(Over.w l).trans (Over.w l').symm`. Take `⟨σ, hσ⟩` from `hlift (i ≫ s) (by rw [← MonObj.pow_comp, hi, MonObj.one_comp])`. Establish `hEt : Etale K.hom` using `inferInstanceAs (Etale (pullback.snd (mulA A M).left η[A].left))`.

Establish `hSep : IsSeparated K.hom` using `inferInstanceAs (IsSeparated (pullback.snd (mulA A M).left η[A].left))`. Establish `key : σ = 𝟙 K`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `eq_of_dominant_geometric_points_of_unramified K.hom K.hom (Over.w σ) (Over.w (𝟙 K)) t ?_` and prove the remaining obligations. Introduce `j hj`.

Set `j' : Over.mk t ⟶ K` to `Over.homMk j hj`. Establish `: j' ≫ σ = j' ≫ 𝟙 K`. Apply `hmono` to reduce the goal to its premises. Rewrite using `[Category.assoc, hσ, Category.comp_id, ← Category.assoc]`. Conclude with `hs _ (by rw [← MonObj.comp_pow, hi, MonObj.comp_one])`.

Conclude with `congr(($this).left)`. Take `⟨l, rfl⟩` from `hlift x hx`. Rewrite using `[Category.assoc, ← hσ, key, Category.id_comp]`.
-/
theorem fix_torsion_of_fix_geometric_of_etale {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : ℕ)
    [Etale (mulA A M).left] [IsSeparated (mulA A M).left]
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : A ⟶ A) [IsMonHom s]
    (hs : ∀ x : Over.mk t ⟶ A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ A) (hx : x ^ M = 1) : x ≫ s = x := by
  have hmul : ∀ {Z : Over S} (y : Z ⟶ A), y ≫ mulA A M = y ^ M := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over S}, (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let K : Over S := Over.mk (pullback.snd (mulA A M).left η[A].left)
  have hη : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  let i : K ⟶ A := Over.homMk (pullback.fst (mulA A M).left η[A].left) (by
    change pullback.fst (mulA A M).left η[A].left ≫ A.hom = pullback.snd (mulA A M).left η[A].left
    rw [← Over.w (mulA A M), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hi : i ^ M = 1 := by
    rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    exact pullback.condition
  have hlift : ∀ {Z : Over S} (y : Z ⟶ A), y ^ M = 1 → ∃ l : Z ⟶ K, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA A M).left = Z.hom ≫ η[A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over S} (l l' : Z ⟶ K), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  obtain ⟨σ, hσ⟩ := hlift (i ≫ s) (by rw [← MonObj.pow_comp, hi, MonObj.one_comp])
  have hEt : Etale K.hom := inferInstanceAs (Etale (pullback.snd (mulA A M).left η[A].left))
  have hSep : IsSeparated K.hom :=
    inferInstanceAs (IsSeparated (pullback.snd (mulA A M).left η[A].left))
  have key : σ = 𝟙 K := by
    apply Over.OverMorphism.ext
    refine eq_of_dominant_geometric_points_of_unramified K.hom K.hom (Over.w σ) (Over.w (𝟙 K)) t ?_
    intro j hj
    let j' : Over.mk t ⟶ K := Over.homMk j hj
    have : j' ≫ σ = j' ≫ 𝟙 K := by
      apply hmono
      rw [Category.assoc, hσ, Category.comp_id, ← Category.assoc]
      exact hs _ (by rw [← MonObj.comp_pow, hi, MonObj.comp_one])
    exact congr(($this).left)
  obtain ⟨l, rfl⟩ := hlift x hx
  rw [Category.assoc, ← hσ, key, Category.id_comp]

/- English proof (translation)
Take `⟨hfin, -, -, het, -⟩` from `hmul S P M hM`. Use `het hMu` as an intermediate fact. Conclude with `fix_torsion_of_fix_geometric_of_etale P.A M t s hs T x hx`.
-/
theorem fix_torsion_of_fix_geometric_of_isDominant (hmul : MulNSt) {S : Scheme.{0}}
    [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (hM : 1 ≤ M) (hMu : IsUnit (M : Γ(S, ⊤)))
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : P.A ⟶ P.A) (hsm : IsMonHom s)
    (hs : ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ s = x := by
  obtain ⟨hfin, -, -, het, -⟩ := hmul S P M hM
  have := het hMu
  exact fix_torsion_of_fix_geometric_of_etale P.A M t s hs T x hx

end GlobalTheory
