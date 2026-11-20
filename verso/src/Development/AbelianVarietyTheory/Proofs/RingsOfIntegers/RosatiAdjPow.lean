import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.RosatiPower

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]

/- English proof (translation)
Unfold `padd`. Simplify using `[IsMonHom.mul_hom]`.
-/
private theorem padd_comp_eq_padd_comp_of_isMonHom {T H K : Over S} [GrpObj H] [GrpObj K] (q : H ⟶ K) [IsMonHom q]
    (a b : T ⟶ H) : padd H a b ≫ q = padd K (a ≫ q) (b ≫ q) := by
  unfold padd
  simp [IsMonHom.mul_hom]

/- English proof (translation)
Unfold `padd`. Use `first`. Consider the case `simp`. Consider the case `simp [Hom.mul_def]`. Consider the case `simp [comp_lift_assoc]`.
-/
private theorem comp_padd_eq_padd_comp {T T' H : Over S} [GrpObj H] (x : T ⟶ T') (a b : T' ⟶ H) :
    x ≫ padd H a b = padd H (x ≫ a) (x ≫ b) := by
  unfold padd
  first
  | simp
  | simp [Hom.mul_def]
  | simp [comp_lift_assoc]

/- English proof (translation)
Establish `e1 : (q ⊗ₘ q) ≫ fst G G = fst G' G' ≫ q` using `by simp`. Establish `e2 : (q ⊗ₘ q) ≫ snd G G = snd G' G' ≫ q` using `by simp`. Establish `key : ∀ (a : G' ⊗ G' ⟶ G') (b : G ⊗ G ⟶ G), a ≫ q = (q ⊗ₘ q) ≫ b → a.left ≫ q.left = (q ⊗ₘ q).left ≫ b.left`. Introduce `a b h`. Rewrite using `[← Over.comp_left, h, Over.comp_left]`.

Apply the tactic sequence `fin_cases k <;> refine key _ _ ?_ <;>`. Simplify using `only [padd_comp_eq_padd_comp_of_isMonHom, comp_padd_eq_padd_comp, Category.assoc, hf, hg, reassoc_of% e1, reassoc_of% e2, e1, e2]`.
-/
theorem rosatiφ_comp (q : G' ⟶ G) [IsMonHom q] {f g : G ⟶ G} {f' g' : G' ⟶ G'}
    (hf : f' ≫ q = q ≫ f) (hg : g' ≫ q = q ≫ g) (k : Fin 6) :
    rosatiφ G' f' g' k ≫ q.left = (q ⊗ₘ q).left ≫ rosatiφ G f g k := by
  have e1 : (q ⊗ₘ q) ≫ fst G G = fst G' G' ≫ q := by simp
  have e2 : (q ⊗ₘ q) ≫ snd G G = snd G' G' ≫ q := by simp
  have key : ∀ (a : G' ⊗ G' ⟶ G') (b : G ⊗ G ⟶ G), a ≫ q = (q ⊗ₘ q) ≫ b →
      a.left ≫ q.left = (q ⊗ₘ q).left ≫ b.left := by
    intro a b h
    rw [← Over.comp_left, h, Over.comp_left]
  fin_cases k <;> refine key _ _ ?_ <;>
    simp only [padd_comp_eq_padd_comp_of_isMonHom, comp_padd_eq_padd_comp, Category.assoc, hf, hg, reassoc_of% e1, reassoc_of% e2, e1, e2]

/- English proof (translation)
Use `⟨q.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) ?_, Scheme.Hom.resLE_comp_ι _ _⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[← Over.w q]`. Conclude with `hx`.
-/
theorem exists_restrict {A B : Over S} (q : A ⟶ B) (U : S.Opens) :
    ∃ n : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      n ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ q.left := by
  refine ⟨q.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  intro x hx
  rw [← Over.w q] at hx
  exact hx

/- English proof (translation)
Set `tS : LB.Sec B` to `⟨fun b => (t.s b : Γ(X, B.U b)), fun i j => by`. Establish `e` using `congrArg Units.val (ht i j)`. Simplify `e⟩` using `[res]`. Establish `hunit : ∀ a, IsUnit ((secOfIso tS hu hA hB).f a)`. Introduce `a`.

Apply `RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace` to reduce the goal to its premises. Introduce `x hx`. Establish `hc` using `cover_inf hB a hx`. Rewrite `hc` using `[TopologicalSpace.Opens.mem_iSup]`. Take `⟨b, hb⟩` from `hc`.

Establish `hsp` using `secOfIso_spec tS hu hA hB a b`. Establish `e1 : X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a) = X.presheaf.germ (A.U a ⊓ B.U b) x hb (rs inf_le_left ((secOfIso tS hu hA hB).f a))`. Simplify using `only [rs, TopCat.Presheaf.germ_res_apply]`. Express the relevant statement in the definitionally equal form `IsUnit (X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a))`. Rewrite using `[e1, hsp, isoCand, map_mul]`.

Use `IsUnit.mul ((Units.isUnit _).map _) ?_` and prove the remaining obligations. Simplify using `only [rs, TopCat.Presheaf.germ_res_apply]`. Conclude with `(Units.isUnit (t.s b)).map _`. Use `⟨⟨fun a => (hunit a).unit⟩, fun i j => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Establish `e` using `(secOfIso tS hu hA hB).compat i j`. Simplify `e` using `[res]`.
-/
private theorem exists_isGen_of_isGen_iso_of_isGen {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB)
    (u : LB.Iso A B) (hu : u.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ t' : LB.Gen A, t'.IsGen := by
  classical
  let tS : LB.Sec B := ⟨fun b => (t.s b : Γ(X, B.U b)), fun i j => by
    have e := congrArg Units.val (ht i j)
    simpa [res] using e⟩
  have hunit : ∀ a, IsUnit ((secOfIso tS hu hA hB).f a) := by
    intro a
    apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace
    intro x hx
    have hc := cover_inf hB a hx
    rw [TopologicalSpace.Opens.mem_iSup] at hc
    obtain ⟨b, hb⟩ := hc
    have hsp := secOfIso_spec tS hu hA hB a b
    have e1 : X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a) =
        X.presheaf.germ (A.U a ⊓ B.U b) x hb (rs inf_le_left ((secOfIso tS hu hA hB).f a)) := by
      simp only [rs, TopCat.Presheaf.germ_res_apply]
    change IsUnit (X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a))
    rw [e1, hsp, isoCand, map_mul]
    refine IsUnit.mul ((Units.isUnit _).map _) ?_
    simp only [rs, TopCat.Presheaf.germ_res_apply]
    exact (Units.isUnit (t.s b)).map _
  refine ⟨⟨fun a => (hunit a).unit⟩, fun i j => ?_⟩
  apply Units.ext
  have e := (secOfIso tS hu hA hB).compat i j
  simpa [res] using e

end GlobalTheory.RosatiPower

open GlobalTheory.RosatiPower in

/- English proof (translation)
Introduce `S G' G _ _ _ _ j p L L' hL hL' hiso f g f' g' hf hg hr`. Establish `hm : ∀ i, IsMonHom (p.pr i)` using `p.hom`. Unfold `RosatiAdj at hr ⊢`. Unfold `boxLB at hiso`. Introduce `s`.

Take `⟨U, hsU, t, ht⟩` from `hr s`. Use `⟨U, hsU, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hiso`. Establish `hn : ∀ i, ∃ n : ((G' ⊗ G').hom ⁻¹ᵁ U).toScheme ⟶ ((G ⊗ G).hom ⁻¹ᵁ U).toScheme, n ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι = ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ (p.pr i ⊗ₘ p.pr i).left` using `fun i => exists_restrict (p.pr i ⊗ₘ p.pr i) U`. Use `choose n hn using hn`.

Establish `hc : ∀ i k, (((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) ≫ (p.pr i).left = n i ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι ≫ rosatiφ G f g k`. Introduce `i k`. Rewrite using `[Category.assoc, rosatiφ_comp (p.pr i) (hf i) (hg i) k, ← Category.assoc, ← hn i, Category.assoc]`. Set `t' : ∀ i, ((L.pull (p.pr i).left).LinComb (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε).Gen` to `fun i => GeneratorPullback.pullAlong L (p.pr i).left (n i) _ rosatiε _ (hc i) t`. Establish `ht' : ∀ i, (t' i).IsGen`.

Introduce `i`. Conclude with `LBxP.isGen_pullAlong L (Over.Hom.left (p.pr i)) (n i) _ rosatiε _ (hc i) t ht`. Establish `hb` using `GlobalTheory.BoxSymmetry.isGen_boxGen L (fun i => (p.pr i).left) _ rosatiε t' ht'`. Establish `hwi` using `linCombIso_isGen w hw (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε`. Conclude with `exists_isGen_of_isGen_iso_of_isGen (linComb_isLB _ hL' _ _) (linComb_isLB _ (linComb_isLB _ hL _ _) _ _) _ hwi _ hb`.
-/
theorem GlobalTheory.rosatiAdj_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → RosatiAdj G L f g → RosatiAdj G' L' f' g' := by
  intro S G' G _ _ _ _ j p L L' hL hL' hiso f g f' g' hf hg hr
  have hm : ∀ i, IsMonHom (p.pr i) := p.hom
  unfold RosatiAdj at hr ⊢
  unfold boxLB at hiso
  intro s
  obtain ⟨U, hsU, t, ht⟩ := hr s
  refine ⟨U, hsU, ?_⟩
  obtain ⟨w, hw⟩ := hiso
  have hn : ∀ i, ∃ n : ((G' ⊗ G').hom ⁻¹ᵁ U).toScheme ⟶ ((G ⊗ G).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι = ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ (p.pr i ⊗ₘ p.pr i).left :=
    fun i => exists_restrict (p.pr i ⊗ₘ p.pr i) U
  choose n hn using hn
  have hc : ∀ i k, (((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) ≫ (p.pr i).left =
      n i ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι ≫ rosatiφ G f g k := by
    intro i k
    rw [Category.assoc, rosatiφ_comp (p.pr i) (hf i) (hg i) k, ← Category.assoc, ← hn i, Category.assoc]
  let t' : ∀ i, ((L.pull (p.pr i).left).LinComb
      (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε).Gen :=
    fun i => GeneratorPullback.pullAlong L (p.pr i).left (n i) _ rosatiε _ (hc i) t
  have ht' : ∀ i, (t' i).IsGen := by
    intro i
    exact LBxP.isGen_pullAlong L (Over.Hom.left (p.pr i)) (n i) _ rosatiε _ (hc i) t ht
  have hb := GlobalTheory.BoxSymmetry.isGen_boxGen L (fun i => (p.pr i).left) _ rosatiε t' ht'
  have hwi := linCombIso_isGen w hw (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε
  exact exists_isGen_of_isGen_iso_of_isGen (linComb_isLB _ hL' _ _) (linComb_isLB _ (linComb_isLB _ hL _ _) _ _) _ hwi _ hb

end
