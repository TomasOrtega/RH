import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsSubsetAbLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareGeneric

/- English proof (translation)
Introduce `R' _ _ _ _ _ G' _ hG hA N hN a`. Use `hG.comm` as an intermediate fact. Set `j` to `jK R'`. Set `πA` to `pullback.fst G'.hom j`. Establish `hp : IsProper (pullback.snd G'.hom j)` using `hA.proper`.

Take `⟨t₀, ht₀⟩` from `GlobalTheory.RigCube.exists_gen_theta_generic G' hG hp hN`. Set `c : G' ⟶ G'` to `toUnit G' ≫ a`. Set `c' : G' ⟶ G'` to `toUnit G' ≫ a⁻¹`. Set `ℓ : G' ⟶ G3 G'` to `lift (𝟙 G') (lift c c')`. Set `h : pullback G'.hom j ⟶ pullback (G3 G').hom j` to `pullback.map _ _ _ _ ℓ.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w]) (by simp)`.

Establish `hh : h ≫ pullback.fst (G3 G').hom j = πA ≫ ℓ.left` using `pullback.lift_fst _ _ _`. Set `t₁` to `LB.pullGen (Theta G' N) (fun _ => pullback.fst (G3 G').hom j) (fun _ => 1) t₀ h`. Establish `ht₁ : t₁.IsGen` using `DVR.pullGen_isGen _ _ _ _ ht₀ _`. Take `⟨t₂, ht₂⟩` from `gen_chartPull (chartPullIn N (thφ G' (x3 G')) thε (h ≫ pullback.fst (G3 G').hom j)) t₁ ht₁`. Establish `hcc : c * c' = 1`.

Simplify using `only [c, c']`. Rewrite using `[← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one]`. Establish `hconst : ∀ s : 𝟙_ (Over (Sp R')) ⟶ G', ∃ i, ∀ y, (πA ≫ (toUnit G' ≫ s).left) y ∈ N.U i`. Introduce `s`. Take `⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R')))` from `inferInstance`.

Take `⟨i, hi⟩` from `exists_chart hN ((j ≫ s.left) p₀)`. Establish `e : πA ≫ (toUnit G' ≫ s).left = pullback.snd G'.hom j ≫ j ≫ s.left`. Establish `w : (toUnit G').left = G'.hom` using `(Category.comp_id _).symm.trans (Over.w (toUnit G'))`. Rewrite using `[Over.comp_left, w, ← Category.assoc, pullback.condition, Category.assoc]`. Use `⟨i, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[e, Scheme.Hom.comp_apply, Subsingleton.elim ((pullback.snd G'.hom j) y) p₀]`. Conclude with `hi`. Set `s₃ : Fin 3 → (𝟙_ (Over (Sp R')) ⟶ G')` to `![a, a⁻¹, η[G']]`. Use `choose i hi using fun k => hconst (s₃ k)`. Set `φw : Fin 3 → (pullback G'.hom j ⟶ G'.left)` to `fun k => πA ≫ (toUnit G' ≫ s₃ k).left`.

Take `⟨w, hw⟩` from `GlobalTheory.AbSquare.exists_gen_of_mem_chart hN φw ![1, 1, -2] i hi`. Set `ψ : Fin 3 → (G'.left ⟶ G'.left)` to `![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left]`. Establish `hF : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FormEq (Sum.elim (fun I => (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) φw) (Sum.elim (fun I => -thε I) ![1, 1, -2]) (fun k => πA ≫ ψ k) ![1, 1, -2]`. Introduce `U _ g`. Rewrite using `[Fintype.prod_sum_type]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Simplify using `only [zpow_neg, Finset.prod_inv_distrib]`. Establish `e : ∀ I, (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I = πA ≫ (ℓ.left ≫ thφ G' (x3 G') I)` using `fun I => by rw [hh, Category.assoc]`. Establish `e2 : (∏ I : thK, g ((h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) ^ thε I) = ∏ I : thK, (fun q => g (πA ≫ q)) ((lift (𝟙 G') (lift c c')).left ≫ thφ G' (x3 G') I) ^ thε I` using `Finset.prod_congr rfl fun I _ => by rw [e I]`. Rewrite using `[e2, prod_cub (𝟙 G') c c' (fun q => g (πA ≫ q))]`.

Rewrite using `[show 𝟙 G' * c * c' = 𝟙 G' by rw [_root_.mul_assoc, hcc, _root_.mul_one], hcc]`. Establish `f0 : φw 0 = πA ≫ c.left` using `rfl`. Establish `f1 : φw 1 = πA ≫ c'.left` using `rfl`. Establish `f2 : φw 2 = πA ≫ (1 : G' ⟶ G').left` using `rfl`. Establish `p0 : ψ 0 = (𝟙 G' * c).left` using `rfl`.

Establish `p1 : ψ 1 = (𝟙 G' * c').left` using `rfl`. Establish `p2 : ψ 2 = Over.Hom.left (𝟙 G')` using `(Over.id_left _).symm`. Rewrite using `[Fin.prod_univ_three, Fin.prod_univ_three, f0, f1, f2, p0, p1, p2]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]`.

Normalize the expressions using the abelian group laws. Take `⟨u, hu, -⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF (LB.mulGen N _ _ _ _ (LB.invGen N _ _ t₂) w) (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht₂) hw)`. Take `⟨v, hv⟩` from `gen_chartPull (chartPullOut N ψ ![1, 1, -2] πA (fun k => πA ≫ ψ k) (fun _ => rfl)) u hu`. Conclude with `GlobalTheory.PicGenericInj.exists_gen_of_generic R' G' hG _ (LB.isLB_linComb hN _ _) ⟨v, hv⟩`.
-/
theorem exists_gen_square :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  intro R' _ _ _ _ _ G' _ hG hA N hN a
  have := hG.comm
  let j := jK R'
  let πA := pullback.fst G'.hom j
  have hp : IsProper (pullback.snd G'.hom j) := hA.proper
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.RigCube.exists_gen_theta_generic G' hG hp hN
  let c : G' ⟶ G' := toUnit G' ≫ a
  let c' : G' ⟶ G' := toUnit G' ≫ a⁻¹
  let ℓ : G' ⟶ G3 G' := lift (𝟙 G') (lift c c')
  let h : pullback G'.hom j ⟶ pullback (G3 G').hom j :=
    pullback.map _ _ _ _ ℓ.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w]) (by simp)
  have hh : h ≫ pullback.fst (G3 G').hom j = πA ≫ ℓ.left := pullback.lift_fst _ _ _
  let t₁ := LB.pullGen (Theta G' N) (fun _ => pullback.fst (G3 G').hom j) (fun _ => 1) t₀ h
  have ht₁ : t₁.IsGen := DVR.pullGen_isGen _ _ _ _ ht₀ _
  obtain ⟨t₂, ht₂⟩ := gen_chartPull (chartPullIn N (thφ G' (x3 G')) thε (h ≫ pullback.fst (G3 G').hom j)) t₁ ht₁
  have hcc : c * c' = 1 := by
    simp only [c, c']
    rw [← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one]

  have hconst : ∀ s : 𝟙_ (Over (Sp R')) ⟶ G', ∃ i, ∀ y, (πA ≫ (toUnit G' ≫ s).left) y ∈ N.U i := by
    intro s
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
    obtain ⟨i, hi⟩ := exists_chart hN ((j ≫ s.left) p₀)
    have e : πA ≫ (toUnit G' ≫ s).left = pullback.snd G'.hom j ≫ j ≫ s.left := by
      have w : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
      rw [Over.comp_left, w, ← Category.assoc, pullback.condition, Category.assoc]
    refine ⟨i, fun y => ?_⟩
    rw [e, Scheme.Hom.comp_apply, Subsingleton.elim ((pullback.snd G'.hom j) y) p₀]
    exact hi
  let s₃ : Fin 3 → (𝟙_ (Over (Sp R')) ⟶ G') := ![a, a⁻¹, η[G']]
  choose i hi using fun k => hconst (s₃ k)
  let φw : Fin 3 → (pullback G'.hom j ⟶ G'.left) := fun k => πA ≫ (toUnit G' ≫ s₃ k).left
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hN φw ![1, 1, -2] i hi
  let ψ : Fin 3 → (G'.left ⟶ G'.left) := ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left]
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FormEq
      (Sum.elim (fun I => (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) φw)
      (Sum.elim (fun I => -thε I) ![1, 1, -2]) (fun k => πA ≫ ψ k) ![1, 1, -2] := by
    intro U _ g
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    have e : ∀ I, (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I = πA ≫ (ℓ.left ≫ thφ G' (x3 G') I) :=
      fun I => by rw [hh, Category.assoc]
    have e2 : (∏ I : thK, g ((h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) ^ thε I) =
        ∏ I : thK, (fun q => g (πA ≫ q)) ((lift (𝟙 G') (lift c c')).left ≫ thφ G' (x3 G') I) ^ thε I :=
      Finset.prod_congr rfl fun I _ => by rw [e I]
    rw [e2, prod_cub (𝟙 G') c c' (fun q => g (πA ≫ q))]
    rw [show 𝟙 G' * c * c' = 𝟙 G' by rw [_root_.mul_assoc, hcc, _root_.mul_one], hcc]
    have f0 : φw 0 = πA ≫ c.left := rfl
    have f1 : φw 1 = πA ≫ c'.left := rfl
    have f2 : φw 2 = πA ≫ (1 : G' ⟶ G').left := rfl
    have p0 : ψ 0 = (𝟙 G' * c).left := rfl
    have p1 : ψ 1 = (𝟙 G' * c').left := rfl
    have p2 : ψ 2 = Over.Hom.left (𝟙 G') := (Over.id_left _).symm
    rw [Fin.prod_univ_three, Fin.prod_univ_three, f0, f1, f2, p0, p1, p2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨u, hu, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF (LB.mulGen N _ _ _ _ (LB.invGen N _ _ t₂) w)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht₂) hw)
  obtain ⟨v, hv⟩ := gen_chartPull (chartPullOut N ψ ![1, 1, -2] πA (fun k => πA ≫ ψ k) (fun _ => rfl)) u hu
  exact GlobalTheory.PicGenericInj.exists_gen_of_generic R' G' hG _ (LB.isLB_linComb hN _ _) ⟨v, hv⟩

end GlobalTheory.SquareGeneric
