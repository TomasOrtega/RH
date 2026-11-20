import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivOfLam

open GlobalTheory.CechPic

/- English proof (translation)
Use `(cls_linComb hL _ _ h).trans ?_` and prove the remaining obligations. Rewrite using `[← Equiv.ulift.symm.sum_comp]`. Establish `hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}}` using `by decide`. Establish `p₀ : psum A ![x, y] ∅ = 1` using `rfl`. Establish `p₁ : psum A ![x, y] {0} = x` using `mul_one x`.

Establish `p₂ : psum A ![x, y] {1} = y` using `mul_one y`. Establish `p₃ : psum A ![x, y] {0, 1} = x * y` using `congrArg (x * ·) (mul_one y)`. Rewrite using `[hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]`. Simplify using `only [Equiv.ulift_symm_apply, p₀, p₁, p₂, p₃]`. Rewrite using `[Finset.card_pair (by decide)]`.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem cls_cube_pair {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (x y : T ⟶ A) (h : (cubeLB A ![x, y] L).IsLB) :
    cls _ h = pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
      pull (1 : T ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.ulift.symm.sum_comp]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := mul_one x
  have p₂ : psum A ![x, y] {1} = y := mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (mul_one y)
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, p₀, p₁, p₂, p₃]
  rw [Finset.card_pair (by decide)]
  simp
  abel

/- English proof (translation)
The claim follows from `(cls_eq_zero_iff (pull_isLB hL f)).2 (GlobalTheory.IsoExtend.exists_gen_of_chart hL f i hf)`.
-/
theorem pull_eq_zero_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (hf : ∀ y, f y ∈ L.U i) : pull f (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL f)).2 (GlobalTheory.IsoExtend.exists_gen_of_chart hL f i hf)

/- English proof (translation)
Establish `: z ∈ (⊤ : X.Opens)` using `trivial`. Rewrite `this` using `[← hL.cover]`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`.
-/
theorem exists_chart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : X) : ∃ i, z ∈ L.U i := by
  have : z ∈ (⊤ : X.Opens) := trivial
  rw [← hL.cover] at this
  exact TopologicalSpace.Opens.mem_iSup.1 this

/- English proof (translation)
Introduce `S B _ _ _ P hP H L hL hiso R _ t x hx`. Use `Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ B).left fun p => ?_)` and prove the remaining obligations. Take `⟨V, hpV, c₀, hc₀⟩` from `hx p`. Take `⟨i, hi⟩` from `exists_chart hL (x.left p)`. Take `⟨j, hj⟩` from `exists_chart hL ((1 : Over.mk t ⟶ B).left p)`.

Set `W : (Spec (CommRingCat.of R)).Opens` to `V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ B).left ⁻¹ᵁ L.U j`. Use `⟨W, ⟨⟨hpV, hi⟩, hj⟩, ?_⟩` and prove the remaining obligations. Set `T₀ : Over S` to `Over.mk t`. Set `TW : Over S` to `Over.mk (W.ι ≫ t)`. Set `ιW : TW ⟶ T₀` to `Over.homMk W.ι rfl`.

It suffices to establish `key : ιW ≫ x = 1 by`. Use `congrArg (fun q => q.left) (key.trans (MonObj.comp_one ιW).symm)` as an intermediate fact. Conclude with `this`. Use `H TW (ιW ≫ x) ?_` and prove the remaining obligations. Set `c` to `cls L hL`.

Establish `hLam : (abelian₂ B L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `hTD : (translDiff B L x).IsLB` using `LB.isLB_linComb hL _ _`. Set `O : (T₀ ⊗ B).left.Opens` to `(fst T₀ B).left ⁻¹ᵁ V`. Establish `h₀ : pull O.ι (cls _ hTD) = 0` using `(cls_eq_zero_iff (pull_isLB hTD _)).2 ⟨c₀, hc₀⟩`. Set `N : B ⊗ TW ⟶ T₀ ⊗ B` to `lift (snd B TW ≫ ιW) (fst B TW)`.

Establish `hN : Set.range N.left.base ⊆ Set.range O.ι.base`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use `show (fst T₀ B).left (N.left z) ∈ V`. Establish `k : N.left ≫ (fst T₀ B).left = (snd B TW).left ≫ W.ι` using `by rw [← Over.comp_left, lift_fst]; rfl`.

Rewrite using `[← Scheme.Hom.comp_apply, k, Scheme.Hom.comp_apply]`. Conclude with `((snd B TW).left z).2.1.1`. Establish `h₁ : pull N.left (cls _ hTD) = 0`. Rewrite using `[← IsOpenImmersion.lift_fac O.ι N.left hN, pull_comp, h₀, map_zero]`. Establish `e₁ : cls _ hTD = pull (lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B]).left c - pull (snd T₀ B).left c`.

Use `(cls_linComb hL _ _ hTD).trans ?_` and prove the remaining obligations. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul, c]`. Conclude with `(sub_eq_add_neg _ _).symm`. Establish `e₂ : pull ((snd B TW ≫ ιW ≫ x) * fst B TW).left c = pull (fst B TW).left c`. Establish `k₁ : N ≫ lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B] = (snd B TW ≫ ιW ≫ x) * fst B TW`.

Rewrite using `[← Category.assoc, comp_lift, ← Category.assoc, lift_fst, lift_snd, Category.assoc]`. Both sides reduce to the same expression. Establish `k₂ : N ≫ snd T₀ B = fst B TW` using `lift_snd _ _`. Rewrite `h₁` using `[e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₁, k₂]`. Conclude with `sub_eq_zero.1 h₁`.

Establish `hcP : cls _ hP = cls _ hLam` using `((cls_eq_iff hLam hP).2 hiso).symm`. Establish `hC : cls _ hLam = pull (fst B B * snd B B).left c - pull (fst B B).left c - pull (snd B B).left c + pull (1 : G2 B ⟶ B).left c` using `cls_cube_pair hL (fst B B) (snd B B) hLam`. Establish `e₃ : pull (snd B TW ≫ ιW ≫ x).left c = 0`. Rewrite using `[Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ x).left i ?_, map_zero]`. Introduce `y`.

Conclude with `y.2.1.2`. Establish `e₄ : pull (1 : B ⊗ TW ⟶ B).left c = 0`. Establish `k : (1 : B ⊗ TW ⟶ B) = snd B TW ≫ ιW ≫ (1 : T₀ ⟶ B)` using `by rw [MonObj.comp_one, MonObj.comp_one]`. Rewrite using `[k, Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ (1 : T₀ ⟶ B)).left j ?_, map_zero]`. Introduce `y`.

Conclude with `y.2.2`. Use `(cls_eq_zero_iff (pull_isLB hP _)).1 ?_` and prove the remaining obligations. Use `show pull _ (cls _ hP) = 0`. Rewrite using `[hcP, hC, map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_one, e₂, e₃, e₄]`. Normalize the expressions using the abelian group laws.
-/
theorem kTriv_of_lam_iso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (P : LB (G2 B).left), P.IsLB →
    (∀ (T : Over S) (x : T ⟶ B), (∃ t : (P.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (L : LB B.left), L.IsLB → LBIso (abelian₂ B L) P → KTriv B L := by
  intro S B _ _ _ P hP H L hL hiso R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ B).left fun p => ?_)
  obtain ⟨V, hpV, c₀, hc₀⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨j, hj⟩ := exists_chart hL ((1 : Over.mk t ⟶ B).left p)
  let W : (Spec (CommRingCat.of R)).Opens := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ B).left ⁻¹ᵁ L.U j
  refine ⟨W, ⟨⟨hpV, hi⟩, hj⟩, ?_⟩
  let T₀ : Over S := Over.mk t
  let TW : Over S := Over.mk (W.ι ≫ t)
  let ιW : TW ⟶ T₀ := Over.homMk W.ι rfl
  suffices key : ιW ≫ x = 1 by
    have := congrArg (fun q => q.left) (key.trans (MonObj.comp_one ιW).symm)
    exact this
  refine H TW (ιW ≫ x) ?_
  let c := cls L hL
  have hLam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hTD : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _

  let O : (T₀ ⊗ B).left.Opens := (fst T₀ B).left ⁻¹ᵁ V
  have h₀ : pull O.ι (cls _ hTD) = 0 := (cls_eq_zero_iff (pull_isLB hTD _)).2 ⟨c₀, hc₀⟩
  let N : B ⊗ TW ⟶ T₀ ⊗ B := lift (snd B TW ≫ ιW) (fst B TW)
  have hN : Set.range N.left.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (fst T₀ B).left (N.left z) ∈ V
    have k : N.left ≫ (fst T₀ B).left = (snd B TW).left ≫ W.ι := by rw [← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, k, Scheme.Hom.comp_apply]
    exact ((snd B TW).left z).2.1.1
  have h₁ : pull N.left (cls _ hTD) = 0 := by
    rw [← IsOpenImmersion.lift_fac O.ι N.left hN, pull_comp, h₀, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B]).left c - pull (snd T₀ B).left c := by
    refine (cls_linComb hL _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul, c]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : pull ((snd B TW ≫ ιW ≫ x) * fst B TW).left c = pull (fst B TW).left c := by
    have k₁ : N ≫ lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B] = (snd B TW ≫ ιW ≫ x) * fst B TW := by
      rw [← Category.assoc, comp_lift, ← Category.assoc, lift_fst, lift_snd, Category.assoc]; rfl
    have k₂ : N ≫ snd T₀ B = fst B TW := lift_snd _ _
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₁, k₂] at h₁
    exact sub_eq_zero.1 h₁
  have hcP : cls _ hP = cls _ hLam := ((cls_eq_iff hLam hP).2 hiso).symm
  have hC : cls _ hLam = pull (fst B B * snd B B).left c - pull (fst B B).left c - pull (snd B B).left c +
      pull (1 : G2 B ⟶ B).left c := cls_cube_pair hL (fst B B) (snd B B) hLam
  have e₃ : pull (snd B TW ≫ ιW ≫ x).left c = 0 := by
    rw [Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ x).left i ?_, map_zero]
    intro y
    exact y.2.1.2
  have e₄ : pull (1 : B ⊗ TW ⟶ B).left c = 0 := by
    have k : (1 : B ⊗ TW ⟶ B) = snd B TW ≫ ιW ≫ (1 : T₀ ⟶ B) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [k, Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ (1 : T₀ ⟶ B)).left j ?_, map_zero]
    intro y
    exact y.2.2
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  show pull _ (cls _ hP) = 0
  rw [hcP, hC, map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_one,
    e₂, e₃, e₄]
  abel

end GlobalTheory.KTrivOfLam
