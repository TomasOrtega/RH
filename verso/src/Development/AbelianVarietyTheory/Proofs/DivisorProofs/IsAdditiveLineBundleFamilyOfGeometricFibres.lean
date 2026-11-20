import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.ZM GlobalTheory.AbLaw.CubeGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddFib

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def quad {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) : Fin 4 → (Z.left ⟶ (A ⊗ T).left) :=
  ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left, (lift 1 y).left]

abbrev uquad (A T : Over S) [GrpObj A] : Fin 4 → ((A ⊗ (A ⊗ T)).left ⟶ (A ⊗ T).left) :=
  quad (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;>`. Simplify using `only [quad, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]`. Rewrite using `[← Over.comp_left, comp_lift]`. Apply the tactic sequence `try simp only [MonObj.comp_mul, MonObj.comp_one]`.
-/
theorem comp_quad {Z Z' : Over S} (r : Z' ⟶ Z) (x x' : Z ⟶ A) (y : Z ⟶ T) (i : Fin 4) :
    r.left ≫ quad x x' y i = quad (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [quad, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

/- English proof (translation)
Break down `h with rfl | rfl` into its components or cases. Simplify using `[Fin.prod_univ_four, quad, -Over.comp_left]`. Simplify using `[Fin.prod_univ_four, quad, -Over.comp_left, mul_comm]`.
-/
theorem prod_quad {Z : Over S} {x x' : Z ⟶ A} (y : Z ⟶ T) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (Z.left ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (quad x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, quad, -Over.comp_left]
  · simp [Fin.prod_univ_four, quad, -Over.comp_left, mul_comm]

/- English proof (translation)
Establish `hb : b = r ≫ Y.hom`. Use `congrArg (· ≫ A.hom) h` as an intermediate fact. Simplify using `only [Category.assoc, Over.w] at this`. Conclude with `(this.trans (Category.comp_id _)).symm`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[Hom.one_def]`. Conclude with `h.trans (by rw [hb]; rfl)`.
-/
theorem homMk_comp_eq_one {Y : Over S} {Z : Scheme.{0}} (r : Z ⟶ Y.left) (u : Y ⟶ A) (b : Z ⟶ S)
    (h : r ≫ u.left = b ≫ η[A].left) : (Over.homMk r rfl : Over.mk (r ≫ Y.hom) ⟶ Y) ≫ u = 1 := by
  have hb : b = r ≫ Y.hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

/- English proof (translation)
Establish `e : ∀ i, r ≫ uquad A T i = quad ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ fst A (A ⊗ T)) ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ fst A T) ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ snd A T) i` using `fun i ↦ comp_quad (Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) _ _ _ i`. Simplify using `only [e]`. Conclude with `prod_quad _ (h.imp (homMk_comp_eq_one r _ b) (homMk_comp_eq_one r _ b)) U k`.
-/
theorem formal_quad {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ (A ⊗ T)).left) (b : Z ⟶ S)
    (h : r ≫ (fst A (A ⊗ T)).left = b ≫ η[A].left ∨ r ≫ (snd A (A ⊗ T) ≫ fst A T).left = b ≫ η[A].left)
    (U : Type) [CommGroup U] (k : (Z ⟶ (A ⊗ T).left) → U) :
    ∏ i, k (r ≫ uquad A T i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  have e : ∀ i, r ≫ uquad A T i = quad ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ fst A (A ⊗ T))
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ fst A T)
      ((Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) ≫ snd A (A ⊗ T) ≫ snd A T) i :=
    fun i ↦ comp_quad (Over.homMk r rfl : Over.mk (r ≫ (A ⊗ (A ⊗ T)).hom) ⟶ _) _ _ _ i
  simp only [e]
  exact prod_quad _ (h.imp (homMk_comp_eq_one r _ b) (homMk_comp_eq_one r _ b)) U k

/- English proof (translation)
Use `(cls_eq_zero_iff (LB.isLB_linComb hN _ _)).symm.trans ?_` and prove the remaining obligations. Rewrite using `[cls_linComb hN, Fin.sum_univ_four]`. Establish `e : ∀ a b c d : Pic Z.left, (1 : ℤ) • a + (-1 : ℤ) • b + (-1 : ℤ) • c + (1 : ℤ) • d = a - b - c + d` using `fun a b c d ↦ by simp only [one_smul, neg_smul]; abel`. Simplify using `only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]`. Rewrite using `[e]`.

Both sides reduce to the same expression.
-/
theorem triv_quad_iff {N : LB (A ⊗ T).left} (hN : N.IsLB) {Z : Over S} (x x' : Z ⟶ A) (y : Z ⟶ T) :
    Triv (LB.LinComb N (quad x x' y) ![1, -1, -1, 1]) ↔
      evc hN (x * x') y - evc hN x y - evc hN x' y + evc hN 1 y = 0 := by
  refine (cls_eq_zero_iff (LB.isLB_linComb hN _ _)).symm.trans ?_
  rw [cls_linComb hN, Fin.sum_univ_four]
  have e : ∀ a b c d : Pic Z.left, (1 : ℤ) • a + (-1 : ℤ) • b + (-1 : ℤ) • c + (1 : ℤ) • d = a - b - c + d :=
    fun a b c d ↦ by simp only [one_smul, neg_smul]; abel
  simp only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
  rw [e]
  rfl

omit [GrpObj A] in

/- English proof (translation)
Use `set B := (Over.pullback (j ≫ T.hom)).obj A`. Establish `hB : IsPullback (pullback.fst A.hom (j ≫ T.hom)) B.hom A.hom (j ≫ T.hom)` using `IsPullback.of_hasPullback _ _`. Establish `h2 : IsPullback (fst A T).left (snd A T).left A.hom T.hom` using `IsPullback.of_hasPullback _ _`. Establish `h3 : IsPullback (fst A (A ⊗ T)).left (snd A (A ⊗ T)).left A.hom (A ⊗ T).hom` using `IsPullback.of_hasPullback _ _`. Establish `hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom` using `IsPullback.of_hasPullback _ _`.

Take `⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ T).left, m ≫ (fst A T).left = pullback.fst A.hom (j ≫ T.hom) ∧ m ≫ (snd A T).left = B.hom ≫ j` from `⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩`. Establish `hm : IsPullback m B.hom (snd A T).left j` using `IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2`. Establish `mw : m ≫ (A ⊗ T).hom = B.hom ≫ j ≫ T.hom`. Rewrite using `[← Over.w (snd A T), ← Category.assoc, m₂, Category.assoc]`. Establish `ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom)) (snd B B).left A.hom (m ≫ (A ⊗ T).hom)`.

Rewrite using `[mw]`. Conclude with `hBB.paste_horiz hB`. Take `⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (A ⊗ (A ⊗ T)).left, q ≫ (fst A (A ⊗ T)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧ q ≫ (snd A (A ⊗ T)).left = (snd B B).left ≫ m` from `⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩`. Establish `hq : IsPullback q (snd B B).left (snd A (A ⊗ T)).left m` using `IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3`. Use `⟨q, ?_, q₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Over.w (snd B B)]`. Conclude with `hq.paste_vert hm`. Use `show q ≫ (snd A (A ⊗ T)).left ≫ (fst A T).left = _`. Rewrite using `[← Category.assoc, q₂, Category.assoc, m₁]`.
-/
theorem exists_chart {X : Scheme.{0}} (j : X ⟶ T.left) :
    ∃ q : ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).left ⟶ (A ⊗ (A ⊗ T)).left,
      IsPullback q ((Over.pullback (j ≫ T.hom)).obj A ⊗ (Over.pullback (j ≫ T.hom)).obj A).hom
        (snd A (A ⊗ T) ≫ snd A T).left j ∧
      q ≫ (fst A (A ⊗ T)).left =
        (fst _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T) ≫ fst A T).left =
        (snd _ _ : _ ⟶ (Over.pullback (j ≫ T.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ T.hom) := by
  set B := (Over.pullback (j ≫ T.hom)).obj A
  have hB : IsPullback (pullback.fst A.hom (j ≫ T.hom)) B.hom A.hom (j ≫ T.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst A T).left (snd A T).left A.hom T.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst A (A ⊗ T)).left (snd A (A ⊗ T)).left A.hom (A ⊗ T).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ T).left, m ≫ (fst A T).left = pullback.fst A.hom (j ≫ T.hom) ∧
      m ≫ (snd A T).left = B.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m B.hom (snd A T).left j := IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2
  have mw : m ≫ (A ⊗ T).hom = B.hom ≫ j ≫ T.hom := by
    rw [← Over.w (snd A T), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom)) (snd B B).left A.hom
      (m ≫ (A ⊗ T).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (A ⊗ (A ⊗ T)).left,
      q ≫ (fst A (A ⊗ T)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ T.hom) ∧
      q ≫ (snd A (A ⊗ T)).left = (snd B B).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ T)).left m :=
    IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · show q ≫ (snd A (A ⊗ T)).left ≫ (fst A T).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

/- English proof (translation)
Establish `hG : Out.GlobalFnsSt` using `GlobalTheory.laws_without_cohomology.1`. Use `hA.geomConnected` as an intermediate fact. Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Establish `one₁ : ∀ {Z : Over S} (y : Z ⟶ T), evc hN (1 : Z ⟶ A) y = 0` using `fun y ↦ by`.

Establish `e` using `congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)`. Rewrite `e` using `[pull_evc, map_zero, Category.comp_id, MonObj.comp_one]`. Then use the resulting hypothesis. Establish `H` using `GlobalTheory.CubeNoeth.fibTriv_clopen N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left (fun R _ _ j ↦ by`. Take `⟨q, hq, q₀, q₁⟩` from `exists_chart (A := A) j`. Establish `hB` using `isAb_baseChange hA (j ≫ T.hom)`.

Establish `one` using `one_left_fst (A := A) (j ≫ T.hom)`. Set `B` to `(Over.pullback (j ≫ T.hom)).obj A`. Establish `: Smooth B.hom` using `hB.smooth`. Establish `: IsProper B.hom` using `hB.proper`. Establish `: GeometricallyConnected B.hom` using `hB.geomConnected`.

Establish `sm : Smooth (B ⊗ B).hom`. Express the relevant statement in the definitionally equal form `Smooth (pullback.fst B.hom B.hom ≫ B.hom)`. Use `infer_instance`. Establish `pr : IsProper (B ⊗ B).hom`. Express the relevant statement in the definitionally equal form `IsProper (pullback.fst B.hom B.hom ≫ B.hom)`.

Use `infer_instance`. Establish `gc : GeometricallyConnected (B ⊗ B).hom`. Express the relevant statement in the definitionally equal form `GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)`. Conclude with `GeometricallyConnected.comp _ _`. Establish `hN' : (LB.LinComb N (fun k ↦ q ≫ uquad A T k) ![1, -1, -1, 1]).IsLB` using `DVR.linComb_isLB _ hN _ _`.

Establish `pf : ∀ M : LB (B ⊗ B).left, M.IsLB → Nonempty (Perf (B ⊗ B).hom M)` using `fun M hM ↦ ProperFinite.nonempty_perf_of_isProper (R := R) (B ⊗ B).hom hM`. Use `⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN' (pf _ hN') (pf _ (isLB_pw hN' _)) pr (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc), fun F _ g Z π f' ↦ CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw (SmallExtLift.exists_gen …` and prove the remaining obligations. Rewrite using `[triv_pull_comp_iff]`. Use `trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inr ?_))` and prove the remaining obligations. Rewrite using `[Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]`.

Conclude with `one B`. Rewrite using `[triv_pull_comp_iff]`. Use `trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inl ?_))` and prove the remaining obligations. Rewrite using `[Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]`. Conclude with `one B)`.

Establish `all : ∀ t, t ∈ fibTriv N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left` using `fun t ↦ by`. Set `K` to `AlgebraicClosure (T.left.residueField t)`. Set `g : Spec (CommRingCat.of K) ⟶ T.left` to `Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) ≫ T.left.fromSpecResidueField t`. Set `s : Sp K ⟶ S` to `g ≫ T.hom`. Set `t' : Over.mk s ⟶ T` to `Over.homMk g rfl`.

Establish `hadd` using `hgeo K s t'`. Set `π` to `pullback.fst (snd A (A ⊗ T) ≫ snd A T).left g`. Set `f'` to `pullback.snd (snd A (A ⊗ T) ≫ snd A T).left g`. Use `⟨K, inferInstance, g, _, π, f', ⟨IsLocalRing.closedPoint K, ?_⟩, IsPullback.of_hasPullback _ _, ?_⟩` and prove the remaining obligations. Use `(Scheme.range_fromSpecResidueField t).le ⟨Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) (IsLocalRing.closedPoint K), rfl⟩` as an intermediate fact.

Conclude with `this`. Set `Zs : Over S` to `Over.mk (f' ≫ s)`. Establish `w : π ≫ (A ⊗ (A ⊗ T)).hom = f' ≫ s`. Rewrite using `[← Over.w (snd A (A ⊗ T) ≫ snd A T), ← Category.assoc, pullback.condition, Category.assoc]`. Set `x : Zs ⟶ A ⊗ (A ⊗ T)` to `Over.homMk π w`.

Set `τ : Zs ⟶ Over.mk s` to `Over.homMk f' rfl`. Establish `hx : x ≫ snd A (A ⊗ T) ≫ snd A T = τ ≫ t'` using `Over.OverMorphism.ext pullback.condition`. Establish `hM : (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t')).IsLB` using `pull_isLB hN _`. Establish `ev₁ : ∀ a : Zs ⟶ A, evc hM a τ = evc hN a (x ≫ snd A (A ⊗ T) ≫ snd A T)` using `fun a ↦ by`. Rewrite using `[evc_ev hN, lift_fst, lift_snd_assoc, hx]`.

Establish `e` using `(isAdditive_iff hM).1 hadd Zs (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T) τ`. Rewrite `e` using `[ev₁, ev₁, ev₁]`. Establish `ef : (fun k ↦ π ≫ uquad A T k) = quad (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T) (x ≫ snd A (A ⊗ T) ≫ snd A T)` using `funext fun k ↦ comp_quad x _ _ _ k`. Unfold `TrivAt`. Rewrite using `[ef, triv_quad_iff hN, one₁, e]`.

Normalize the expressions using the abelian group laws. Set `e : T ⟶ A ⊗ (A ⊗ T)` to `lift 1 (lift 1 (𝟙 T))`. Establish `e₀ : e ≫ fst A (A ⊗ T) = 1` using `by simp [e]`. Establish `e₂ : e ≫ snd A (A ⊗ T) ≫ snd A T = 𝟙 _` using `by simp [e]`. Establish `htr` using `triv_of_local hN (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left e.left (congrArg (fun q ↦ q.left) e₂) (fun Z b ↦ formal_quad (b ≫ e.left) (b ≫ T.hom) (Or.inl ?_)) (fun V ↦ ?_) (fun s ↦ H.1 (all s))`.

Use `rotate_left`. Rewrite using `[Category.assoc, ← Over.comp_left, e₀, Category.assoc]`. Both sides reduce to the same expression. Take `⟨q, hq, -⟩` from `exists_chart (A := A) V.ι`. Establish `hB` using `isAb_baseChange hA (V.ι ≫ T.hom)`.

Use `⟨_, q, _, hq, ?_⟩` and prove the remaining obligations. Rewrite using `[← Over.w (snd _ _)]`. Conclude with `surj_comp (surj_snd hG hB _) (hG _ _ hB).2`. Use `(isAdditive_iff hN).2 fun Y a a' t ↦ ?_` and prove the remaining obligations. Establish `h1 : TrivAt N (uquad A T) ![1, -1, -1, 1] (lift a (lift a' t)).left`.

Establish `h0' : TrivAt N (uquad A T) ![1, -1, -1, 1] (𝟙 _)`. Unfold `TrivAt`. Simplify using `only [Category.id_comp]`. Conclude with `htr`. Use `h0'.comp (lift a (lift a' t)).left` as an intermediate fact.

Rewrite `this` using `[Category.comp_id]`. Then use the resulting hypothesis. Establish `ef : (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) = quad a a' t` using `funext fun k ↦ by`. Rewrite using `[comp_quad]`. Simplify using `only [lift_fst, lift_snd_assoc, lift_snd]`. Establish `h2 : Triv (LB.LinComb N (quad a a' t) ![1, -1, -1, 1])`.

Establish `h1' : Triv (LB.LinComb N (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) ![1, -1, -1, 1])` using `h1`. Rewrite `h1'` using `[ef]`. Then use the resulting hypothesis. Establish `h3` using `(triv_quad_iff hN a a' t).1 h2`. Rewrite `h3` using `[one₁, add_zero, sub_sub, sub_eq_zero]`. Conclude with `h3`.
-/
theorem isAdditive_of_geomFibres (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (N : LB (A ⊗ T).left) (hN : N.IsLB) (h0 : Triv (ev N (1 : T ⟶ A) (𝟙 T)))
    (hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T),
      IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) : IsAdditive N := by
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  have := hA.geomConnected
  have := hA.smooth
  have := hA.proper
  have one₁ : ∀ {Z : Over S} (y : Z ⟶ T), evc hN (1 : Z ⟶ A) y = 0 := fun y ↦ by
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  have H := GlobalTheory.CubeNoeth.fibTriv_clopen N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left
    (fun R _ _ j ↦ by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_chart (A := A) j
    have hB := isAb_baseChange hA (j ≫ T.hom)
    have one := one_left_fst (A := A) (j ≫ T.hom)
    let B := (Over.pullback (j ≫ T.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN' : (LB.LinComb N (fun k ↦ q ≫ uquad A T k) ![1, -1, -1, 1]).IsLB := DVR.linComb_isLB _ hN _ _
    have pf : ∀ M : LB (B ⊗ B).left, M.IsLB → Nonempty (Perf (B ⊗ B).hom M) := fun M hM ↦
      ProperFinite.nonempty_perf_of_isProper (R := R) (B ⊗ B).hom hM
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN' (pf _ hN') (pf _ (isLB_pw hN' _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' ↦ CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN' (pf _ hN') ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inr ?_))
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hN _ (formal_quad _ (B.hom ≫ j ≫ T.hom) (Or.inl ?_))
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have all : ∀ t, t ∈ fibTriv N (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left := fun t ↦ by
    let K := AlgebraicClosure (T.left.residueField t)
    let g : Spec (CommRingCat.of K) ⟶ T.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) ≫ T.left.fromSpecResidueField t
    let s : Sp K ⟶ S := g ≫ T.hom
    let t' : Over.mk s ⟶ T := Over.homMk g rfl
    have hadd := hgeo K s t'
    let π := pullback.fst (snd A (A ⊗ T) ≫ snd A T).left g
    let f' := pullback.snd (snd A (A ⊗ T) ≫ snd A T).left g
    refine ⟨K, inferInstance, g, _, π, f', ⟨IsLocalRing.closedPoint K, ?_⟩, IsPullback.of_hasPullback _ _, ?_⟩
    · have := (Scheme.range_fromSpecResidueField t).le
        ⟨Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) K)) (IsLocalRing.closedPoint K), rfl⟩
      exact this
    let Zs : Over S := Over.mk (f' ≫ s)
    have w : π ≫ (A ⊗ (A ⊗ T)).hom = f' ≫ s := by
      rw [← Over.w (snd A (A ⊗ T) ≫ snd A T), ← Category.assoc, pullback.condition, Category.assoc]
    let x : Zs ⟶ A ⊗ (A ⊗ T) := Over.homMk π w
    let τ : Zs ⟶ Over.mk s := Over.homMk f' rfl
    have hx : x ≫ snd A (A ⊗ T) ≫ snd A T = τ ≫ t' := Over.OverMorphism.ext pullback.condition
    have hM : (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t')).IsLB := pull_isLB hN _
    have ev₁ : ∀ a : Zs ⟶ A, evc hM a τ = evc hN a (x ≫ snd A (A ⊗ T) ≫ snd A T) := fun a ↦ by
      rw [evc_ev hN, lift_fst, lift_snd_assoc, hx]
    have e := (isAdditive_iff hM).1 hadd Zs (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T) τ
    rw [ev₁, ev₁, ev₁] at e
    have ef : (fun k ↦ π ≫ uquad A T k) = quad (x ≫ fst A (A ⊗ T)) (x ≫ snd A (A ⊗ T) ≫ fst A T)
        (x ≫ snd A (A ⊗ T) ≫ snd A T) := funext fun k ↦ comp_quad x _ _ _ k
    unfold TrivAt
    rw [ef, triv_quad_iff hN, one₁, e]
    abel
  let e : T ⟶ A ⊗ (A ⊗ T) := lift 1 (lift 1 (𝟙 T))
  have e₀ : e ≫ fst A (A ⊗ T) = 1 := by simp [e]
  have e₂ : e ≫ snd A (A ⊗ T) ≫ snd A T = 𝟙 _ := by simp [e]
  have htr := triv_of_local hN (uquad A T) ![1, -1, -1, 1] (snd A (A ⊗ T) ≫ snd A T).left e.left
    (congrArg (fun q ↦ q.left) e₂) (fun Z b ↦ formal_quad (b ≫ e.left) (b ≫ T.hom) (Or.inl ?_))
    (fun V ↦ ?_) (fun s ↦ H.1 (all s))
  rotate_left
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_chart (A := A) V.ι
    have hB := isAb_baseChange hA (V.ι ≫ T.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2
  refine (isAdditive_iff hN).2 fun Y a a' t ↦ ?_
  have h1 : TrivAt N (uquad A T) ![1, -1, -1, 1] (lift a (lift a' t)).left := by
    have h0' : TrivAt N (uquad A T) ![1, -1, -1, 1] (𝟙 _) := by
      unfold TrivAt; simp only [Category.id_comp]; exact htr
    have := h0'.comp (lift a (lift a' t)).left
    rwa [Category.comp_id] at this
  have ef : (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) = quad a a' t := funext fun k ↦ by
    rw [comp_quad]; simp only [lift_fst, lift_snd_assoc, lift_snd]
  have h2 : Triv (LB.LinComb N (quad a a' t) ![1, -1, -1, 1]) := by
    have h1' : Triv (LB.LinComb N (fun k ↦ (lift a (lift a' t)).left ≫ uquad A T k) ![1, -1, -1, 1]) := h1
    rwa [ef] at h1'
  have h3 := (triv_quad_iff hN a a' t).1 h2
  rw [one₁, add_zero, sub_sub, sub_eq_zero] at h3
  exact h3

end GlobalTheory.AddFib
