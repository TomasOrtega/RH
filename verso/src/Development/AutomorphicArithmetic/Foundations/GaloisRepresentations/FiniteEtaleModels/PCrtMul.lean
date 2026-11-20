import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `p _ D R _ b N S s o 𝔞 𝔟 hab T l₁ l₂ h1 h2`. Establish `hmon : ∀ c, IsMonHom (o.act.act c)` using `o.act.hom`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, b', hb, habe⟩ : ∃ a ∈ 𝔞, ∃ b' ∈ 𝔟, a + b' = 1 := by`. Establish `h1m : (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟`. Rewrite using `[hab]`.

Conclude with `Submodule.mem_top`. Take `⟨a, ha, b', hb, h⟩` from `Submodule.mem_sup.1 h1m`. Conclude with `⟨a, ha, b', hb, h⟩`. Establish `split : ∀ {X : Over S} (f : X ⟶ o.A), f ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) * f ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') = f`. Introduce `X f`.

Rewrite using `[← MonObj.comp_mul, ← o.act.add, ← map_add, habe, map_one, o.act.one, Category.comp_id]`. Establish `gen : ∀ (I : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y : D.La, algebraMap (𝓞 D.F) D.O c • y ∈ wSub D I 1`. Introduce `I c hc y`. Conclude with `Submodule.subset_span ⟨c, by simpa using hc, y, rfl⟩`. Establish `mulsub : ∀ (I J : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y ∈ wSub D J 1, algebraMap (𝓞 D.F) D.O c • y ∈ wSub D (I * J) 1`.

Introduce `I J c hc y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨c', hc', z', rfl⟩` from `hz`. Rewrite using `[← mul_smul, ← map_mul]`.

Conclude with `gen _ _ (Ideal.mul_mem_mul hc (by simpa using hc')) z'`. Consider the case `zero`. Rewrite using `[smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul o' x _ hx`. Rewrite using `[← mul_smul, Algebra.commutes, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.

Establish `wmono : ∀ (I J : Ideal (𝓞 D.F)), I ≤ J → wSub D I 1 ≤ wSub D J 1`. Introduce `I J h`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `z ⟨c, hc, z', rfl⟩`. Conclude with `⟨c, by simpa using h (by simpa using hc), z', rfl⟩`.

Establish `kill : ∀ (I : Ideal (𝓞 D.F)) (l : D.La → (T ⟶ o.A)), IsEtLevOver o I 1 l → ∀ {X : Over S} (P : X ⟶ T) (y : D.La) (c : 𝓞 D.F), c ∈ I → (P ≫ l y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1`. Introduce `I l hl X P y c hc`. Rewrite using `[Category.assoc, ← hl.2.1, hl.2.2.1 _ (gen I c hc y), MonObj.comp_one]`. Use `⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[h1.1, h2.1]`. Conclude with `mul_mul_mul_comm _ _ _ _`. Simplify using `only`. Rewrite using `[h1.2.1, h2.2.1, MonObj.mul_comp]`. Simplify using `only`.

Establish `hxa : x ∈ wSub D 𝔞 1` using `wmono (𝔞 * 𝔟) 𝔞 (Ideal.mul_le_left : 𝔞 * 𝔟 ≤ 𝔞) hx`. Establish `hxb : x ∈ wSub D 𝔟 1` using `wmono (𝔞 * 𝔟) 𝔟 (Ideal.mul_le_right : 𝔞 * 𝔟 ≤ 𝔟) hx`. Rewrite using `[h1.2.2.1 x hxa, h2.2.2.1 x hxb]`. Conclude with `mul_one 1`. Simplify using `only at hy`.

Rewrite `hy` using `[MonObj.comp_mul]`. Establish `hu : Over.homMk (U` using `Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y = 1 := by`. Establish `e1` using `congrArg (· ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) hy`. Simplify using `only [MonObj.mul_comp, MonObj.one_comp, kill _ l₂ h2 _ _ _ hb, _root_.mul_one] at e1`. Rewrite using `[← split (Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y), kill _ l₁ h1 _ _ _ ha, e1, _root_.one_mul]`.

Establish `hv : Over.homMk (U` using `Over.mk (x ≫ T.hom)) (V := T) x ≫ l₂ y = 1 := by`. Rewrite `hy` using `[hu, _root_.one_mul]`. Conclude with `hy`. Establish `y1` using `(h1.2.2.2 k x).1 y hu`. Establish `y2` using `(h2.2.2.2 k x).1 y hv`.

Establish `hsplit : y = algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b' • y`. Rewrite using `[← add_smul, ← map_add, habe, map_one, one_smul]`. Rewrite using `[hsplit]`. Use `Submodule.add_mem _ (mulsub 𝔞 𝔟 a ha y y2) ?_` and prove the remaining obligations. Establish `h3` using `mulsub 𝔟 𝔞 b' hb y y1`.

Rewrite `h3` using `[mul_comm]`. Then use the resulting hypothesis. Establish `hg' : ∀ c ∈ 𝔞 * 𝔟, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1` using `fun c hc => hg c (by simpa using hc)`. Establish `hk1 : ∀ c ∈ 𝔞, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1`. Introduce `c hc`. Rewrite using `[Category.assoc, ← o.act.mul, ← map_mul]`.

Conclude with `hg' _ (Ideal.mul_mem_mul hc hb)`. Establish `hk2 : ∀ c ∈ 𝔟, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1`. Introduce `c hc`. Rewrite using `[Category.assoc, ← o.act.mul, ← map_mul, mul_comm]`. Conclude with `hg' _ (Ideal.mul_mem_mul ha hc)`.

Take `⟨y₁, hy₁⟩` from `(h1.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) (fun c hc => hk1 c (by simpa using hc))`. Take `⟨y₂, hy₂⟩` from `(h2.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) (fun c hc => hk2 c (by simpa using hc))`. Establish `e1 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') = g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')` using `by conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))]`. Rewrite using `[hk1 a ha, _root_.one_mul]`. Establish `e2 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)` using `by conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))]`.

Rewrite using `[hk2 b' hb, _root_.mul_one]`. Use `⟨algebraMap (𝓞 D.F) D.O b' • y₁ + algebraMap (𝓞 D.F) D.O a • y₂, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[h1.1, h2.1, h1.2.2.1 _ (gen 𝔞 a ha y₂), h2.2.2.1 _ (gen 𝔟 b' hb y₁), _root_.mul_one, _root_.one_mul, h1.2.1, h2.2.1, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, hy₁, hy₂, e1, e2, mul_comm]`. Conclude with `split g`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.crtMul_holds :
    CrtMul := by
  intro p _ D R _ b N S s o 𝔞 𝔟 hab T l₁ l₂ h1 h2
  have hmon : ∀ c, IsMonHom (o.act.act c) := o.act.hom
  obtain ⟨a, ha, b', hb, habe⟩ : ∃ a ∈ 𝔞, ∃ b' ∈ 𝔟, a + b' = 1 := by
    have h1m : (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟 := by
      rw [hab]
      exact Submodule.mem_top
    obtain ⟨a, ha, b', hb, h⟩ := Submodule.mem_sup.1 h1m
    exact ⟨a, ha, b', hb, h⟩
  have split : ∀ {X : Over S} (f : X ⟶ o.A),
      f ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) * f ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') = f := by
    intro X f
    rw [← MonObj.comp_mul, ← o.act.add, ← map_add, habe, map_one, o.act.one, Category.comp_id]
  have gen : ∀ (I : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y : D.La,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D I 1 := by
    intro I c hc y
    exact Submodule.subset_span ⟨c, by simpa using hc, y, rfl⟩
  have mulsub : ∀ (I J : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y ∈ wSub D J 1,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D (I * J) 1 := by
    intro I J c hc y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c', hc', z', rfl⟩ := hz
      rw [← mul_smul, ← map_mul]
      exact gen _ _ (Ideal.mul_mem_mul hc (by simpa using hc')) z'
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul o' x _ hx =>
      rw [← mul_smul, Algebra.commutes, mul_smul]
      exact Submodule.smul_mem _ _ hx
  have wmono : ∀ (I J : Ideal (𝓞 D.F)), I ≤ J → wSub D I 1 ≤ wSub D J 1 := by
    intro I J h
    apply Submodule.span_mono
    rintro z ⟨c, hc, z', rfl⟩
    exact ⟨c, by simpa using h (by simpa using hc), z', rfl⟩
  have kill : ∀ (I : Ideal (𝓞 D.F)) (l : D.La → (T ⟶ o.A)), IsEtLevOver o I 1 l →
      ∀ {X : Over S} (P : X ⟶ T) (y : D.La) (c : 𝓞 D.F), c ∈ I →
        (P ≫ l y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro I l hl X P y c hc
    rw [Category.assoc, ← hl.2.1, hl.2.2.1 _ (gen I c hc y), MonObj.comp_one]
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · dsimp only
    rw [h1.1, h2.1]
    exact mul_mul_mul_comm _ _ _ _
  · dsimp only
    rw [h1.2.1, h2.2.1, MonObj.mul_comp]
  · dsimp only
    have hxa : x ∈ wSub D 𝔞 1 := wmono (𝔞 * 𝔟) 𝔞 (Ideal.mul_le_left : 𝔞 * 𝔟 ≤ 𝔞) hx
    have hxb : x ∈ wSub D 𝔟 1 := wmono (𝔞 * 𝔟) 𝔟 (Ideal.mul_le_right : 𝔞 * 𝔟 ≤ 𝔟) hx
    rw [h1.2.2.1 x hxa, h2.2.2.1 x hxb]
    exact mul_one 1
  · dsimp only at hy
    rw [MonObj.comp_mul] at hy
    have hu : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y = 1 := by
      have e1 := congrArg (· ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) hy
      simp only [MonObj.mul_comp, MonObj.one_comp, kill _ l₂ h2 _ _ _ hb, _root_.mul_one] at e1
      rw [← split (Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y), kill _ l₁ h1 _ _ _ ha, e1, _root_.one_mul]
    have hv : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₂ y = 1 := by
      rw [hu, _root_.one_mul] at hy
      exact hy
    have y1 := (h1.2.2.2 k x).1 y hu
    have y2 := (h2.2.2.2 k x).1 y hv
    have hsplit : y = algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b' • y := by
      rw [← add_smul, ← map_add, habe, map_one, one_smul]
    rw [hsplit]
    refine Submodule.add_mem _ (mulsub 𝔞 𝔟 a ha y y2) ?_
    have h3 := mulsub 𝔟 𝔞 b' hb y y1
    rwa [mul_comm] at h3
  · have hg' : ∀ c ∈ 𝔞 * 𝔟, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hg c (by simpa using hc)
    have hk1 : ∀ c ∈ 𝔞, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul]
      exact hg' _ (Ideal.mul_mem_mul hc hb)
    have hk2 : ∀ c ∈ 𝔟, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm]
      exact hg' _ (Ideal.mul_mem_mul ha hc)
    obtain ⟨y₁, hy₁⟩ := (h1.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))
      (fun c hc => hk1 c (by simpa using hc))
    obtain ⟨y₂, hy₂⟩ := (h2.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
      (fun c hc => hk2 c (by simpa using hc))
    have e1 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))]
      rw [hk1 a ha, _root_.one_mul]
    have e2 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))]
      rw [hk2 b' hb, _root_.mul_one]
    refine ⟨algebraMap (𝓞 D.F) D.O b' • y₁ + algebraMap (𝓞 D.F) D.O a • y₂, ?_⟩
    dsimp only
    rw [h1.1, h2.1, h1.2.2.1 _ (gen 𝔞 a ha y₂), h2.2.2.1 _ (gen 𝔟 b' hb y₁), _root_.mul_one, _root_.one_mul,
      h1.2.1, h2.2.1, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, hy₁, hy₂, e1, e2, mul_comm]
    exact split g
