import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.GroupGlue

variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})

/- English proof (translation)
Use `Scheme.Cover.hom_ext (𝒰.pullback₁ t) p q fun i => ?_` and prove the remaining obligations. Conclude with `h i _ (pullback.fst t (𝒰.f i)) (pullback.snd t (𝒰.f i)) pullback.condition.symm`.
-/
theorem ext_small {T Y : Scheme.{0}} (t : T ⟶ X) {p q : T ⟶ Y}
    (h : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (g : S ⟶ T) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ t → g ≫ p = g ≫ q) :
    p = q := by
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ t) p q fun i => ?_
  exact h i _ (pullback.fst t (𝒰.f i)) (pullback.snd t (𝒰.f i)) pullback.condition.symm

/- English proof (translation)
Use `choose z hz using fun i => ex i _ (pullback.fst t (𝒰.f i)) (pullback.snd t (𝒰.f i)) pullback.condition.symm`. Establish `key : ∀ (S : Scheme.{0}) (g : S ⟶ T) (w : S ⟶ Y), P S g w → ∀ i (m : S ⟶ pullback t (𝒰.f i)), m ≫ pullback.fst t (𝒰.f i) = g → m ≫ z i = w`. Introduce `S g w hw i m hm`. Establish `h1` using `nat _ _ m _ _ (hz i)`. Rewrite `h1` using `[hm]`.

Conclude with `uniq _ _ _ _ h1 hw`. Use `⟨Scheme.Cover.glueMorphisms (𝒰.pullback₁ t) z ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Establish `h2` using `nat _ _ (pullback.snd (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j))) _ _ (hz j)`. Establish `hc : pullback.snd (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j)) ≫ pullback.fst t (𝒰.f j) = pullback.fst (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j)) ≫ pullback.fst t (𝒰.f i)` using `pullback.condition.symm`.

Rewrite `h2` using `[hc]`. Conclude with `key _ _ _ h2 i _ rfl`. Introduce `S g w hw`. Use `ext_small 𝒰 (g ≫ t) fun i S' k u hu => ?_` and prove the remaining obligations. Take `⟨m, hm⟩ : ∃ m : S' ⟶ pullback t (𝒰.f i), m ≫ pullback.fst t (𝒰.f i) = k ≫ g` from `⟨pullback.lift (k ≫ g) u (by simp [hu]), pullback.lift_fst _ _ _⟩`.

Establish `e1` using `key _ _ _ (nat _ _ k _ _ hw) i m hm`. Rewrite using `[← e1, ← Category.assoc, ← hm, Category.assoc]`. Use `congr 1`. Conclude with `Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ t) z _ i`.
-/
theorem exists_glue {T Y : Scheme.{0}} (t : T ⟶ X) (P : ∀ S : Scheme.{0}, (S ⟶ T) → (S ⟶ Y) → Prop)
    (ex : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (g : S ⟶ T) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ t → ∃ z, P S g z)
    (nat : ∀ (S S' : Scheme.{0}) (k : S' ⟶ S) (g : S ⟶ T) (z : S ⟶ Y), P S g z → P S' (k ≫ g) (k ≫ z))
    (uniq : ∀ (S : Scheme.{0}) (g : S ⟶ T) (z z' : S ⟶ Y), P S g z → P S g z' → z = z') :
    ∃ z : T ⟶ Y, ∀ (S : Scheme.{0}) (g : S ⟶ T) (z' : S ⟶ Y), P S g z' → g ≫ z = z' := by
  choose z hz using fun i => ex i _ (pullback.fst t (𝒰.f i)) (pullback.snd t (𝒰.f i)) pullback.condition.symm
  have key : ∀ (S : Scheme.{0}) (g : S ⟶ T) (w : S ⟶ Y), P S g w →
      ∀ i (m : S ⟶ pullback t (𝒰.f i)), m ≫ pullback.fst t (𝒰.f i) = g → m ≫ z i = w := by
    intro S g w hw i m hm
    have h1 := nat _ _ m _ _ (hz i)
    rw [hm] at h1
    exact uniq _ _ _ _ h1 hw
  refine ⟨Scheme.Cover.glueMorphisms (𝒰.pullback₁ t) z ?_, ?_⟩
  · intro i j
    have h2 := nat _ _ (pullback.snd (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j))) _ _ (hz j)
    have hc : pullback.snd (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j)) ≫ pullback.fst t (𝒰.f j) =
        pullback.fst (pullback.fst t (𝒰.f i)) (pullback.fst t (𝒰.f j)) ≫ pullback.fst t (𝒰.f i) :=
      pullback.condition.symm
    rw [hc] at h2
    exact key _ _ _ h2 i _ rfl
  · intro S g w hw
    refine ext_small 𝒰 (g ≫ t) fun i S' k u hu => ?_
    obtain ⟨m, hm⟩ : ∃ m : S' ⟶ pullback t (𝒰.f i), m ≫ pullback.fst t (𝒰.f i) = k ≫ g :=
      ⟨pullback.lift (k ≫ g) u (by simp [hu]), pullback.lift_fst _ _ _⟩
    have e1 := key _ _ _ (nat _ _ k _ _ hw) i m hm
    rw [← e1, ← Category.assoc, ← hm, Category.assoc]
    congr 1
    exact Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ t) z _ i

variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk ((hψ i).lift x u h.symm) ((hψ i).lift_snd _ _ _), (hψ i).lift_fst _ _ _⟩`.
-/
theorem exists_lift (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) (i : 𝒰.I₀) {S : Scheme.{0}}
    (u : S ⟶ 𝒰.X i) (x : S ⟶ G.left) (h : u ≫ 𝒰.f i = x ≫ G.hom) :
    ∃ a : Over.mk u ⟶ H i, a.left ≫ ψ i = x := ⟨Over.homMk ((hψ i).lift x u h.symm) ((hψ i).lift_snd _ _ _), (hψ i).lift_fst _ _ _⟩

/- English proof (translation)
Establish `hw` using `Over.w a`. Simplify using `only [Over.mk_hom] at hw`. Rewrite using `[Category.assoc, (hψ i).w, ← Category.assoc, hw]`.
-/
theorem base_eq (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) {i : 𝒰.I₀} {S : Scheme.{0}}
    {u : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) : u ≫ 𝒰.f i = (a.left ≫ ψ i) ≫ G.hom := by
  have hw := Over.w a
  simp only [Over.mk_hom] at hw
  rw [Category.assoc, (hψ i).w, ← Category.assoc, hw]

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext ((hψ i).hom_ext h (by rw [Over.w a, Over.w b]))`.
-/
theorem pt_ext (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) {i : 𝒰.I₀} {T : Over (𝒰.X i)}
    {a b : T ⟶ H i} (h : a.left ≫ ψ i = b.left ≫ ψ i) : a = b := Over.OverMorphism.ext ((hψ i).hom_ext h (by rw [Over.w a, Over.w b]))

def res {Y S S' : Scheme.{0}} (k : S' ⟶ S) (u : S ⟶ Y) : Over.mk (k ≫ u) ⟶ Over.mk u := Over.homMk k rfl

/- English proof (translation)
Take `⟨z, hz⟩` from `exists_glue 𝒰 G.hom (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i), a.left ≫ ψ i = g ∧ (a ≫ e i).left ≫ ψ i = w) (fun i S g u hu => by`. Take `⟨a, ha⟩` from `exists_lift hψ i u g hu`. Conclude with `⟨_, i, u, a, ha, rfl⟩)`. Use the proof step `(fun S S' k g _ ⟨i, u, a, ha, hw⟩ => ⟨i, k ≫ u, res k u ≫ a, by simp [res, ha], by simp [res, ← hw]⟩)`. Use the proof step `(fun S g w w' ⟨i, u, a, ha, hw⟩ ⟨j, v, b, hb, hw'⟩ => by`.

Rewrite using `[← hw, ← hw']`. Conclude with `he i j S u v a b (ha.trans hb.symm))`. Establish `hzG : z ≫ G.hom = G.hom`. Use `ext_small 𝒰 G.hom fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_lift hψ i u g hu`.

Rewrite using `[← Category.assoc, hz S g _ ⟨i, u, a, ha, rfl⟩, ← base_eq hψ (a ≫ e i)]`. Conclude with `hu`. Use `⟨Over.homMk z hzG, fun i => ?_⟩` and prove the remaining obligations. Establish `e1` using `hz _ (ψ i) _ ⟨i, (H i).hom, Over.homMk (𝟙 _) (by simp), by simp, rfl⟩`. Simplify using `using e1.symm`.
-/
theorem exists_endo (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) (e : ∀ i, H i ⟶ H i)
    (he : ∀ (i j : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (a : Over.mk u ⟶ H i)
      (b : Over.mk v ⟶ H j), a.left ≫ ψ i = b.left ≫ ψ j → (a ≫ e i).left ≫ ψ i = (b ≫ e j).left ≫ ψ j) :
    ∃ E : G ⟶ G, ∀ i, (e i).left ≫ ψ i = ψ i ≫ E.left := by
  obtain ⟨z, hz⟩ := exists_glue 𝒰 G.hom
    (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i) (a : Over.mk u ⟶ H i), a.left ≫ ψ i = g ∧ (a ≫ e i).left ≫ ψ i = w)
    (fun i S g u hu => by
      obtain ⟨a, ha⟩ := exists_lift hψ i u g hu
      exact ⟨_, i, u, a, ha, rfl⟩)
    (fun S S' k g _ ⟨i, u, a, ha, hw⟩ => ⟨i, k ≫ u, res k u ≫ a, by simp [res, ha], by simp [res, ← hw]⟩)
    (fun S g w w' ⟨i, u, a, ha, hw⟩ ⟨j, v, b, hb, hw'⟩ => by
      rw [← hw, ← hw']
      exact he i j S u v a b (ha.trans hb.symm))
  have hzG : z ≫ G.hom = G.hom := by
    refine ext_small 𝒰 G.hom fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_lift hψ i u g hu
    rw [← Category.assoc, hz S g _ ⟨i, u, a, ha, rfl⟩, ← base_eq hψ (a ≫ e i)]
    exact hu
  refine ⟨Over.homMk z hzG, fun i => ?_⟩
  have e1 := hz _ (ψ i) _ ⟨i, (H i).hom, Over.homMk (𝟙 _) (by simp), by simp, rfl⟩
  simpa using e1.symm

variable [∀ i, GrpObj (H i)]

def MulCompat (ψ : ∀ i, (H i).left ⟶ G.left) : Prop :=
  ∀ (i j : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (a a' : Over.mk u ⟶ H i)
    (b b' : Over.mk v ⟶ H j), a.left ≫ ψ i = b.left ≫ ψ j → a'.left ≫ ψ i = b'.left ≫ ψ j →
      (a * a').left ≫ ψ i = (b * b').left ≫ ψ j

/- English proof (translation)
Establish `h1` using `base_eq hψ (1 : Over.mk u ⟶ H i)`. Take `⟨b, hb⟩` from `exists_lift hψ j v ((1 : Over.mk u ⟶ H i).left ≫ ψ i) (h.symm.trans h1)`. Establish `h2` using `hm i j S u v 1 1 b b hb.symm hb.symm`. Rewrite `h2` using `[_root_.mul_one, ← hb]`. Establish `h3 : b * b = b` using `pt_ext hψ h2.symm`.

Rewrite `h3` using `[_root_.mul_eq_left]`. Rewrite using `[← hb, h3]`.
-/
theorem MulCompat.one (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i))
    {i j : 𝒰.I₀} {S : Scheme.{0}} (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (h : u ≫ 𝒰.f i = v ≫ 𝒰.f j) :
    (1 : Over.mk u ⟶ H i).left ≫ ψ i = (1 : Over.mk v ⟶ H j).left ≫ ψ j := by
  have h1 := base_eq hψ (1 : Over.mk u ⟶ H i)
  obtain ⟨b, hb⟩ := exists_lift hψ j v ((1 : Over.mk u ⟶ H i).left ≫ ψ i) (h.symm.trans h1)
  have h2 := hm i j S u v 1 1 b b hb.symm hb.symm
  rw [_root_.mul_one, ← hb] at h2
  have h3 : b * b = b := pt_ext hψ h2.symm
  rw [_root_.mul_eq_left] at h3
  rw [← hb, h3]

/- English proof (translation)
Establish `hu : u ≫ 𝒰.f i = v ≫ 𝒰.f j` using `by rw [base_eq hψ a, base_eq hψ b, h]`. Take `⟨c, hc⟩` from `exists_lift hψ j v ((a⁻¹).left ≫ ψ i) (hu.symm.trans (base_eq hψ a⁻¹))`. Establish `h2` using `hm i j S u v a a⁻¹ b c h hc.symm`. Rewrite `h2` using `[_root_.mul_inv_cancel, MulCompat.one hm hψ u v hu]`. Establish `h3 : b * c = 1` using `pt_ext hψ h2.symm`.

Rewrite using `[← hc, ← inv_eq_of_mul_eq_one_right h3]`.
-/
theorem MulCompat.inv (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i))
    {i j : 𝒰.I₀} {S : Scheme.{0}} {u : S ⟶ 𝒰.X i} {v : S ⟶ 𝒰.X j} (a : Over.mk u ⟶ H i)
    (b : Over.mk v ⟶ H j) (h : a.left ≫ ψ i = b.left ≫ ψ j) : (a⁻¹).left ≫ ψ i = (b⁻¹).left ≫ ψ j := by
  have hu : u ≫ 𝒰.f i = v ≫ 𝒰.f j := by rw [base_eq hψ a, base_eq hψ b, h]
  obtain ⟨c, hc⟩ := exists_lift hψ j v ((a⁻¹).left ≫ ψ i) (hu.symm.trans (base_eq hψ a⁻¹))
  have h2 := hm i j S u v a a⁻¹ b c h hc.symm
  rw [_root_.mul_inv_cancel, MulCompat.one hm hψ u v hu] at h2
  have h3 : b * c = 1 := pt_ext hψ h2.symm
  rw [← hc, ← inv_eq_of_mul_eq_one_right h3]

/- English proof (translation)
Take `⟨z, hz⟩` from `exists_glue 𝒰 (G ⊗ G).hom (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i) (a b : Over.mk u ⟶ H i), a.left ≫ ψ i = g ≫ (fst G G).left ∧ b.left ≫ ψ i = g ≫ (snd G G).left ∧ (a * b).left ≫ ψ i = w) (fun i S g u hu => by`. Take `⟨a, ha⟩` from `exists_lift hψ i u (g ≫ (fst G G).left) (by simp [hu, pullback.condition])`. Take `⟨b, hb⟩` from `exists_lift hψ i u (g ≫ (snd G G).left) (by simp [hu, pullback.condition])`. Conclude with `⟨_, i, u, a, b, ha, hb, rfl⟩)`. Use the proof step `(fun S S' k g _ ⟨i, u, a, b, ha, hb, hw⟩ => ⟨i, k ≫ u, res k u ≫ a, res k u ≫ b, by simp [res, ha], by simp [res, hb], by rw [← MonObj.comp_mul]; simp [res, ← hw]⟩)`.

Use the proof step `(fun S g w w' ⟨i, u, a, b, ha, hb, hw⟩ ⟨j, v, a', b', ha', hb', hw'⟩ => by`. Rewrite using `[← hw, ← hw']`. Conclude with `hm i j S u v a b a' b' (ha.trans ha'.symm) (hb.trans hb'.symm))`. Establish `hzG : z ≫ G.hom = (G ⊗ G).hom`. Use `ext_small 𝒰 (G ⊗ G).hom fun i S g u hu => ?_` and prove the remaining obligations.

Take `⟨a, ha⟩` from `exists_lift hψ i u (g ≫ (fst G G).left) (by simp [hu, pullback.condition])`. Take `⟨b, hb⟩` from `exists_lift hψ i u (g ≫ (snd G G).left) (by simp [hu, pullback.condition])`. Rewrite using `[← Category.assoc, hz S g _ ⟨i, u, a, b, ha, hb, rfl⟩, ← base_eq hψ (a * b)]`. Conclude with `hu`. Use `⟨Over.homMk z hzG, fun i S u a b T x y g ha hb => ?_⟩` and prove the remaining obligations.

Establish `e1` using `hz S (g ≫ (lift x y).left) _ ⟨i, u, a, b, by rw [Category.assoc, ← Over.comp_left, lift_fst]; exact ha, by rw [Category.assoc, ← Over.comp_left, lift_snd]; exact hb, rfl⟩`. Rewrite using `[← e1]`. Simplify using the standard rewrite rules.
-/
theorem exists_mul (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) :
    ∃ m : G ⊗ G ⟶ G, ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (a b : Over.mk u ⟶ H i) (T : Over X)
      (x y : T ⟶ G) (g : S ⟶ T.left), a.left ≫ ψ i = g ≫ x.left → b.left ≫ ψ i = g ≫ y.left →
        (a * b).left ≫ ψ i = g ≫ (lift x y ≫ m).left := by
  obtain ⟨z, hz⟩ := exists_glue 𝒰 (G ⊗ G).hom
    (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i) (a b : Over.mk u ⟶ H i), a.left ≫ ψ i = g ≫ (fst G G).left ∧
      b.left ≫ ψ i = g ≫ (snd G G).left ∧ (a * b).left ≫ ψ i = w)
    (fun i S g u hu => by
      obtain ⟨a, ha⟩ := exists_lift hψ i u (g ≫ (fst G G).left) (by simp [hu, pullback.condition])
      obtain ⟨b, hb⟩ := exists_lift hψ i u (g ≫ (snd G G).left) (by simp [hu, pullback.condition])
      exact ⟨_, i, u, a, b, ha, hb, rfl⟩)
    (fun S S' k g _ ⟨i, u, a, b, ha, hb, hw⟩ => ⟨i, k ≫ u, res k u ≫ a, res k u ≫ b, by simp [res, ha],
      by simp [res, hb], by rw [← MonObj.comp_mul]; simp [res, ← hw]⟩)
    (fun S g w w' ⟨i, u, a, b, ha, hb, hw⟩ ⟨j, v, a', b', ha', hb', hw'⟩ => by
      rw [← hw, ← hw']
      exact hm i j S u v a b a' b' (ha.trans ha'.symm) (hb.trans hb'.symm))
  have hzG : z ≫ G.hom = (G ⊗ G).hom := by
    refine ext_small 𝒰 (G ⊗ G).hom fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_lift hψ i u (g ≫ (fst G G).left) (by simp [hu, pullback.condition])
    obtain ⟨b, hb⟩ := exists_lift hψ i u (g ≫ (snd G G).left) (by simp [hu, pullback.condition])
    rw [← Category.assoc, hz S g _ ⟨i, u, a, b, ha, hb, rfl⟩, ← base_eq hψ (a * b)]
    exact hu
  refine ⟨Over.homMk z hzG, fun i S u a b T x y g ha hb => ?_⟩
  have e1 := hz S (g ≫ (lift x y).left) _ ⟨i, u, a, b,
    by rw [Category.assoc, ← Over.comp_left, lift_fst]; exact ha,
    by rw [Category.assoc, ← Over.comp_left, lift_snd]; exact hb, rfl⟩
  rw [← e1]
  simp

/- English proof (translation)
Take `⟨z, hz⟩` from `exists_glue 𝒰 (𝟙_ (Over X)).hom (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ (𝟙_ (Over X)).hom ∧ (1 : Over.mk u ⟶ H i).left ≫ ψ i = w) (fun i S g u hu => ⟨_, i, u, hu, rfl⟩) (fun S S' k g _ ⟨i, u, hu, hw⟩ => ⟨i, k ≫ u, by simp [hu], by`. Establish `e0 : (1 : Over.mk (k ≫ u) ⟶ H i) = res k u ≫ 1` using `(MonObj.comp_one _).symm`. Rewrite using `[e0, ← hw, Over.comp_left, Category.assoc]`. Use the proof step `rfl⟩)`. Use the proof step `(fun S g w w' ⟨i, u, hu, hw⟩ ⟨j, v, hv, hw'⟩ => by`.

Rewrite using `[← hw, ← hw']`. Conclude with `MulCompat.one hm hψ u v (hu.trans hv.symm))`. Establish `hzG : z ≫ G.hom = (𝟙_ (Over X)).hom`. Use `ext_small 𝒰 (𝟙_ (Over X)).hom fun i S g u hu => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hz S g _ ⟨i, u, hu, rfl⟩, ← base_eq hψ (1 : Over.mk u ⟶ H i)]`.

Conclude with `hu`. Use `⟨Over.homMk z hzG, fun i S u T g hg => ?_⟩` and prove the remaining obligations. Establish `e1` using `hz S (g ≫ (toUnit T).left) _ ⟨i, u, by rw [hg, Category.assoc, Over.w], rfl⟩`. Rewrite using `[← e1]`. Simplify using the standard rewrite rules.
-/
theorem exists_one (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) :
    ∃ e : 𝟙_ (Over X) ⟶ G, ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (T : Over X)
      (g : S ⟶ T.left), u ≫ 𝒰.f i = g ≫ T.hom →
        (1 : Over.mk u ⟶ H i).left ≫ ψ i = g ≫ (toUnit T ≫ e).left := by
  obtain ⟨z, hz⟩ := exists_glue 𝒰 (𝟙_ (Over X)).hom
    (fun S g w => ∃ (i : 𝒰.I₀) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ (𝟙_ (Over X)).hom ∧
      (1 : Over.mk u ⟶ H i).left ≫ ψ i = w)
    (fun i S g u hu => ⟨_, i, u, hu, rfl⟩)
    (fun S S' k g _ ⟨i, u, hu, hw⟩ => ⟨i, k ≫ u, by simp [hu], by
      have e0 : (1 : Over.mk (k ≫ u) ⟶ H i) = res k u ≫ 1 := (MonObj.comp_one _).symm
      rw [e0, ← hw, Over.comp_left, Category.assoc]
      rfl⟩)
    (fun S g w w' ⟨i, u, hu, hw⟩ ⟨j, v, hv, hw'⟩ => by
      rw [← hw, ← hw']
      exact MulCompat.one hm hψ u v (hu.trans hv.symm))
  have hzG : z ≫ G.hom = (𝟙_ (Over X)).hom := by
    refine ext_small 𝒰 (𝟙_ (Over X)).hom fun i S g u hu => ?_
    rw [← Category.assoc, hz S g _ ⟨i, u, hu, rfl⟩, ← base_eq hψ (1 : Over.mk u ⟶ H i)]
    exact hu
  refine ⟨Over.homMk z hzG, fun i S u T g hg => ?_⟩
  have e1 := hz S (g ≫ (toUnit T).left) _ ⟨i, u, by rw [hg, Category.assoc, Over.w], rfl⟩
  rw [← e1]
  simp

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (ext_small 𝒰 T.hom h)`.
-/
theorem over_ext {T : Over X} {p q : T ⟶ G}
    (h : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (g : S ⟶ T.left) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ T.hom →
      g ≫ p.left = g ≫ q.left) : p = q := Over.OverMorphism.ext (ext_small 𝒰 T.hom h)

omit [∀ i, GrpObj (H i)] in
/- English proof (translation)
The claim follows from `exists_lift hψ i u (g ≫ x.left) (by simp [h])`.
-/
theorem exists_rep (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) {i : 𝒰.I₀} {S : Scheme.{0}}
    {u : S ⟶ 𝒰.X i} {T : Over X} {g : S ⟶ T.left} (h : u ≫ 𝒰.f i = g ≫ T.hom) (x : T ⟶ G) :
    ∃ a : Over.mk u ⟶ H i, a.left ≫ ψ i = g ≫ x.left := exists_lift hψ i u (g ≫ x.left) (by simp [h])

/- English proof (translation)
Take `⟨m, hM⟩` from `exists_mul hm hψ`. Take `⟨e, hE⟩` from `exists_one hm hψ`. Take `⟨v, hv⟩` from `exists_endo hψ (fun i => ι[H i]) (fun i j S u w a b hab => by`. Rewrite using `[← Hom.inv_def, ← Hom.inv_def]`. Conclude with `MulCompat.inv hm hψ a b hab)`.

Establish `hv' : ∀ i, (ι[H i]).left ≫ ψ i = ψ i ≫ v.left` using `hv`. Establish `hI : ∀ (T : Over X) (x : T ⟶ G) (i : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (g : S ⟶ T.left) (a : Over.mk u ⟶ H i), a.left ≫ ψ i = g ≫ x.left → (a⁻¹).left ≫ ψ i = g ≫ (x ≫ v).left`. Introduce `T x i S u g a ha`. Rewrite using `[Hom.inv_def, Over.comp_left, Category.assoc, hv', ← Category.assoc, ha]`. Simplify using the standard rewrite rules.

Establish `LA : ∀ (T : Over X) (x y w : T ⟶ G), lift (lift x y ≫ m) w ≫ m = lift x (lift y w ≫ m) ≫ m`. Introduce `T x y w`. Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_rep hψ hu x`. Take `⟨b, hb⟩` from `exists_rep hψ hu y`.

Take `⟨c, hc⟩` from `exists_rep hψ hu w`. Rewrite using `[← hM i S u _ _ T _ _ g (hM i S u a b T x y g ha hb) hc, ← hM i S u _ _ T _ _ g ha (hM i S u b c T y w g hb hc), _root_.mul_assoc]`. Establish `L1 : ∀ (T : Over X) (t : T ⟶ 𝟙_ (Over X)) (x : T ⟶ G), lift (t ≫ e) x ≫ m = x`. Introduce `T t x`. Take `rfl : t = toUnit T` from `toUnit_unique _ _`.

Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_rep hψ hu x`. Rewrite using `[← hM i S u _ _ T _ _ g (hE i S u T g hu) ha, _root_.one_mul, ha]`. Establish `L2 : ∀ (T : Over X) (t : T ⟶ 𝟙_ (Over X)) (x : T ⟶ G), lift x (t ≫ e) ≫ m = x`. Introduce `T t x`.

Take `rfl : t = toUnit T` from `toUnit_unique _ _`. Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_rep hψ hu x`. Rewrite using `[← hM i S u _ _ T _ _ g ha (hE i S u T g hu), _root_.mul_one, ha]`. Establish `L3 : ∀ (T : Over X) (x : T ⟶ G), lift (x ≫ v) x ≫ m = toUnit T ≫ e`.

Introduce `T x`. Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_rep hψ hu x`. Rewrite using `[← hM i S u _ _ T _ _ g (hI T x i S u g a ha) ha, _root_.inv_mul_cancel, hE i S u T g hu]`. Establish `L4 : ∀ (T : Over X) (x : T ⟶ G), lift x (x ≫ v) ≫ m = toUnit T ≫ e`.

Introduce `T x`. Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_rep hψ hu x`. Rewrite using `[← hM i S u _ _ T _ _ g ha (hI T x i S u g a ha), _root_.mul_inv_cancel, hE i S u T g hu]`. Use `⟨{ one := e, mul := m, inv := v, one_mul := ?_, mul_one := ?_, mul_assoc := ?_, left_inv := ?_, right_inv := ?_ }, fun i => ⟨hψ i, fun T' x y x₀ y₀ hx hy => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[leftUnitor_hom]`. Use `L1 _ (fst _ _) (snd _ _) using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Rewrite using `[rightUnitor_hom]`. Use `L2 _ (snd _ _) (fst _ _) using 2` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Rewrite using `[← Category.assoc]`. Apply the tactic sequence `convert LA _ (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _) using 2 <;>`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Rewrite using `[← Category.assoc]`.

Use `congr 1`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Establish `e1` using `L3 G (𝟙 G)`. Rewrite `e1` using `[Category.id_comp]`. Then use the resulting hypothesis. Establish `e1` using `L4 G (𝟙 G)`.

Rewrite `e1` using `[Category.id_comp]`. Then use the resulting hypothesis. Use `show (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i`. Set `k : Over.mk T'.hom ⟶ T'` to `Over.homMk (𝟙 _) (by simp)`. Establish `e1` using `hM i T'.left T'.hom (k ≫ x) (k ≫ y) _ x₀ y₀ (𝟙 _) (by simp [k, hx]) (by simp [k, hy])`. Rewrite `e1` using `[← MonObj.comp_mul]`.

Simplify `e1.symm` using `[k]`.
-/
theorem exists_grpObj (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) :
    ∃ _ : GrpObj G, ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i) := by
  obtain ⟨m, hM⟩ := exists_mul hm hψ
  obtain ⟨e, hE⟩ := exists_one hm hψ
  obtain ⟨v, hv⟩ := exists_endo hψ (fun i => ι[H i]) (fun i j S u w a b hab => by
    rw [← Hom.inv_def, ← Hom.inv_def]
    exact MulCompat.inv hm hψ a b hab)
  have hv' : ∀ i, (ι[H i]).left ≫ ψ i = ψ i ≫ v.left := hv
  have hI : ∀ (T : Over X) (x : T ⟶ G) (i : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (g : S ⟶ T.left)
      (a : Over.mk u ⟶ H i), a.left ≫ ψ i = g ≫ x.left → (a⁻¹).left ≫ ψ i = g ≫ (x ≫ v).left := by
    intro T x i S u g a ha
    rw [Hom.inv_def, Over.comp_left, Category.assoc, hv', ← Category.assoc, ha]
    simp
  have LA : ∀ (T : Over X) (x y w : T ⟶ G), lift (lift x y ≫ m) w ≫ m = lift x (lift y w ≫ m) ≫ m := by
    intro T x y w
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu x
    obtain ⟨b, hb⟩ := exists_rep hψ hu y
    obtain ⟨c, hc⟩ := exists_rep hψ hu w
    rw [← hM i S u _ _ T _ _ g (hM i S u a b T x y g ha hb) hc,
      ← hM i S u _ _ T _ _ g ha (hM i S u b c T y w g hb hc), _root_.mul_assoc]
  have L1 : ∀ (T : Over X) (t : T ⟶ 𝟙_ (Over X)) (x : T ⟶ G), lift (t ≫ e) x ≫ m = x := by
    intro T t x
    obtain rfl : t = toUnit T := toUnit_unique _ _
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu x
    rw [← hM i S u _ _ T _ _ g (hE i S u T g hu) ha, _root_.one_mul, ha]
  have L2 : ∀ (T : Over X) (t : T ⟶ 𝟙_ (Over X)) (x : T ⟶ G), lift x (t ≫ e) ≫ m = x := by
    intro T t x
    obtain rfl : t = toUnit T := toUnit_unique _ _
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu x
    rw [← hM i S u _ _ T _ _ g ha (hE i S u T g hu), _root_.mul_one, ha]
  have L3 : ∀ (T : Over X) (x : T ⟶ G), lift (x ≫ v) x ≫ m = toUnit T ≫ e := by
    intro T x
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu x
    rw [← hM i S u _ _ T _ _ g (hI T x i S u g a ha) ha, _root_.inv_mul_cancel, hE i S u T g hu]
  have L4 : ∀ (T : Over X) (x : T ⟶ G), lift x (x ≫ v) ≫ m = toUnit T ≫ e := by
    intro T x
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu x
    rw [← hM i S u _ _ T _ _ g ha (hI T x i S u g a ha), _root_.mul_inv_cancel, hE i S u T g hu]
  refine ⟨{ one := e, mul := m, inv := v, one_mul := ?_, mul_one := ?_, mul_assoc := ?_, left_inv := ?_, right_inv := ?_ }, fun i => ⟨hψ i, fun T' x y x₀ y₀ hx hy => ?_⟩⟩
  · rw [leftUnitor_hom]
    convert L1 _ (fst _ _) (snd _ _) using 2
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · rw [rightUnitor_hom]
    convert L2 _ (snd _ _) (fst _ _) using 2
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · rw [← Category.assoc]
    convert LA _ (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) (snd _ _) using 2 <;>
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · have e1 := L3 G (𝟙 G)
    rwa [Category.id_comp] at e1
  · have e1 := L4 G (𝟙 G)
    rwa [Category.id_comp] at e1
  · show (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i
    let k : Over.mk T'.hom ⟶ T' := Over.homMk (𝟙 _) (by simp)
    have e1 := hM i T'.left T'.hom (k ≫ x) (k ≫ y) _ x₀ y₀ (𝟙 _) (by simp [k, hx]) (by simp [k, hy])
    rw [← MonObj.comp_mul] at e1
    simpa [k] using e1.symm

variable [GrpObj G]

/- English proof (translation)
Take `⟨-, hmul⟩` from `h i`. Set `k : Over.mk (u ≫ 𝒰.f i) ⟶ T` to `Over.homMk g (by simp [hg])`. Establish `e` using `hmul (Over.mk u) a b (k ≫ x) (k ≫ y) (by simp [k, ha]) (by simp [k, hb])`. Rewrite using `[← e, ← MonObj.comp_mul]`. Simplify using `[k]`.
-/
theorem rep_mul (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) {i : 𝒰.I₀} {S : Scheme.{0}} {u : S ⟶ 𝒰.X i}
    {a b : Over.mk u ⟶ H i} {T : Over X} {x y : T ⟶ G} {g : S ⟶ T.left} (hg : u ≫ 𝒰.f i = g ≫ T.hom)
    (ha : a.left ≫ ψ i = g ≫ x.left) (hb : b.left ≫ ψ i = g ≫ y.left) :
    (a * b).left ≫ ψ i = g ≫ (x * y).left := by
  obtain ⟨-, hmul⟩ := h i
  let k : Over.mk (u ≫ 𝒰.f i) ⟶ T := Over.homMk g (by simp [hg])
  have e := hmul (Over.mk u) a b (k ≫ x) (k ≫ y) (by simp [k, ha]) (by simp [k, hb])
  rw [← e, ← MonObj.comp_mul]
  simp [k]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `mul (𝟙_ _) 1 1`. Rewrite `h1` using `[_root_.mul_one, eq_comm, _root_.mul_eq_left]`. Simplify using `only [MonObj.one_eq_one]`. Conclude with `h1`.

Establish `h2` using `mul (A ⊗ A) (fst A A) (snd A A)`. Rewrite `h2` using `[← MonObj.mul_eq_mul]`. Rewrite using `[h2, Hom.mul_def]`. Use `congr 1`.
-/
theorem isMonHom_of_points {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ⟶ B)
    (mul : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  refine ⟨?_, ?_⟩
  · have h1 := mul (𝟙_ _) 1 1
    rw [_root_.mul_one, eq_comm, _root_.mul_eq_left] at h1
    simp only [MonObj.one_eq_one]
    exact h1
  · have h2 := mul (A ⊗ A) (fst A A) (snd A A)
    rw [← MonObj.mul_eq_mul] at h2
    rw [h2, Hom.mul_def]
    congr 1

/- English proof (translation)
Establish `hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)` using `fun i => (h i).1`. Use `choose E hE using fun x => exists_endo hψ (fun i => (α i).act x) (he x)`. Establish `hE' : ∀ x i, ((α i).act x).left ≫ ψ i = ψ i ≫ (E x).left` using `hE`. Establish `hE'' : ∀ x i {Z : Scheme.{0}} (k : G.left ⟶ Z), ((α i).act x).left ≫ ψ i ≫ k = ψ i ≫ (E x).left ≫ k`. Introduce `x i Z k`.

Rewrite using `[← Category.assoc, hE', Category.assoc]`. Establish `uniqE : ∀ F F' : G ⟶ G, (∀ i, ψ i ≫ F.left = ψ i ≫ F'.left) → F = F'`. Introduce `F F' hF`. Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_lift hψ i u g hu`.

Rewrite using `[← ha, Category.assoc, Category.assoc, hF i]`. Establish `hmon : ∀ x, IsMonHom (E x)`. Introduce `x`. Use `isMonHom_of_points (E x) fun T y z => ?_` and prove the remaining obligations. Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations.

Take `⟨a, ha⟩` from `exists_rep hψ hu y`. Take `⟨b, hb⟩` from `exists_rep hψ hu z`. Use `(α i).hom x` as an intermediate fact. Establish `hay : (a ≫ (α i).act x).left ≫ ψ i = g ≫ (y ≫ E x).left`. Rewrite using `[Over.comp_left, Category.assoc, hE', ← Category.assoc, ha]`.

Simplify using the standard rewrite rules. Establish `hbz : (b ≫ (α i).act x).left ≫ ψ i = g ≫ (z ≫ E x).left`. Rewrite using `[Over.comp_left, Category.assoc, hE', ← Category.assoc, hb]`. Simplify using the standard rewrite rules. Rewrite using `[Over.comp_left, ← Category.assoc, ← rep_mul h hu ha hb, ← rep_mul h hu hay hbz, Category.assoc, ← hE', ← Category.assoc, ← Over.comp_left, MonObj.mul_comp]`.

Use `⟨{ act := E, hom := hmon, one := ?_, mul := ?_, add := ?_ }, hE'⟩` and prove the remaining obligations. Apply `uniqE` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← hE', (α i).one]`. Simplify using the standard rewrite rules.

Introduce `x y`. Apply `uniqE` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← hE', (α i).mul]`. Simplify using `only [Over.comp_left, Category.assoc, hE', hE'']`.

Introduce `x y`. Apply `uniqE` to reduce the goal to its premises. Introduce `i`. Set `k : Over.mk (H i).hom ⟶ H i` to `Over.homMk (𝟙 _) (by simp)`. Establish `e2` using `rep_mul h (hψ i).w.symm (a := k ≫ (α i).act x) (b := k ≫ (α i).act y) (x := E x) (y := E y) (by simp [k, hE']) (by simp [k, hE'])`.

Rewrite using `[← e2, ← MonObj.comp_mul, ← (α i).add, ← hE']`. Simplify using `[k]`.
-/
theorem exists_oAct {O : Type} [CommRing O] (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) (α : ∀ i, OAct O (H i))
    (he : ∀ (x : O) (i j : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (a : Over.mk u ⟶ H i)
      (b : Over.mk v ⟶ H j), a.left ≫ ψ i = b.left ≫ ψ j →
        (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α j).act x).left ≫ ψ j) :
    ∃ A : OAct O G, ∀ x i, ((α i).act x).left ≫ ψ i = ψ i ≫ (A.act x).left := by
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := fun i => (h i).1
  choose E hE using fun x => exists_endo hψ (fun i => (α i).act x) (he x)
  have hE' : ∀ x i, ((α i).act x).left ≫ ψ i = ψ i ≫ (E x).left := hE
  have hE'' : ∀ x i {Z : Scheme.{0}} (k : G.left ⟶ Z), ((α i).act x).left ≫ ψ i ≫ k = ψ i ≫ (E x).left ≫ k := by
    intro x i Z k
    rw [← Category.assoc, hE', Category.assoc]
  have uniqE : ∀ F F' : G ⟶ G, (∀ i, ψ i ≫ F.left = ψ i ≫ F'.left) → F = F' := by
    intro F F' hF
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_lift hψ i u g hu
    rw [← ha, Category.assoc, Category.assoc, hF i]
  have hmon : ∀ x, IsMonHom (E x) := by
    intro x
    refine isMonHom_of_points (E x) fun T y z => ?_
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu y
    obtain ⟨b, hb⟩ := exists_rep hψ hu z
    have := (α i).hom x
    have hay : (a ≫ (α i).act x).left ≫ ψ i = g ≫ (y ≫ E x).left := by
      rw [Over.comp_left, Category.assoc, hE', ← Category.assoc, ha]
      simp
    have hbz : (b ≫ (α i).act x).left ≫ ψ i = g ≫ (z ≫ E x).left := by
      rw [Over.comp_left, Category.assoc, hE', ← Category.assoc, hb]
      simp
    rw [Over.comp_left, ← Category.assoc, ← rep_mul h hu ha hb, ← rep_mul h hu hay hbz, Category.assoc,
      ← hE', ← Category.assoc, ← Over.comp_left, MonObj.mul_comp]
  refine ⟨{ act := E, hom := hmon, one := ?_, mul := ?_, add := ?_ }, hE'⟩
  · apply uniqE
    intro i
    rw [← hE', (α i).one]
    simp
  · intro x y
    apply uniqE
    intro i
    rw [← hE', (α i).mul]
    simp only [Over.comp_left, Category.assoc, hE', hE'']
  · intro x y
    apply uniqE
    intro i
    let k : Over.mk (H i).hom ⟶ H i := Over.homMk (𝟙 _) (by simp)
    have e2 := rep_mul h (hψ i).w.symm (a := k ≫ (α i).act x) (b := k ≫ (α i).act y) (x := E x) (y := E y)
      (by simp [k, hE']) (by simp [k, hE'])
    rw [← e2, ← MonObj.comp_mul, ← (α i).add, ← hE']
    simp [k]

omit [∀ i, GrpObj (H i)] [GrpObj G] in
/- English proof (translation)
Use `IsZariskiLocalAtTarget.of_openCover (P := P) (𝒰 := 𝒰) (f := G.hom) fun i => ?_` and prove the remaining obligations. Establish `e0 : (hψ i).isoPullback.hom ≫ pullback.snd G.hom (𝒰.f i) = (H i).hom` using `(hψ i).isoPullback_hom_snd`. Establish `h1 : P (pullback.snd G.hom (𝒰.f i))`. Rewrite using `[← P.cancel_left_of_respectsIso (hψ i).isoPullback.hom, e0]`. Conclude with `hP i`.

Conclude with `h1`.
-/
theorem of_charts (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) (hP : ∀ i, P (H i).hom) : P G.hom := by
  refine IsZariskiLocalAtTarget.of_openCover (P := P) (𝒰 := 𝒰) (f := G.hom) fun i => ?_
  have e0 : (hψ i).isoPullback.hom ≫ pullback.snd G.hom (𝒰.f i) = (H i).hom := (hψ i).isoPullback_hom_snd
  have h1 : P (pullback.snd G.hom (𝒰.f i)) := by
    rw [← P.cancel_left_of_respectsIso (hψ i).isoPullback.hom, e0]
    exact hP i
  exact h1

/- English proof (translation)
Establish `hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)` using `fun i => (h i).1`. Establish `i1 : IsZariskiLocalAtTarget @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtTarget @Smooth`. Establish `i2'` using `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat.{0}`. Establish `i2` using `@HasAffineProperty.instIsZariskiLocalAtTarget _ _ i2'`. Establish `i3 : IsZariskiLocalAtTarget @GeometricallyConnected.{0}` using `GeometricallyConnected.eq_geometrically ▸ inferInstance`.

Establish `hcomm : ∀ (T : Over X) (x y : T ⟶ G), x * y = y * x`. Introduce `T x y`. Use `over_ext (𝒰 := 𝒰) fun i S g u hu => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `exists_rep hψ hu x`. Take `⟨b, hb⟩` from `exists_rep hψ hu y`.

Use `(hs i).comm` as an intermediate fact. Rewrite using `[← rep_mul h hu ha hb, ← rep_mul h hu hb ha, _root_.mul_comm]`. Conclude with `{ comm := ⟨by`. Establish `e1` using `hcomm _ (fst G G) (snd G G)`. Establish `e2 : (β_ G G).hom = lift (snd G G) (fst G G)`.

Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Rewrite `e1` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`. Rewrite using `[e2, ← e1]⟩,`. Use `smooth := of_charts _ hψ fun i => (hs i).smooth,`. Use `separated := of_charts _ hψ fun i => (hs i).separated,`.

Use `quasiCompact := @of_charts _ _ _ _ _ _ i2 hψ fun i => (hs i).quasiCompact,`. Use `geomConnected := of_charts _ hψ fun i => (hs i).geomConnected,`. Use `fibres := by`. Introduce `Ω _ _ p`. Take `⟨y0⟩ : Nonempty (Spec (CommRingCat.of Ω))` from `inferInstance`.

Establish `hr : Set.range p ⊆ Set.range (𝒰.f (𝒰.idx (p y0)))`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Subsingleton.elim y y0]`. Conclude with `𝒰.covers (p y0)`. Take `⟨T⟩` from `(hs (𝒰.idx (p y0))).fibres Ω (IsOpenImmersion.lift _ p hr)`.

Establish `h1` using `(isGrpPullback_pullback (H (𝒰.idx (p y0))) (IsOpenImmersion.lift _ p hr)).comp (h (𝒰.idx (p y0)))`. Rewrite `h1` using `[IsOpenImmersion.lift_fac]`. Take `⟨e, he, -⟩` from `grpPullback_iso h1 (isGrpPullback_pullback G p)`. Conclude with `⟨torusExtOfIso e T⟩ }`.
-/
theorem isSemiAbelian_of_charts (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) (hs : ∀ i, IsSemiAbelian (H i)) :
    IsSemiAbelian G := by
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := fun i => (h i).1
  have i1 : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget @Smooth
  have i2' := AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat.{0}
  have i2 := @HasAffineProperty.instIsZariskiLocalAtTarget _ _ i2'
  have i3 : IsZariskiLocalAtTarget @GeometricallyConnected.{0} :=
    GeometricallyConnected.eq_geometrically ▸ inferInstance
  have hcomm : ∀ (T : Over X) (x y : T ⟶ G), x * y = y * x := by
    intro T x y
    refine over_ext (𝒰 := 𝒰) fun i S g u hu => ?_
    obtain ⟨a, ha⟩ := exists_rep hψ hu x
    obtain ⟨b, hb⟩ := exists_rep hψ hu y
    have := (hs i).comm
    rw [← rep_mul h hu ha hb, ← rep_mul h hu hb ha, _root_.mul_comm]
  exact { comm := ⟨by
            have e1 := hcomm _ (fst G G) (snd G G)
            have e2 : (β_ G G).hom = lift (snd G G) (fst G G) := by
              apply CartesianMonoidalCategory.hom_ext <;> simp
            rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e1
            rw [e2, ← e1]⟩,
          smooth := of_charts _ hψ fun i => (hs i).smooth,
          separated := of_charts _ hψ fun i => (hs i).separated,
          quasiCompact := @of_charts _ _ _ _ _ _ i2 hψ fun i => (hs i).quasiCompact,
          geomConnected := of_charts _ hψ fun i => (hs i).geomConnected,
          fibres := by
            intro Ω _ _ p
            obtain ⟨y0⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
            have hr : Set.range p ⊆ Set.range (𝒰.f (𝒰.idx (p y0))) := by
              rintro _ ⟨y, rfl⟩
              rw [Subsingleton.elim y y0]
              exact 𝒰.covers (p y0)
            obtain ⟨T⟩ := (hs (𝒰.idx (p y0))).fibres Ω (IsOpenImmersion.lift _ p hr)
            have h1 := (isGrpPullback_pullback (H (𝒰.idx (p y0))) (IsOpenImmersion.lift _ p hr)).comp
              (h (𝒰.idx (p y0)))
            rw [IsOpenImmersion.lift_fac] at h1
            obtain ⟨e, he, -⟩ := grpPullback_iso h1 (isGrpPullback_pullback G p)
            exact ⟨torusExtOfIso e T⟩ }

end GlobalTheory.GroupGlue
