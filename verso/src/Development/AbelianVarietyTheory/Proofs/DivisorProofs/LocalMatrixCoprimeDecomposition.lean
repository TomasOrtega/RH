import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {S : Scheme.{0}}

def postHom {T A : Over S} [GrpObj A] (φ : A ⟶ A) [IsMonHom φ] : (T ⟶ A) →* (T ⟶ A) where
  toFun f := f ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' f g := MonObj.mul_comp _ _ _

/- English proof (translation)
Introduce `c a`. Rewrite using `[GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => F c a) (fun c c' => hF1 c c' a) c, GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => G c a) (fun c c' => hG1 c c' a) c]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[GlobalTheory.LatticeTorsion.eq_prod_zpow bL (F (bM i)) (hF2 _) a, GlobalTheory.LatticeTorsion.eq_prod_zpow bL (G (bM i)) (hG2 _) a]`.

Simplify using `only [h]`.
-/
theorem bilin_ext {M La Q I J : Type} [AddCommGroup M] [AddCommGroup La] [CommGroup Q] [Fintype I] [Fintype J]
    (bM : Module.Basis I ℤ M) (bL : Module.Basis J ℤ La) (F G : M → La → Q)
    (hF1 : ∀ c c' a, F (c + c') a = F c a * F c' a) (hF2 : ∀ c a a', F c (a + a') = F c a * F c a')
    (hG1 : ∀ c c' a, G (c + c') a = G c a * G c' a) (hG2 : ∀ c a a', G c (a + a') = G c a * G c a')
    (h : ∀ i j, F (bM i) (bL j) = G (bM i) (bL j)) : ∀ c a, F c a = G c a := by
  intro c a
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => F c a) (fun c c' => hF1 c c' a) c,
    GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => G c a) (fun c c' => hG1 c c' a) c]
  refine Finset.prod_congr rfl fun i _ => ?_
  beta_reduce
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bL (F (bM i)) (hF2 _) a, GlobalTheory.LatticeTorsion.eq_prod_zpow bL (G (bM i)) (hG2 _) a]
  simp only [h]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Kil {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (f : T ⟶ o.A) : Prop :=
  ∀ c ∈ w0 ^ r, f ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1

/- English proof (translation)
Introduce `c hc` and use `by rw [Category.assoc, hf c hc, MonObj.comp_one]`.
-/
theorem Kil.comp {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T T' : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (h : T' ⟶ T) : Kil o w0 r (h ≫ f) := fun c hc => by
  rw [Category.assoc, hf c hc, MonObj.comp_one]

/- English proof (translation)
Introduce `c hc` and use `by haveI := o.act.hom d rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, hf c hc, MonObj.one_comp]`.
-/
theorem Kil.act {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (d : D.O) : Kil o w0 r (f ≫ o.act.act d) := fun c hc => by
  haveI := o.act.hom d
  rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, hf c hc, MonObj.one_comp]

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨c, hc, z', rfl⟩` from `hz`. Rewrite using `[hlin]`.

Conclude with `hk z' c hc`. Consider the case `zero`. Establish `h0` using `hadd 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `(mul_eq_left.1 h0.symm)`.

Consider the case `add x y _ _ hx hy => rw [hadd, hx, hy, _root_.mul_one]`. Consider the case `smul d x _ hx => haveI := o.act.hom d`. Rewrite using `[hlin, hx, MonObj.one_comp]`.
-/
theorem vanish {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} (l : D.La → (T ⟶ o.A)) (hadd : ∀ x y, l (x + y) = l x * l y)
    (hlin : ∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) (hk : ∀ a, Kil o w0 r (l a)) :
    ∀ x ∈ wSub D w0 r, l x = 1 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, z', rfl⟩ := hz
    rw [hlin]
    exact hk z' c hc
  | zero =>
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact (mul_eq_left.1 h0.symm)
  | add x y _ _ hx hy => rw [hadd, hx, hy, _root_.mul_one]
  | smul d x _ hx =>
    haveI := o.act.hom d
    rw [hlin, hx, MonObj.one_comp]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev

open RepLat in

/- English proof (translation)
Introduce `p _ D R _ b N w0 r _ S _ s o K κ hKf hKe hκ hK`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Use `haveI := D.freeO`. Use `haveI := D.finO`.

Use `haveI := hKf`. Use `haveI := hKe`. Establish `hκ' : Kil o w0 r κ` using `hκ`. Establish `hcan : ∀ {T : Over S} (v v' : T ⟶ K), v ≫ κ = v' ≫ κ → v = v'` using `fun v v' e => (hK _ (v' ≫ κ) (hκ'.comp v')).unique e rfl`. Establish `hfac : ∀ {T : Over S} (f : T ⟶ o.A), Kil o w0 r f → ∃ u : T ⟶ K, u ≫ κ = f` using `fun f hf => (hK _ f hf).exists`.

Set `bb` to `Module.finBasis ℤ D.La`. Set `n` to `Module.finrank ℤ D.La`. Set `bO` to `Module.finBasis ℤ D.O`. Set `Z₀` to `Out.powObj K n`. Set `x : Fin n → (Z₀ ⟶ o.A)` to `fun i => Out.powPr K i ≫ κ`.

Set `et₀ : D.La → (Z₀ ⟶ o.A)` to `fun a => ∏ i, x i ^ (bb.repr a i)`. Establish `hadd : ∀ a c, et₀ (a + c) = et₀ a * et₀ c` using `fun a c => by`. Simplify using `only [et₀, map_add, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]`. Establish `hb : ∀ i, et₀ (bb i) = x i` using `fun i => by`. Simplify using `only [et₀, Module.Basis.repr_self]`.

Rewrite using `[Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]`. Simplify using the standard rewrite rules. Establish `hkil : ∀ a, Kil o w0 r (et₀ a)` using `fun a c hc => by haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)`. Express the relevant statement in the definitionally equal form `postHom (T := Z₀) _ (∏ i, x i ^ (bb.repr a i)) = 1`. Rewrite using `[map_prod]`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow]`. Express the relevant statement in the definitionally equal form `(x i ≫ _) ^ _ = 1`. Rewrite using `[(hκ'.comp (Out.powPr K i)) c hc, one_zpow]`. Use `haveI hZf : IsFinite Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @IsFinite K hKf n`.

Use `haveI hZe : Etale Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @Etale K hKe n`. Establish `c1 : ClopenCond Z₀ fun _ h => ∀ (c : D.O) a, h ≫ et₀ (c • a) = h ≫ (et₀ a ≫ o.act.act c)`. Establish `hfin : ClopenCond Z₀ fun _ h => ∀ ji : Fin (Module.finrank ℤ D.O) × Fin n, h ≫ et₀ (bO ji.1 • bb ji.2) = h ≫ (et₀ (bb ji.2) ≫ o.act.act (bO ji.1))`. Use `ClopenCond.forall_finite fun ji => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `hfac _ (hkil (bO ji.1 • bb ji.2))`.

Take `⟨u', hu'⟩` from `hfac _ ((hkil (bb ji.2)).act (bO ji.1))`. Use `(clopenCond_eq u u').congr fun T' h => ?_` and prove the remaining obligations. Rewrite using `[← hu, ← hu', ← Category.assoc, ← Category.assoc]`. Conclude with `⟨hcan _ _, fun e => by rw [e]⟩`. Use `hfin.congr fun T' h => ⟨fun H ji => H _ _, fun H => ?_⟩` and prove the remaining obligations.

Use `bilin_ext bO bb (fun c a => h ≫ et₀ (c • a)) (fun c a => h ≫ (et₀ a ≫ o.act.act c)) (fun c c' a => by beta_reduce; rw [add_smul, hadd, MonObj.comp_mul]) (fun c a a' => by beta_reduce; rw [smul_add, hadd, MonObj.comp_mul]) (fun c c' a => by beta_reduce; rw [o.act.add, MonObj.comp_ …` and prove the remaining obligations. Rewrite using `[hadd, MonObj.mul_comp, MonObj.comp_mul])`. Use the proof step `(fun j i => H (j, i))`. Take `⟨U, hU, HU⟩` from `c1`. Take `⟨V, i, hV1, hV2, hmono, Hi⟩` from `exists_sub U hU`.

Establish `hi` using `(HU V i).2 ((Hi V i).2 ⟨𝟙 V, Category.id_comp i⟩)`. Establish `hVadd : ∀ a c, i ≫ et₀ (a + c) = (i ≫ et₀ a) * (i ≫ et₀ c)` using `fun a c => by`. Rewrite using `[hadd, MonObj.comp_mul]`. Establish `hVlin : ∀ (c : D.O) a, i ≫ et₀ (c • a) = (i ≫ et₀ a) ≫ o.act.act c` using `fun c a => by`. Rewrite using `[hi, Category.assoc]`.

Use `⟨V, fun a => i ≫ et₀ a, hV1, hV2, hVadd, hVlin, vanish _ hVadd hVlin fun a => (hkil a).comp i, fun T l hladd hllin hlw => ?_⟩` and prove the remaining obligations. Establish `hlk : ∀ a, Kil o w0 r (l a)` using `fun a c hc => by`. Rewrite using `[← hllin]`. Conclude with `hlw _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)`. Use `choose y hy using fun j : Fin n => hfac _ (hlk (bb j))`.

Set `h : T ⟶ Z₀` to `(Out.powIsLimit K n).lift (Fan.mk T y)`. Establish `hh : ∀ j, h ≫ Out.powPr K j = y j` using `fun j => (Out.powIsLimit K n).fac (Fan.mk T y) ⟨j⟩`. Establish `hhe : ∀ a, h ≫ et₀ a = l a` using `fun a => by`. Rewrite using `[GlobalTheory.LatticeTorsion.eq_prod_zpow bb (fun a => h ≫ et₀ a) (fun a c => by rw [hadd, MonObj.comp_mul]) a, GlobalTheory.LatticeTorsion.eq_prod_zpow bb l hladd a]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[hb, ← hy j, ← hh j, Category.assoc]`. Establish `hext : ∀ u u' : T ⟶ Z₀, (∀ a, u ≫ et₀ a = u' ≫ et₀ a) → u = u'` using `fun u u' e => (Out.powIsLimit K n).hom_ext fun ⟨j⟩ => by`. Use `e (bb j)` as an intermediate fact. Rewrite `this` using `[hb]`.

Conclude with `hcan _ _ (by simp only [x, Category.assoc] at this; exact this)`. Take `⟨h', hh'⟩` from `(Hi T h).1 ((HU T h).1 fun c a => by rw [hhe, hllin, ← hhe a, Category.assoc])`. Use `⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hhe], fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `(cancel_mono i).1 (hext _ _ fun a => by`. Rewrite using `[Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hhe])`.
-/
theorem exists_finiteEtale_linTorsHom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ x y, et (x + y) = et x * et y) ∧ (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) ∧ (∀ x ∈ wSub D w0 r, et x = 1) ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), (∀ x y, l (x + y) = l x * l y) → (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, l x = 1) → ∃! h : T ⟶ Z, ∀ y, h ≫ et y = l y := by
  intro p _ D R _ b N w0 r _ S _ s o K κ hKf hKe hκ hK
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI := hKf
  haveI := hKe
  have hκ' : Kil o w0 r κ := hκ
  have hcan : ∀ {T : Over S} (v v' : T ⟶ K), v ≫ κ = v' ≫ κ → v = v' := fun v v' e =>
    (hK _ (v' ≫ κ) (hκ'.comp v')).unique e rfl
  have hfac : ∀ {T : Over S} (f : T ⟶ o.A), Kil o w0 r f → ∃ u : T ⟶ K, u ≫ κ = f := fun f hf =>
    (hK _ f hf).exists
  let bb := Module.finBasis ℤ D.La
  let n := Module.finrank ℤ D.La
  let bO := Module.finBasis ℤ D.O
  let Z₀ := Out.powObj K n
  let x : Fin n → (Z₀ ⟶ o.A) := fun i => Out.powPr K i ≫ κ
  let et₀ : D.La → (Z₀ ⟶ o.A) := fun a => ∏ i, x i ^ (bb.repr a i)
  have hadd : ∀ a c, et₀ (a + c) = et₀ a * et₀ c := fun a c => by
    simp only [et₀, map_add, Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et₀ (bb i) = x i := fun i => by
    simp only [et₀, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  have hkil : ∀ a, Kil o w0 r (et₀ a) := fun a c hc => by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    change postHom (T := Z₀) _ (∏ i, x i ^ (bb.repr a i)) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_zpow]
    change (x i ≫ _) ^ _ = 1
    rw [(hκ'.comp (Out.powPr K i)) c hc, one_zpow]
  haveI hZf : IsFinite Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @IsFinite K hKf n
  haveI hZe : Etale Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @Etale K hKe n
  have c1 : ClopenCond Z₀ fun _ h => ∀ (c : D.O) a, h ≫ et₀ (c • a) = h ≫ (et₀ a ≫ o.act.act c) := by
    have hfin : ClopenCond Z₀ fun _ h => ∀ ji : Fin (Module.finrank ℤ D.O) × Fin n,
        h ≫ et₀ (bO ji.1 • bb ji.2) = h ≫ (et₀ (bb ji.2) ≫ o.act.act (bO ji.1)) := by
      refine ClopenCond.forall_finite fun ji => ?_
      obtain ⟨u, hu⟩ := hfac _ (hkil (bO ji.1 • bb ji.2))
      obtain ⟨u', hu'⟩ := hfac _ ((hkil (bb ji.2)).act (bO ji.1))
      refine (clopenCond_eq u u').congr fun T' h => ?_
      rw [← hu, ← hu', ← Category.assoc, ← Category.assoc]
      exact ⟨hcan _ _, fun e => by rw [e]⟩
    refine hfin.congr fun T' h => ⟨fun H ji => H _ _, fun H => ?_⟩
    refine bilin_ext bO bb (fun c a => h ≫ et₀ (c • a)) (fun c a => h ≫ (et₀ a ≫ o.act.act c))
      (fun c c' a => by beta_reduce; rw [add_smul, hadd, MonObj.comp_mul])
      (fun c a a' => by beta_reduce; rw [smul_add, hadd, MonObj.comp_mul])
      (fun c c' a => by beta_reduce; rw [o.act.add, MonObj.comp_mul, MonObj.comp_mul])
      (fun c a a' => by
        beta_reduce
        haveI := o.act.hom c
        rw [hadd, MonObj.mul_comp, MonObj.comp_mul])
      (fun j i => H (j, i))
  obtain ⟨U, hU, HU⟩ := c1
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU V i).2 ((Hi V i).2 ⟨𝟙 V, Category.id_comp i⟩)
  have hVadd : ∀ a c, i ≫ et₀ (a + c) = (i ≫ et₀ a) * (i ≫ et₀ c) := fun a c => by
    rw [hadd, MonObj.comp_mul]
  have hVlin : ∀ (c : D.O) a, i ≫ et₀ (c • a) = (i ≫ et₀ a) ≫ o.act.act c := fun c a => by
    rw [hi, Category.assoc]
  refine ⟨V, fun a => i ≫ et₀ a, hV1, hV2, hVadd, hVlin,
    vanish _ hVadd hVlin fun a => (hkil a).comp i, fun T l hladd hllin hlw => ?_⟩
  have hlk : ∀ a, Kil o w0 r (l a) := fun a c hc => by
    rw [← hllin]
    exact hlw _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)
  choose y hy using fun j : Fin n => hfac _ (hlk (bb j))
  let h : T ⟶ Z₀ := (Out.powIsLimit K n).lift (Fan.mk T y)
  have hh : ∀ j, h ≫ Out.powPr K j = y j := fun j => (Out.powIsLimit K n).fac (Fan.mk T y) ⟨j⟩
  have hhe : ∀ a, h ≫ et₀ a = l a := fun a => by
    rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bb (fun a => h ≫ et₀ a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
      GlobalTheory.LatticeTorsion.eq_prod_zpow bb l hladd a]
    refine Finset.prod_congr rfl fun j _ => ?_
    beta_reduce
    rw [hb, ← hy j, ← hh j, Category.assoc]
  have hext : ∀ u u' : T ⟶ Z₀, (∀ a, u ≫ et₀ a = u' ≫ et₀ a) → u = u' := fun u u' e =>
    (Out.powIsLimit K n).hom_ext fun ⟨j⟩ => by
      have := e (bb j)
      rw [hb] at this
      exact hcan _ _ (by simp only [x, Category.assoc] at this; exact this)
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 fun c a => by rw [hhe, hllin, ← hhe a, Category.assoc])
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hhe], fun g hg => ?_⟩
  exact (cancel_mono i).1 (hext _ _ fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hhe])

end GlobalTheory.UPel.HT.EtLev
