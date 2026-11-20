import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

namespace GlobalTheory.EigBasisPrime

/- English proof (translation)
Establish `unit : ∀ q ∈ S, IsUnit (algebraMap R R' q)` using `fun q hq => IsLocalization.map_units R' ⟨q, hq⟩`. Establish `inj : ∀ d : Fin m → R', ∑ i, d i • f (v i) = 0 → d = 0` using `fun d hd => by`. Take `⟨⟨q, hq⟩, hqi⟩` from `IsLocalization.exist_integer_multiples_of_finite S d`. Use `choose d' hd' using hqi`. Establish `h0 : f (∑ i, d' i • v i) = 0`.

Simplify using `only [map_sum, hs, hd', Algebra.smul_def, mul_smul]`. Rewrite using `[← Finset.smul_sum, hd, smul_zero]`. Take `⟨r, hr, h1⟩` from `uniq _ h0`. Establish `h2 : r • d' = 0` using `(hv 0 (by simp)).unique (by rw [← h1, Finset.smul_sum]; simp [mul_smul]) (by simp)`. Use function extensionality and compare the values at `i`.

Establish `h3` using `congrArg (algebraMap R R') (congrFun h2 i)`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, hd', Algebra.smul_def, Pi.zero_apply, map_zero] at h3`. Conclude with `(unit q hq).mul_right_eq_zero.1 ((unit r hr).mul_right_eq_zero.1 h3)`. Take `⟨q, hq, x, hx⟩` from `lift w`. Establish `h1 : ∀ a : O, ∃ r ∈ S, r • (a • x - χ a • x) = 0` using `fun a => uniq _ (by`.

Rewrite using `[map_sub, ha, hs, hx, smul_comm a, hw, smul_comm, sub_self])`. Use `choose r hr h1 using h1`. Take `⟨s, hsp⟩` from `Module.Finite.fg_top (R := ℤ) (M := O)`. Establish `hQ : ∏ a ∈ s, r a ∈ S` using `S.prod_mem fun a _ => hr a`. Take `⟨c, hc, -⟩` from `hv ((∏ a ∈ s, r a) • x) fun a => by`.

Establish `: a ∈ Submodule.span ℤ (s : Set O)` using `hsp ▸ Submodule.mem_top`. Proceed by induction on `this using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem r (Finset.mem_coe.1 hb)`. Rewrite using `[smul_comm b, smul_comm (χ b), ← sub_eq_zero, ← smul_sub, hk, _root_.mul_comm, mul_smul, h1, smul_zero]`.

Consider the case `zero => simp`. Consider the case `add b b' _ _ e e' => rw [add_smul, e, e', map_add, add_smul]`. Consider the case `smul k b _ e => rw [smul_assoc, e, map_zsmul, smul_assoc]`. Establish `h2` using `congrArg f hc`. Simplify using `only [map_sum, hs, hx, smul_smul] at h2`.

Take `⟨u, hu⟩` from `((unit _ hQ).mul (unit q hq)).exists_left_inv`. Establish `h3 : w = ∑ i, (u * algebraMap R R' (c i)) • f (v i)`. Simplify using `only [mul_smul u]`. Rewrite using `[← Finset.smul_sum, ← h2, smul_smul, hu, one_smul]`. Use `⟨_, h3, fun c' hc' => sub_eq_zero.1 (inj _ ?_)⟩` and prove the remaining obligations.

Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hc', ← h3, sub_self]`.
-/
theorem eig_localization {R R' O L L' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (S : Submonoid R)
    [IsLocalization S R'] [CommRing O] [Module.Finite ℤ O] [AddCommGroup L] [Module R L] [Module O L]
    [SMulCommClass O R L] [AddCommGroup L'] [Module R' L'] [Module O L'] [SMulCommClass O R' L'] (f : L →+ L')
    (hs : ∀ (r : R) x, f (r • x) = algebraMap R R' r • f x) (ha : ∀ (a : O) x, f (a • x) = a • f x)
    (lift : ∀ y, ∃ q ∈ S, ∃ x, f x = algebraMap R R' q • y) (uniq : ∀ x, f x = 0 → ∃ q ∈ S, q • x = 0)
    (χ : O →+* R) {m : ℕ} (v : Fin m → L)
    (hv : ∀ w : L, (∀ a, a • w = χ a • w) → ∃! c : Fin m → R, w = ∑ i, c i • v i)
    (w : L') (hw : ∀ a, a • w = algebraMap R R' (χ a) • w) : ∃! c : Fin m → R', w = ∑ i, c i • f (v i) := by
  classical
  have unit : ∀ q ∈ S, IsUnit (algebraMap R R' q) := fun q hq => IsLocalization.map_units R' ⟨q, hq⟩
  have inj : ∀ d : Fin m → R', ∑ i, d i • f (v i) = 0 → d = 0 := fun d hd => by
    obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples_of_finite S d
    choose d' hd' using hqi
    have h0 : f (∑ i, d' i • v i) = 0 := by
      simp only [map_sum, hs, hd', Algebra.smul_def, mul_smul]
      rw [← Finset.smul_sum, hd, smul_zero]
    obtain ⟨r, hr, h1⟩ := uniq _ h0
    have h2 : r • d' = 0 := (hv 0 (by simp)).unique
      (by rw [← h1, Finset.smul_sum]; simp [mul_smul]) (by simp)
    funext i
    have h3 := congrArg (algebraMap R R') (congrFun h2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hd', Algebra.smul_def, Pi.zero_apply,
      map_zero] at h3
    exact (unit q hq).mul_right_eq_zero.1 ((unit r hr).mul_right_eq_zero.1 h3)
  obtain ⟨q, hq, x, hx⟩ := lift w
  have h1 : ∀ a : O, ∃ r ∈ S, r • (a • x - χ a • x) = 0 := fun a => uniq _ (by
    rw [map_sub, ha, hs, hx, smul_comm a, hw, smul_comm, sub_self])
  choose r hr h1 using h1
  obtain ⟨s, hsp⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  have hQ : ∏ a ∈ s, r a ∈ S := S.prod_mem fun a _ => hr a
  obtain ⟨c, hc, -⟩ := hv ((∏ a ∈ s, r a) • x) fun a => by
    have : a ∈ Submodule.span ℤ (s : Set O) := hsp ▸ Submodule.mem_top
    induction this using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem r (Finset.mem_coe.1 hb)
      rw [smul_comm b, smul_comm (χ b), ← sub_eq_zero, ← smul_sub, hk, _root_.mul_comm, mul_smul, h1, smul_zero]
    | zero => simp
    | add b b' _ _ e e' => rw [add_smul, e, e', map_add, add_smul]
    | smul k b _ e => rw [smul_assoc, e, map_zsmul, smul_assoc]
  have h2 := congrArg f hc
  simp only [map_sum, hs, hx, smul_smul] at h2
  obtain ⟨u, hu⟩ := ((unit _ hQ).mul (unit q hq)).exists_left_inv
  have h3 : w = ∑ i, (u * algebraMap R R' (c i)) • f (v i) := by
    simp only [mul_smul u]
    rw [← Finset.smul_sum, ← h2, smul_smul, hu, one_smul]
  refine ⟨_, h3, fun c' hc' => sub_eq_zero.1 (inj _ ?_)⟩
  simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [← hc', ← h3, sub_self]

/- English proof (translation)
Introduce `E _ _ _ H R _ p _ t t' n χ m v v' hv hv'`. Use `t.semi.smooth` as an intermediate fact. Establish `: ∀ s : R, Smooth (Chart.Gs t.G s).hom` using `fun s => show Smooth (pullback.snd t.G.hom _) from inferInstance`. Set `j` to `algebraMap R (Localization.AtPrime p)`. Use `choose g hg hgu using fun x : epsR R ⟶ t.G => existsUnique_isVecOver (f := j) n.cart.1 x`.

Set `f₀ : Serre.Lie t.act → Serre.Lie t'.act` to `fun x => Serre.Lie.mk _ (g x.hom) ((hg _).isTangent n.cart x.isTangent)`. Establish `hf : ∀ x y, f₀ x = y ↔ IsVecOver j n.φ x.hom y.hom` using `fun x y => ⟨fun e => e ▸ hg _, fun e => Serre.Lie.ext (hgu _ _ e).symm⟩`. Establish `comb : ∀ (k : ℕ) (c : Fin k → R) (x : Fin k → Serre.Lie t.act), f₀ (∑ i, c i • x i) = ∑ i, j (c i) • f₀ (x i)` using `fun k c x => (hf _ _).2 ((lieComb_baseChange _ _ j t.G t'.G n.φ n.cart k (fun i => (x i).hom) _ c (fun i => (f₀ (x i)).hom) _ (fun i => hg _) ((Serre.Lie.isLieComb_iff c x _).2 rfl)).2 ((Serre.Lie.isLieComb_iff _ _ _).2 rfl))`. Set `f : Serre.Lie t.act →+ Serre.Lie t'.act` to `AddMonoidHom.mk' f₀ fun x y => by`. Simplify using `using comb 2 1 ![x, y]`.

Establish `hs : ∀ (r : R) x, f (r • x) = j r • f x` using `fun r x => by`. Express the relevant statement in the definitionally equal form `f₀ _ = _ • f₀ _`. Simplify using `using comb 1 ![r] ![x]`. Establish `ha : ∀ (a : 𝓞 E) x, f (a • x) = a • f x` using `fun a x => (hf _ _).2 (by`. Use `hg x.hom` as an intermediate fact.

Simplify using `only [IsVecOver] at this ⊢`. Express the relevant statement in the definitionally equal form `(g x.hom ≫ t'.act.act a).left ≫ _ = _ ≫ (x.hom ≫ t.act.act a).left`. Rewrite using `[Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])`. Take `⟨e, he⟩` from `LiePull.exists_pushEquiv n.cart (epsR (Localization.AtPrime p)) (spMap (algebraMap R (DualNumber (Localization.AtPrime p)))) (spMap_comp_spMap _ _).symm`. Take `⟨e₀, he₀⟩` from `LiePull.exists_pushEquiv n.cart (𝟙_ (Over (Sp (Localization.AtPrime p)))) (spMap j) (Category.id_comp _).symm`.

Establish `one : (1 : Over.mk (spMap j) ⟶ t.G).left = η[t'.G].left ≫ n.φ`. Rewrite using `[← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]`. Establish `lift : ∀ y, ∃ q ∈ p.primeCompl, ∃ x, f x = j q • y` using `fun y => by`. Take `⟨q, hq, w, hw, hwy⟩` from `Chart.tan_prime_lift p (y' := e y.hom) (Over.OverMorphism.ext (by`. Use `Eq.trans ?_ one.symm` and prove the remaining obligations.

Rewrite using `[Over.comp_left, he, ← y.isTangent]`. Conclude with `(Category.assoc _ _ _).symm))`. Use `⟨q, hq, Serre.Lie.mk _ w ((Chart.isTan_iff _).1 hw), (hf _ _).2 ?_⟩` and prove the remaining obligations. Use `congrArg (fun z => z.left) hwy` as an intermediate fact. Simplify using `only [Over.comp_left, he] at this`.

Conclude with `(Category.assoc _ _ _).trans this.symm`. Establish `uniq : ∀ x, f x = 0 → ∃ q ∈ p.primeCompl, q • x = 0` using `fun x hx => by`. Take `⟨q, hq, h⟩` from `Chart.tan_prime_uniq p (w := x.hom) ((Chart.isTan_iff _).2 x.isTangent) (Over.OverMorphism.ext (by`. Rewrite using `[← map_one e, he]`. Conclude with `((hf _ _).1 hx).symm))`.

Conclude with `⟨q, hq, Serre.Lie.ext h⟩`. Set `y : Fin m → Serre.Lie t.act` to `fun i => Serre.Lie.mk _ (v i) (hv.1 i).1`. Establish `hy : v' = fun i => (f (y i)).hom` using `funext fun i => hgu _ _ (hv' i)`. Substitute `hy` using the available equality. Use `⟨fun i => ⟨Serre.Lie.isTangent _, Serre.Lie.mem_eig_iff_left.1 fun a => ?_⟩, fun w hw => ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha, (Serre.Lie.mem_eig_iff_left (v := y i)).2 (hv.1 i).2 a, hs]`. Both sides reduce to the same expression. Use `(existsUnique_congr fun c => ?_).1 (eig_localization p.primeCompl f hs ha lift uniq χ y (fun z hz => (existsUnique_congr fun c => ?_).1 (hv.2 z.hom ⟨z.isTangent, (Serre.Lie.mem_eig_iff_left (τ := χ) (v := z)).1 hz⟩)) (Serre.Lie.mk _ w hw.1) ((Serre.Lie.mem_eig_iff_left (τ := j.co …` and prove the remaining obligations. Rewrite using `[Serre.Lie.isLieComb_iff]`. Conclude with `⟨fun h => congrArg Serre.Lie.hom h, fun h => Serre.Lie.ext h⟩`.

Conclude with `(Serre.Lie.isLieComb_iff c y _).trans ⟨fun h => Serre.Lie.ext h, fun h => congrArg Serre.Lie.hom h⟩`.
-/
theorem isEigBasis_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (t : SAB H (Sp R)) (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act χ v → (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v' := by
  intro E _ _ _ H R _ p _ t t' n χ m v v' hv hv'
  have := t.semi.smooth
  have : ∀ s : R, Smooth (Chart.Gs t.G s).hom := fun s => show Smooth (pullback.snd t.G.hom _) from inferInstance
  let j := algebraMap R (Localization.AtPrime p)
  choose g hg hgu using fun x : epsR R ⟶ t.G => existsUnique_isVecOver (f := j) n.cart.1 x
  let f₀ : Serre.Lie t.act → Serre.Lie t'.act := fun x =>
    Serre.Lie.mk _ (g x.hom) ((hg _).isTangent n.cart x.isTangent)
  have hf : ∀ x y, f₀ x = y ↔ IsVecOver j n.φ x.hom y.hom := fun x y =>
    ⟨fun e => e ▸ hg _, fun e => Serre.Lie.ext (hgu _ _ e).symm⟩
  have comb : ∀ (k : ℕ) (c : Fin k → R) (x : Fin k → Serre.Lie t.act),
      f₀ (∑ i, c i • x i) = ∑ i, j (c i) • f₀ (x i) := fun k c x =>
    (hf _ _).2 ((lieComb_baseChange _ _ j t.G t'.G n.φ n.cart k (fun i => (x i).hom) _ c (fun i => (f₀ (x i)).hom) _
      (fun i => hg _) ((Serre.Lie.isLieComb_iff c x _).2 rfl)).2 ((Serre.Lie.isLieComb_iff _ _ _).2 rfl))
  let f : Serre.Lie t.act →+ Serre.Lie t'.act := AddMonoidHom.mk' f₀ fun x y => by
    simpa using comb 2 1 ![x, y]
  have hs : ∀ (r : R) x, f (r • x) = j r • f x := fun r x => by
    change f₀ _ = _ • f₀ _
    simpa using comb 1 ![r] ![x]
  have ha : ∀ (a : 𝓞 E) x, f (a • x) = a • f x := fun a x => (hf _ _).2 (by
    have := hg x.hom
    simp only [IsVecOver] at this ⊢
    change (g x.hom ≫ t'.act.act a).left ≫ _ = _ ≫ (x.hom ≫ t.act.act a).left
    rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, this, Category.assoc, Over.comp_left])
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv n.cart (epsR (Localization.AtPrime p))
    (spMap (algebraMap R (DualNumber (Localization.AtPrime p)))) (spMap_comp_spMap _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv n.cart (𝟙_ (Over (Sp (Localization.AtPrime p)))) (spMap j)
    (Category.id_comp _).symm
  have one : (1 : Over.mk (spMap j) ⟶ t.G).left = η[t'.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have lift : ∀ y, ∃ q ∈ p.primeCompl, ∃ x, f x = j q • y := fun y => by
    obtain ⟨q, hq, w, hw, hwy⟩ := Chart.tan_prime_lift p (y' := e y.hom) (Over.OverMorphism.ext (by
      refine Eq.trans ?_ one.symm
      rw [Over.comp_left, he, ← y.isTangent]
      exact (Category.assoc _ _ _).symm))
    refine ⟨q, hq, Serre.Lie.mk _ w ((Chart.isTan_iff _).1 hw), (hf _ _).2 ?_⟩
    have := congrArg (fun z => z.left) hwy
    simp only [Over.comp_left, he] at this
    exact (Category.assoc _ _ _).trans this.symm
  have uniq : ∀ x, f x = 0 → ∃ q ∈ p.primeCompl, q • x = 0 := fun x hx => by
    obtain ⟨q, hq, h⟩ := Chart.tan_prime_uniq p (w := x.hom) ((Chart.isTan_iff _).2 x.isTangent)
      (Over.OverMorphism.ext (by
        rw [← map_one e, he]
        exact ((hf _ _).1 hx).symm))
    exact ⟨q, hq, Serre.Lie.ext h⟩
  let y : Fin m → Serre.Lie t.act := fun i => Serre.Lie.mk _ (v i) (hv.1 i).1
  have hy : v' = fun i => (f (y i)).hom := funext fun i => hgu _ _ (hv' i)
  subst hy
  refine ⟨fun i => ⟨Serre.Lie.isTangent _, Serre.Lie.mem_eig_iff_left.1 fun a => ?_⟩, fun w hw => ?_⟩
  · rw [← ha, (Serre.Lie.mem_eig_iff_left (v := y i)).2 (hv.1 i).2 a, hs]
    rfl
  · refine (existsUnique_congr fun c => ?_).1 (eig_localization p.primeCompl f hs ha lift uniq χ y
      (fun z hz => (existsUnique_congr fun c => ?_).1
        (hv.2 z.hom ⟨z.isTangent, (Serre.Lie.mem_eig_iff_left (τ := χ) (v := z)).1 hz⟩))
      (Serre.Lie.mk _ w hw.1) ((Serre.Lie.mem_eig_iff_left (τ := j.comp χ) (v := Serre.Lie.mk _ w hw.1)).2 hw.2))
    · rw [Serre.Lie.isLieComb_iff]
      exact ⟨fun h => congrArg Serre.Lie.hom h, fun h => Serre.Lie.ext h⟩
    · exact (Serre.Lie.isLieComb_iff c y _).trans ⟨fun h => Serre.Lie.ext h, fun h => congrArg Serre.Lie.hom h⟩

end GlobalTheory.EigBasisPrime
